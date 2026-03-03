use anyhow::{Context, Result, bail};
use clap::Parser as ClapParser;
use goblin::mach::load_command::CommandVariant;
use goblin::mach::{
  Mach,
  constants::cputype::{CPU_TYPE_ARM64, CPU_TYPE_ARM64_32, CPU_TYPE_X86_64},
};
use memchr::memmem;
use scroll::{LE, Pread};
use std::fs::{self, File};
use std::io;
use std::path::{Path, PathBuf};
use walkdir::WalkDir;

const PATCH_RETURN_FALSE: &[u8] = &[0xE0, 0x03, 0x1F, 0x2A, 0xC0, 0x03, 0x5F, 0xD6];
const PATCH_PERFORM_DEFAULT: &[u8] = &[
  0x29, 0x00, 0x80, 0xD2, 0x09, 0x01, 0x00, 0xF9, 0x1F, 0x05, 0x00, 0xF9, 0xC0, 0x03, 0x5F, 0xD6,
];
const PINNING_ERROR_STRINGS: &[&[u8]] = &[
  b"Failing request to ",
  b"No certificate in the chain matched one of the expected public keys",
];

#[derive(ClapParser)]
#[command(about = "Certificate pinning are sucks")]
struct Cli {
  input: PathBuf,
  #[arg(short, long)]
  output: Option<PathBuf>,
}

#[derive(Clone, Copy)]
enum PtrFmt {
  Chained64,
  Chained64Offset,
  Raw,
}

struct MachO {
  classlist: Option<SectionInfo>,
  image_base: u64,
  ptr_fmt: PtrFmt,
  segments: Vec<Segment>,
  text: Option<SectionInfo>,
}

struct SectionInfo {
  offset: u32,
  size: u64,
}

#[derive(Clone)]
struct Segment {
  fileoff: u64,
  filesize: u64,
  vmaddr: u64,
  vmsize: u64,
}

impl MachO {
  fn parse(data: &[u8]) -> Result<Self> {
    let parsed = goblin::mach::MachO::parse(data, 0)
      .map_err(|e| anyhow::anyhow!("failed to parse mach-o: {e}"))?;
    let segments: Vec<Segment> = parsed
      .segments
      .iter()
      .map(|seg| Segment {
        fileoff: seg.fileoff,
        filesize: seg.filesize,
        vmaddr: seg.vmaddr,
        vmsize: seg.vmsize,
      })
      .collect();
    let image_base = parsed
      .segments
      .iter()
      .find(|seg| seg.name().is_ok_and(|name| name == "__TEXT"))
      .map_or_else(
        || segments.iter().map(|seg| seg.vmaddr).min().unwrap_or(0),
        |seg| seg.vmaddr,
      );
    let mut text = None;
    let mut classlist = None;

    for seg in &parsed.segments {
      if let Ok(sections) = seg.sections() {
        for (section, _) in sections {
          let sname = section.name().unwrap_or("");
          let seg_name = section.segname().unwrap_or("");

          if sname == "__text" && seg_name == "__TEXT" {
            text = Some(SectionInfo {
              offset: section.offset,
              size: section.size,
            });
          }

          if sname == "__objc_classlist" {
            classlist = Some(SectionInfo {
              offset: section.offset,
              size: section.size,
            });
          }
        }
      }
    }

    let mut ptr_fmt = PtrFmt::Raw;

    for lc in &parsed.load_commands {
      if let CommandVariant::DyldChainedFixups(ref cmd) = lc.command {
        let dataoff = usize::try_from(cmd.dataoff)?;
        let starts_offset: u32 = data
          .pread_with(dataoff + 4, LE)
          .context("dyld chained fixups: failed to read starts_offset")?;
        let starts = dataoff + usize::try_from(starts_offset)?;
        let seg_count: u32 = data
          .pread_with(starts, LE)
          .context("dyld chained fixups: failed to read seg_count")?;

        for i in 0..usize::try_from(seg_count)? {
          let seg_info_off: u32 = data
            .pread_with(starts + 4 + i * 4, LE)
            .context("dyld chained fixups: failed to read seg_info_offset")?;

          if seg_info_off == 0 {
            continue;
          }

          let base = starts + usize::try_from(seg_info_off)?;
          let pf: u16 = data
            .pread_with(base + 6, LE)
            .context("dyld chained fixups: failed to read pointer_format")?;

          ptr_fmt = match pf {
            2 => PtrFmt::Chained64,
            6 => PtrFmt::Chained64Offset,
            _ => bail!("unsupported dyld chained fixup pointer format: {pf}"),
          };

          break;
        }

        break;
      }
    }

    Ok(Self {
      classlist,
      image_base,
      ptr_fmt,
      segments,
      text,
    })
  }

  fn vm2off(&self, vmaddr: u64) -> Option<usize> {
    for seg in &self.segments {
      if vmaddr >= seg.vmaddr && vmaddr < seg.vmaddr + seg.vmsize {
        return usize::try_from(vmaddr - seg.vmaddr + seg.fileoff).ok();
      }
    }

    None
  }

  fn off2vm(&self, fileoff: usize) -> Option<u64> {
    let f = u64::try_from(fileoff).ok()?;

    for seg in &self.segments {
      if f >= seg.fileoff && f < seg.fileoff + seg.filesize {
        return Some(f - seg.fileoff + seg.vmaddr);
      }
    }

    None
  }

  const fn decode_ptr(&self, raw: u64) -> u64 {
    if raw == 0 {
      return 0;
    }

    match self.ptr_fmt {
      PtrFmt::Raw => raw,
      PtrFmt::Chained64 => {
        if raw >> 63 != 0 {
          return 0;
        }

        let target = raw & 0xF_FFFF_FFFF;
        let high8 = (raw >> 36) & 0xFF;

        (high8 << 56) | target
      }
      PtrFmt::Chained64Offset => {
        if raw >> 63 != 0 {
          return 0;
        }

        let target = raw & 0xF_FFFF_FFFF;
        let high8 = (raw >> 36) & 0xFF;

        self.image_base + ((high8 << 56) | target)
      }
    }
  }

  fn text_file_range(&self) -> Option<(usize, usize)> {
    let t = self.text.as_ref()?;
    let start = usize::try_from(t.offset).ok()?;
    let size = usize::try_from(t.size).ok()?;
    let end = start.checked_add(size)?;

    Some((start, end))
  }
}

fn read_u32_le(data: &[u8], off: usize) -> Option<u32> {
  data.pread_with(off, LE).ok()
}

fn read_u64_le(data: &[u8], off: usize) -> Option<u64> {
  data.pread_with(off, LE).ok()
}

fn read_i32_le(data: &[u8], off: usize) -> Option<i32> {
  data.pread_with(off, LE).ok()
}

fn read_cstring(data: &[u8], off: usize) -> Option<&str> {
  let bytes = data.get(off..)?;
  let end = memchr::memchr(0, bytes).unwrap_or(bytes.len());

  std::str::from_utf8(&bytes[..end]).ok()
}

fn format_mb(bytes: u64) -> String {
  let whole = bytes / (1024 * 1024);
  let frac = (bytes % (1024 * 1024)) * 10 / (1024 * 1024);

  format!("{whole}.{frac}")
}

fn choose_macho_slice_range(data: &[u8]) -> Result<(usize, usize)> {
  match Mach::parse(data).context("failed to detect mach-o container type")? {
    Mach::Binary(_) => Ok((0, data.len())),
    Mach::Fat(fat) => {
      let selected = if let Some(arch) = fat.find_cputype(CPU_TYPE_ARM64)? {
        arch
      } else if let Some(arch) = fat.find_cputype(CPU_TYPE_ARM64_32)? {
        arch
      } else if let Some(arch) = fat.find_cputype(CPU_TYPE_X86_64)? {
        arch
      } else {
        fat
          .iter_arches()
          .next()
          .transpose()?
          .context("fat mach-o has no architecture entry")?
      };
      let start = usize::try_from(selected.offset)?;
      let size = usize::try_from(selected.size)?;
      let end = start
        .checked_add(size)
        .context("fat mach-o architecture range overflow")?;

      if end > data.len() {
        bail!("fat mach-o architecture range is out of bounds");
      }

      eprintln!(
        "fat mach-o detected; selected cputype=0x{:X}, slice=0x{:X}..0x{:X}",
        selected.cputype, start, end
      );

      Ok((start, end))
    }
  }
}

fn vmaddr_add_rel(base: u64, rel: i32) -> u64 {
  if rel >= 0 {
    base + u64::from(rel.unsigned_abs())
  } else {
    base - u64::from(rel.unsigned_abs())
  }
}

fn find_adrp_add_xrefs(data: &[u8], text: (usize, usize), target: usize) -> Vec<usize> {
  let target_page = target & !0xFFF;
  let page_off = target & 0xFFF;
  let (start, end) = (text.0, text.1.min(data.len().saturating_sub(8)));
  let mut results = Vec::new();

  for off in (start..end).step_by(4) {
    let Some(insn) = read_u32_le(data, off) else {
      continue;
    };

    if (insn & 0x9F00_0000) == 0x9000_0000 {
      let immlo = i64::from((insn >> 29) & 0x3);
      let immhi = i64::from((insn >> 5) & 0x7_FFFF);
      let mut imm = (immhi << 2) | immlo;

      if imm & (1 << 20) != 0 {
        imm -= 1 << 21;
      }

      let base = off & !0xFFF;
      let shift = usize::try_from(imm.unsigned_abs()).unwrap() * 4096;
      let page = if imm >= 0 {
        base.checked_add(shift)
      } else {
        base.checked_sub(shift)
      };

      if let Some(page) = page
        && page == target_page
      {
        let Some(next) = read_u32_le(data, off + 4) else {
          continue;
        };

        if (next & 0xFFC0_0000) == 0x9100_0000
          && usize::try_from((next >> 10) & 0xFFF).ok().is_some_and(|imm12| imm12 == page_off)
        {
          results.push(off);
        }
      }
    }
  }
  results
}

const fn is_prologue(insn: u32) -> bool {
  let rn = (insn >> 5) & 0x1F;

  if (insn & 0xFFE0_0C00) == 0xF800_0C00 && rn == 31 {
    return true;
  }

  if (insn & 0x7FC0_0000) == 0x2980_0000 && rn == 31 {
    return true;
  }

  if (insn & 0xFF00_03FF) == 0xD100_03FF {
    return true;
  }

  false
}

fn find_function_start(data: &[u8], ref_offset: usize, text_start: usize) -> Option<usize> {
  let lower = ref_offset.saturating_sub(0x2000).max(text_start + 4);
  let mut off = ref_offset.saturating_sub(4);

  while off >= lower {
    let prev = read_u32_le(data, off - 4)?;
    let is_boundary = prev == 0xD65F_03C0 || (prev & 0xFFE0_001F) == 0xD420_0000;

    if is_boundary && read_u32_le(data, off).is_some_and(is_prologue) {
      return Some(off);
    }

    off -= 4;
  }

  None
}

fn find_method_imp(
  data: &[u8],
  macho: &MachO,
  methods_vmaddr: u64,
  selector: &str,
) -> Option<usize> {
  let methods_foff = macho.vm2off(methods_vmaddr)?;

  if methods_foff + 8 > data.len() {
    return None;
  }

  let entsize_and_flags = read_u32_le(data, methods_foff)?;
  let count = usize::try_from(read_u32_le(data, methods_foff + 4)?).ok()?;
  let is_relative = entsize_and_flags & 0x8000_0000 != 0;
  let entry_size: usize = if is_relative { 12 } else { 24 };

  for i in 0..count {
    let entry_foff = methods_foff + 8 + i * entry_size;

    if entry_foff + entry_size > data.len() {
      break;
    }

    let (sel_name, imp_vmaddr) = if is_relative {
      let name_rel = read_i32_le(data, entry_foff)?;
      let imp_rel = read_i32_le(data, entry_foff + 8)?;
      let entry_vm = macho.off2vm(entry_foff)?;
      let selref_vm = vmaddr_add_rel(entry_vm, name_rel);
      let selref_foff = macho.vm2off(selref_vm)?;

      if selref_foff + 8 > data.len() {
        continue;
      }

      let sel_ptr = macho.decode_ptr(read_u64_le(data, selref_foff)?);
      let sel_foff = macho.vm2off(sel_ptr)?;
      let name = read_cstring(data, sel_foff)?;
      let imp_vm = vmaddr_add_rel(entry_vm + 8, imp_rel);

      (name, imp_vm)
    } else {
      let sel_raw = read_u64_le(data, entry_foff)?;
      let sel_vm = macho.decode_ptr(sel_raw);
      let sel_foff = macho.vm2off(sel_vm)?;
      let name = read_cstring(data, sel_foff)?;
      let imp_raw = read_u64_le(data, entry_foff + 16)?;
      let imp_vm = macho.decode_ptr(imp_raw);

      (name, imp_vm)
    };

    if sel_name == selector {
      return macho.vm2off(imp_vmaddr);
    }
  }

  None
}

fn find_method_in_class(
  data: &[u8],
  macho: &MachO,
  class_vmaddr: u64,
  selector: &str,
) -> Option<usize> {
  let class_foff = macho.vm2off(class_vmaddr)?;

  if class_foff + 40 > data.len() {
    return None;

  }

  let data_raw = read_u64_le(data, class_foff + 32)?;
  let ro_vmaddr = macho.decode_ptr(data_raw) & !0x7;
  let ro_foff = macho.vm2off(ro_vmaddr)?;

  if ro_foff + 40 > data.len() {
    return None;
  }

  let methods_raw = read_u64_le(data, ro_foff + 32)?;
  let methods_vm = macho.decode_ptr(methods_raw);

  if methods_vm == 0 {
    return None;
  }

  find_method_imp(data, macho, methods_vm, selector)
}

fn find_can_init_with_request(data: &[u8], macho: &MachO) -> Option<usize> {
  let cl = macho.classlist.as_ref()?;
  let cl_foff = usize::try_from(cl.offset).ok()?;
  let cl_count = usize::try_from(cl.size).ok()? / 8;

  for i in 0..cl_count {
    let ptr_foff = cl_foff + i * 8;

    if ptr_foff + 8 > data.len() {
      break;
    }

    let Some(class_raw) = read_u64_le(data, ptr_foff) else {
      continue;
    };
    let class_vm = macho.decode_ptr(class_raw);

    if class_vm == 0 {
      continue;
    }

    let Some(class_foff) = macho.vm2off(class_vm) else {
      continue;
    };

    if class_foff + 40 > data.len() {
      continue;
    }

    let Some(data_raw) = read_u64_le(data, class_foff + 32) else {
      continue;
    };
    let ro_vm = macho.decode_ptr(data_raw) & !0x7;
    let Some(ro_foff) = macho.vm2off(ro_vm) else {
      continue;
    };

    if ro_foff + 40 > data.len() {
      continue;
    }

    let Some(name_raw) = read_u64_le(data, ro_foff + 24) else {
      continue;
    };
    let name_vm = macho.decode_ptr(name_raw);
    let Some(name_foff) = macho.vm2off(name_vm) else {
      continue;
    };
    let Some(name) = read_cstring(data, name_foff) else {
      continue;
    };

    if !name.contains("CertificatePinningURLProtocol") {
      continue;
    }

    eprintln!("detected ObjC class: {name}");

    let Some(isa_raw) = read_u64_le(data, class_foff) else {
      continue;
    };
    let metaclass_vm = macho.decode_ptr(isa_raw);

    if let Some(imp) = find_method_in_class(data, macho, metaclass_vm, "canInitWithRequest:") {
      return Some(imp);
    }

    if let Some(imp) = find_method_in_class(data, macho, class_vm, "canInitWithRequest:") {
      return Some(imp);
    }
  }

  None
}

fn find_handle_pinning_challenge(data: &[u8], macho: &MachO) -> Option<usize> {
  let text = macho.text_file_range()?;

  for needle in PINNING_ERROR_STRINGS {
    for str_off in memmem::find_iter(data, needle) {
      eprintln!(
        "String  \"{}...\" -> 0x{:08X}",
        String::from_utf8_lossy(&needle[..needle.len().min(40)]),
        str_off
      );

      let xrefs = find_adrp_add_xrefs(data, text, str_off);

      if xrefs.is_empty() {
        continue;
      }

      eprintln!(
        "Reference: {}",
        xrefs
          .iter()
          .map(|x| format!("0x{x:08X}"))
          .collect::<Vec<_>>()
          .join(", ")
      );

      for xref in &xrefs {
        if let Some(func_start) = find_function_start(data, *xref, text.0)
          && read_u32_le(data, func_start).is_some_and(is_prologue)
        {
          return Some(func_start);
        }
      }
    }
  }

  None
}

fn apply_patch(data: &mut [u8], offset: usize, patch: &[u8]) -> bool {
  if offset + patch.len() > data.len() {
    eprintln!("overflow: 0x{offset:08X}");
    return false;
  }

  if !read_u32_le(data, offset).is_some_and(is_prologue) {
    eprintln!("0x{offset:08X} is not function prologue");
    return false;
  }

  eprintln!(
    "offset: 0x{offset:08X} before: {}",
    hex::encode(&data[offset..offset + patch.len()])
  );

  data[offset..offset + patch.len()].copy_from_slice(patch);

  eprintln!("after: {}", hex::encode(patch));

  true
}

fn extract_ipa(ipa_path: &Path, dest: &Path) -> Result<()> {
  let file = File::open(ipa_path).context("failed to open ipa")?;
  let mut archive = zip::ZipArchive::new(file).context("failed  to load ipa")?;

  for i in 0..archive.len() {
    let mut entry = archive.by_index(i)?;
    let Some(name) = entry.enclosed_name() else {
      continue;
    };
    let out_path = dest.join(name);

    if entry.is_dir() {
      fs::create_dir_all(&out_path)?;
    } else {
      if let Some(parent) = out_path.parent() {
        fs::create_dir_all(parent)?;
      }

      let mut out = File::create(&out_path)?;

      io::copy(&mut entry, &mut out)?;
    }

    #[cfg(unix)]
    if let Some(mode) = entry.unix_mode() {
      use std::os::unix::fs::PermissionsExt;

      let _ = fs::set_permissions(&out_path, fs::Permissions::from_mode(mode));
    }
  }

  Ok(())
}

fn create_ipa(work_dir: &Path, output: &Path) -> Result<()> {
  if output.exists() {
    fs::remove_file(output)?;
  }

  let file = File::create(output).context("failed to create output file")?;
  let mut zip = zip::ZipWriter::new(file);
  let payload = work_dir.join("Payload");

  for entry in WalkDir::new(&payload).min_depth(1) {
    let entry = entry?;
    let entry_path = entry.path();
    let rel = entry_path.strip_prefix(work_dir).unwrap_or(entry_path);
    let rel_str = rel.to_string_lossy();

    if entry.file_type().is_dir() {
      let dir_name = if rel_str.ends_with('/') {
        rel_str.into_owned()
      } else {
        format!("{rel_str}/")
      };
      let mut options = zip::write::SimpleFileOptions::default()
        .compression_method(zip::CompressionMethod::Deflated);

      #[cfg(unix)]
      {
        use std::os::unix::fs::PermissionsExt;

        let mode = fs::metadata(entry_path)?.permissions().mode();
        options = options.unix_permissions(mode);
      }

      zip.add_directory(&dir_name, options)?;
    } else {
      let mut options = zip::write::SimpleFileOptions::default()
        .compression_method(zip::CompressionMethod::Deflated);

      #[cfg(unix)]
      {
        use std::os::unix::fs::PermissionsExt;

        let mode = fs::metadata(entry_path)?.permissions().mode();
        options = options.unix_permissions(mode);
      }

      zip.start_file(rel_str.as_ref(), options)?;

      let mut f = File::open(entry_path)?;

      io::copy(&mut f, &mut zip)?;
    }
  }

  zip.finish()?;

  eprintln!(
    "IPA created: {} ({} MB)",
    output.display(),
    format_mb(fs::metadata(output)?.len())
  );

  Ok(())
}

fn find_framework_binary(app_dir: &Path, app_name: &str) -> Result<PathBuf> {
  let needle = b"CertificatePinningURLProtocol";
  let contains_pinning =
    |p: &Path| -> bool { fs::read(p).is_ok_and(|d| memmem::find(&d, needle).is_some()) };
  let main_bin = app_dir.join(app_name);

  if main_bin.exists() && contains_pinning(&main_bin) {
    return Ok(main_bin);
  }

  let fw_dir = app_dir.join("Frameworks");

  if fw_dir.exists() {
    for entry in fs::read_dir(&fw_dir)? {
      let path = entry?.path();

      if path.extension().is_some_and(|e| e == "framework") {
        let name = path.file_stem().unwrap().to_string_lossy().to_string();
        let bin = path.join(&name);

        if bin.exists() && contains_pinning(&bin) {
          return Ok(bin);
        }
      }
    }
  }

  bail!("cannot find `CertificatePinning`")
}

fn remove_codesign_all(app_dir: &Path) {
  let mut removed = 0u32;

  for entry in WalkDir::new(app_dir)
    .into_iter()
    .filter_map(std::result::Result::ok)
  {
    if entry.file_name() == "_CodeSignature" && entry.file_type().is_dir() {
      let _ = fs::remove_dir_all(entry.path());
      removed += 1;
    }
  }

  if removed > 0 {
    eprintln!("deleted {removed} signature(s)");
  }
}

fn run() -> Result<()> {
  let cli = Cli::parse();
  let ipa_path = &cli.input;

  if !ipa_path.exists() {
    bail!("Cannot find ipa file: {}", ipa_path.display());
  }

  let output_path = cli.output.unwrap_or_else(|| {
    let stem = ipa_path.file_stem().unwrap().to_string_lossy();

    ipa_path.with_file_name(format!("{stem}_patched.ipa"))
  });
  let temp_dir = tempfile::TempDir::new()?;
  let tmp = temp_dir.path();

  eprintln!("extracting ipa file: {}", ipa_path.display());
  extract_ipa(ipa_path, tmp)?;

  let payload = tmp.join("Payload");

  if !payload.exists() {
    bail!("`Payload` directory not found");
  }

  let app_dir = fs::read_dir(&payload)?
    .filter_map(std::result::Result::ok)
    .find(|e| e.path().extension().is_some_and(|x| x == "app"))
    .map(|e| e.path())
    .context(".app bundle not found")?;
  let app_name = app_dir.file_stem().unwrap().to_string_lossy().to_string();

  eprintln!("raping {app_name}");

  let binary_path = find_framework_binary(&app_dir, &app_name)?;

  eprintln!(
    "target: {}",
    binary_path
      .strip_prefix(tmp)
      .unwrap_or(&binary_path)
      .display()
  );

  let mut data = fs::read(&binary_path).context("failed to load binary")?;

  eprintln!(
    "size: {} MB",
    format_mb(u64::try_from(data.len()).unwrap_or(0))
  );

  let (macho_start, macho_end) = choose_macho_slice_range(&data)?;
  let macho = MachO::parse(&data[macho_start..macho_end])?;
  let mut applied = 0u32;

  eprintln!("patching CertificatePinningURLProtocol.canInitWithRequest:");

  match find_can_init_with_request(&data[macho_start..macho_end], &macho) {
    Some(addr) => {
      eprintln!("detected: 0x{addr:08X}");

      if apply_patch(
        &mut data[macho_start..macho_end],
        addr,
        PATCH_RETURN_FALSE,
      ) {
        applied += 1;
      }
    }

    None => eprintln!("cannot find `canInitWithRequest:`"),
  }

  eprintln!("patching handleCertificatePinningChallenge");

  match find_handle_pinning_challenge(&data[macho_start..macho_end], &macho) {
    Some(addr) => {
      eprintln!("detected: 0x{addr:08X}");

      if apply_patch(
        &mut data[macho_start..macho_end],
        addr,
        PATCH_PERFORM_DEFAULT,
      ) {
        applied += 1;
      }
    }

    None => eprintln!("cannot find `handleCertificatePinningChallenge`"),
  }

  if applied == 0 {
    bail!("there are no patches");
  }

  fs::write(&binary_path, &data).context("failed to write output")?;
  eprintln!("applied {applied} patch(es)");

  remove_codesign_all(&app_dir);

  create_ipa(tmp, &output_path)?;

  eprintln!("output: {}", output_path.display());

  Ok(())
}

fn main() {
  if let Err(e) = run() {
    eprintln!("Error: {e:#}");

    std::process::exit(1);
  }
}
