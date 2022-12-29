use std::env;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};

// Copied from https://stackoverflow.com/a/65192210.
fn copy_dir_all(
    src: impl AsRef<Path>,
    dst: impl AsRef<Path>,
) -> io::Result<()> {
    fs::create_dir_all(&dst)?;
    for entry in fs::read_dir(src)? {
        let entry = entry?;
        let ty = entry.file_type()?;
        if ty.is_dir() {
            copy_dir_all(entry.path(), dst.as_ref().join(entry.file_name()))?;
        } else {
            fs::copy(entry.path(), dst.as_ref().join(entry.file_name()))?;
        }
    }
    Ok(())
}

fn main() {
    let dst_dir = PathBuf::from(env::var_os("OUT_DIR").unwrap());
    let lib_dir = dst_dir.join("lib");
    fs::create_dir_all(&lib_dir).unwrap();

    let gibbon_dir = env::var_os("GIBBONDIR").unwrap();
    copy_dir_all(
        format!("{}/gibbon-rts/build", gibbon_dir.to_str().unwrap()),
        &lib_dir,
    )
    .unwrap();

    println!("cargo:root={}", dst_dir.to_str().unwrap());
    println!("cargo:rustc-link-search={}", lib_dir.to_str().unwrap());
    println!("cargo:include={}", lib_dir.to_str().unwrap());
    println!("cargo:rustc-link-lib=gibbon_rts");
    println!("cargo:rustc-link-lib=gibbon_rts_ng");
    println!("cargo:rustc-link-arg=-Wl,-rpath,{}", lib_dir.to_str().unwrap());
}
