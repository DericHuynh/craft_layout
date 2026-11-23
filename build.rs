use std::{env, process::Command};

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rustc-check-cfg=cfg(keru_avx512)");
    if env::var("CARGO_CFG_TARGET_ARCH").as_deref() != Ok("x86_64") {
        return;
    }

    // Rust 1.89 stabilized the AVX-512 intrinsics and target features.
    // Builds with the 1.88 minimum still get the other backends.
    let Some(rustc) = env::var_os("RUSTC") else { return };
    let Ok(output) = Command::new(rustc).arg("--version").output() else { return };
    if !output.status.success() { return; }
    let version = String::from_utf8_lossy(&output.stdout);
    let Some(release) = version.split_whitespace().nth(1) else { return };
    let mut components = release.split('.');
    let major = components.next().and_then(|part| part.parse::<u32>().ok());
    let minor = components.next().and_then(|part| part.parse::<u32>().ok());
    if let (Some(major), Some(minor)) = (major, minor)
        && (major > 1 || major == 1 && minor >= 89)
    {
        println!("cargo:rustc-cfg=keru_avx512");
    }
}
