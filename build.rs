fn main() {
    println!("cargo:rustc-check-cfg=cfg(doccfg)");
    if let Some(true) = version_check::supports_feature("doc_cfg") {
        if let Some(true) = version_check::supports_feature("doc_auto_cfg") {
            // `doc` is already generated by rustdoc on stable
            // `docrs` is generated by docs.rs when building
            // This enables local builds to have feature annotations when supported using `doccfg`
            println!("cargo:rustc-cfg=doccfg");
        }
    }
}
