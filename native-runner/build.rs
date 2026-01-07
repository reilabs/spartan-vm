fn main() {
    // Export symbols from the binary so dlopen'd libraries can find them
    // This is needed for the __write_* callbacks (defined in runner.rs)
    // Note: __field_* functions are in the runtime library, not here

    #[cfg(target_os = "linux")]
    println!("cargo:rustc-link-arg=-Wl,--export-dynamic");

    #[cfg(target_os = "macos")]
    {
        // macOS uses -exported_symbol for each symbol (note: C symbols get _ prefix)
        // Only export symbols that are actually defined in this binary
        println!("cargo:rustc-link-arg=-Wl,-exported_symbol,___write_witness");
        println!("cargo:rustc-link-arg=-Wl,-exported_symbol,___write_a");
        println!("cargo:rustc-link-arg=-Wl,-exported_symbol,___write_b");
        println!("cargo:rustc-link-arg=-Wl,-exported_symbol,___write_c");
    }
}
