let
  pkgs =
    import
      (builtins.fetchTarball {
        url = "https://github.com/NixOS/nixpkgs/archive/refs/tags/25.11.tar.gz";
        sha256 = "1zn1lsafn62sz6azx6j735fh4vwwghj8cc9x91g5sx2nrg23ap9k";
      })
      {
        overlays = [ (import ./nix/overlay.nix) ];
      };

  clang = pkgs.llvmPackages_opencilk.clang;
  llvm = pkgs.llvmPackages_opencilk.llvm;
  gibbon_dir = builtins.toString ./.;
in
with pkgs;

mkShell {

  # we use default Haskell toolchain supplied with the chosen nixpkgs; this way we hit their cache
  inputsFrom = [ (pkgs.haskellPackages.callCabal2nix "gibbon-compiler" ./gibbon-compiler { }).env ];

  name = "basicGibbonEnv";
  buildInputs = [
    # C/C++
    clang
    llvm
    gcc
    boehmgc
    uthash
    # Rust
    rustc
    cargo
    # Racket
    racket
    # Other utilities
    stdenv
    ncurses
    unzip
    which
    rr
    rustfmt
    clippy
    ghcid
    gdb
    valgrind
  ];
  shellHook = ''
    export GIBBONDIR=${gibbon_dir}
  '';
}
