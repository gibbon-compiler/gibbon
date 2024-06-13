let
  pkgs = import (builtins.fetchGit {
                   url = "https://github.com/nixos/nixpkgs/";
                   ref = "refs/tags/24.05";
                 }) {};

  clang = pkgs.clang_16;
  llvm = pkgs.llvm_16;
  gibbon_dir = builtins.toString ./.;
in
  with pkgs;

  # we are stuck with GCC 7 because Cilk was kicked out in GCC 8,
  # OpenCilk needs packaging in nixpkgs, see
  # https://github.com/NixOS/nixpkgs/issues/144256
  mkShell.override { stdenv = pkgs.gcc7Stdenv; }  {

    # we use default Haskell toolchain supplied with the chosen nixpkgs; this way we hit their cache
    inputsFrom = [ (pkgs.haskellPackages.callCabal2nix "gibbon-compiler" ./gibbon-compiler { }).env ];

    name = "basicGibbonEnv";
    buildInputs = [
                    # C/C++
                    clang llvm gcc7 boehmgc uthash
                    # Rust
                    rustc cargo
                    # Racket
                    racket
                    # Other utilities
                    stdenv ncurses unzip which rr rustfmt clippy ghcid gdb valgrind
                  ];
    shellHook = ''
      export GIBBONDIR=${gibbon_dir}
    '';
  }
