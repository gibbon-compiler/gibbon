let
  pkgs = import (builtins.fetchGit {
                   url = "https://github.com/nixos/nixpkgs/";
                   ref = "refs/tags/24.05";
                 }) {};

  opencilk-pkgs = import (builtins.fetchGit {
                    url = "https://github.com/Noir01/nixpkgs";
                    rev = "ec057fb50aaea43dc26690840c3198922d6604fc";
                  }) {};

  clang = opencilk-pkgs.llvmPackages_opencilk.clang;
  llvm = opencilk-pkgs.llvmPackages_opencilk.llvm;
  gibbon_dir = builtins.toString ./.;
in
  with pkgs;

  # gcc7Stdenv is kept for C codebase compatibility;
  # Cilk support is provided by OpenCilk clang via -fopencilk
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
