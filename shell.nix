let
  moz_overlay = import (builtins.fetchGit {
                   name = "nixpkgs-mozilla-2021-10-24";
                   url = "https://github.com/ckoparkar/nixpkgs-mozilla";
                   ref = "refs/heads/master";
                   # Commit hash for nixpkgs-mozilla as of 2022-12-30
                   rev = "e365e1346c3390cf7fde486c2441abe178e384e8";
                 });
  pkgs = import (builtins.fetchGit {
                   url = "https://github.com/nixos/nixpkgs/";
                   ref = "refs/tags/22.11";
                 }) { overlays = [ moz_overlay ]; };
  stdenv = pkgs.overrideCC pkgs.stdenv pkgs.gcc7;
  ghc = pkgs.haskell.compiler.ghc943;
  rust = (pkgs.rustChannelOf { rustToolchain = ./gibbon-rts/rust-toolchain; }).rust;
  clang = pkgs.clang_14;
  llvm = pkgs.llvm_14;
  gibbon_dir = builtins.toString ./.;
in
  with pkgs;
  stdenv.mkDerivation {
    name = "basicGibbonEnv";
    buildInputs = [ # Haskell
                    ghc cabal-install stack
                    # C/C++
                    clang llvm gcc7 boehmgc uthash
                    # Rust
                    rust
                    # Racket
                    racket
                    # Other utilities
                    stdenv ncurses unzip which rr rustfmt clippy ghcid gdb valgrind
                  ];
    shellHook = ''
      export GIBBONDIR=${gibbon_dir}
    '';
  }
