let
  moz_overlay = import (builtins.fetchGit {
                   name = "nixpkgs-mozilla-2023-11-13";
                   url = "https://github.com/mozilla/nixpkgs-mozilla";
                   ref = "refs/heads/master";
                   # Most recent commit hash as of 2023-11-13
                   rev = "6eabade97bc28d707a8b9d82ad13ef143836736e";
                 });
  pkgs = import (builtins.fetchGit {
                   url = "https://github.com/nixos/nixpkgs/";
                   ref = "refs/tags/23.05";
                 }) { overlays = [ moz_overlay ]; };
  stdenv = pkgs.overrideCC pkgs.stdenv pkgs.gcc7;
  ghc = pkgs.haskell.compiler.ghc94;
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
