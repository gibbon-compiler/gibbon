let
  moz_overlay = import (builtins.fetchGit {
                   name = "nixpkgs-mozilla-2021-10-24";
                   url = "https://github.com/mozilla/nixpkgs-mozilla/";
                   ref = "refs/heads/master";
                   # Commit hash for nixpkgs-mozilla as of 2021-10-24
                   rev = "6070a8ee799f629cb1d0004821f77ceed94d3992";
                 });
  pkgs = import (builtins.fetchGit {
                   url = "https://github.com/nixos/nixpkgs/";
                   ref = "refs/heads/master";
                   # Commit hash for nixos-unstable as of 2022-01-30
                   rev = "8b01281b66cba818abea8dbbdb3614b1b38961e3";
                 }) { overlays = [ moz_overlay ]; };
  stdenv = pkgs.overrideCC pkgs.stdenv pkgs.gcc7;
  ghc = pkgs.haskell.compiler.ghc902;
  rust = (pkgs.rustChannelOf { rustToolchain = ./gibbon-rts/rust-toolchain; }).rust;
  gibbon_dir = builtins.toString ./.;
in
  with pkgs;
  stdenv.mkDerivation {
    name = "basicGibbonEnv";
    buildInputs = [ ghc cabal-install stack gcc7 boehmgc uthash rust racket
                    # dev environment
                    stdenv ncurses unzip which rr rustfmt clippy ghcid gdb valgrind
                  ];
    shellHook = ''
      export GIBBONDIR=${gibbon_dir} \
             GIBBON_NEWRTS_DIR="${gibbon_dir}/gibbon-rts"
    '';
  }
