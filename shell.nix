let
  moz_overlay = import (builtins.fetchGit {
                   name = "nixpkgs-mozilla-2021-10-24";
                   url = "https://github.com/mozilla/nixpkgs-mozilla/";
                   ref = "refs/heads/master";
                   # Commit hash for nixpkgs-mozilla as of 2021-10-24
                   rev = "6070a8ee799f629cb1d0004821f77ceed94d3992";
                 });
  pkgs = import (builtins.fetchGit {
                   name = "nixos-unstable-2021-03-11";
                   url = "https://github.com/nixos/nixpkgs/";
                   ref = "refs/heads/master";
                   # Commit hash for nixos-unstable as of 2021-03-11
                   rev = "a3228bb6e8bdbb9900f30a11fe09006fdabf7b71";
                 }) { overlays = [ moz_overlay ]; };
  stdenv = pkgs.overrideCC pkgs.stdenv pkgs.gcc7;
  ghc = pkgs.haskell.compiler.ghc865;
  ghc901 = pkgs.haskell.compiler.ghc901;
  rust = (pkgs.rustChannelOf { rustToolchain = ./gibbon-rts/rust-toolchain; }).rust;
in
  with pkgs;
  stdenv.mkDerivation {
    name = "basicGibbonEnv";
    buildInputs = [ ghc ghc901 gcc7 which boehmgc uthash racket cabal-install ghcid
                    gdb valgrind stack stdenv ncurses unzip rr rust
                  ];
  }
