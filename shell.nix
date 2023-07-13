{
  pkgs ? import (builtins.fetchGit {
    name = "nixos-master";
    url = "https://github.com/nixos/nixpkgs/";
    # Commit hash for nixos as of 2023-07-05
    # `git ls-remote https://github.com/nixos/nixpkgs master`
    ref = "refs/heads/master";
    rev = "26402a0a438220e418c31a2c93c15f319d19527a";
  }) {}
, stdenv ? pkgs.overrideCC pkgs.stdenv pkgs.gcc7
, ghc ? pkgs.haskell.compiler.ghc96
, ghc902 ? pkgs.haskell.compiler.ghc902
}:

with pkgs;

stdenv.mkDerivation {
  name = "basicGibbonEnv";
  buildInputs = [ ghc ghc902 gcc7 which boehmgc uthash racket cabal-install ghcid
                  gdb valgrind stack stdenv ncurses unzip rr
                ];
}
