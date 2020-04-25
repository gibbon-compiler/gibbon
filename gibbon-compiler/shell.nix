# See ../.nix_default_environment.txt for the fixed version of nixpkgs
# which we test with in CI.  Using this file directly will use
# whatever nixpkgs your user account is currently pointing at.
{ pkgs ? import (fetchTarball (import ../.nix_default_environment.txt)) {}
, ghc ? pkgs.haskell.compiler.ghc865
, stdenv ? pkgs.overrideCC pkgs.stdenv pkgs.gcc7 }:

with pkgs;

stdenv.mkDerivation {
  name = "basicGibbonEnv";
  buildInputs = [ ghc gcc7 which boehmgc uthash racket cabal-install ghcid
                  gdb valgrind
                ];
}
