# This Nix environment contains everything needed to run the tests.

# Currently using a snapshot of the nixos-18.03 channel.
# Default GHC should match the current LTS in stack.yaml:
{ pkgs ? import (fetchTarball (import ./.nix_default_environment.txt)) {}
, ghc ? pkgs.haskell.compiler.ghc865 }:

with pkgs;

haskell.lib.buildStackProject {
  inherit ghc;
  name = "basicGibbonEnv";
  buildInputs = [ stdenv ghc stack which racket
                  ncurses boehmgc uthash
                ];
}
