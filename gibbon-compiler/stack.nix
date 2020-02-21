# This nix environmemnt is *just* for building the Gibbon compiler,
# nothing more.
#
# This is intended for use with stack/nix integration, i.e. stack's
# --nix argument.

# See ../.nix_default_environment.txt for the fixed version of nixpkgs
# which we test with in CI.  Using this file directly will use
# whatever nixpkgs your user account is currently pointing at.
{ pkgs ? import (fetchTarball (import ../.nix_default_environment.txt)) {}
 # Default should match the current LTS in stack.yaml:
, ghc ? pkgs.haskell.compiler.ghc865 }:

with pkgs;

haskell.lib.buildStackProject {
  inherit ghc;
  name = "basicGibbonEnv";
  buildInputs = [ gcc which boehmgc uthash racket cabal-install
                ];
}
