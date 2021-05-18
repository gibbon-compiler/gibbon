{
  pkgs ? import (builtins.fetchGit {
                   name = "nixos-unstable-2021-03-11";
                   url = "https://github.com/nixos/nixpkgs/";
                   # Commit hash for nixos-unstable as of 2021-03-11
                   # `git ls-remote https://github.com/nixos/nixpkgs master`
                   ref = "refs/heads/master";
                   rev = "a3228bb6e8bdbb9900f30a11fe09006fdabf7b71";
                 }) {}
, stdenv ? pkgs.overrideCC pkgs.stdenv pkgs.gcc7
, ghc ? pkgs.haskell.compiler.ghc865
, ghc901 ? pkgs.haskell.compiler.ghc901
}:

with pkgs;

haskell.lib.buildStackProject {
  name = "treevelocityEnv";
  buildInputs = [ stdenv ghc ghc901 stack which racket
                  ncurses boehmgc uthash unzip
                ];
}
