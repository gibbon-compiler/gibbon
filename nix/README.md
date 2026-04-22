# OpenCilk overlay

`overlay.nix` adds `llvmPackages_opencilk` to the pinned nixpkgs package set.
The `llvm/` subtree is the small LLVM packaging subtree from the upstream
OpenCilk nixpkgs work in NixOS/nixpkgs#494221, including the OpenCilk source
assembly, Cheetah runtime, and wrapper resource-root changes.

This keeps the project off a full nixpkgs fork while preserving the package
shape used by the previous fork-based shell:

```nix
pkgs.llvmPackages_opencilk.clang
pkgs.llvmPackages_opencilk.llvm
```
