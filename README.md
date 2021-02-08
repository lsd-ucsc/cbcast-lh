# CBCAST in LH

Implementation of CBCAST from _Lightweight Causal and Atomic Group Multicast_
[[info](https://dl.acm.org/doi/abs/10.1145/128738.128742),
[pdf](https://infoscience.epfl.ch/record/50197/files/BSS91.pdf)]. Verification
of safety property written with [Liquid
Haskell](https://github.com/ucsd-progsys/liquidhaskell).

## Status

* Algorithm is implemented.
* Verification is ongoing.

## Building

### Stack

* For most systems, `stack build` should do the trick.
* On `nix`-enabled systems, you might consider enabling nix (see `stack.yaml`),
  but this is not necessary.

### NixOS/Nix

* Use `nix-shell` to enter a development environment.
* Use `nix-build` to build the project.
