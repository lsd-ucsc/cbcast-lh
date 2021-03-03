# Verified Causal Broadcast with Liquid Haskell

Implementation of the CBCAST protocol from _Lightweight Causal and
Atomic Group Multicast_
[[info](https://dl.acm.org/doi/abs/10.1145/128738.128742),
[pdf](https://infoscience.epfl.ch/record/50197/files/BSS91.pdf)]. Verification
of causal safety with [Liquid
Haskell](https://github.com/ucsd-progsys/liquidhaskell).

To follow the proof, we suggest reading
`lib/Causal/CBCAST/VectorClock.hs`, then
`lib/Causal/CBCAST/Message.hs`, then `lib/Causal/CBCAST/Safety.hs`.

The file `lib/Causal/CBCAST/VerificationSummary.hs` contains a short,
self-contained summary of the main ideas of our proof development.  It
is not connected to the running implementation.

## Building

### Stack

* For most systems, `stack build` should do the trick.
* On `nix`-enabled systems, you might consider enabling nix (see `stack.yaml`),
  but this is not necessary.

### NixOS/Nix

* Use `nix-shell` to enter a development environment.
* Use `nix-build` to build the project.
