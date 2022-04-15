# Verified Causal Broadcast with Liquid Haskell

Implementation of the CBCAST protocol from
_Lightweight Causal and Atomic Group Multicast_
[[info](https://dl.acm.org/doi/abs/10.1145/128738.128742),
 [pdf](https://infoscience.epfl.ch/record/50197/files/BSS91.pdf)].
Verification of causal delivery with
[Liquid Haskell](https://github.com/ucsd-progsys/liquidhaskell).

To follow the proof, we suggest:
* The top level theorem and proof are in
  `lib/MessagePassingAlgorithm/CBCAST/Step/Verification.hs`.
* The definition(s) of PLCD and preservation are in
  `lib/MessagePassingAlgorithm/CBCAST/Verification/PLCD.hs` and
  `lib/MessagePassingAlgorithm/VectorClockAdapter/Verification/ProcessLocalCausalDelivery.hs`.

## Building

Compiling the project will run the Liquid Haskell verification as a GHC plugin.
It normally takes about 75 minutes (on a 2015 MacBookPro).
To skip the verification and just build the code, you can turn off the Liquid Haskell plugin in `package.yaml`.

### Stack

* For most systems, `stack build` should do the trick.

### NixOS/Nix

* Use `nix-shell` to enter a development environment.
* Use `nix-build` to build the project.
