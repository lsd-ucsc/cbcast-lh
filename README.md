# Verified Causal Broadcast with Liquid Haskell

Implementation of the CBCAST protocol from
_Lightweight Causal and Atomic Group Multicast_
[[info](https://dl.acm.org/doi/abs/10.1145/128738.128742),
 [pdf](https://infoscience.epfl.ch/record/50197/files/BSS91.pdf)].
Verification of causal delivery with
[Liquid Haskell](https://github.com/ucsd-progsys/liquidhaskell).

To follow the proof, we suggest:

* The top level theorem and proof are in
  `lib/CBCAST/Verification/PLCDpresStep.hs`: The theorem `trcPLCDpres` states
  that, for all PLCD-observing processes, applying an arbitrary list of
  operations obtains a PLCD-observing process.

* The definition of PLCD (process-local causal delivery) is in
  `lib/CBCAST/Verification/PLCD.hs`: The definition `PLCD` states that, given a
  process `p`, for all messages `m₁` and `m₂` delivered at `p` and with sent-VC
  of `m₁` less than sent-VC of `m₂`, `p` delivers first `m₁` and second `m₂`.

* The definition of PLCD-preservation is in
  `lib/CBCAST/Verification/PLCDpres.hs`: The definition `PLCDpreservation`
  states that, given an operation, for all PLCD-observing processes, applying
  the operation obtains a PLCD-observing process.

## Building

Compiling the project will run the Liquid Haskell verification as a GHC plugin.
It normally takes about 75 minutes (on a 2015 MacBookPro).
To skip the verification and just build the code, you can turn off the Liquid Haskell plugin in `package.yaml`.

### Stack

* For most systems, `stack build` should do the trick.

### NixOS/Nix

* Use `nix-shell` to enter a development environment.
* Use `nix-build` to build the project.
