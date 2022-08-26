# Verified Causal Broadcast with Liquid Haskell

Implementation of causal broadcast inspired by the CBCAST protocol from
**Lightweight Causal and Atomic Group Multicast**
[[doi:10.1145/128738.128742](https://doi.org/10.1145/128738.128742),
 [pdf](https://infoscience.epfl.ch/record/50197/files/BSS91.pdf)].
Verification of causal delivery with
[Liquid Haskell](https://github.com/ucsd-progsys/liquidhaskell),
described in our paper **Verified Causal Broadcast with Liquid Haskell**
[[arXiv:2206.14767](https://arxiv.org/abs/2206.14767),
 [pdf](https://arxiv.org/pdf/2206.14767.pdf)].
 
## Use the library

The implementation is suitable for inclusion in real world projects, except for the known caveats of the algorithm, namely that the set of processes (view) cannot change during runtime. There is a [client library module, `CBCAST`](lib/CBCAST.hs) for clients that don't use Liquid Haskell, and an [example key value server](ExampleKvServer.hs). Both have extensive docstring comments. If your project uses Liquid Haskell, you could probably import the internal modules [`CBCAST.{Core,Transitions}`](https://github.com/lsd-ucsc/cbcast-lh/tree/main/lib/CBCAST). Finally, the [`deploy` directory readme](deploy#nixops-deployment) has NixOps scripts for deployment on AWS.

## Read the proof

To follow the proof that applying operations to processes in an execution
preserves *causal delivery* (CD), we suggest:

* The top level theorem and proof are in
  [CBCAST/Verification/Global/CDpresXStep.hs](lib/CBCAST/Verification/Global/CDpresXStep.hs):
  The theorem `trcCDpres` states that for all CD-observing executions,
  applying an arbitrary list of operations to processes in the execution
  obtains a CD-observing execution.

  * The definition of CD is in
    [CBCAST/Verification/Global/Core.hs](lib/CBCAST/Verification/Global/Core.hs):
    The definition `CausalDelivery r N X` states that for some number of
    processes `N` and some execution `X`, for all process identifiers `p_id` in
    `X`, and messages `m₁` and `m₂` delivered at `X p_id` with `m₁`
    happens-before `m₂`, `X p_id` delivers `m₁` before `m₂`.

  * The definition of CD-preservation is in
    [CBCAST/Verification/Global/CDpresXStep.hs](lib/CBCAST/Verification/Global/CDpresXStep.hs):
    The definition `CDpreservation r N F` states that for some number of
    processes `N` and function `F`, for all CD-observing executions `x`, the
    execution `F x` is CD-observing.

  * An execution (`Xsized r N`) is a function (or mapping), for some number of
    processes `N`, from a process identifier on `[0,N)` to a process with that
    identifier in
    [CBCAST/Verification/Global/Core.hs](lib/CBCAST/Verification/Global/Core.hs).

  * Happens before (`→`) is an uninterpreted predicate on two events in an
    execution. We provide the axiom `preserveHB` which says `e → e' ⇒ VC(e) <
    VC(e')` and `reflectHB` which says `VC(e) < VC(e') ⇒ e → e'` in
    [CBCAST/Verification/Global/Core.hs](lib/CBCAST/Verification/Global/Core.hs).

This relies on our work showing that applying operations to a **single**
process preserves *process-local causal delivery* (PLCD).

* The top level theorem and proof are in
  [CBCAST/Verification/PLCDpresStep.hs](lib/CBCAST/Verification/PLCDpresStep.hs):
  The theorem `trcPLCDpres` states that for all PLCD-observing processes,
  applying an arbitrary list of operations to the process obtains a
  PLCD-observing process.

  * The definition of PLCD is in
    [CBCAST/Verification/PLCD.hs](lib/CBCAST/Verification/PLCD.hs): The
    definition `PLCD r N PROC` states that for some number of processes `N` and
    some process `PROC`, for all messages `m₁` and `m₂` delivered at `PROC`
    with sent-VC of `m₁` less-than sent-VC of `m₂`, `PROC` delivers `m₁` before
    `m₂`.

  * The definition of PLCD-preservation is in
    [CBCAST/Verification/PLCDpres.hs](lib/CBCAST/Verification/PLCDpres.hs): The
    definition `PLCDpreservation r N F` states that for some number of
    processes `N` and some function `F`, for all PLCD-observing processes `p`,
    the process `F p` is PLCD-observing.

### Proof diagram

Here's a diagram of the important components of the proof. Purple theorems are
concerned with global properties of an execution, blue theorems assist with
translating between process-local and global-execution properties, and yellow
theorems are concerned with process local properties. Dashed arrows indicate inclusion
via lemmas.

![Proof diagram](scripts/diag/output/output-flattened.png)

## Build the project

Compiling the project will run the Liquid Haskell verification as a GHC plugin.
It normally takes about 4 minutes (on a 2015 MacBookPro).
To skip the verification and just build the code, you can turn off the Liquid Haskell plugin in `package.yaml`.

### Stack

* For most systems, `stack build` should do the trick.

### NixOS/Nix

* Use `nix-shell` to enter a development environment or use `nix-build` to build the project.
* Flake commands work too.
