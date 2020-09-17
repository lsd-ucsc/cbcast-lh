{ config ? { allowBroken = true; }, ... }:
let
  # get pinned/overridden haskellPackages containing LH
  lh-source = (import <nixpkgs> {}).fetchFromGitHub {
    owner = "plredmond";
    repo = "liquidhaskell";
    rev = "261394e8fd1afd5e688eb5459de3424a973e14f4"; # HEAD as of Thu 17 Sep 2020 12:38:06 AM UTC
    sha256 = "0k61m8w0vh5qrf590k8riq1lvl26rrh6cjwpf5wksd9fkdpyjvzm";
    fetchSubmodules = true;
  };
  # extract pinned nixpkgs and haskellPackages
  elsewhere = import lh-source { inherit config; tests = false; mkEnv = false; };
  nixpkgs = elsewhere.nixpkgs;
  haskellPackages = elsewhere.haskellPackages.override (
    old: {
      overrides = self: super: with nixpkgs.haskell.lib; (old.overrides self super) // {
        doctest = self.callHackage "doctest" "0.16.3" {}; # nixpkgs version doesn't bulid
        tls = self.callHackage "tls" "1.5.4" {}; # nixpkgs version too old for hpack
      };
    }
  );
  # define the derivation and the environment
  drv = nixpkgs.haskell.lib.overrideCabal
    (haskellPackages.callCabal2nix "cbcast-in-lh" (nixpkgs.nix-gitignore.gitignoreSource [] ./.) {})
    (old: { doCheck = true; doHaddock = true; buildTools = old.buildTools or [] ++ [ nixpkgs.z3 ]; });
  env = (drv.envFunc { withHoogle = true; }).overrideAttrs
    (old: { nativeBuildInputs = old.nativeBuildInputs ++ [ nixpkgs.ghcid ]; });
in
if nixpkgs.lib.inNixShell then env else drv
