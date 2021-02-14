{ config ? { allowBroken = true; }, ... }:
let
  # get pinned/overridden haskellPackages containing LH
  lh-source = (import <nixpkgs> {}).fetchFromGitHub {
    owner = "plredmond";
    repo = "liquidhaskell";
    rev = "a4b24ab24"; # nixify branch built from LH `develop` branch source Fri 12 Feb 2021 07:31:04 PM UTC
    sha256 = "1ms2d7rabidssjm12kxxd63ngxff8ni02fpzd27pzqwwkcdx0d70";
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
    (
      old: {
        doCheck = true;
        doHaddock = false; # FIXME: bug in LH, https://github.com/ucsd-progsys/liquidhaskell/issues/1727
        buildTools = old.buildTools or [] ++ [ nixpkgs.z3 ];
      }
    );
  env = (drv.envFunc { withHoogle = true; }).overrideAttrs
    (old: { nativeBuildInputs = old.nativeBuildInputs ++ [ nixpkgs.ghcid ]; });
in
if nixpkgs.lib.inNixShell then env else drv
