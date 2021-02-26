{ config ? { allowBroken = true; }, ... }:
let
  # get pinned/overridden haskellPackages containing LH
  lh-source = (import <nixpkgs> { }).fetchFromGitHub {
    owner = "plredmond";
    repo = "liquidhaskell";
    rev = "72b37d540"; # nixify branch built from LH `develop` and `propoteDC` branches source Fri 26 Feb 2021 03:50:32 PM UTC
    sha256 = "0hc98kwiffzh2ln2r7b1cln3422y28l6n81dqwwx91q4nk44f2ja";
    fetchSubmodules = true;
  };
  # extract pinned nixpkgs and haskellPackages
  elsewhere = import lh-source { inherit config; tests = false; mkEnv = false; };
  nixpkgs = elsewhere.nixpkgs;
  haskellPackages = elsewhere.haskellPackages.override (
    old: {
      overrides = self: super: with nixpkgs.haskell.lib; (old.overrides self super) // {
        doctest = self.callHackage "doctest" "0.16.3" { }; # nixpkgs version doesn't bulid
        tls = self.callHackage "tls" "1.5.4" { }; # nixpkgs version too old for hpack
        # use server versions from this century
        servant = self.callHackage "servant" "0.18.2" { };
        servant-client = self.callHackage "servant-client" "0.18.2" { };
        servant-client-core = self.callHackage "servant-client-core" "0.18.2" { };
        servant-server = self.callHackage "servant-server" "0.18.2" { };
      };
    }
  );
  # define the derivation and the environment
  drv = nixpkgs.haskell.lib.overrideCabal
    (haskellPackages.callCabal2nix "cbcast-in-lh" (nixpkgs.nix-gitignore.gitignoreSource [ ] ./.) { })
    (
      old: {
        doCheck = true;
        doHaddock = false; # FIXME: bug in LH, https://github.com/ucsd-progsys/liquidhaskell/issues/1727
        buildTools = old.buildTools or [ ] ++ [ nixpkgs.z3 ];
      }
    );
  env = (drv.envFunc { /*withHoogle = true;*/ }).overrideAttrs
    (old: { nativeBuildInputs = old.nativeBuildInputs ++ [ nixpkgs.ghcid ]; });
in
if nixpkgs.lib.inNixShell then env else drv
