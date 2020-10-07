{ config ? { allowBroken = true; }, ... }:
let
  # get pinned/overridden haskellPackages containing LH
  lh-source = (import <nixpkgs> {}).fetchFromGitHub {
    owner = "plredmond";
    repo = "liquidhaskell";
    rev = "25ca22970"; # nixify branch built from LH `develop` branch source Wed 07 Oct 2020 08:06:19 PM UTC
    sha256 = "1ms2d7rabidssjm12kxxd63ngxff8ni02fpzd27pzqwwkcdx0d70";
    #rev = "34698bb69"; # nixify-hackage branch as of Sat 19 Sep 2020 02:00:21 AM UTC
    #sha256 = "0igbk5v5bagr62bcgj1zcqm5nw8c4crhvvb84m8bxqbwwr5d3d59";
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
