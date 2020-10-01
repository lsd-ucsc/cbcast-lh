{ config ? { allowBroken = true; }, ... }:
let
  # get pinned/overridden haskellPackages containing LH
  lh-source = (import <nixpkgs> {}).fetchFromGitHub {
    owner = "plredmond";
    repo = "liquidhaskell";
    rev = "5ba294b19"; # nixify branch built from LH source Tue 29 Sep 2020 10:50:47 PM UTC
    sha256 = "0z0r0nf3qn4zxcpnx8xw84p5i4x795ac5jih33pjivlsgchk3fag";
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
