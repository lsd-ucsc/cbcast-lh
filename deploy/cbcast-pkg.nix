let
  cbcast-flake = import ../default.nix;
  pkgs = import cbcast-flake.inputs.nixpkgs {
    overlays = [ cbcast-flake.overlay.${builtins.currentSystem} ];
  };
in
pkgs.haskell.packages."ghc8102".cbcast-lh
