{
  description = "CBCAST LH";

  inputs = {
    nixpkgs.url = github:NixOS/nixpkgs/nixos-20.09;

    flake-utils.url = github:numtide/flake-utils;

    liquidhaskell.url = github:plredmond/liquidhaskell/nix-flake;
    liquidhaskell.inputs.nixpkgs.follows = "nixpkgs";
    liquidhaskell.inputs.flake-utils.follows = "flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils, liquidhaskell }:
    let
      composeOverlays = funs: builtins.foldl' nixpkgs.lib.composeExtensions (self: super: {}) funs;
      haskellPackagesOverlay = compiler: final: prev: overrides: {
        haskell = prev.haskell // {
          packages = prev.haskell.packages // {
            ${compiler} = prev.haskell.packages.${compiler}.extend overrides;
          };
        };
      };
      ghc = "ghc8102";
      mkOutputs = system:
        {

          overlays = {
            addCBCASTLH = final: prev: haskellPackagesOverlay ghc final prev (
              self: super:
                let
                  callCabal2nix = prev.haskell.packages.${ghc}.callCabal2nix; # XXX shouldn't this be just haskellPackages.callCabal2nix? there's no reason to specify the compiler
                in
                  with prev.haskell.lib; {
                    cbcast-lh =
                      let
                        src = prev.nix-gitignore.gitignoreSource [ "*.nix" "result" "*.cabal" ] ./.;
                      in
                        callCabal2nix "cbcast-lh" src {};
                  }
            );
          };

          overlay = composeOverlays [
            liquidhaskell.overlay.${system}
            self.overlays.${system}.addCBCASTLH
          ];

          packages =
            let
              pkgs = import nixpkgs { inherit system; overlays = [ self.overlay.${system} ]; };
            in
              { cbcast-lh = pkgs.haskell.packages.${ghc}.cbcast-lh; };

          defaultPackage = self.packages.${system}.cbcast-lh;

          devShell = self.defaultPackage.${system};
        };
    in
      flake-utils.lib.eachDefaultSystem mkOutputs;

}
