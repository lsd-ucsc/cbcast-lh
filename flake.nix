{
  description = "CBCAST LH";

  inputs = {
    nixpkgs.url = github:NixOS/nixpkgs/nixos-21.05;

    flake-utils.url = github:numtide/flake-utils;

    liquidhaskell.url = github:plredmond/liquidhaskell/nix-flake;
    liquidhaskell.inputs.nixpkgs.follows = "nixpkgs";
    liquidhaskell.inputs.flake-utils.follows = "flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils, liquidhaskell }:
    let
      composeOverlays = funs: builtins.foldl' nixpkgs.lib.composeExtensions (self: super: { }) funs;
      haskellOverlay = compiler: final: prev: new:
        let new-overrides = new.overrides or (a: b: { }); in
        {
          haskell = prev.haskell // {
            packages = prev.haskell.packages // {
              ${compiler} = prev.haskell.packages.${compiler}.override
                (old: old // new // {
                  overrides = self: super: old.overrides self super // new-overrides self super;
                });
            };
          };
        };
      haskellPackagesOverlay = compiler: final: prev: cur-packages-overlay:
        haskellOverlay compiler final prev { overrides = cur-packages-overlay; };
      ghc = "ghc8107"; # Based on https://github.com/ucsd-progsys/liquid-fixpoint/blob/develop/stack.yaml#L3
      mkOutputs = system: {

        overlays = {
          addCBCASTLH = final: prev: haskellPackagesOverlay ghc final prev (self: super:
            with prev.haskell.lib; {
              cbcast-lh =
                let
                  src = prev.nix-gitignore.gitignoreSource [ "*.nix" "result" "build-env" "*.cabal" "deploy/" "dist/" ] ./.;
                  drv = super.callCabal2nix "cbcast-lh" src { };
                in
                overrideCabal drv (old: {
                  enableLibraryProfiling = false;
                  buildTools = old.buildTools or [ ] ++ [ final.z3 ];
                });
            });
        };

        overlay = composeOverlays [
          liquidhaskell.overlay.${system}
          self.overlays.${system}.addCBCASTLH
        ];

        packages =
          let pkgs = import nixpkgs { inherit system; overlays = [ self.overlay.${system} ]; };
          in { cbcast-lh = pkgs.haskell.packages.${ghc}.cbcast-lh; };

        defaultPackage = self.packages.${system}.cbcast-lh;

        devShell = self.defaultPackage.${system}.env;
      };
    in
    flake-utils.lib.eachDefaultSystem mkOutputs;

}
