let
  # import cbcast-lh and access nixpkgs & haskellPackages in the passthru
  elsewhere = import ../. { mkEnv = false; };
  pkgs = elsewhere.passthru.nixpkgs;
in
pkgs.mkShell {
  # make sure the shell environment uses the pinned nixpkgs
  NIX_PATH = "nixpkgs=${pkgs.path}";

  # use the nixops state in cwd; be careful it doesn't get copied to the nix store
  NIXOPS_STATE = builtins.toPath (./. + "/deployments.nixops");
  # use nixops
  buildInputs = with pkgs; [ nixops sqlite ];
}
