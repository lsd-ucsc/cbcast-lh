let
  lib = (import <nixpkgs> { }).lib;
  nodes = import ./cluster.nix { node-count = 2; } lib;
in
{
  network.description = "machines on virtualbox";

  defaults = {
    # tell nixops where to deploy
    deployment.targetEnv = "virtualbox";
    deployment.virtualbox.headless = true;

    # virtualbox target doesn't work for alternate ports
    services.openssh.ports = lib.mkForce [ 22 ];
  };
}
  // nodes
