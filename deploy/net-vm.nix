let
  lib = (import <nixpkgs> { }).lib;
  args = {
    node-count = 2;
    clients-per-node = 3;
    skip-build = true;
  };
  nodes = import ./cluster.nix args lib;
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
