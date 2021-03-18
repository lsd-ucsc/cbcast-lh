let
  nodes = import ./cluster.nix {
    node-regions = [ "world" ];
    #node-regions = [ "apples" "oranges" ];
    #clients-per-node = 3;
    skip-build = false;
  };
in
{
  network.description = "machines on virtualbox";

  defaults = (import ./common.nix) // {
    # tell nixops where to deploy
    deployment.targetEnv = "virtualbox";
    deployment.virtualbox.headless = true;

    # virtualbox target doesn't work for alternate ports
    services.openssh.ports = (import <nixpkgs> { }).lib.mkForce [ 22 ];
  };
}
  // nodes
