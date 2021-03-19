let
  nodes = import ./cluster.nix {
    node-regions = [ "apples" "oranges" ];
    clients-per-node = 1;
    skip-build = false;
  };
in
{
  network.description = "machines on virtualbox";

  defaults = {
    # tell nixops where to deploy
    deployment.targetEnv = "virtualbox";
    deployment.virtualbox.headless = true;
    # virtualbox target doesn't work for alternate ports
    services.openssh.ports = (import <nixpkgs> { }).lib.mkForce [ 22 ];

    imports = [ ./common.nix ];
  };
}
  // nodes
