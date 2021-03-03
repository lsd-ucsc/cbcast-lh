{
  network.description = "machines on virtualbox";

  kv-server_test2 = args@{ pkgs, lib, ... }:
    (import ./host-kv.nix args)
    // {
      # tell nixops where to deploy
      deployment.targetEnv = "virtualbox";
      deployment.virtualbox.headless = true;

      # virtualbox target doesn't work for alternate ports
      services.openssh.ports = [ 22 ];
    };

}
