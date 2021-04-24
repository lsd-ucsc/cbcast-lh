let
  node-prefix = "kv";
  skip-build = true;
  bogus = {
    boot.loader.grub.devices = [ "/dev/null" ];
    fileSystems."/" = { device = "/dev/null"; };
  };
in
{
  network.description = "machines on docker via ssh";

  defaults = {
    # tell nixops where to deploy
    deployment.targetEnv = "none";

    imports = [ ./common.nix ];
  };

  kv0 = import ./host-kv.nix { inherit node-prefix;inherit skip-build; kv-store-offset = 0; kv-store-ip-explicit = "10.10.0.10"; kv-store-port = 7780; modules = [{ deployment.targetHost = "localhost"; deployment.targetPort = 7720; } bogus]; };
  kv1 = import ./host-kv.nix { inherit node-prefix;inherit skip-build; kv-store-offset = 1; kv-store-ip-explicit = "10.10.0.11"; kv-store-port = 7780; modules = [{ deployment.targetHost = "localhost"; deployment.targetPort = 7721; } bogus]; };
  kv2 = import ./host-kv.nix { inherit node-prefix;inherit skip-build; kv-store-offset = 2; kv-store-ip-explicit = "10.10.0.12"; kv-store-port = 7780; modules = [{ deployment.targetHost = "localhost"; deployment.targetPort = 7722; } bogus]; };

}
