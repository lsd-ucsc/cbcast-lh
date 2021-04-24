{ target-kv-store
, target-kv-store-port
, skip-build ? false
, modules ? [ ]
}:

{ pkgs, lib, nodes, ... }:
let
  get-ip = config: if config.networking.publicIPv4 == null then config.networking.privateIPv4 else config.networking.publicIPv4;
  target-ip = get-ip nodes.${target-kv-store}.config;
in
{
  imports = modules;

  # run a client service
  systemd.services."kv-client" = {
    serviceConfig = {
      ExecStart = import ./pkg-client.nix {
        targetAddr = "${target-ip}:${toString target-kv-store-port}";
        inherit pkgs;
      };
    };
  };

}
