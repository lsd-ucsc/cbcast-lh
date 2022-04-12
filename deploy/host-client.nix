{ target-kv-store
, target-kv-store-port
, skip-build ? false
, modules ? [ ]
}:

{ pkgs, lib, nodes, ... }:
let
  get-ip = config:
    let ip = config.networking.publicIPv4;
    in lib.traceIf (ip == null) "ip is null; are you doing --build-only?" ip;
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
