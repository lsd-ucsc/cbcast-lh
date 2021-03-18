{ kv-store-offset
, kv-store-port
, node-prefix
, skip-build ? false
, cbcast-pkg
, modules ? [ ]
}:

{ pkgs, lib, nodes, ... }:
let
  node-names = builtins.filter (lib.hasPrefix node-prefix) (builtins.attrNames nodes);
  #get-ip = config: if config.networking.publicIPv4 == null then config.networking.privateIPv4 else config.networking.publicIPv4;
  #node-addrs = map (nn: nodes.${nn}.config.networking.privateIPv4) node-names;
  node-addrs = map (nn: "${nn}:${toString kv-store-port}") node-names; # nixops populates the hosts file with hostnames
  kv-store-args = "${toString kv-store-offset} ${builtins.concatStringsSep " " node-addrs}";
in
{
  imports = modules;

  networking.firewall.allowedTCPPorts = [ kv-store-port ];

  # run a kv store service
  systemd.services."kv-store" = {
    wantedBy = [ "multi-user.target" ];
    after = [ "network-online.target" ];
    serviceConfig = {
      ExecStart =
        if skip-build
        then "${pkgs.bash}/bin/bash -c 'echo example ${kv-store-args}'"
        else "${cbcast-pkg}/bin/example ${kv-store-args}";
    };
  };

}
