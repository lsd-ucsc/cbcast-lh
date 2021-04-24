{ kv-store-offset
, kv-store-port
, node-prefix
, kv-store-ip-explicit ? null
, skip-build ? false
, modules ? [ ]
}:

{ pkgs, lib, nodes, ... }:
let
  node-names = builtins.filter (lib.hasPrefix node-prefix) (builtins.attrNames nodes);
  get-ip = config: if kv-store-ip-explicit != null then kv-store-ip-explicit else config.networking.publicIPv4; # when do we use config.networking.publicIPv4?
  node-ipports = map (nn: "${get-ip nodes.${nn}.config}:${toString kv-store-port}") node-names;
  node-hostports = map (nn: "${nn}:${toString kv-store-port}") node-names; # nixops populates the hosts file with hostnames
  kv-store-args = "${toString kv-store-offset} ${builtins.concatStringsSep " " node-ipports}";
  debugScript = ''
    echo example ${kv-store-args}
    echo hostports ${toString node-hostports}
    echo ipports ${toString node-ipports}
  '';
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
        then "${pkgs.bash}/bin/bash ${pkgs.writeText "debug.sh" debugScript}"
        else "${(import ../default.nix).default}/bin/example ${kv-store-args}";
    };
  };

}
