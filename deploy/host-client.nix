{ target-kv-store
, skip-build ? false
, modules ? [ ]
}:

{ pkgs, lib, nodes, ... }:
{
  imports = modules;

  # run a client service
  systemd.services."kv-client" = {
    wantedBy = [ "multi-user.target" ];
    after = [ "network-online.target" ];
    serviceConfig = {
      ExecStart =
        if skip-build
        then "${pkgs.bash}/bin/bash -c 'echo example ${target-kv-store}'"
        else "${(import ../default.nix).default}/bin/example ${target-kv-store}";
    };
  };

}
