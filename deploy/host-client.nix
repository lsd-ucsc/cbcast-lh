{ target-kv-store
, skip-build ? false
}:

{ pkgs, lib, nodes, ... }:
{
  imports = [ ./common.nix ];

  # run a client service
  systemd.services."kv-client" = {
    wantedBy = [ "multi-user.target" ];
    after = [ "network-online.target" ];
    serviceConfig = {
      ExecStart =
        if skip-build
        then "${pkgs.bash}/bin/bash -c 'echo ${target-kv-store}'"
        else "${import ../. { mkEnv = false; }}/bin/example ${target-kv-store}";
    };
  };

}
