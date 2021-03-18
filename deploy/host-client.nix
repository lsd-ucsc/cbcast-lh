{ target-kv-store
, skip-build ? false
, cbcast-pkg
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
        else "${cbcast-pkg}/bin/example ${target-kv-store}";
    };
  };

}
