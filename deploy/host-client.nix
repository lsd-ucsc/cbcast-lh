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
        then "${pkgs.bash}/bin/bash -c 'echo example ${target-kv-store}'"
        else "${pkgs.haskellPackages.cbcast-lh}/bin/example ${target-kv-store}";
    };
  };

}
