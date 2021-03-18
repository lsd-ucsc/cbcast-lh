{ target-kv-store
, skip-build ? false
, modules ? [ ]
}:

{ pkgs, lib, nodes, ... }:
let
  ghc = "ghc8102"; # FIXME obtain this from nixpkgs config
in
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
        else "${pkgs.haskell.packages.${ghc}.cbcast-lh}/bin/example ${target-kv-store}";
    };
  };

}
