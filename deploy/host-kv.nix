{ kv-store-id
, kv-store-port ? 7780
, node-prefix
}:

{ pkgs, lib, nodes, ... }:
let
  node-names = builtins.filter (lib.hasPrefix node-prefix) (builtins.attrNames nodes);
  #get-ip = config: if config.networking.publicIPv4 == null then config.networking.privateIPv4 else config.networking.publicIPv4;
  #node-addrs = map (nn: nodes.${nn}.config.networking.privateIPv4) node-names;
  node-addrs = map (nn: "${nn}:${toString kv-store-port}") node-names; # nixops populates the hosts file with hostnames
  kv-store-args = "${toString kv-store-id} ${builtins.concatStringsSep " " node-addrs}";
in
{
  # users are static (vm target requires a password or a pubkey)
  users.mutableUsers = false;
  users.users."root".password = "trivial plaintext password which will never be used";

  # sshd config, necessary for ssh/nixops administration
  services.openssh = {
    enable = true;
    challengeResponseAuthentication = false;
    passwordAuthentication = false;
    forwardX11 = false;
    permitRootLogin = "prohibit-password";
  };

  # use less obvious ports
  services.openssh.ports = [ 7722 ];
  networking.firewall.allowedTCPPorts = [ kv-store-port ];

  # run a kv store service
  systemd.services."kv-store" = {
    wantedBy = [ "multi-user.target" ];
    after = [ "network-online.target" ];
    serviceConfig = {
      #ExecStart = "${pkgs.bash}/bin/bash -c 'echo ${kv-store-args}'";
      ExecStart = "${import ../. { mkEnv = false; }}/bin/example ${kv-store-args}";
    };
  };

}
