{ kv-store-offset
, kv-store-port
, node-prefix
, skip-build ? false
, modules ? [ ]
}:

{ pkgs, lib, nodes, ... }:
let
  node-names = builtins.filter (lib.hasPrefix node-prefix) (builtins.attrNames nodes);
  get-ip = config:
    let ip = if config.networking.publicIPv4 == null then config.networking.privateIPv4 else config.networking.publicIPv4;
    in lib.traceIf (ip == null) "ip is null; are you doing --build-only?" ip;
  node-ipports = map (nn: "${get-ip nodes.${nn}.config}:${toString kv-store-port}") node-names;
  node-hostports = map (nn: "${nn}:${toString kv-store-port}") node-names; # nixops populates the hosts file with hostnames
  kv-store-args = "${toString kv-store-offset} ${builtins.concatStringsSep " " node-ipports}";
  # debugscript starts a flask server binding the host:port specified in
  # kv-store-args, and after 3sec attempts to hit the node-hostports and
  # node-ipports
  debugScript = ''
    #!${pkgs.python3.withPackages (p: [p.flask p.requests])}/bin/python

    import sys
    import flask
    import requests
    import threading
    log = lambda *args, **kwargs: print(*args, flush=True, **kwargs)

    kvStoreArgs = """${toString kv-store-args}""".split()
    hostPorts = """${toString node-hostports}""".split()
    ipPorts = """${toString node-ipports}""".split()

    pid = int(kvStoreArgs.pop(0))
    assert len(kvStoreArgs) == len(hostPorts) == len(ipPorts)

    def background():
        for hp in hostPorts + ipPorts:
            try:
                requests.head(f'http://{hp}')
            except Exception as e:
                log(f'[FAIL] {hp} {e.__class__.__name__}')
            else:
                log(f'[OKAY] {hp}')

    if __name__ == '__main__':
        threading.Timer(3, background).start()
        host, _, port = kvStoreArgs[pid].partition(':')
        flask.Flask(__name__).run(host=host, port=port)
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
        then pkgs.writeScript "debug.py" debugScript
        else "${(import ../default.nix).default}/bin/example ${kv-store-args}";
    };
  };

}
