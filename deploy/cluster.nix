{ node-regions ? [ ] # one kv-store will be deployed to each region
, clients-per-node ? 0
, skip-build ? false
}:
let
  lib = (import <nixpkgs> { }).lib;
  node-port = 7780;
  node-prefix = "kv";
  node-hostname = { node-ofs, node-region }: "${node-prefix}${toString node-ofs}";
  client-hostname = node-spec@{ node-ofs, ... }: client-ofs: "${node-hostname node-spec}client${toString client-ofs}";

  mergeNAttrs = xs: lib.foldr lib.mergeAttrs { } xs;
  #nix-repl> mergeNAttrs [ {foo=3; bar=4;} {bar=0; baz=0;} ]
  #{ bar = 0; baz = 0; foo = 3; }
  indexes = n: if n < 1 then [ ] else lib.range 0 (n - 1);
  # nix-repl> indexes 3
  # [ 0 1 2 ]
  genNodeIds = regions: map ({ fst, snd }: { node-id = fst; node-region = snd; }) (lib.zipLists (indexes (builtins.length regions)) regions);
  # nix-repl> :p genNodeIds ["us-east-1" "us-west-1" "us-west-2"]
  # [ { node-id = 0; node-region = "us-east-1"; } { node-id = 1; node-region = "us-west-1"; } { node-id = 2; node-region = "us-west-2"; } ]


  # client named with both node info and client id; targets the node
  mkClientFragment = node-spec@{ node-id, node-region }: client-id: {
    ${client-hostname node-spec client-id} = import ./host-client.nix {
      target-kv-store = "${node-hostname node-spec}:${toString node-port}";
      inherit skip-build;
      modules = [{ deployment.ec2.region = node-region; }];
    };
  };

  # node named with node info
  mkNodeFragment = node-spec@{ node-id, node-region }: {
    # only the first argument to ./host-kv.nix is passed here the {pkgs, ... }
    # argument is passed by nixops
    ${node-hostname node-spec} = import ./host-kv.nix {
      kv-store-offset = node-id;
      kv-store-port = node-port;
      inherit node-prefix;
      inherit skip-build;
      modules = [{ deployment.ec2.region = node-region; }];
    };
  };

  node-specs = genNodeIds node-regions;
  client-ids = indexes clients-per-node;

  nodes = map mkNodeFragment node-specs;
  clients = lib.crossLists mkClientFragment [ node-specs client-ids ];
in
mergeNAttrs (nodes ++ clients)
