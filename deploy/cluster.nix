{ node-regions ? [ ] # one kv-store will be deployed to each region
, clients-per-node ? 0
, skip-build ? false
}:

lib:
let
  node-port = 7780;
  node-prefix = "kv-store-";

  mergeNAttrs = xs: lib.foldr lib.mergeAttrs { } xs;
  indexes = n: if n < 1 then [ ] else lib.range 0 (n - 1);
  mkIds = n: if n < 1 then throw "id-count must be 1 or greater" else lib.range 0 (n - 1);

  # client named with both node and client id; targets the node
  mkClientFragment = node-id: client-id: {
    "kv-client-${toString node-id}-${toString client-id}" = import ./host-client.nix {
      target-kv-store = "${node-prefix}${toString node-id}:${toString node-port}";
      inherit skip-build;
    };
  };

  # node named with node-prefix and id
  mkNodeFragment = node-id: {
    # only the first argument to ./host-kv.nix is passed here the {pkgs, ... }
    # argument is passed by nixops
    "${node-prefix}${toString node-id}" = import ./host-kv.nix {
      kv-store-id = node-id;
      kv-store-port = node-port;
      inherit node-prefix;
      inherit skip-build;
    };
  };

  client-ids = indexes clients-per-node;

  nodes = map mkNodeFragment node-regions;
  clients = lib.crossLists mkClientFragment [ node-regions client-ids ];
in
mergeNAttrs (nodes ++ clients)
