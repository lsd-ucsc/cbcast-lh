{ node-count ? 1
, clients-per-node ? 0
, skip-build ? false
}:

lib:
let
  kv-store-port = 7780;
  node-prefix = "kv-store-";

  mergeNAttrs = xs: lib.foldr lib.mergeAttrs { } xs;
  makeIds = n: if n < 1 then throw "id-count must be 1 or greater" else lib.range 0 (n - 1);

  # only the first argument to ./host-kv.nix is passed here
  # the second argument is passed by nixops
  mkNodeFun = kv-store-id: import ./host-kv.nix {
    inherit kv-store-id;
    inherit kv-store-port;
    inherit node-prefix;
    inherit skip-build;
  };
  mkClientFun = kv-store-id: import ./host-client.nix {
    target-kv-store = "${node-prefix}${toString kv-store-id}:${toString kv-store-port}";
    inherit skip-build;
  };

  node-ids = makeIds node-count;
  client-ids = makeIds clients-per-node;

  # one node and several clients per fragment
  mkNetworkFragment = kv-store-id: {
    "${node-prefix}${toString kv-store-id}" = mkNodeFun kv-store-id;
  };
  #// lib.listToAttrs (map (id: {"kv-client-${toString kv-store-id}-${toString client-id}"=mkClientFun client-id;};
  # "kv-client-${toString kv-store-id}
in
mergeNAttrs
  (map mkNetworkFragment node-ids)
