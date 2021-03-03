{ node-count ? 1
, clients-per-node ? 0
, skip-build ? false
}:

lib:
let
  kv-store-port = 7780;
  node-prefix = "kv-store-";
  node-ids =
    if node-count < 1
    then throw "node must be 1 or greater"
    else lib.range 0 (node-count - 1);

  # only the first argument to ./host-kv.nix is passed here
  # the second argument is passed by nixops
  mk-node-fun = kv-store-id: import ./host-kv.nix {
    inherit kv-store-id;
    inherit kv-store-port;
    inherit node-prefix;
    inherit skip-build;
  };
  mk-client-fun = kv-store-id: import ./host-client.nix {
    target-kv-store = "${node-prefix}${toString kv-store-id}:${toString kv-store-port}";
    inherit skip-build;
  };

  # one node per fragment, and optionally some clients
  mk-network-fragment = kv-store-id: {
    "${node-prefix}${toString kv-store-id}" = mk-node-fun kv-store-id;
    # "kv-client-${toString kv-store-id}
  };
in
lib.foldr lib.mergeAttrs { }
  (map mk-network-fragment node-ids)
