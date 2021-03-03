{ node-count ? 1
}:

lib:
let
  node-prefix = "kv-store-";
  node-ids =
    if node-count < 1
    then throw "node must be 1 or greater"
    else lib.range 0 (node-count - 1);

  # only the first argument to ./host-kv.nix is passed here
  # the second argument is passed by nixops
  mk-node-fun = kv-store-id: import ./host-kv.nix {
    inherit kv-store-id;
    inherit node-prefix;
  };

  mk-network-fragment = kv-store-id: {
    "${node-prefix}${toString kv-store-id}" = mk-node-fun kv-store-id;
  };
in
lib.foldr lib.mergeAttrs { }
  (map mk-network-fragment node-ids)
