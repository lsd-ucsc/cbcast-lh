{
  # One kv-store will be deployed for each region string. To deploy two stores
  # in one region, name the region twice.
  node-regions ? [ ]
  # How many clients to create for each kv-store. Clients are created in the
  # same region as the kv-store.
, clients-per-node ? 0
  # Name of the AWS access key profile.
, accessKeyId ? ""
  # For debugging
, skip-build ? false
}:
let
  lib = (import <nixpkgs> { }).lib;

  node-port = 7780;
  node-prefix = "kv"; # XXX nodes use the prefix to figure out their peer list; clients must have a distinct prefix
  nodeHostname = { node-ofs, node-region }: "${node-prefix}${toString node-ofs}";
  clientHostname = node-spec@{ node-ofs, ... }: client-ofs: "client${toString client-ofs}${nodeHostname node-spec}";
  kpName = region: "kp-${region}";
  sgName = region: "sg-${region}";

  mergeNAttrs = xs: lib.foldr lib.mergeAttrs { } xs; # XXX cannot merge attrs deeply { foo.bar = [ 4 ]; } will be completely overwritten by { foo.bar = null; }
  #nix-repl> mergeNAttrs [ {foo=3; bar=4;} {bar=0; baz=0;} ]
  #{ bar = 0; baz = 0; foo = 3; }
  indexes = n: if n < 1 then [ ] else lib.range 0 (n - 1);
  # nix-repl> indexes 3
  # [ 0 1 2 ]
  genNodeIds = regions: map ({ fst, snd }: { node-ofs = fst; node-region = snd; }) (lib.zipLists (indexes (builtins.length regions)) regions);
  # nix-repl> :p genNodeIds ["us-east-1" "us-west-1" "us-west-2"]
  # [ { node-ofs = 0; node-region = "us-east-1"; } { node-ofs = 1; node-region = "us-west-1"; } { node-ofs = 2; node-region = "us-west-2"; } ]

  # don't generate the gated attrset when there's no accessKeyId
  awsGate = attrs: if accessKeyId == "" then { } else attrs;

  # aws ec2 properties for a host
  mkEc2PropsModule = node-region: { resources, ... }: {
    deployment.ec2.region = node-region;
    deployment.ec2.accessKeyId = accessKeyId; # refers to ~/.ec2-keys or ~/.aws/credentials
    deployment.ec2.keyPair = resources.ec2KeyPairs."${kpName node-region}";
    deployment.ec2.securityGroups = [ resources.ec2SecurityGroups."${sgName node-region}" ];
  };

  # aws ec2 key-pair for a region
  mkKpFragment = region: {
    "${kpName region}" = {
      inherit region accessKeyId;
    };
  };
  # aws ec2 security-group for a region
  mkSgFragment = region: {
    "${sgName region}" = {
      inherit region accessKeyId;
      rules = [
        { sourceIp = "0.0.0.0/0"; toPort = 22; fromPort = 22; }
        { sourceIp = "0.0.0.0/0"; toPort = node-port; fromPort = node-port; }
      ];
    };
  };

  # client named with both node info and client id; targets the node
  mkClientFragment = node-spec@{ node-region, ... }: client-ofs: {
    ${clientHostname node-spec client-ofs} = import ./host-client.nix {
      target-kv-store = nodeHostname node-spec;
      target-kv-store-port = node-port;
      inherit skip-build;
      modules = [ (mkEc2PropsModule node-region) ];
    };
  };

  # node named with node info
  mkNodeFragment = node-spec@{ node-ofs, node-region }: {
    # only the first argument to ./host-kv.nix is passed here the {pkgs, ... }
    # argument is passed by nixops
    ${nodeHostname node-spec} = import ./host-kv.nix {
      kv-store-offset = node-ofs;
      kv-store-port = node-port;
      inherit node-prefix;
      inherit skip-build;
      modules = [ (mkEc2PropsModule node-region) ];
    };
  };

  regionFragment = let regions = lib.unique node-regions; in
    {
      resources.ec2KeyPairs = mergeNAttrs (map mkKpFragment regions);
      resources.ec2SecurityGroups = mergeNAttrs (map mkSgFragment regions);
    };

  node-specs = genNodeIds node-regions;
  client-offsets = indexes clients-per-node;

  nodes = map mkNodeFragment node-specs;
  clients = lib.crossLists mkClientFragment [ node-specs client-offsets ];
in
awsGate regionFragment // mergeNAttrs (nodes ++ clients)
