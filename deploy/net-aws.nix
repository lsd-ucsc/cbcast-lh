let
  nodes = import ./cluster.nix {
    node-regions = [ "us-west-1" "us-west-2" "us-east-1" ];
    clients-per-node = 2;
    skip-build = false;
    cbcast-pkg = import ./cbcast-pkg.nix;
  };
in
{
  network.description = "machines on aws";

  defaults = {
    # tell nixops where to deploy
    deployment.targetEnv = "ec2";
    deployment.ec2.instanceType = "t3.micro";
    deployment.ec2.keyPair = "cbcast";
    deployment.ec2.privateKey = "./cbcast-test-deploy-2021-group.csv";

    imports = [ ./common.nix ];
  };
}
  // nodes
