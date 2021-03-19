let
  nodes = import ./cluster.nix {
    node-regions = [ "us-west-1" "us-west-2" "us-east-1" ];
    skip-build = false;
    accessKeyId = "cbcast";
  };
in
{
  network.description = "machines on aws";

  defaults = {
    # tell nixops where to deploy
    deployment.targetEnv = "ec2";
    deployment.ec2.instanceType = "t3.micro";

    imports = [ ./common.nix ];
  };
}
  // nodes
