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
    #deployment.ec2.accessKeyId = we set this on the individual instances in cluster.nix, because it's necessary for the regional SGs and KPs anyway
    deployment.ec2.instanceType = "t3.micro";
    deployment.ec2.ebsInitialRootDiskSize = 8;

    imports = [ ./common.nix ];
  };
}
  // nodes
