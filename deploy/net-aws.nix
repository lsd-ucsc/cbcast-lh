let
  nodes = import ./cluster.nix {
    # 8 nodes with 3 clients each is 24 hosts
    node-regions = [
      "us-west-1" # 0 -- N. California (SJC)
      "us-west-1" # 1 -- N. California (SJC)
      "us-west-2" # 2 -- Oregon (SEA)
      "us-east-1" # 3 -- N. Virginia
      "us-east-1" # 4 -- N. Virginia
      "ap-northeast-1" # 5 -- Tokyo
      "eu-central-1" # 6 -- N. Virginia
      "eu-central-1" # 7 -- N. Virginia
    ];
    clients-per-node = 3;
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
