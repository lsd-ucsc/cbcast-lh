let
  nodes = import ./cluster.nix {
    node-regions = [ "us-west-1" "us-west-2" "us-east-1" ];
    clients-per-node = 2;
    skip-build = false;
  };
  accessKeyId = "cbcast";
in
{
  network.description = "machines on aws";

  resources.ec2KeyPairs.nixops-admin = {
    inherit accessKeyId;
    region = "us-west-1";
  };

  defaults = { resources, ... }: {
    # tell nixops where to deploy
    deployment.targetEnv = "ec2";
    deployment.ec2.instanceType = "t3.micro";
    deployment.ec2.accessKeyId = accessKeyId; # refers to ~/.ec2-keys or ~/.aws/credentials
    deployment.ec2.keyPair = resources.ec2KeyPairs.nixops-admin;

    imports = [ ./common.nix ];
  };
}
  // nodes
