{
  users.mutableUsers = false;

  boot.cleanTmpDir = true;
  nix.gc.automatic = true;
  system.autoUpgrade.enable = false; # would be cool, but not in production

  # when users are not mutable, the vm tarket requires a password or pubkey set
  users.users."root".password = "trivial plaintext password which will never be used";

  # sshd config, necessary for ssh/nixops administration
  services.openssh = {
    enable = true;
    challengeResponseAuthentication = false;
    passwordAuthentication = false;
    forwardX11 = false;
    permitRootLogin = "prohibit-password";
  };
}
