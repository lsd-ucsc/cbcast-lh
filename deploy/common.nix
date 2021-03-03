{ ... }:

{
  # users are static (vm target requires a password or a pubkey)
  users.mutableUsers = false;
  users.users."root".password = "trivial plaintext password which will never be used";

  # sshd config, necessary for ssh/nixops administration
  services.openssh = {
    enable = true;
    ports = [ 7722 ];
    challengeResponseAuthentication = false;
    passwordAuthentication = false;
    forwardX11 = false;
    permitRootLogin = "prohibit-password";
  };
}
