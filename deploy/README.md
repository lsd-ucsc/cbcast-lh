# Nixops deployment

[Nixops manual](https://releases.nixos.org/nixops/nixops-1.7/manual/manual.html)

## Virtualbox

```sh-session
nixops create -d vm net-vm.nix
nixops deploy --force-reboot
```

* If you delete, sometimes nixops fails to destroy vbox disks. Do
  <https://github.com/NixOS/nixops/issues/1173> to remove the conflicting
  disks.
* Sometimes virtualbox service fails on first deploy. Do `nixops deploy -d vm
  --force-reboot` to clear it up.

## AWS
