# Nixops deployment

## Virtualbox

```sh-session
nixops create -d vm net-vm.nix
nixops deploy
```

* If you delete, sometimes nixops fails to destroy vbox disks:
  <https://github.com/NixOS/nixops/issues/1173>

## AWS
