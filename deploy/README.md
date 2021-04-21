# Nixops deployment

[Nixops manual](https://releases.nixos.org/nixops/nixops-1.7/manual/manual.html)

## Virtualbox

* If you delete, sometimes nixops fails to destroy vbox disks. Do
  <https://github.com/NixOS/nixops/issues/1173> to remove the conflicting
  disks.
* Sometimes virtualbox service fails on first deploy. Do `nixops deploy -d vm
  --force-reboot` to clear it up.
* Deploy like this
  ```sh-session
nixops create -d vm net-vm.nix
nixops deploy --force-reboot
```

## AWS

Using account <cbcast-test-deploy-2021-group@ucsc.edu>

* Default disk size of the nixos ami is small and breaks the (first dep
  ```sh-session
[root@ip-172-31-2-66:~]# df -h .
Filesystem                Size  Used Avail Use% Mounted on
/dev/disk/by-label/nixos  3.0G  1.4G  1.5G  49% /
```
  * Made it bigger
    ```sh-session
[root@ip-172-31-10-72:~]# df -h .
Filesystem                Size  Used Avail Use% Mounted on
/dev/disk/by-label/nixos  7.9G  1.4G  6.1G  19% /
```

* Deploy like this
  ```sh-session
nixops create -d aws net-aws.nix
nixops deploy -d aws
```
