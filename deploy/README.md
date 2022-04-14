# Nixops deployment

[Nixops manual](https://releases.nixos.org/nixops/nixops-1.7/manual/manual.html)

## Virtualbox

* If you delete, sometimes nixops fails to destroy vbox disks. Do
  <https://github.com/NixOS/nixops/issues/1173> to remove the conflicting
  disks.
* Sometimes virtualbox service fails on first deploy. Do `nixops deploy -d vm
  --force-reboot` or open the VirtualBox UI's media manager and delete the
  disks to clear it up.
* Deploy like this
  ```sh-session
nixops create -d vm net-vm.nix
nixops deploy --force-reboot
```

## AWS

Make a credentials file `$FILE` with a `cbcast` profile:
```
[cbcast]
aws_access_key_id = AKIABOGUSACCESSKEY
aws_secret_access_key = BOGUSSECRETACCESSKEY
```
Run nixops with an envvar to locate `$FILE`.
```sh
export AWS_SHARED_CREDENTIALS_FILE=$FILE
```
Make sure you have no conflicting files or profiles (such as `~/.ec2-keys` or
`~/.aws/credentials` containing a `cbcast` profile).

* Deploy like this
  ```sh-session
nixops create -d aws net-aws.nix
nixops deploy -d aws
```
* Default disk size of the nixos ami is small and breaks the (first deploy has to upgrade nixos to the one we're pinned on, as well as upload haskell libraries)
  ```sh-session
[root@ip-172-31-2-66:~]# df -h .
Filesystem                Size  Used Avail Use% Mounted on
/dev/disk/by-label/nixos  3.0G  1.4G  1.5G  49% /
```
  * Made it bigger in nix code
    ```sh-session
[root@ip-172-31-10-72:~]# df -h .
Filesystem                Size  Used Avail Use% Mounted on
/dev/disk/by-label/nixos  7.9G  1.4G  6.1G  19% /
```
  * After initial deployment
    ```sh-session
[root@ip-172-31-10-72:~]# df -h .
Filesystem                Size  Used Avail Use% Mounted on
/dev/disk/by-label/nixos  7.9G  6.3G  1.2G  85% /
```
