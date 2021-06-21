#!/usr/bin/env bash
set -e -u -o pipefail
set -x

DEPLOYMENT=aws
NIX_NETWORK=net-aws.nix

if nixops info -d $DEPLOYMENT > /dev/null; then
    echo found $DEPLOYMENT deployment
else
    nixops create -d $DEPLOYMENT $NIX_NETWORK
    nixops deploy -d $DEPLOYMENT --force-reboot
fi

nixops ssh-for-each -d $DEPLOYMENT -- systemctl stop kv-client.service || true
nixops ssh-for-each -d $DEPLOYMENT -- journalctl --rotate
nixops ssh-for-each -d $DEPLOYMENT -- journalctl --vacuum-size=1B
nixops ssh-for-each -d $DEPLOYMENT -- nix-collect-garbage
nixops reboot -d $DEPLOYMENT #nixops ssh-for-each -d $DEPLOYMENT -- systemctl restart kv-store

date -u | tee check.log
nixops check -d $DEPLOYMENT | tee check.log || true

nixops ssh-for-each -d $DEPLOYMENT -- systemctl start kv-client.service || true
trap "nixops ssh-for-each -d $DEPLOYMENT 'systemctl status kv-client' 2>&1| tee clients.log" SIGINT EXIT

while sleep 10; do
    date -u | tee -a check.log
    nixops check -d $DEPLOYMENT | tee -a check.log || true
done