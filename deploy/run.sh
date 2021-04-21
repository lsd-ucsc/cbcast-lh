#!/usr/bin/env bash
set -x

nixops ssh-for-each -d aws -- journalctl --rotate
nixops ssh-for-each -d aws -- journalctl --vacuum-size=1B
nixops ssh-for-each -d aws -- systemctl restart kv-store

time ./kv0.sh > query-kv0 &
time ./kv1.sh > query-kv1 &
time ./kv2.sh > query-kv2

echo canary has finished, but others might still be running
ps aux | grep kv
