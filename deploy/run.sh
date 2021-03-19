#!/usr/bin/env bash
set -x

nixops ssh-for-each -d vm -- journalctl --rotate
nixops ssh-for-each -d vm -- journalctl --vacuum-size=1B
nixops ssh-for-each -d vm -- systemctl restart kv-store

time ./kv0.sh > query-kv0 &
time ./kv1.sh > query-kv1 &
time ./kv2.sh > query-kv2 &
time ./kv3.sh > query-kv3

echo canary has finished, but others might still be running
ps aux | grep kv
