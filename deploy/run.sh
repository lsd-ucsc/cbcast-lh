#!/usr/bin/env bash
set -x

nixops ssh-for-each -- journalctl --rotate
nixops ssh-for-each -- journalctl --vacuum-size=1B
nixops ssh-for-each -- systemctl restart kv-store

time ./kv-store-6.sh &
time ./kv-store-7.sh &
time ./kv-store-4.sh &
time ./kv-store-5.sh &
time ./kv-store-2.sh &
time ./kv-store-3.sh &
time ./kv-store-0.sh &
time ./kv-store-1.sh > query

echo canary has finished, but others might still be running
ps aux | grep kv-store
