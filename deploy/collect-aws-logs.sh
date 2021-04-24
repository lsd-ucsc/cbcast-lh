#!/usr/bin/env bash
set -e -u -o pipefail
set -x

nixops ssh-for-each -d $DEPLOYMENT -- journalctl -u kv-store -u kv-client | tee log
