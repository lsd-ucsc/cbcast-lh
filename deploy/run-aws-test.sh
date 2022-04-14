#!/usr/bin/env bash
set -e -u -o pipefail
set -x

DEPLOYMENT=aws
NIX_NETWORK=net-aws.nix

# make sure the nixops-network exists
if nixops info -d $DEPLOYMENT > /dev/null; then
    echo found $DEPLOYMENT deployment
else
    nixops create -d $DEPLOYMENT $NIX_NETWORK
    nixops deploy -d $DEPLOYMENT --force-reboot
fi

# obtain lists of clients and servers
clients=$(nixops info -d vm --plain | cut -f1 | grep client)
servers=$(nixops info -d vm --plain | cut -f1 | grep -v client)

# prepare all nodes by clearing journals and empty nix store and freshbooting
nixops ssh-for-each -d $DEPLOYMENT --include $clients -- systemctl stop kv-client.service || true
nixops ssh-for-each -d $DEPLOYMENT -- journalctl --rotate
nixops ssh-for-each -d $DEPLOYMENT -- journalctl --vacuum-size=1B
nixops ssh-for-each -d $DEPLOYMENT -- nix-collect-garbage
#nixops reboot -d $DEPLOYMENT # slow mode
nixops ssh-for-each -d $DEPLOYMENT --include $servers -- systemctl restart kv-store.service # fast mode

# check machines once before starting
nixops check -d $DEPLOYMENT || true

# start all the clients (see pkg-client.nix; they generate curl commands and then run them)
# TODO: write a proper python client to observe conflicts
nixops ssh-for-each -d $DEPLOYMENT --include $clients -- systemctl start kv-client.service

# wait for the clients to finish
truncate -s0 stats.log
clientCount=$(echo $clients | wc -w)
while sleep 10; do
    # log host stats
    nixops ssh-for-each -d $DEPLOYMENT -- 'uptime && curl -s localhost:9890 --header "Accept: application/json" || true' 2>&1 | tee -a stats.log
    # check if clients are done
    doneCount=$(nixops ssh-for-each -d $DEPLOYMENT --include $clients -- journalctl -u kv-client -n2 2>&1 | grep -i succeeded -c || true)
    if [[ $clientCount -eq $doneCount ]]; then
        break
    fi
done
