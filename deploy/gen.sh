#!/usr/bin/env bash
set -x

./spit.py 192.168.56.151 7780 --mut > kv0.sh
./spit.py 192.168.56.152 7780 --mut > kv1.sh
./spit.py 192.168.56.153 7780 --mut > kv2.sh
./spit.py 192.168.56.154 7780       > kv3.sh

chmod +x kv*sh
