#!/usr/bin/env bash
set -x

./spit.py 54.183.9.206  7780 --mut > kv0.sh
./spit.py 35.82.28.205  7780 --mut > kv1.sh
./spit.py 52.204.233.91 7780       > kv2.sh

chmod +x kv*sh
