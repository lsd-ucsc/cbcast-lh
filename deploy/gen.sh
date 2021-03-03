#!/usr/bin/env bash
set -x

./spit.py 192.168.56.131 7780 --mut > kv-store-6.sh
./spit.py 192.168.56.128 7780 --mut > kv-store-7.sh
./spit.py 192.168.56.132 7780 --mut > kv-store-4.sh
./spit.py 192.168.56.129 7780 --mut > kv-store-5.sh
./spit.py 192.168.56.135 7780 --mut > kv-store-2.sh
./spit.py 192.168.56.133 7780 --mut > kv-store-3.sh
./spit.py 192.168.56.130 7780 --mut > kv-store-0.sh
./spit.py 192.168.56.134 7780       > kv-store-1.sh

chmod +x kv-store*sh
