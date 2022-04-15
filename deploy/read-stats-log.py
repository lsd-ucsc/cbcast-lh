#!/usr/bin/env python3
import os
import sys
import json
import datetime
import collections

statlog = sys.argv[1]

Sample = collections.namedtuple('Sample', 'host timestamp uptime userct one five fifteen ekg')
host_samples = collections.defaultdict(list)

for line in open(statlog).readlines():
    host, _, line = line.strip().partition('> ')
    host = host.rstrip('.')
    try:
        ekg = json.loads(line)
        assert host_samples[host][-1].ekg is None
        host_samples[host][-1] = host_samples[host][-1]._replace(ekg=ekg)
    except json.decoder.JSONDecodeError:
        timestamp, __up, uptime, userct, __users, __load, __average, one, five, fifteen = line.split()
        # parse betterer
        timestamp = datetime.datetime.strptime(timestamp, '%H:%M:%S').time()
        uptime = datetime.datetime.strptime(uptime, '%H:%M,')
        uptime = uptime - uptime.replace(hour=0, minute=0)
        userct = int(userct)
        one = float(one.strip(','))
        five = float(five.strip(','))
        fifteen = float(fifteen.strip(','))
        host_samples[host].append(Sample(host=host, timestamp=timestamp, uptime=uptime, userct=userct, one=one, five=five, fifteen=fifteen, ekg=None))

# NOTE uptime only has minute-granularity, but timestamp has second-granularity


# GNUPLOT
# https://gist.github.com/fearofcode/5034126

#for host, samples in host_samples.items():
#    print(json.dumps(host))
#    for s in samples:
#        print(s.timestamp, s.one)
#    print()
#    print()

for host, samples in host_samples.items():
    if 'client' in host:
        continue
    print(json.dumps(host))
    for s in samples:
        print(
                s.timestamp,
                'send', s.ekg['cbcast']['broadcastCount']['val'],
                'recv', s.ekg['cbcast']['receiveCount']['val'],
                'dlvr', s.ekg['cbcast']['deliverCount']['val'],
                'd2', s.ekg['cbcast']['dqSizeDist'],
                )
    print()
    print()
