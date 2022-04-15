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

t2dt = lambda t: datetime.datetime.combine(datetime.datetime.strptime('','').date(), t)

for host, samples in host_samples.items():
    if 'client' in host:
        continue
    print(json.dumps(host))
    first = None
    for i, s in enumerate(samples):
        if first is None:
            first = s
        # comment this branch to show all samples
        if i < len(samples) - 1:
            continue
        print(
                t2dt(s.timestamp) - t2dt(first.timestamp),
                f'''send {s.ekg['cbcast']['broadcastCount']['val']:6}''',
                f'''recv {s.ekg['cbcast']['receiveCount']['val']:6}''',
                f'''dlvr {s.ekg['cbcast']['deliverCount']['val']:6}''',
                'OKAY' if s.ekg['cbcast']['receiveCount']['val'] == s.ekg['cbcast']['deliverCount']['val'] else 'WAIT',
#               'dq', s.ekg['cbcast']['dqSizeDist'],
                f'''dq-mean-size {s.ekg['cbcast']['dqSizeDist']['mean']:<10.4}''',
                f'''one-minute-load {s.one:<10}''',
                )
    print()
    print()
