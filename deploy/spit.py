#!/usr/bin/env python3
import argparse
import json
import random
import string

def randdata(fuel):
    if fuel < 0:
        return None

    t = random.choice([dict,list,int,float,str,None])
    l = random.randint(0, fuel*4)
    s = lambda: ''.join(random.choice(string.ascii_letters) for _ in range(l))

    if t is dict:
        d = dict()
        for n in range(l):
            fuel -= 1
            d[s()] = randdata(fuel)
        return d
    elif t is list:
        d = list()
        for n in range(l):
            fuel -= 1
            d.append(randdata(fuel))
        return d
    elif t is int:
        return l
    elif t is float:
        return random.random()
    elif t is str:
        return s()
    else:
        return None

get    = lambda addr,key,val: f'''curl -v -s --write-out '\\n' {addr}/kv/{key}'''
delete = lambda addr,key,val: f'''curl -v -s -X DELETE {addr}/kv/{key}'''
put    = lambda addr,key,val: f'''curl -v -s -X PUT -H "Content-type: application/json" -d '{json.dumps(val)}' {addr}/kv/{key}'''

if __name__ == '__main__':

    ap = argparse.ArgumentParser()
    ap.add_argument('addr')
    ap.add_argument('--verbose', action='store_true')
    ap.add_argument('--mut', action='store_true')
    ns = ap.parse_args()

    print('#!/usr/bin/env bash')
    print('set -x')

    request_count = 10_000
    test_length_sec = 8 * 60
    requests_per_sec = request_count / test_length_sec
    sec_per_request = 1 / requests_per_sec
    print('request count:', request_count)
    print('test length sec:', test_length_sec)
    print('RPS:', requests_per_sec)
    print('request delay:', sec_per_request)

    for n in range(request_count):
        req = random.choice([get,delete,put]) if ns.mut else get
        cmd = req(ns.addr,random.choice(string.ascii_lowercase),randdata(5))
        if not ns.verbose:
            cmd += ' 2> /dev/null'
        print(cmd)
        print(f'sleep {sec_per_request:10.10f}')
