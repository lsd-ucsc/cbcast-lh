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

get    = lambda ip,port,key,val: f'''curl --silent {ip}:{port}/kv/{key}'''
delete = lambda ip,port,key,val: f'''curl --silent -X DELETE {ip}:{port}/kv/{key}'''
put    = lambda ip,port,key,val: f'''curl --silent -X PUT -H "Content-type: application/json" -d '{json.dumps(val)}' {ip}:{port}/kv/{key}'''

if __name__ == '__main__':

    ap = argparse.ArgumentParser()
    ap.add_argument('ip')
    ap.add_argument('port')
    ap.add_argument('--mut', action='store_true')
    ns = ap.parse_args()

    print('#!/usr/bin/env bash')
    for n in range(round(1e5)):
        req = random.choice([get,delete,put]) if ns.mut else get
        cmd = req(ns.ip,ns.port,random.choice(string.ascii_lowercase),randdata(5))
        if ns.mut:
            cmd += ' > /dev/null'
        print(cmd)
