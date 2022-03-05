#!/usr/bin/env python3 

import os,os.path,sys,subprocess

print('digraph G {')
print('rankdir=BT;')

#for line in filter(None, map(str.strip, subprocess.check_output(['ag', '^import', 'lib/']).decode('utf8').split('\n'))):
#    fpath, _, mpath = line.partition(':')
#    importer, _ = os.path.splitext(os.path.basename(fpath))
#    imported = mpath.split()[1].split('.')[-1]
#    print('\t', importer, '->', imported)

modules = set()

is_verif = lambda s: 'Verif' in s or 'Liquid' in s

for line in filter(None, map(str.strip, subprocess.check_output(['ag', '^import', 'lib/']).decode('utf8').split('\n'))):
    fpath, _, mpath = line.partition(':')
    #print(fpath, mpath)
    importer = os.path.splitext(fpath)[0].replace('lib/', '').replace('/', '\\n')
    imported = mpath.split()[1].replace('.', '\\n')

    modules.add(importer)
    modules.add(imported)

    wt = 2
    pw = 2
    color = 'black'
    if is_verif(importer) and is_verif(imported):
        color = 'red'
    elif not is_verif(importer) and not is_verif(imported):
        color = 'red'
        color = 'blue'
    elif importer.startswith(imported) and imported != 'MessagePassingAlgorithm':
        wt = 3
        pw = 3
    else:
        wt = 1
        pw = 0.5

    if imported.endswith('ProofCombinators'):
        continue

    shorten = lambda s: s.replace('MessagePassingAlgorithm', 'MPA').replace('Verification', 'Verif')
    print(f'\t"{shorten(importer)}" -> "{shorten(imported)}" [weight={wt},penwidth={pw},color={color}];')

for mod in sorted(modules):
    shape = 'oval'
    color = 'blue'
    if is_verif(mod):
        shape = 'box'
        color = 'red'

    if mod.endswith('ProofCombinators'):
        continue

    print(f'\t"{shorten(mod)}" [shape={shape},color={color}];')

print('}')
