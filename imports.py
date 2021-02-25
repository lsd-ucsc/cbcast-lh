import os,os.path,sys,subprocess

print('digraph G {')

for line in filter(None, map(str.strip, subprocess.check_output(['ag', '^import', 'lib/']).decode('utf8').split('\n'))):
    fpath, _, mpath = line.partition(':')
    importer, _ = os.path.splitext(os.path.basename(fpath))
    imported = mpath.split()[1].split('.')[-1]
    print('\t', importer, '->', imported)

print('}')
