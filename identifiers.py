import os
import re
import sys
import math
import itertools
import collections

def get_binders(toks):
    alnum_toks = list(itertools.chain.from_iterable(re.findall(r'\w+', b) for b in toks))
    return set(toks + alnum_toks)

class NotBinder(Exception):
    pass

pattern_binder = lambda s: s[0].isupper() # assuming no type-operator style constructors

def split_binder(toks, infix_operator_names, current_binder=None):
    line = ' '.join(toks)
    if False:
        pass

    elif toks[0] in {'ple', 'reflect', 'measure', 'inline', 'INLINE'}:
        assert len(toks) == 2
        return toks[1], []

    elif toks[0] == 'type':
        if '=' in toks:
            index = toks.index('=')
            before, after = toks[:index], toks[index+1:]
        else:
            before, after = toks, []
        binder = before.pop(1)
        return binder, after

    elif toks[0] == 'data':
        if '=' in toks:
            index = toks.index('=')
            before, after = toks[:index], toks[index+1:]
        else:
            before, after = toks, []
        binder = before.pop(1)
        return binder, after


    elif '::' in toks:
        index = toks.index('::')
        before, after = toks[:index], toks[index+1:]
        (binder,) = before
        return binder.strip('()'), after

    elif '=' in toks or toks[0] == current_binder:
        if '=' not in toks:
            toks = toks + ['=']
        index = toks.index('=')
        before, after = toks[:index], toks[index+1:]
        binder = None
        for op in infix_operator_names:
            if op in before:
                assert binder is None, (binder, line)
                binder = before.pop(before.index(op)).strip('()')
                break
        else:
            assert binder is None, (binder, line)
            binder = before.pop(0)
        arg_identifier_toks = list(itertools.chain.from_iterable(re.findall(r'\w+', b) for b in before))
        return binder, list(filter(pattern_binder, arg_identifier_toks)) + after

    else:
        raise NotBinder(line)
    return None, toks

def walk(path):
    try:
        subs = os.listdir(path)
        return itertools.chain.from_iterable(
                walk(os.path.join(path, sub)) for sub in subs)
    except NotADirectoryError:
        return [path]

def haskell(sourcecode):
    ignored = {'{-@', '@-}', '{-#', '#-}'}
    infix_operator_names = {'===>', '||||'} # no way to detect infix operator bodies
    binder = None
    binders = list()
    for line in sourcecode.split('\n'):
        if re.match(r'\s*--', line):
            continue # skip single line comments

        # ignore midline comments
        midline_comment = re.search(r'--', line)
        if midline_comment:
            comment_start, _ = midline_comment.span()
            line = line[:comment_start]

        indented = bool(re.match('\s+', line))

        toks = [t for t in line.split() if t not in ignored]
        if not toks:
            continue # skip empty lines

        # end the current binder
        if not indented and binder is not None and toks[0] != binder:
            yield binder, binders
            binder = None
            binders = list()

        # start a new binder
        if not indented:
            try:
                binder, toks = split_binder(toks, infix_operator_names, binder)
            except NotBinder as e:
                if toks[0] in {'import', 'module', 'OPTIONS_GHC'}:
                    continue
                print('NOT BINDER', e, file=sys.stderr)

        # add sub-binders to the binder
        binders.extend(get_binders(toks))

file_binder = collections.defaultdict(list)
binder_subbinders = collections.defaultdict(list)

for p in itertools.chain.from_iterable(map(walk, os.environ['WALK_PATHS'].split())):
    if p.endswith('.swp') or p.endswith('.swo'):
        continue # skip vim files
    if p.endswith('.py'):
        continue # skip python files
    print('READING:', p, file=sys.stderr)
    with open(p, mode='r', encoding='utf8') as fd:
        for binder, subbinders in haskell(fd.read()):
            file_binder[p].append(binder)
            binder_subbinders[binder].extend(subbinders)

#binders = set(itertools.chain.from_iterable(file_binder.values()))
#print(file_binder)
#print(binders)
#print(binder_subbinders)

def ignore(binder):
    ignored = {'deliverableAfterTick_lemma',
            'deliverableAfterTick',
            'deliverableNewMessage',
            'broadcastAlwaysDelivers',
            }
    return      ('sized' in binder) \
            or re.search('as[A-Z]$', binder) \
            or binder.startswith('list') \
            or (binder in ignored) \
            or pattern_binder(binder)

print('digraph g {')
for binder, subbinders in binder_subbinders.items():
    if ignore(binder):
        continue
    shape = 'cylinder' if pattern_binder(binder) else 'box'
    print(f'"{binder}" [shape={shape}];')
    for sub in set(subbinders):
        if ignore(sub):
            continue
        if sub in binder_subbinders:
            if pattern_binder(binder) and pattern_binder(sub):
                wt = 2
                wd = 2
                color = 'red'
            elif not pattern_binder(binder) and not pattern_binder(sub):
                wt = 2
                wd = 2
                color = 'blue'
            else:
                wt = 1
                wd = 1
                color = 'black'
            #wt = subbinders.count(sub)
            #wd = 1 + round(math.log(wt))
            print(f'"{binder}" -> "{sub}";')
            #print(f'"{binder}" -> "{sub}" [weight={wt},penwidth={wd},color={color}];')
print('}')
