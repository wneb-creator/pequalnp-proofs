"""Reproduce the signed-source instances used in the L-meta-2592 search.

Usage: python3 build_signed_cases.py OUTPUT_DIRECTORY
This generates CNFs and metadata only. No solver or network call is made.
"""
import itertools
import json
from pathlib import Path
import shutil
import subprocess
import sys

out = Path(sys.argv[1])
out.mkdir(parents=True, exist_ok=True)
generator = Path(__file__).with_name('signed_source.py')

def generate(name, count, not_count=None, lex=True):
    path = out / (name + '.cnf')
    args = [sys.executable, str(generator), 'generate', '--gates', str(count),
            '--rows', 'all', '--used', '--out', str(path)]
    args += ['--unrestricted-negation'] if not_count is None else ['--not-count', str(not_count)]
    if lex: args.append('--lex')
    subprocess.run(args, check=True)
    return path, json.loads(path.with_suffix('.meta.json').read_text())

def add(source, name, clauses, variables=None):
    dest = out / (name + '.cnf')
    with source.open() as src, dest.open('w') as dst:
        h = src.readline().split()
        dst.write(f'p cnf {variables or int(h[2])} {int(h[3]) + len(clauses)}\n')
        shutil.copyfileobj(src, dst)
        for clause in clauses: dst.write(' '.join(map(str, clause)) + ' 0\n')
    return dest

def reader_limit(source, meta, name, pins):
    variables, extra = meta['vars'], []
    for pin in pins:
        readers = []
        for gate in meta['gates']:
            variables += 1
            reader = variables
            readers.append(reader)
            a, b = gate['select'][0][pin], gate['select'][1][pin]
            extra += [[-a, reader], [-b, reader], [-reader, a, b]]
        extra += [[-r for r in triple] for triple in itertools.combinations(readers, 3)]
    return add(source, name, extra, variables)

source, meta = generate('signed2-lex-full', 17, 2)
proper = []
for gate in meta['gates']:
    proper += [[-gate['select'][0][10]], [-gate['select'][1][10]]]
    proper += [[-gate['select'][0][i], -gate['select'][1][i]]
               for i in range(len(gate['select'][0]))]
for kind, second in [('or', 1), ('or', 2), ('nor', 1), ('nor', 2)]:
    gate, negative = meta['gates'][0], kind == 'nor'
    first = [[(-1 if negative else 1) * gate['or']],
             [(1 if negative else -1) * gate['sign'][0]],
             [(1 if negative else -1) * gate['sign'][1]],
             [gate['select'][0][0]], [gate['select'][1][second]]]
    add(source, f'signed2-proper-{kind}0{second}', proper + first)
source = out / 'signed2-proper-nor01.cnf'
reader_limit(source, meta, 'signed2-readers-nor01', [0, 1])
extra = [[-meta['output_sign']]]
for gate in meta['gates'][1:]:
    extra += [[-gate['sign'][0]], [-gate['sign'][1]],
              [-gate['select'][0][0], -gate['select'][1][1]]]
for pin in [0, 1]:
    selected = [gate['select'][side][pin] for gate in meta['gates'][1:] for side in [0, 1]]
    extra.append(selected)
    extra += [[-a, -b] for a, b in itertools.combinations(selected, 2)]
add(source, 'signed2-strong-nor01', extra)

source, meta = generate('signed1-lex-full', 18, 1)
source = add(source, 'signed1-input0', [[meta['marks'][0]]])
reader_limit(source, meta, 'signed1-input0-readers', [0])

source, meta = generate('signed17-free-lex', 17)
extra = []
for gate in meta['gates']:
    extra += [[-gate['or']], [-gate['select'][0][10]], [-gate['select'][1][10]]]
    extra += [[-gate['select'][0][i], -gate['select'][1][i]]
              for i in range(len(gate['select'][0]))]
gate = meta['gates'][0]
extra += [[gate['sign'][0]], [gate['sign'][1]],
          [gate['select'][0][0]], [gate['select'][1][2]]]
add(source, 'signed17-aig-lex-nor02', extra)
