"""Independently replay rational row traces and extract a polynomial certificate.

The CAS's Groebner claim is never used. Each input row must be a scalar monomial
multiple of an already established polynomial; every output is checked exactly.
"""
import argparse
from collections import Counter, defaultdict
from fractions import Fraction
import json
import re
from pathlib import Path
import sympy as sp

ap = argparse.ArgumentParser(description=__doc__)
ap.add_argument('input')
ap.add_argument('trace')
ap.add_argument('output')
args = ap.parse_args()
lines = Path(args.input).read_text().splitlines()
_, n, m = map(int, lines[0].split())
names = lines[1].split()
assert len(names) == n
variables = sp.symbols(' '.join(names), seq=True)
locals_ = dict(zip(names, variables))
name_index = {name:i for i,name in enumerate(names)}

def parse(text):
    if text.startswith('('):
        result = {}
        for term in text.split(' + '):
            match = re.fullmatch(r'\((-?\d+(?:/\d+)?)\*(.+)\)', term)
            assert match, ('Malformed OpenF4 term', term)
            coeff = Fraction(match.group(1));monomial = match.group(2)
            exponents = [0]*n
            if monomial != '1':
                for factor in monomial.split('*'):
                    pair = factor.split('^')
                    assert len(pair) == 2 and pair[0] in name_index and pair[1].isdigit()
                    exponents[name_index[pair[0]]] += int(pair[1])
            key = tuple(exponents)
            result[key] = result.get(key,Fraction(0))+coeff
            if not result[key]:del result[key]
        return result
    p = sp.Poly(sp.sympify(text.replace('^', '**'), locals=locals_), *variables, domain=sp.QQ)
    return {tuple(mon): Fraction(int(c.p), int(c.q)) for mon, c in p.terms() if c}

def add(dst, src, scalar=Fraction(1), shift=None):
    if shift is None:
        shift = (0,) * n
    for mon, coeff in src.items():
        new = tuple(a+b for a,b in zip(mon, shift))
        dst[new] = dst.get(new, Fraction(0)) + scalar*coeff
        if not dst[new]:
            del dst[new]

def shape(poly):
    assert poly
    low = tuple(min(mon[i] for mon in poly) for i in range(n))
    lead = poly[max(poly)]
    key = tuple(sorted((tuple(a-b for a,b in zip(mon,low)), c/lead) for mon,c in poly.items()))
    return key, low, lead

known = []
by_shape = defaultdict(list)
def register(poly, kind, parents=None):
    key, low, lead = shape(poly)
    for old in by_shape[key]:
        if known[old]['poly'] == poly:
            return old
    idx = len(known)
    known.append({'poly':poly, 'kind':kind, 'parents':parents or [], 'low':low, 'lead':lead})
    by_shape[key].append(idx)
    return idx

def identify(poly):
    key, low, lead = shape(poly)
    for old in by_shape[key]:
        entry = known[old]
        shift = tuple(a-b for a,b in zip(low,entry['low']))
        if min(shift) >= 0:
            return old, lead/entry['lead'], shift
    raise AssertionError(('Unproved matrix input row', poly))

generators = [parse(line) for line in lines[2:2+m]]
assert len(generators) == m
records = [line.split('\t') for line in Path(args.trace).read_text().splitlines()]
refs = Counter()
for rec in records:
    if rec[0] == 'A':
        refs[int(rec[2])] += 1
        refs[int(rec[3])] += 1
    elif rec[0] in ('S','O'):
        refs[int(rec[2] if rec[0] == 'S' else rec[1])] += 1
vectors, input_polys, input_sources = {}, {}, {}
counts = Counter()
last_constant = None
def consume(idx):
    refs[idx] -= 1
    if refs[idx] == 0:
        vectors.pop(idx, None)

for rec in records:
    kind = rec[0]
    counts[kind] += 1
    if kind == 'G':
        idx = int(rec[1]); poly = parse(rec[2])
        assert poly == generators[idx], ('Generator mismatch', idx)
        register(poly, {'generator':idx})
    elif kind == 'I':
        idx = int(rec[1]); poly = parse(rec[2])
        input_sources[idx] = identify(poly)
        input_polys[idx] = poly
        vectors[idx] = {idx: Fraction(1)}
    elif kind == 'S':
        idx, old = map(int,rec[1:3]); scalar = Fraction(rec[3])
        vectors[idx] = {key:scalar*c for key,c in vectors[old].items() if scalar*c}
        consume(old)
    elif kind == 'A':
        idx, left, right = map(int,rec[1:4]); scalar = Fraction(rec[4])
        out = dict(vectors[left])
        for key,c in vectors[right].items():
            out[key] = out.get(key,Fraction(0))+scalar*c
            if not out[key]:del out[key]
        vectors[idx] = out
        consume(left); consume(right)
    elif kind == 'O':
        idx = int(rec[1]); actual = parse(rec[2]); expected = {}
        parents = defaultdict(Fraction)
        for inp,coeff in vectors[idx].items():
            add(expected,input_polys[inp],coeff)
            source,scalar,shift = input_sources[inp]
            parents[(source,shift)] += coeff*scalar
        assert expected == actual, ('Exact output identity failed', idx, expected, actual)
        edges = [(source,shift,coeff) for (source,shift),coeff in parents.items() if coeff]
        if actual:
            output_idx = register(actual, {'output_node':idx}, edges)
            if set(actual) == {(0,)*n}:
                last_constant = output_idx
        consume(idx)
    else:
        raise AssertionError(('Unknown trace record', rec))

needed = set()
def visit(idx):
    if idx in needed:return
    needed.add(idx)
    for parent,shift,coeff in known[idx]['parents']:visit(parent)
if last_constant is not None:visit(last_constant)
def serial_poly(poly):
    return [[list(mon),str(coeff)] for mon,coeff in sorted(poly.items())]
result = {'input':args.input,'trace':args.trace,'variables':names,'record_counts':dict(counts),
          'verified_output_count':counts['O'],'proved_nonzero_constant':last_constant is not None,
          'constant_step':last_constant,'needed_steps':sorted(needed),
          'steps':[{'index':idx,'polynomial':serial_poly(entry['poly']),'kind':entry['kind'],
                    'parents':[[p,list(shift),str(c)] for p,shift,c in entry['parents']]}
                   for idx,entry in enumerate(known)]}
Path(args.output).write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({key:value for key,value in result.items() if key not in ('steps','needed_steps')}))
print('needed_steps', len(needed), 'all_steps', len(known), flush=True)
