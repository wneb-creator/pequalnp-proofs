import argparse
import itertools
import json
import pathlib

parser = argparse.ArgumentParser()
parser.add_argument('points', type=int)
parser.add_argument('lines', type=int)
parser.add_argument('--transpose', action='store_true')
parser.add_argument('--output', required=True)
args = parser.parse_args()
n, m = args.points, args.lines
assert not args.transpose or n == m
prs = list(itertools.permutations(range(n)))
pcs = list(itertools.permutations(range(m)))
rows = []
for mask in range(1, 1 << (n*m)):
    edges = {(p,l) for p in range(n) for l in range(m) if mask & (1 << (m*p+l))}
    if any(all((p,l) in edges for p in ps for l in ls)
           for ps in itertools.combinations(range(n),2)
           for ls in itertools.combinations(range(m),2)):
        continue
    forms = [sum(1 << (m*pr[p]+pc[l]) for p,l in edges) for pr in prs for pc in pcs]
    if args.transpose:
        forms.extend(sum(1 << (m*pc[l]+pr[p]) for p,l in edges) for pr in prs for pc in pcs)
    if mask != min(forms):
        continue
    matching = max(r for r in range(min(n,m)+1)
                   for es in itertools.combinations(edges,r)
                   if len({p for p,l in es}) == r and len({l for p,l in es}) == r)
    rows.append({'mask':mask, 'edges':len(edges), 'matching':matching,
                 'predicted':len(edges)+matching-1})
pathlib.Path(args.output).write_text(json.dumps(rows, indent=2))
print(json.dumps({'points':n, 'lines':m, 'transpose':args.transpose,
                  'nonempty_types':len(rows)}))
