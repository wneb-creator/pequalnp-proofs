from pathlib import Path
import json

root = Path(__file__).resolve().parent
scratch = Path('/tmp/oec/pequalnp-pilot-104/counterexample2590')
values = list(map(int, (scratch / 'petersen.txt').read_text().split()))
edges = list(zip(values[2::2], values[3::2]))
gates = []
def gate(op, a, b):
    gates.append((op, a, b))
    return 9 + len(gates)
def biclique(a, b, c, d):
    left = gate(1, a, b)
    right = gate(1, c, d)
    return gate(0, left, right)
def star(center, leaves):
    left = gate(1, leaves[0], leaves[1])
    both = gate(1, left, leaves[2])
    return gate(0, center, both)
blocks = [biclique(0,3,2,4), biclique(0,7,2,5),
          star(1,[0,2,6]), star(8,[3,5,6]), star(9,[4,7,6])]
out = blocks[0]
for b in blocks[1:]:
    out = gate(1,out,b)
assert len(gates) == 19

def evaluate(gs, x, output):
    v = [bool((x >> i) & 1) for i in range(10)]
    for op,a,b in gs:
        assert 0 <= a < len(v) and 0 <= b < len(v)
        v.append((v[a] or v[b]) if op else (v[a] and v[b]))
    return v[output]
def target(x, es):
    return any((x >> a) & 1 and (x >> b) & 1 for a,b in es)
def write_net(path, gs):
    path.write_text(''.join(f'{op} {a} {b}\n' for op,a,b in gs) + f'output {out}\n')
wrong = [x for x in range(1024) if evaluate(gates,x,out) != target(x,edges+[(0,2)])]
assert not wrong
false_positive = [x for x in range(1024) if evaluate(gates,x,out) and not target(x,edges)]
false_negative = [x for x in range(1024) if target(x,edges) and not evaluate(gates,x,out)]
write_net(scratch / 'supergraph-02-19.txt', gates)
print('SUPERGRAPH verified all1024; gates=19; extraedge=(0,2); falsepositives=',false_positive,'falsenegatives=',false_negative)
perms = json.loads((root.parent / 'orch' / 'few_nots_automorphisms.json').read_text())
seen = set(); files=[]
for p in perms:
    edge = tuple(sorted((p[0],p[2])))
    if edge in seen:
        continue
    seen.add(edge)
    gs = [(op,p[a] if a<10 else a,p[b] if b<10 else b) for op,a,b in gates]
    assert all(evaluate(gs,x,out)==target(x,edges+[edge]) for x in range(1024))
    path = scratch / f'supergraph-{edge[0]}-{edge[1]}-19.txt'
    write_net(path, gs); files.append(str(path))
(scratch / 'supergraph-seeds.txt').write_text('\n'.join(files)+'\n')
print('all verified supergraph seeds',len(files))
