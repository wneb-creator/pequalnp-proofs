from pathlib import Path
import argparse,json
p=argparse.ArgumentParser();p.add_argument('--stem',required=True);a=p.parse_args()
stem=Path(a.stem)
m=json.loads(stem.with_suffix('.meta.json').read_text())
lines=stem.with_suffix('.sol').read_text().splitlines()
assert any(line.strip()=='s SATISFIABLE' for line in lines)
truth={}
for line in lines:
 if line.startswith('v '):
  for x in map(int,line.split()[1:]):
   if x:truth[abs(x)]=x>0
clauses=0
for line in stem.with_suffix('.cnf').read_text().splitlines():
 if line.startswith(('p','c')) or not line.strip():continue
 clause=[int(x) for x in line.split() if x!='0']
 assert any(truth[abs(v)]==(v>0) for v in clause)
 clauses+=1
program=[]
for ss in m['selectors']:
 sides=[[i for i,v in enumerate(side) if truth[v]] for side in ss]
 assert all(sides)
 program.append(sides)
outs=[i for i,v in enumerate(m['outs']) if truth[v]]
assert outs
if m.get('aut',False):
 from itertools import permutations
 current=[u in program[0][side] for side in range(2) for u in range(m['n'])]
 for perm in permutations(range(3)):
  for flip in range(2):
   mapping=[1,0] if flip else [0,1]
   for i in range(3):mapping.extend([2*perm[i]+2+flip,2*perm[i]+3-flip])
   inverse=[mapping.index(i) for i in range(m['n'])]
   for swap in range(2):
    transformed=[inverse[u] in program[0][side^swap] for side in range(2) for u in range(m['n'])]
    assert current>=transformed
if m.get('live',False):
 reach=set(outs)
 for g in reversed(range(m['k'])):
  if g in reach:
   reach.update(v-m['n'] for side in program[g] for v in side if v>=m['n'])
 assert reach==set(range(m['k']))
bad=[]
accepted_edges=[]
for x in range(1<<m['n']):
 vals=[bool(x>>i&1) for i in range(m['n'])]
 for left,right in program:vals.append(all(vals[i] for i in left) or all(vals[i] for i in right))
 got=all(vals[m['n']+i] for i in outs)
 expected=any(x>>u&1 and x>>v&1 for u,v in m['edges'])
 if got and not expected:bad.append(x)
 if any(x==(1<<u)|(1<<v) for u,v in m.get('required_edges',m['edges'])) and not got:bad.append(x)
 if got and x.bit_count()==2:accepted_edges.append([i for i in range(m['n']) if x>>i&1])
r={'n':m['n'],'ors':m['k'],'program':program,'output_generator_indices':outs,'full_truth_rows':1<<m['n'],'mismatches':bad,'accepted_edges':accepted_edges,'cnf_clauses_checked':clauses}
stem.with_suffix('.decoded.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r,indent=2))
assert not bad
