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
if 'edgevars' in m:
 m['edges']=[e for e,v in zip(m['edges'],m['edgevars']) if truth[v]]
 assert len(m['edges'])>=m['min_edges']
 if not m['allow_c4']:
  from itertools import combinations
  eset=set(map(tuple,m['edges']))
  assert not any(all((u,v) in eset for u in aa for v in bb) for aa in combinations(range(m['side']),2) for bb in combinations(range(m['side'],m['n']),2))
program=[]
for ss in m['selectors']:
 sides=[[i for i,v in enumerate(side) if truth[v]] for side in ss]
 assert all(sides)
 program.append(sides)
outs=[i for i,v in enumerate(m['outs']) if truth[v]]
assert outs
bad=[]
for x in range(1<<m['n']):
 vals=[bool(x>>i&1) for i in range(m['n'])]
 for left,right in program:vals.append(all(vals[i] for i in left) or all(vals[i] for i in right))
 got=all(vals[m['n']+i] for i in outs)
 expected=any(x>>u&1 and x>>v&1 for u,v in m['edges'])
 if got!=expected:bad.append(x)
r={'n':m['n'],'ors':m['k'],'program':program,'output_generator_indices':outs,'full_truth_rows':1<<m['n'],'mismatches':bad,'graph_edges':m['edges'],'cnf_clauses_checked':clauses}
stem.with_suffix('.decoded.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r,indent=2))
assert not bad
