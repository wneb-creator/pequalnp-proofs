import argparse,hashlib,json
from pathlib import Path

ap=argparse.ArgumentParser()
ap.add_argument('--data',required=True);ap.add_argument('--prefix',required=True)
ap.add_argument('--expected-errors',required=True,type=int)
a=ap.parse_args();p=Path(a.prefix);data=json.loads(Path(a.data).read_text())
m=json.loads(p.with_suffix('.mapping.json').read_text());rows=m['rows'];gates=m['warm_gates']
edges={(p,13+l) for p in range(13) for l in range(13) if (p+l)%13 in (0,1,3,9)}
assert m['n']==26 and set(map(tuple,data['edges']))==edges
positive=set(data['positive_rows']);negative=set(data['negative_rows'])
assert positive=={(1<<p)|(1<<l) for p,l in edges}
neighbors=[sum(1<<l for l in range(13) if (p,13+l) in edges) for p in range(13)]
regenerated=set()
for points in range(8192):
 lines=8191
 for q in range(13):
  if points&(1<<q):lines&=~neighbors[q]
 if points==sum(1<<q for q in range(13) if not neighbors[q]&lines):regenerated.add(points|(lines<<13))
assert negative==regenerated
assert len(positive)==52 and len(negative)==704 and set(rows)==positive|negative and len(rows)==756
values=[sum(bool(r&(1<<i))<<k for k,r in enumerate(rows)) for i in range(26)]
for j,(op,u,v) in enumerate(gates):
 assert op in (0,1) and 0<=u<26+j and 0<=v<26+j
 values.append(values[u]|values[v] if op else values[u]&values[v])
expected=[r for k,r in enumerate(rows) if bool(values[-1]&(1<<k))!=(r in positive)]
assert len(expected)==a.expected_errors
negmask=sum(1<<k for k,r in enumerate(rows) if r in negative)
dirty=[26+j for j,(op,u,v) in enumerate(gates) if op==0 and bool(values[26+j]&negmask)]
rowmap=dict(zip(m['outputs'],rows));count=0;bad_rows=[];bad_cut=[];digest=hashlib.sha256()
for raw in p.with_suffix('.cnf').open('rb'):
 digest.update(raw)
 if raw.startswith(b'p '):
  _,_,nvars,nclauses=raw.split();nvars=int(nvars)
  assert nvars==m['dirty_at_least_two_variable']
  assert all(type(v)is int and 1<=v<=nvars for v in m['flipped_variables'])
  nclauses=int(nclauses);continue
 if raw.startswith(b'c ') or not raw.strip():continue
 c=list(map(int,raw.split()));assert c.pop()==0;count+=1
 if not any(x<0 for x in c):
  assert len(c)==1
  if c[0] in rowmap:bad_rows.append({'index':count,'row':rowmap[c[0]],'literal':c[0]})
  else:
   assert c==[m['dirty_at_least_two_variable']] and count==nclauses
   bad_cut.append({'index':count,'literal':c[0]})
assert count==nclauses and sorted(x['row'] for x in bad_rows)==sorted(expected)
assert len(bad_cut)==int(len(dirty)<2)
r={'scope':'Exact warm-phase diagnostic; no target correctness claim','cnf_sha256':digest.hexdigest(),'clauses':count,'dirty_AND_wires':dirty,'expected_output_mismatch_rows':expected,'output_unit_failures':bad_rows,'expected_dirty_cut_failures':bad_cut,'unexpected_clause_failures':0}
p.with_suffix('.phase-check.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
