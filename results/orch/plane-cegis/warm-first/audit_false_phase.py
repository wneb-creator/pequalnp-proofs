import argparse,json,hashlib
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument('--data',required=True);ap.add_argument('--prefix',required=True);ap.add_argument('--expected-errors',required=True,type=int);a=ap.parse_args()
p=Path(a.prefix);d=json.loads(Path(a.data).read_text());m=json.loads(p.with_suffix('.mapping.json').read_text());rows=m['rows'];gates=m['warm_gates'];rowmap=dict(zip(m['outputs'],rows));expected=[]
for row in rows:
 vs=[bool(row&(1<<i)) for i in range(m['n'])]
 for op,u,v in gates:vs.append(vs[u] or vs[v] if op else vs[u] and vs[v])
 truth=any(bool(row&(1<<u)) and bool(row&(1<<v)) for u,v in d['edges'])
 if vs[-1]!=truth:expected.append(row)
assert len(expected)==a.expected_errors
bad=[];count=0;digest=hashlib.sha256()
for raw in p.with_suffix('.cnf').open('rb'):
 digest.update(raw)
 if raw.startswith((b'p',b'c')):continue
 c=list(map(int,raw.split()));assert c.pop()==0;count+=1
 if not any(x<0 for x in c):
  assert len(c)==1 and abs(c[0]) in rowmap
  bad.append({'clause_index':count,'row':rowmap[abs(c[0])],'literal':c[0]})
assert sorted(x['row'] for x in bad)==sorted(expected)
r={'clauses':count,'cnf_sha256':digest.hexdigest(),'expected_mismatch_rows':expected,'phase_failures':bad,'unexpected_added_constraint_failures':0,'status':'replayed hint satisfies every clause except its exact expected output units'}
p.with_suffix('.phase-check.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
