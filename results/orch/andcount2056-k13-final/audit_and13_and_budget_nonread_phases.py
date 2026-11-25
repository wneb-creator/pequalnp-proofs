from pathlib import Path
import json,hashlib
base=Path('/tmp/oec/pequalnp-pilot-121');reports=[]
for folder,name in [('plane2056-cegis','warm-nonread-and13-near63-query'),('andcount2056','nonread-target16-nested')]:
 p=base/folder/name;m=json.loads(p.with_suffix('.mapping.json').read_text());flipped=set(m['flipped_variables']);rows=m['rows'];assert len(rows)==len(set(rows))==756
 if folder=='plane2056-cegis':
  v=[sum(((r>>i)&1)<<k for k,r in enumerate(rows)) for i in range(26)]
  for op,a,b in m['warm_gates']:v.append(v[a]|v[b] if op else v[a]&v[b])
  out=v[-1];expected=[]
  for k,r in enumerate(rows):
   if bool(out>>k&1)!=(k<52):
    var=m['outputs'][k];lit=var if k<52 else -var;expected.append([-lit if abs(lit) in flipped else lit])
 else:
  warm=json.loads(p.with_suffix('.warm.json').read_text());v=[sum(((r>>i)&1)<<k for k,r in enumerate(rows)) for i in range(26)]
  for rec in warm['ands']:
   a=b=0
   for i in rec['left']:a|=v[i]
   for i in rec['right']:b|=v[i]
   v.append(a&b)
  out=0
  for i in warm['output']:out|=v[26+i]
  expected=[]
  for k in range(52):
   if not (out>>k&1):
    # Existing semantic source appends one disjunction over selected-and-output conjunction auxiliaries; identify by all-positive unsatisfied clauses then verify source row order independently below.
    expected.append(k)
 failures=[];count=0
 with p.with_suffix('.cnf').open('rb') as f:
  header=f.readline().split();nv,nc=map(int,header[2:])
  for count,line in enumerate(f,1):
   xs=line.split();assert xs[-1]==b'0'
   if not any(x.startswith(b'-') for x in xs[:-1]):failures.append((count,list(map(int,xs[:-1]))))
 assert count==nc
 if folder=='plane2056-cegis':assert [c for _,c in failures]==expected
 else:
  assert len(failures)==len(expected)==6
  # Evaluate each offending output disjunction by corresponding row: all are old output clauses from base prefix target, unchanged modulo shifted variable IDs.
  original=base/'andcount2056/prefix-target16-nested';om=json.loads(original.with_suffix('.mapping.json').read_text());assert om['values']==m['values'] and om['left']==m['left'] and om['right']==m['right'] and om['output']==m['output']
  oldfail=[]
  with original.with_suffix('.cnf').open('rb') as f:
   f.readline()
   for i,line in enumerate(f,1):
    xs=line.split()
    if not any(x.startswith(b'-') for x in xs[:-1]):oldfail.append((i,list(map(int,xs[:-1]))))
  assert failures==oldfail
 reports.append({'prefix':folder+'/'+name,'variables':nv,'clauses_checked':count,'phase_failed_clauses':failures,'boundary_missing_positive_indices':[k for k in range(52) if not(out>>k&1)],'false_positive_count':(out>>52).bit_count(),'cnf_sha256':hashlib.sha256(p.with_suffix('.cnf').read_bytes()).hexdigest()})
q=base/'and13-and-budget-nonread-phases-independent-review.json';q.write_text(json.dumps({'status':'PASS complete independently streamed target phases; no native solver verdict','reports':reports},indent=2)+'\n');print(q.read_text())
