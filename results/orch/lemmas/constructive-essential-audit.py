from pathlib import Path
import sys,json,hashlib,datetime,itertools
base=Path(sys.argv[1]); reports=[]
inputs=[sum(1<<mask for mask in range(16384) if mask&(1<<i)) for i in range(14)]
for tag in ['sat-p14-compact-essential28-control','sat-p14-compact-essential-host-control','sat-p14-compact-essential18-target']:
 m=json.loads((base/(tag+'.metadata.json')).read_text());ex=m['incomparability']
 with (base/(tag+'.cnf')).open() as f:
  assert f.readline().split()==['p','cnf',str(m['variables']),str(m['clauses'])]
  clauses=[tuple(map(int,line.split()[:-1])) for line in f]
 assert len(clauses)==m['clauses']
 expected=[];newvars=[]
 if ex['enabled']:
  nr=[j for j,x in enumerate(m['tests']) if x in m['negative']];assert nr==ex['negative_rows'];assert len(ex['atoms'])==m['cap']
  for atom,info in zip(m['atoms'],ex['atoms']):
   assert atom['active']==info['active']
   for first,second,ds in [(atom['slots'][0],atom['slots'][1],info['directions'][0]),(atom['slots'][1],atom['slots'][0],info['directions'][1])]:
    assert len(ds)==len(nr)
    for row,d in zip(nr,ds):
     a=first['values'][row];b=second['values'][row]
     expected.extend([(-a,b,d),(a,-d),(-b,-d)]);newvars.append(d)
    expected.append(tuple([-atom['active']]+ds))
 assert clauses[ex['clause_begin']:ex['clause_end']]==expected
 assert ex['clause_end']==len(clauses)
 assert newvars==list(range(ex['variable_begin']+1,m['variables']+1))
 result={'tag':tag,'new_clauses_reconstructed':len(expected),'new_variables_checked':len(newvars),'enabled':ex['enabled']}
 if tag.endswith('target'):
  reports.append(result);continue
 assignment={int(k):bool(v) for k,v in json.loads((base/(tag+'.complete-assignment.json')).read_text()).items()};c=json.loads((base/(tag+'.compact-control.json')).read_text())
 assert set(assignment)==set(range(1,m['variables']+1))
 for j,row in enumerate(clauses):assert any(assignment[abs(v)]==(v>0) for v in row),(tag,j)
 vals=[];slotvals=[]
 for j,atom in enumerate(m['atoms']):
  active=j<len(c['atoms']);assert assignment[atom['active']]==active
  ss=[]
  for side,slot in enumerate(atom['slots']):
   selected=c['atoms'][j]['slots'][side] if active else {'primary':[],'prior':[]}
   for k,v in enumerate(slot['primary']):assert assignment[v]==(k in selected['primary'])
   for k,v in enumerate(slot['prior']):assert assignment[v]==(k in selected['prior'])
   sv=0
   for k in selected['primary']:sv|=inputs[k]
   for k in selected['prior']:assert k<j;sv|=vals[k]
   for row,mask in enumerate(m['tests']):assert assignment[slot['values'][row]]==bool((sv>>mask)&1)
   ss.append(sv)
  slotvals.append(ss);vals.append(ss[0]&ss[1])
  if ex['enabled']:
   for side,ds in enumerate(ex['atoms'][j]['directions']):
    witnesses=0
    for row,d in zip(ex['negative_rows'],ds):
     mask=m['tests'][row];actual=bool((ss[side]>>mask)&1) and not bool((ss[1-side]>>mask)&1)
     assert assignment[d]==actual;witnesses+=actual
    assert not active or witnesses>0
 out=0
 for j,v in enumerate(m['final']):assert assignment[v]==(j in c['final'])
 for j in c['final']:out|=vals[j]
 target=0
 for p,l in m['edges']:target|=inputs[p]&inputs[l]
 assert out==target
 negatives=[]
 for mask in range(16384):
  if (target>>mask)&1:continue
  if all((target>>(mask|(1<<i)))&1 for i in range(14) if not mask&(1<<i)):negatives.append(mask)
 assert negatives==sorted(m['negative'])
 derivatives=[]
 for initial,seed in [(0,7),(7,0)]:
  vs=[];ds=[]
  for atom in c['atoms']:
   sv=[];sd=[]
   for slot in atom['slots']:
    sv.append(initial in slot['primary'] or any(vs[k] for k in slot['prior']))
    sd.append(seed in slot['primary'] or any(ds[k] for k in slot['prior']))
   vs.append(sv[0] and sv[1]);ds.append((sv[0] and sd[1]) or (sd[0] and sv[1]))
  d=any(ds[j] for j in c['final']);assert not d;derivatives.append(d)
 result.update(clauses_checked=len(clauses),variables_checked=len(assignment),active_atoms=len(c['atoms']),inactive_suffix=m['cap']-len(c['atoms']),truth_rows_checked=16384,derivatives=derivatives,maximal_negative_rows=len(negatives));reports.append(result)
for a,b,d in itertools.product([False,True],repeat=3):
 actual=((not a) or b or d) and (a or not d) and ((not b) or not d)
 assert actual==(d==(a and not b))
report={'verdict':'PASS','reviewer':'constructive_search','reviewed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'encoder_sha256':hashlib.sha256((base/'sat-p14-compact-essential.py').read_bytes()).hexdigest(),'controls':reports,'mathematical_audit':['If an AND operand implies the other on every maximal negative assignment, replacing that AND by the implying operand preserves all maximal-negative output zeros. It only increases outputs, so retains every positive edge. Monotonicity and the boundary certificate give the same Fano function with one fewer gate, contradicting the accepted ordinary27 lower bound. This argument is about minimal27 Fano circuits, not arbitrary circuits.','The new cut therefore requires both directions of operand incomparability at maximal negative rows, guarded by active. It does not assume trace-preserving deletion.','Every added clause and variable is reconstructed independently from frozen metadata; complete controls are checked against every CNF clause and their exact selected operands, full truth tables, and direct raw derivatives.','The28gate Fano control enables the new cut with equality/nine-free cuts disabled. The matching control retains old cuts but disables the Fano-minimality cut. The inactive suffix remains allowed.'],'scope':'Independent encoder/positive-control review only; no SAT outcome or Lean certificate.'}
(base/'constructive-essential-encoder-review.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({'verdict':'PASS','encoder_sha256':report['encoder_sha256'],'controls':reports}))
