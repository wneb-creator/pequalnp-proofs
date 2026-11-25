import json,hashlib,datetime,importlib.util
from pathlib import Path
base=Path('/tmp/oec/pequalnp-pilot-81');repo=Path('/workspace/pequalnp-proofs/results/orch/lemmas')
spec=importlib.util.spec_from_file_location('compact',base/'sat-p14-compact.py');mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
def flatten(gates):
 wires=[({i},set()) for i in range(14)];atoms=[]
 for op,a,b in gates:
  sa,ta=wires[a];sb,tb=wires[b]
  if op=='or':wires.append((sa|sb,ta|tb))
  else:
   assert not sa&sb
   atoms.append(dict(slots=[dict(primary=sorted(sa),prior=sorted(ta)),dict(primary=sorted(sb),prior=sorted(tb))],mode=None));wires.append((set(),{len(atoms)-1}))
 assert not wires[-1][0]
 result=dict(atoms=atoms,final=sorted(wires[-1][1]))
 for j,a in enumerate(atoms):
  uses=[s for k,z in enumerate(atoms) if k>j for s in z['slots'] if j in s['prior']]
  if len(uses)+(j in result['final'])==1:a['mode']=0
  elif len(uses)==2 and j not in result['final']:
   common=set(uses[0]['primary'])&set(uses[1]['primary'])
   if common:a['mode']=1+min(common)
 return result

def assign(meta,control):
 A={};n=len(control['atoms']);cap=meta['cap'];assert n<=cap
 def put(v,b):
  assert type(v)==int and v not in A;A[v]=bool(b)
 for j,a in enumerate(meta['atoms']):
  put(a['active'],j<n)
  actual=control['atoms'][j] if j<n else dict(slots=[dict(primary=[],prior=[]) for _ in range(2)],mode=None)
  for s,src in zip(a['slots'],actual['slots']):
   for x,v in enumerate(s['primary']):put(v,x in src['primary'])
   for k,v in enumerate(s['prior']):put(v,k in src['prior'])
  for k,v in enumerate(a['modes']):put(v,j<n and k==actual['mode'])
 for j,v in enumerate(meta['final']):put(v,j in control['final'])
 def literal(x):return x if type(x)==bool else A[abs(x)] if x>0 else not A[-x]
 def dp(d):
  for z in d['cells']:put(z['var'],sum(literal(v) for v in d['literals'][:z['prefix']])>=z['threshold'])
 for x in meta['primary_counts']:dp(x['dp'])
 for a in meta['atoms']:
  if a['use_dp']:dp(a['use_dp'])
 for j,a in enumerate(meta['atoms']):
  for s in a['slots']:
   for row,mask in enumerate(meta['tests']):
    for k,z in enumerate(s['terms'][row]):put(z,A[s['prior'][k]] and A[meta['atoms'][k]['values'][row]])
    put(s['values'][row],any(A[z] for x,z in enumerate(s['primary']) if mask>>x&1) or any(A[z] for z in s['terms'][row]))
  for row,v in enumerate(a['values']):put(v,A[a['slots'][0]['values'][row]] and A[a['slots'][1]['values'][row]])
 for row,v in enumerate(meta['final_values']):
  for j,z in enumerate(meta['final_terms'][row]):put(z,A[meta['final'][j]] and A[meta['atoms'][j]['values'][row]])
  put(v,any(A[z] for z in meta['final_terms'][row]))
 assert set(A)==set(range(1,meta['variables']+1));return A
reports=[]
cases=[('sat-p14-compact35-control',base/'sat-p14-canonical35-control.json',True),('sat-p14-compact-matching-control',base/'sat-p14-matching27-structural-control.json',True),('sat-p14-compact-nested-control',repo/'stochastic-p14-flatten-control.json',False)]
for tag,path,full in cases:
 data=json.loads(path.read_text());control=flatten(data['gates']);meta=json.loads((base/(tag+'.metadata.json')).read_text());A=assign(meta,control);output_units={v if mask in meta['positive'] else -v for v,mask in zip(meta['final_values'],meta['tests'])};checked=0;ignored=0
 with (base/(tag+'.cnf')).open() as f:
  assert f.readline().split()==['p','cnf',str(meta['variables']),str(meta['clauses'])]
  for line in f:
   clause=list(map(int,line.split()))[:-1]
   if not full and len(clause)==1 and clause[0] in output_units:ignored+=1;continue
   assert any(A[abs(v)] if v>0 else not A[-v] for v in clause),(tag,checked,clause)
   checked+=1
 assert full or ignored==len(meta['tests'])
 for mask in range(1<<14):
  vals=[bool(mask>>i&1) for i in range(14)]
  for op,a,b in data['gates']:vals.append(vals[a] and vals[b] if op=='and' else vals[a] or vals[b])
  assert mod.evaluate(control,mask)==vals[-1]
 reports.append(dict(tag=tag,active_atoms=len(control['atoms']),variables=len(A),clauses_checked=checked,final_function_units_ignored=ignored,truth_rows=16384,scope='Full emitted CNF' if full else 'All structural and gate-semantic clauses; exactly58 Fano-output requirements omitted; NOT Fano'))
 (base/(tag+'.compact-control.json')).write_text(json.dumps(control,indent=2)+'\n')
report=dict(verdict='PASS',source_sha256=hashlib.sha256((base/'sat-p14-compact.py').read_bytes()).hexdigest(),controls=reports)
(base/'sat-p14-compact-controls.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
