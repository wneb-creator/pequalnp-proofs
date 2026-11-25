import argparse,hashlib,json
from pathlib import Path

p=argparse.ArgumentParser()
for name in ['library','mapping','cnf','prefix','appender-source']:p.add_argument('--'+name,required=True)
p.add_argument('--base-phase');p.add_argument('--base-mapping');p.add_argument('--model')
a=p.parse_args();digest=lambda path:hashlib.sha256(Path(path).read_bytes()).hexdigest()
lib=json.loads(Path(a.library).read_text());mapping=json.loads(Path(a.mapping).read_text())
assert mapping['library_sha256']==digest(a.library) and mapping['require_nonread_edge']
assert bool(a.model)!=bool(a.base_phase);nvars=mapping['variables'];base_vars=mapping['base_variables'];phase=[False]*(nvars+1);expected=[];provenance={}
if a.model:
 seen=set();sat=False
 for line in Path(a.model).read_text().splitlines():
  if line.startswith('s '):sat=line.strip()=='s SATISFIABLE'
  if line.startswith('v '):
   for token in line[2:].split():
    literal=int(token)
    if not literal:continue
    var=abs(literal);assert 1<=var<=nvars
    assert var not in seen or phase[var]==(literal>0);seen.add(var);phase[var]=literal>0
 assert sat and len(seen)==nvars;provenance={'preferred_model_sha256':digest(a.model)}
else:
 assert a.base_mapping and mapping['bound']==63 and mapping['pin_circuit'] is None
 bp_path=Path(a.base_phase);bp=json.loads(bp_path.read_text());bm=json.loads(Path(a.base_mapping).read_text())
 assert bp['variables']==base_vars==bm['variables'] and bp['initial_phase'] is True
 assert bp['mapping_sha256']==digest(a.base_mapping)==mapping['base_mapping_sha256']
 assert bp['original_cnf_sha256']==mapping['base_cnf_sha256'] and bp['library_sha256']==digest(a.library)
 assert all(mapping[k]==bm[k] for k in ['selected','chosen','ranks'])
 mask=(bp_path.parent/bp['mask_name']).read_bytes();assert hashlib.sha256(mask).hexdigest()==bp['mask_sha256']
 for var in range(1,base_vars+1):phase[var]=not(mask[(var-1)//8]>>((var-1)%8)&1)
 chosen={}
 for index,var in enumerate(mapping['chosen']):
  if phase[var]:
   q,op,left,right=lib['productions'][index];assert q not in chosen;chosen[q]=(op,left,right)
 assert set(chosen)==set(lib['baseline64']['topological_profiles'])
 picked_edge=0;point,line=mapping['joint_edges'][picked_edge];assert (point,line)==(0,13)
 assigned=set()
 def assign(var,value):
  if type(var)is bool:assert var==value;return
  assert base_vars<var<=nvars;phase[var]=bool(value);assigned.add(var)
 for index,var in enumerate(mapping['joint_edge_selectors']):assign(var,index==picked_edge)
 states={q:(q==point,q==line,False) for q in range(26)};visiting=set()
 def state(q):
  if q in states:return states[q]
  assert q in chosen and q not in visiting;visiting.add(q);op,left,right=chosen[q];u,v=state(left),state(right)
  states[q]=tuple(x or y for x,y in zip(u,v)) if op else (False,False,(u[0] and v[1])or(u[1] and v[0]))
  visiting.remove(q);return states[q]
 for q in chosen:state(q)
 assert states[lib['goal']]==(False,False,True)
 for q,variables in enumerate(mapping['joint_states']):
  for var,value in zip(variables,states.get(q,(False,False,False))):assign(var,value)
 assert assigned==set(range(base_vars+1,nvars+1))
 expected=bp['violated_original_clauses']+[{'index':mapping['clauses'],'literals':[-mapping['joint_states'][lib['goal']][2]]}]
 assert expected==[{'index':1845804,'literals':[-90,-465339]},{'index':3984136,'literals':[-876810]}]
 provenance={'base_phase_sha256':digest(a.base_phase),'base_phase_builder_sha256':bp['source_sha256'],'preferred_edge_index':0}
prefix=Path(a.prefix);prefix.parent.mkdir(parents=True,exist_ok=True);mask=bytearray((nvars+7)//8)
for var in range(1,nvars+1):
 if not phase[var]:mask[(var-1)//8]|=1<<((var-1)%8)
mask_path=prefix.with_suffix('.mask.bin');mask_path.write_bytes(mask);warm=prefix.with_suffix('.cnf');violated=[];count=0
with Path(a.cnf).open() as src,warm.open('w') as out:
 for line in src:
  if line.startswith('p '):
   assert line.split()==['p','cnf',str(nvars),str(mapping['clauses'])];out.write(line);continue
  if not line.strip() or line.startswith('c '):out.write(line);continue
  literals=list(map(int,line.split()));assert literals[-1]==0 and all(0<abs(x)<=nvars for x in literals[:-1]);count+=1
  if not any((x>0)==phase[abs(x)] for x in literals[:-1]):violated.append({'index':count,'literals':literals[:-1]})
  out.write(' '.join(str(x if phase[abs(x)] else -x) for x in literals[:-1])+' 0\n')
assert count==mapping['clauses'] and violated==expected
report={'variables':nvars,'clauses':count,'bound':mapping['bound'],'initial_phase':True,'preferred_selected_noninputs':sum(phase[var] for var in mapping['selected'][26:]),'violated_original_clauses':violated,'source_sha256':digest(__file__),'appender_source_sha256':digest(a.appender_source),'library_sha256':digest(a.library),'mapping_sha256':digest(a.mapping),'original_cnf_sha256':digest(a.cnf),'warm_cnf_sha256':digest(warm),'mask_name':mask_path.name,'mask_sha256':digest(mask_path),'equivalence':'Original variable equals renamed variable XOR mask bit; all clauses retained.',**provenance}
prefix.with_suffix('.phase.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report),flush=True)
