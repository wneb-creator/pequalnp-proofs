import argparse,hashlib,json
from collections import defaultdict
from pathlib import Path

p=argparse.ArgumentParser()
for name in ['library','mapping','base-mapping','cnf','prefix','appender-source','preferred-model','preferred-mapping']:p.add_argument('--'+name,required=True)
a=p.parse_args();digest=lambda path:hashlib.sha256(Path(path).read_bytes()).hexdigest()
lib=json.loads(Path(a.library).read_text());mapping=json.loads(Path(a.mapping).read_text());base=json.loads(Path(a.base_mapping).read_text());preferred=json.loads(Path(a.preferred_mapping).read_text())
assert mapping['library_sha256']==base['library_sha256']==preferred['library_sha256']==digest(a.library)
assert mapping['base_mapping_sha256']==digest(a.base_mapping) and mapping['require_nonread_edge']
assert all(mapping[k]==base[k] for k in ['selected','chosen','ranks'])
model={};sat=False
for line in Path(a.preferred_model).read_text().splitlines():
 if line.startswith('s '):sat=line.strip()=='s SATISFIABLE'
 if line.startswith('v '):
  for token in line[2:].split():
   x=int(token)
   if x:assert abs(x) not in model or model[abs(x)]==(x>0);model[abs(x)]=x>0
assert sat
selected_profiles={q for q,var in enumerate(preferred['selected']) if model[var]}
selected_producers={i for i,var in enumerate(preferred['chosen']) if model[var]}
n=lib['inputs'];N=len(lib['profiles']);prods=lib['productions'];bound=base['bound'];width=base['rank_width']
assert n==26 and bound in (63,67) and width==bound.bit_length()
chosen={}
for i in selected_producers:
 q,op,left,right=prods[i];assert q not in chosen;chosen[q]=(op,left,right)
assert len(chosen)==67 and set(chosen)==selected_profiles-set(range(n)) and set(range(n))<=selected_profiles
depths={q:0 for q in range(n)};visiting=set()
def depth(q):
 if q in depths:return depths[q]
 assert q not in visiting and q in chosen;visiting.add(q);op,left,right=chosen[q];depths[q]=max(depth(left),depth(right))+1;visiting.remove(q);return depths[q]
for q in chosen:depth(q)
depths[lib['goal']]=bound;assert max(depths.values())<=bound
phase=[False]
def fresh(value):phase.append(bool(value));return len(phase)-1
selected=[fresh(q in selected_profiles) for q in range(N)]
producer_variables=[fresh(i in selected_producers) for i in range(len(prods))]
ranks=[None]*n+[[fresh(depths.get(q,0)>>j&1) for j in range(width)] for q in range(n,N)]
assert selected==base['selected'] and producer_variables==base['chosen'] and ranks==base['ranks']
incoming=defaultdict(list)
for i,(q,op,left,right) in enumerate(prods):incoming[q].append(i)
for q in range(n,N):
 seen=False
 for i in incoming[q][:-1]:seen=seen or i in selected_producers;fresh(seen)
comparisons=set()
for q,op,left,right in prods:
 for child in (left,right):
  if child<n or (child,q) in comparisons:continue
  comparisons.add((child,q));x,y=depths.get(child,0),depths.get(q,0);fresh(x<y);equal=True
  for j in reversed(range(width)):equal=equal and (x>>j&1)==(y>>j&1);fresh(equal)
count=0;previous=[];expected_literals=[]
for i,q in enumerate(range(n,N)):
 if q in selected_profiles:
  if count>=bound:expected_literals.append([-selected[q],-previous[-1]])
  count+=1
 previous=[fresh(count>=j+1) for j in range(min(bound,i+1))]
assert count==67 and len(phase)-1==base['variables']==mapping['base_variables']
assert len(expected_literals)==max(0,67-bound)
nvars=mapping['variables'];base_vars=base['variables'];phase.extend([False]*(nvars-base_vars));assigned=set()
def assign(var,value):
 if type(var)is bool:assert var==value;return
 assert base_vars<var<=nvars;phase[var]=bool(value);assigned.add(var)
picked=[i for i,var in enumerate(preferred['joint_edge_selectors']) if model[var]];assert len(picked)==1
edge=picked[0];assert mapping['joint_edges']==preferred['joint_edges'];point,line=mapping['joint_edges'][edge]
for i,var in enumerate(mapping['joint_edge_selectors']):assign(var,i==edge)
states={q:(q==point,q==line,False) for q in range(n)};visiting=set()
def state(q):
 if q in states:return states[q]
 assert q in chosen and q not in visiting;visiting.add(q);op,left,right=chosen[q];u,v=state(left),state(right)
 states[q]=tuple(x or y for x,y in zip(u,v)) if op else (False,False,(u[0] and v[1])or(u[1] and v[0]));visiting.remove(q);return states[q]
for q in chosen:state(q)
assert states[lib['goal']]==(False,False,False)
for q,variables in enumerate(mapping['joint_states']):
 for var,value in zip(variables,states.get(q,(False,False,False))):assign(var,value)
assert assigned==set(range(base_vars+1,nvars+1))
prefix=Path(a.prefix);prefix.parent.mkdir(parents=True,exist_ok=True);mask=bytearray((nvars+7)//8)
for var in range(1,nvars+1):
 if not phase[var]:mask[(var-1)//8]|=1<<((var-1)%8)
mask_path=prefix.with_suffix('.mask.bin');mask_path.write_bytes(mask);warm=prefix.with_suffix('.cnf');violated=[];clauses=0
with Path(a.cnf).open() as src,warm.open('w') as out:
 for row in src:
  if row.startswith('p '):assert row.split()==['p','cnf',str(nvars),str(mapping['clauses'])];out.write(row);continue
  if not row.strip() or row.startswith('c '):out.write(row);continue
  literals=list(map(int,row.split()));assert literals[-1]==0 and all(0<abs(x)<=nvars for x in literals[:-1]);clauses+=1
  if not any((x>0)==phase[abs(x)] for x in literals[:-1]):violated.append({'index':clauses,'literals':literals[:-1]})
  out.write(' '.join(str(x if phase[abs(x)] else -x) for x in literals[:-1])+' 0\n')
assert clauses==mapping['clauses'] and [r['literals'] for r in violated]==expected_literals
report={'variables':nvars,'clauses':clauses,'bound':bound,'initial_phase':True,'preferred_selected_noninputs':67,'preferred_edge_index':edge,'preferred_edge':[point,line],'preferred_root_joint_read1':False,'violated_original_clauses':violated,'violated_class':'cardinality_overflow_only','source_sha256':digest(__file__),'appender_source_sha256':digest(a.appender_source),'preferred_model_sha256':digest(a.preferred_model),'preferred_mapping_sha256':digest(a.preferred_mapping),'library_sha256':digest(a.library),'mapping_sha256':digest(a.mapping),'original_cnf_sha256':digest(a.cnf),'warm_cnf_sha256':digest(warm),'mask_name':mask_path.name,'mask_sha256':digest(mask_path),'equivalence':'Original variable equals renamed variable XOR mask bit; all clauses retained.'}
prefix.with_suffix('.phase.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report),flush=True)
