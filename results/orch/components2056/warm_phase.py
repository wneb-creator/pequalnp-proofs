import argparse,hashlib,json
from collections import defaultdict
from pathlib import Path

p=argparse.ArgumentParser()
for option in ['library','mapping','cnf','prefix']:p.add_argument('--'+option,required=True)
a=p.parse_args();lib_text=Path(a.library).read_text();lib=json.loads(lib_text)
mapping=json.loads(Path(a.mapping).read_text());assert hashlib.sha256(lib_text.encode()).hexdigest()==mapping['library_sha256']
n=lib['inputs'];N=len(lib['profiles']);prods=lib['productions'];bound=mapping['bound'];width=mapping['rank_width']
assert n==26 and bound in (63,64) and width==bound.bit_length()
baseline=lib['baseline64'];selected_profiles=set(baseline['topological_profiles'])
lookup={tuple(x):i for i,x in enumerate(prods)};selected_producers={lookup[tuple(x)] for x in baseline['chosen']}
assert len(selected_profiles)==len(selected_producers)==64
depths={q:0 for q in range(N)};by_parent={x[0]:x for x in baseline['chosen']}
for q in baseline['topological_profiles']:
 _,_,left,right=by_parent[q];depths[q]=max(depths[left],depths[right])+1
depths[lib['goal']]=bound;assert max(depths.values())<=bound
phase=[False]
def fresh(value):
 phase.append(bool(value));return len(phase)-1
selected=[fresh(q<n or q in selected_profiles) for q in range(N)]
chosen=[fresh(i in selected_producers) for i in range(len(prods))]
ranks=[None]*n+[[fresh(depths[q]>>j&1) for j in range(width)] for q in range(n,N)]
assert selected==mapping['selected'] and chosen==mapping['chosen'] and ranks==mapping['ranks']
incoming=defaultdict(list)
for i,(q,op,left,right) in enumerate(prods):incoming[q].append(i)
# The producer at-most-one chain means some earlier producer was chosen.
for q in range(n,N):
 seen=False
 for i in incoming[q][:-1]:
  seen=seen or i in selected_producers;fresh(seen)
# Reproduce the cached strict-comparator allocation, including equal-prefix bits.
comparisons=set()
for q,op,left,right in prods:
 for child in (left,right):
  if child<n or (child,q) in comparisons:continue
  comparisons.add((child,q));fresh(depths[child]<depths[q]);equal=True
  for j in reversed(range(width)):
   equal=equal and (depths[child]>>j&1)==(depths[q]>>j&1);fresh(equal)
# Saturated prefix cardinality counters encode the exact selected-prefix count.
count=0
for i,q in enumerate(range(n,N)):
 count+=q in selected_profiles
 for j in range(min(bound,i+1)):fresh(count>=j+1)
assert len(phase)-1==mapping['variables'] and count==64
prefix=Path(a.prefix);prefix.parent.mkdir(parents=True,exist_ok=True)
mask=bytearray((mapping['variables']+7)//8)
for var in range(1,len(phase)):
 if not phase[var]:mask[(var-1)//8]|=1<<((var-1)%8)
mask_path=prefix.with_suffix('.mask.bin');mask_path.write_bytes(mask)
output_path=prefix.with_suffix('.cnf');violated=[];clause_count=0
with Path(a.cnf).open() as src,output_path.open('w') as out:
 for line in src:
  if line.startswith('p '):
   _,kind,nvars,nclauses=line.split();assert kind=='cnf' and int(nvars)==mapping['variables'] and int(nclauses)==mapping['clauses'];out.write(line);continue
  if not line.strip() or line.startswith('c '):out.write(line);continue
  literals=list(map(int,line.split()));assert literals[-1]==0 and all(0<abs(x)<len(phase) for x in literals[:-1])
  clause_count+=1
  if not any((x>0)==phase[abs(x)] for x in literals[:-1]):violated.append({'index':clause_count,'literals':literals[:-1]})
  out.write(' '.join(str(x if phase[abs(x)] else -x) for x in literals[:-1])+' 0\n')
assert clause_count==mapping['clauses'] and len(violated)==64-bound
def digest(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
report={'variables':mapping['variables'],'clauses':clause_count,'bound':bound,'baseline_selected_noninput_profiles':64,'initial_phase':True,'inverted_variables':sum(not x for x in phase[1:]),'violated_original_clauses':violated,'source_sha256':digest(__file__),'library_sha256':digest(a.library),'mapping_sha256':digest(a.mapping),'original_cnf_sha256':digest(a.cnf),'warm_cnf_sha256':digest(output_path),'mask_name':mask_path.name,'mask_sha256':digest(mask_path),'equivalence':'Each original variable equals the renamed variable XOR its mask bit; no clauses or constraints added.'}
prefix.with_suffix('.phase.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report),flush=True)
