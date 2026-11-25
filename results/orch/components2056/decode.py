import argparse
import hashlib
import json
from pathlib import Path

p=argparse.ArgumentParser()
p.add_argument('--library',required=True);p.add_argument('--data',required=True)
p.add_argument('--mapping',required=True);p.add_argument('--model',required=True);p.add_argument('--output',required=True)
a=p.parse_args();text=Path(a.library).read_text();lib=json.loads(text);mapping=json.loads(Path(a.mapping).read_text())
assert hashlib.sha256(text.encode()).hexdigest()==mapping['library_sha256']
data_text=Path(a.data).read_text();assert hashlib.sha256(data_text.encode()).hexdigest()==lib['data_sha256']
data=json.loads(data_text);n=lib['inputs'];values=[int(s,16) for s in lib['profiles']]
assignment={};sat=False
for line in Path(a.model).read_text().splitlines():
 if line.startswith('s '):sat='SATISFIABLE' in line and 'UNSATISFIABLE' not in line
 if line.startswith('v '):
  for item in line[2:].split():
   value=int(item)
   if value:
    key=abs(value);assert key not in assignment or assignment[key]==(value>0);assignment[key]=value>0
assert sat
def truth(var):
 assert var in assignment,('missing decision/rank variable',var)
 return assignment[var]
selected={i for i,var in enumerate(mapping['selected']) if truth(var)}
assert set(range(n))<=selected and lib['goal'] in selected
assert len(selected-set(range(n)))<=mapping['bound']
chosen={}
for i,var in enumerate(mapping['chosen']):
 if truth(var):
  parent,op,left,right=lib['productions'][i]
  assert parent in selected and left in selected and right in selected and parent not in chosen
  assert values[parent]==(values[left]|values[right] if op else values[left]&values[right])
  chosen[parent]=(op,left,right)
assert set(chosen)==selected-set(range(n))
ranks={i:0 for i in range(n)}
for q in selected-set(range(n)):
 rank=sum((1<<j) for j,var in enumerate(mapping['ranks'][q]) if truth(var));assert 1<=rank<=mapping['bound'];ranks[q]=rank
for parent,(_,left,right) in chosen.items():assert ranks[left]<ranks[parent] and ranks[right]<ranks[parent]
# Also detect graph cycles directly; reconstruction does not trust rank bits alone.
colour={};order=[]
def visit(q):
 if q<n:return
 assert colour.get(q,0)!=1,('cycle',q)
 if colour.get(q,0)==2:return
 colour[q]=1;_,left,right=chosen[q];visit(left);visit(right);colour[q]=2;order.append(q)
visit(lib['goal'])
wire={i:i for i in range(n)};gates=[]
for q in order:
 op,left,right=chosen[q];wire[q]=n+len(gates);gates.append([op,wire[left],wire[right]])
output=wire[lib['goal']];assert len(gates)<=mapping['bound']
rows=data['rows'];bits=[sum(((r>>i)&1)<<j for j,r in enumerate(rows)) for i in range(n)]
for j,(op,left,right) in enumerate(gates):
 assert op in (0,1) and 0<=left<n+j and 0<=right<n+j
 bits.append(bits[left]|bits[right] if op else bits[left]&bits[right])
assert bits[output]==(1<<len(data['positive']))-1
result={'gates':gates,'output':output,'size':len(gates),'selected_noninput_profiles':len(selected)-n,'bound':mapping['bound'],'critical_rows_checked':len(rows),'selected_profile_order':order}
Path(a.output).write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ('gates','selected_profile_order')}),flush=True)
