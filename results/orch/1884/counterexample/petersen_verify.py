import argparse,json
from pathlib import Path

parser=argparse.ArgumentParser()
parser.add_argument('stem')
args=parser.parse_args()
base=Path('/tmp/oec/pequalnp-pilot-154/counterexample')
data=json.loads((base/(args.stem+'.json')).read_text())
model={}
for line in (base/(args.stem+'.model')).read_text().splitlines():
    if line.startswith('v '):
        for z in map(int,line[2:].split()):
            if z:model[abs(z)]=z>0
def truth(lit):return model[abs(lit)]==(lit>0)
gates=[]
for op,ss in zip(data['ops'],data['selectors']):
    operations=[i for i,l in enumerate(op) if truth(l)]
    operands=[[i for i,l in enumerate(sp) if truth(l)] for sp in ss]
    assert len(operations)==1 and all(len(x)==1 for x in operands)
    gates.append((operations[0],operands[0][0],operands[1][0]))
not_count=sum(op==2 for op,a,b in gates)
if data.get('monotone_internal'):assert not_count==0
if data.get('max_nots') is not None:assert not_count<=data['max_nots']
if data.get('exact_nots') is not None:assert not_count==data['exact_nots']
if data.get('single_polarity_readers'):
    for wire,operation in [(0,1),(10,0)]:
        readers=[g for g,(op,a,b) in enumerate(gates) if wire in [a,b]]
        assert len(readers)==1 and gates[readers[0]][0]==operation
edge_masks=[(1<<a)|(1<<b) for a,b in data['edges']]
logical_n=data.get('logical_input_count',10)
extra_not=data.get('extra_not_input',True)
errors=[]
for x in range(1<<logical_n):
    vs=[bool(x>>i&1) for i in range(logical_n)]
    if extra_not:vs.append(not bool(x&1))
    for op,a,b in gates:
        assert 0<=a<len(vs) and 0<=b<len(vs)
        vs.append((vs[a] and vs[b]) if op==0 else (vs[a] or vs[b]) if op==1 else not vs[a])
    if x==0:values_at_zero=vs[:]
    if vs[data['output']]!=any(x&e==e for e in edge_masks):errors.append(x)
clauses=0
with (base/(args.stem+'.cnf')).open() as f:
    for line in f:
        if line.startswith('p '):continue
        clause=list(map(int,line.split()))
        assert clause[-1]==0
        assert any(truth(l) for l in clause[:-1]),(clauses,clause)
        clauses+=1
assert clauses==data['clauses']
live=set();pending=[data['output']]
while pending:
    w=pending.pop()
    if w<data['input_count'] or w in live:continue
    live.add(w)
    op,a,b=gates[w-data['input_count']]
    pending.extend([a] if op==2 else [a,b])
result={'gates':gates,'gate_count':len(gates),'output':data['output'],'all_rows_correct':not errors,
 'rows_verified':1<<logical_n,
 'errors':errors,'clauses_verified':clauses,'and_count':sum(op==0 for op,a,b in gates),
 'or_count':sum(op==1 for op,a,b in gates),'not_count':not_count,
 'live_gate_count':len(live),
 'not_gates':[{'gate':g,'value_at_zero':values_at_zero[data['input_count']+g],
   'live':data['input_count']+g in live} for g,(op,a,b) in enumerate(gates) if op==2],
 'free_input':'not x0' if extra_not else None,'model_variables':len(model)}
(base/(args.stem+'-verification.json')).write_text(json.dumps(result,indent=2))
print(json.dumps(result),flush=True)
assert not errors
