import hashlib
import itertools
import json
from pathlib import Path
import time

base=Path('/tmp/oec/pequalnp-pilot-62/meta2448')
source=Path('/workspace/pequalnp-proofs/results/meta2448/petersen-L584-exact20-independent-replay.json')
data=json.loads(source.read_text());n=data['input_count'];gates=data['gates'];full=(1<<(1<<n))-1
inputs=[sum(1<<q for q in range(1<<n) if q>>i&1) for i in range(n)]
values=inputs.copy()
for op,a,b in gates:values.append(values[a]&values[b] if op=='and' else values[a]|values[b])
expected=sum(1<<q for q in range(1<<n) if any(q>>a&1 and q>>b&1 for a,b in data['edges']))
assert values[data['output_wire']]==expected

def replay(changed, replacement):
    row=values[:n+changed]+[replacement]
    for op,a,b in gates[changed+1:]:row.append(row[a]&row[b] if op=='and' else row[a]|row[b])
    return row[-1]

def normalize(replace_gate, replacement):
    mapping=list(range(n));new=[]
    for g,(op,a,b) in enumerate(gates):
        if g==replace_gate:
            value=replacement if type(replacement) is bool else mapping[replacement]
        else:
            a,b=mapping[a],mapping[b]
            if op=='and' and (a is False or b is False):value=False
            elif op=='or' and (a is True or b is True):value=True
            elif type(a) is bool:value=b
            elif type(b) is bool:value=a
            elif a==b:value=a
            else:new.append([op,*sorted((a,b))]);value=n+len(new)-1
        mapping.append(value)
    output=mapping[data['output_wire']];assert type(output) is int
    used=set()
    def visit(v):
        if v<n or v-n in used:return
        used.add(v-n)
        for c in new[v-n][1:]:visit(c)
    visit(output);remap={i:i for i in range(n)};kept=[]
    for g,(op,a,b) in enumerate(new):
        if g in used:remap[n+g]=n+len(kept);kept.append([op,remap[a],remap[b]])
    return {'input_count':n,'gates':kept,'output_wire':remap[output],'gate_count':len(kept)}

start=time.monotonic();records=[];witnesses=[]
for g in range(len(gates)):
    candidates=[('wire',i,values[i]) for i in range(n+g)]+[('constant',False,0),('constant',True,full)]
    for kind,replacement,signature in candidates:
        result=replay(g,signature);diff=result^expected
        record={'gate':g,'kind':kind,'replacement':replacement,'wrong_assignments':diff.bit_count(),'lost_true':(expected&~result).bit_count(),'gained_false':(result&~expected).bit_count()}
        records.append(record)
        if not diff:
            witness=normalize(g,replacement);assert witness['gate_count']<len(gates)
            row=inputs.copy()
            for op,a,b in witness['gates']:row.append(row[a]&row[b] if op=='and' else row[a]|row[b])
            assert row[witness['output_wire']]==expected
            witness.update({'replacement':record,'checked_assignments':1<<n});witnesses.append(witness)
report={'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'checked_assignments_per_replacement':1<<n,'replacement_count':len(records),'successful_deletions':len(witnesses),'elapsed_seconds':time.monotonic()-start,'records':records,'witnesses':witnesses,'scope':'All single-gate aliases to earlier wires and false/true constants, with exact full truth-table replay and constant/dead-gate cleanup. No broader optimality claim.'}
(base/'L584-single-deletion-replay.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in ['records','witnesses']}))
for i,w in enumerate(witnesses):(base/('L584-deletion-witness-'+str(i)+'.json')).write_text(json.dumps(w,indent=2)+'\n')
