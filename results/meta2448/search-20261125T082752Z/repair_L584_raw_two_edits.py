import hashlib
import itertools
import json
from pathlib import Path
import resource
import time

resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
base=Path('/tmp/oec/pequalnp-pilot-62/meta2448')
source=Path('/workspace/pequalnp-proofs/results/meta2448/petersen-L584-exact20-independent-replay.json')
data=json.loads(source.read_text());n=data['input_count'];original=data['gates']
edges=sorted(set(tuple(sorted(e)) for e in data['edges']));edge_masks=[(1<<a)|(1<<b) for a,b in edges]
negative=[q for q in range(1<<n) if not any(q&e==e for e in edge_masks) and all(any((q|(1<<i))&e==e for e in edge_masks) for i in range(n) if not(q>>i&1))]
samples=edge_masks+negative;target=(1<<len(edges))-1
inputs=[sum(1<<r for r,q in enumerate(samples) if q>>i&1) for i in range(n)]
full_inputs=[sum(1<<q for q in range(1<<n) if q>>i&1) for i in range(n)]
full_target=sum(1<<q for q in range(1<<n) if any(q&e==e for e in edge_masks))

def evaluate(gates,initial):
    row=initial.copy()
    for op,a,b in gates:row.append(row[a]&row[b] if op=='and' else row[a]|row[b])
    return row

def prune(gates,output):
    if type(output) is bool or output<n:return [],output
    used=set()
    def visit(v):
        if v<n or v-n in used:return
        used.add(v-n)
        for a in gates[v-n][1:]:visit(a)
    visit(output);mapping={i:i for i in range(n)};new=[]
    for g,(op,a,b) in enumerate(gates):
        if g in used:mapping[n+g]=n+len(new);new.append([op,mapping[a],mapping[b]])
    return new,mapping[output]

def delete(g,replacement,rewire=None):
    mapping=list(range(n));new=[]
    for h,(op,a,b) in enumerate(original):
        if h==g:value=replacement if type(replacement) is bool else mapping[replacement]
        else:
            if rewire is not None and h==rewire[0]:op,a,b=rewire[1:]
            a,b=mapping[a],mapping[b]
            if op=='and' and (a is False or b is False):value=False
            elif op=='or' and (a is True or b is True):value=True
            elif type(a) is bool:value=b
            elif type(b) is bool:value=a
            elif a==b:value=a
            else:new.append([op,*sorted((a,b))]);value=n+len(new)-1
        mapping.append(value)
    return prune(new,mapping[data['output_wire']])

assert evaluate(original,full_inputs)[data['output_wire']]==full_target
start=time.monotonic();original_values=evaluate(original,inputs);checks=0;cases=[];witness=None;stop_reason=None
for g in range(len(original)):
    for replacement in list(range(n+g))+[False,True]:
        record={'deleted_gate':g,'replacement_type':'constant' if type(replacement) is bool else 'wire','replacement':replacement,'tested_rewires':0};cases.append(record)
        for h in range(len(original)):
            if h==g:continue
            for a,b in itertools.combinations(range(n+h),2):
                for op in ['and','or']:
                    if checks%256==0:
                        if time.monotonic()-start>=120:stop_reason='wall_limit';break
                        if int(Path('/sys/fs/cgroup/memory.current').read_text())>=6.5*1024**3:stop_reason='shared_memory_guard';break
                    first=min(g,h);row=original_values[:n+first]
                    for j,(old,x,y) in enumerate(original[first:],start=first):
                        if j==g:value=((1<<len(samples))-1 if replacement else 0) if type(replacement) is bool else row[replacement]
                        elif j==h:value=row[a]&row[b] if op=='and' else row[a]|row[b]
                        else:value=row[x]&row[y] if old=='and' else row[x]|row[y]
                        row.append(value)
                    checks+=1;record['tested_rewires']+=1
                    if row[data['output_wire']]==target:
                        candidate,new_output=delete(g,replacement,(h,op,a,b))
                        assert type(new_output) is int
                        full=evaluate(candidate,full_inputs);assert full[new_output]==full_target and len(candidate)<=19
                        witness={'input_count':n,'gates':candidate,'output_wire':new_output,'gate_count':len(candidate),'deletion':record.copy(),'rewired_gate':h,'replacement_gate':[op,a,b],'checked_assignments':1<<n}
                        (base/'L584-raw-two-edit-witness.json').write_text(json.dumps(witness,indent=2)+'\n');stop_reason='witness';break
                if stop_reason:break
            if stop_reason:break
        if stop_reason:break
    if stop_reason:break
report={'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'deletion_cases':cases,'rewire_checks':checks,'elapsed_seconds':time.monotonic()-start,'stop_reason':stop_reason or 'exhausted','witness':witness,'scope':'Deletion and one distinct-gate rewire are both applied to the original20gate program before any simplification. Aliases are evaluated dynamically if the earlier rewire changes their source. The rewire may reference the deleted wire, interpreted as its free alias/constant. After complete30row screening, a witness is constant/alias-simplified and dead-pruned, then verified on all1024inputs with<=19gates. No global lower bound is claimed.'}
(base/'L584-raw-two-edit-replay.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in ['deletion_cases','witness']}),flush=True)
if witness:print(json.dumps(witness),flush=True)
