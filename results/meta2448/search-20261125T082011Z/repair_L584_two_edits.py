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

def delete(g,replacement):
    mapping=list(range(n));new=[]
    for h,(op,a,b) in enumerate(original):
        if h==g:value=replacement if type(replacement) is bool else mapping[replacement]
        else:
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
start=time.monotonic();cases=[];unique=[];seen={}
for g in range(len(original)):
    for replacement in list(range(n+g))+[False,True]:
        gates,output=delete(g,replacement);assert len(gates)<20
        key=json.dumps([gates,output])
        if key not in seen:seen[key]=len(unique);unique.append({'gates':gates,'output_wire':output,'tested_rewires':0})
        cases.append({'deleted_gate':g,'replacement_type':'constant' if type(replacement) is bool else 'wire','replacement':replacement,'normalized_base':seen[key]})
checks=0;witness=None;stop_reason=None
for index,item in enumerate(unique):
    gates=item['gates'];output=item['output_wire']
    if type(output) is bool or output<n:continue
    assert output==n+len(gates)-1
    values=evaluate(gates,inputs)
    for h in range(len(gates)):
        for a,b in itertools.combinations(range(n+h),2):
            for op in ['and','or']:
                if checks%256==0:
                    if time.monotonic()-start>=120:stop_reason='wall_limit';break
                    if int(Path('/sys/fs/cgroup/memory.current').read_text())>=6.5*1024**3:stop_reason='shared_memory_guard';break
                changed=values[a]&values[b] if op=='and' else values[a]|values[b]
                row=values[:n+h]+[changed]
                for later,x,y in gates[h+1:]:row.append(row[x]&row[y] if later=='and' else row[x]|row[y])
                checks+=1;item['tested_rewires']+=1
                if row[output]==target:
                    candidate=[list(g) for g in gates];candidate[h]=[op,a,b];candidate,new_output=prune(candidate,output)
                    full=evaluate(candidate,full_inputs);assert full[new_output]==full_target and len(candidate)<=19
                    witness={'input_count':n,'gates':candidate,'output_wire':new_output,'gate_count':len(candidate),'normalized_base':index,'rewired_gate':h,'replacement':[op,a,b],'checked_assignments':1<<n}
                    (base/'L584-two-edit-witness.json').write_text(json.dumps(witness,indent=2)+'\n');stop_reason='witness';break
            if stop_reason:break
        if stop_reason:break
    if stop_reason:break
report={'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'deletion_cases':cases,'normalized_bases':unique,'normalized_base_count':len(unique),'rewire_checks':checks,'elapsed_seconds':time.monotonic()-start,'stop_reason':stop_reason or 'exhausted','witness':witness,'scope':'Each430direct wire/constant deletion is first simplified by constant/alias propagation and dead-gate pruning. One surviving gate is then replaced by either binary AND/OR of any two distinct earlier wires. Constant/input-output bases have no surviving gate to rewrite. Separation-row screening is followed by full1024input verification for any witness. This is a restricted two-edit neighborhood, not a global lower bound.'}
(base/'L584-two-edit-replay.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in ['deletion_cases','normalized_bases','witness']}),flush=True)
if witness:print(json.dumps(witness),flush=True)
