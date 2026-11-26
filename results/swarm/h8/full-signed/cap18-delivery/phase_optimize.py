import argparse
import json
from pathlib import Path

parser = argparse.ArgumentParser(description='Minimize explicit NOT gates over phases of a fixed signed binary DAG.')
parser.add_argument('candidate', type=Path)
parser.add_argument('--output', required=True, type=Path)
args = parser.parse_args()
candidate = json.loads(args.candidate.read_text())
ninputs = candidate['inputs']
gates = candidate['gates']
n = len(gates)
output = candidate['output']
masks = [0] * (ninputs+n)
signs = [0] * (ninputs+n)
for j, (op,a,b) in enumerate(gates):
    assert 0 <= op < 4 and 0 <= a < ninputs+j and 0 <= b < ninputs+j and a != b
    for src,neg in [(a,op==3),(b,op==2)]:
        masks[src] |= 1<<j
        if neg: signs[src] |= 1<<j
masks[output] |= 1<<n

best=n+ninputs+1
choice=0
for assignment in range(1<<n):
    cost=0
    for src,(mask,sign) in enumerate(zip(masks,signs)):
        phase = 0 if src < ninputs else assignment>>(src-ninputs)&1
        required=(assignment^sign)&mask
        if required != (mask if phase else 0): cost+=1
        if cost>=best: break
    if cost<best:
        best=cost
        choice=assignment

physical=[]
slots={}
opposite={}
phases=[0]*ninputs+[(choice>>j)&1 for j in range(n)]
needs=[((choice^s)&m)!=(m if p else 0) for m,s,p in zip(masks,signs,phases)]
def append(op,inputs):
    physical.append([op,inputs])
    return ninputs+len(physical)-1
for src in range(ninputs):
    slots[src]=src
    if needs[src]: opposite[src]=append('not',[src])
for j,(op,a,b) in enumerate(gates):
    src=ninputs+j
    p=phases[src]
    pa=p^(op==3)
    pb=p^(op==2)
    aa=slots[a] if pa==phases[a] else opposite[a]
    bb=slots[b] if pb==phases[b] else opposite[b]
    is_or=(op==1)^bool(p)
    slots[src]=append('or' if is_or else 'and',[aa,bb])
    if needs[src]: opposite[src]=append('not',[slots[src]])
physical_output=slots[output] if phases[output]==0 else opposite[output]
assert sum(op=='not' for op,_ in physical)==best

edges=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
errors=[]
for row in range(1<<ninputs):
    signed=[bool(row>>i&1) for i in range(ninputs)]
    for op,a,b in gates:
        x,y=signed[a],signed[b]
        signed.append((x and y) if op==0 else (x or y) if op==1 else (x and not y) if op==2 else (not x and y))
    actual=[bool(row>>i&1) for i in range(ninputs)]
    for op,indices in physical:
        values=[actual[i] for i in indices]
        actual.append(all(values) if op=='and' else any(values) if op=='or' else not values[0])
    assert actual[physical_output]==signed[output]
    target=any(bool(row>>a&1) and bool(row>>b&1) for a,b in edges)
    if target!=actual[physical_output]:errors.append(row)

result=dict(inputs=ninputs,signed_gate_count=n,min_not_count=best,total_gate_count=len(physical),
            phase_assignment=choice,gates=physical,output=physical_output,petersen_errors=errors)
args.output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['signed_gate_count','min_not_count','total_gate_count','petersen_errors']}))
