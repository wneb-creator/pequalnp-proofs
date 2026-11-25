import argparse
import itertools
import json
from pathlib import Path

P = argparse.ArgumentParser()
P.add_argument('candidate')
P.add_argument('output_prefix')
args = P.parse_args()
HERE = Path(__file__).resolve().parent
data = json.loads((HERE/'data.json').read_text())
EDGES = [tuple(e) for e in data['edges']]
POS = data['positive_rows']
NEG = data['negative_rows']
ROWS = POS+NEG
candidate = json.loads(Path(args.candidate).read_text())
gates = candidate['gates'] if isinstance(candidate,dict) else candidate

def evaluate(gs,x,zero=None):
    values = [bool(x >> j & 1) for j in range(14)]
    for i,(op,a,b) in enumerate(gs):
        values.append(False if i==zero else (values[a] or values[b]) if op else (values[a] and values[b]))
    return values[-1]

def target(x):
    return any(x >> a & 1 and x >> b & 1 for a,b in EDGES)

def cover(es):
    best = None
    for mask in range(1<<7):
        left = [a for a in range(7) if mask >> a & 1]
        right = sorted({b for a,b in es if a not in left})
        selected = left+right
        if best is None or len(selected)<len(best):
            best = selected
    return best

def rewrite(gs,index,pivotal):
    new=[]
    signatures=[sum(1<<k for k,x in enumerate(ROWS) if x >> j & 1) for j in range(14)]
    known={sig:j for j,sig in enumerate(signatures)}
    known[0]=-1
    def add(op,a,b):
        if a==-1 or b==-1:
            if op==0:
                return -1
            return b if a==-1 else a
        signature=(signatures[a] | signatures[b]) if op else (signatures[a] & signatures[b])
        if signature in known:
            return known[signature]
        wire=14+len(new)
        new.append([op,a,b]);signatures.append(signature);known[signature]=wire
        return wire
    mapping={j:j for j in range(14)}
    for i,(op,a,b) in enumerate(gs):
        if i!=index:
            mapping[14+i]=add(op,mapping[a],mapping[b])
            continue
        remaining=list(pivotal);terms=[]
        for center in cover(remaining):
            incident=[e for e in remaining if center in e]
            if not incident:
                continue
            others=[b if a==center else a for a,b in incident]
            summed=others[0]
            for other in others[1:]:
                summed=add(1,summed,other)
            terms.append(add(0,center,summed))
            remaining=[e for e in remaining if e not in incident]
        value=-1
        for term in terms:
            value=add(1,value,term)
        mapping[14+i]=value
    output=mapping[14+len(gs)-1]
    assert output>=0
    used=set()
    def visit(wire):
        if wire<14 or wire in used:
            return
        used.add(wire)
        _,a,b=new[wire-14];visit(a);visit(b)
    visit(output)
    remap={j:j for j in range(14)}
    compact=[]
    for i,(op,a,b) in enumerate(new):
        if 14+i in used:
            remap[14+i]=14+len(compact)
            compact.append([op,remap[a],remap[b]])
    assert remap[output]==14+len(compact)-1
    return compact

assert all(evaluate(gates,x)==target(x) for x in range(1<<14))
records=[]
best=gates
for i in range(len(gates)):
    pivotal=[edge for edge,x in zip(EDGES,POS) if not evaluate(gates,x,zero=i)]
    changed=rewrite(gates,i,pivotal)
    assert all(evaluate(changed,x)==target(x) for x in ROWS)
    if len(changed)<len(best):
        assert all(evaluate(changed,x)==target(x) for x in range(1<<14))
        best=changed
        Path(args.output_prefix+'-best.json').write_text(json.dumps({'gates':best,'size':len(best),'full_rows_checked':16384,'replaced_gate':i,'pivotal_edges':pivotal},indent=2)+'\n')
    records.append({'gate':i,'pivotal_edges':pivotal,'rewritten_size':len(changed)})
report={'original_size':len(gates),'best_size':len(best),'records':records}
Path(args.output_prefix+'-report.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'original_size':len(gates),'best_size':len(best)}))
