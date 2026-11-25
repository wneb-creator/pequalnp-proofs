import argparse,json
from pathlib import Path
CORE=[0,2,3,6,7,8,9]
SATELLITES=[1,4,5]
TRIPLES=[(0,1,3),(0,2,6),(0,4,5)]
CYCLE=[(1,2),(2,5),(5,3),(3,6),(6,4),(4,1)]
PETERSEN=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]

def evaluate(gates,inputs):
    wires=list(inputs)
    for g in gates:
        pins=[wires[i] if i<len(wires) else False for i in g['inputs']]
        assert g['op'] in ['and','or','not'] and len(pins)<=2
        wires.append(all(pins) if g['op']=='and' else any(pins) if g['op']=='or' else not(pins[0] if pins else False))
    return wires

def validate_and_lift(data):
    gs=data['gates'];out=data['outputs'];assert len(gs)<=14 and len(out)==4
    core=[]
    for i,g in enumerate(gs):
        assert g['a']<7+i and g['b']<7+i
        core.append(dict(op=g['op'],inputs=[g['a']] if g['op']=='not' else [g['a'],g['b']]))
    assert all(0<=o<7+len(gs) for o in out)
    core_bad=[]
    for mask in range(128):
        x=[bool(mask>>i&1) for i in range(7)]
        v=evaluate(core,x)
        m=any(x[a] and x[b] for a,b in CYCLE)
        target=[any(x[j] for j in t) for t in TRIPLES]+[m]
        for k in range(4):
            if (k==3 or not m) and v[out[k]]!=target[k]:core_bad.append((mask,k))
    def remap(w):return CORE[w] if w<7 else 10+w-7
    lifted=[dict(op=g['op'],inputs=[remap(w) for w in g['inputs']]) for g in core]
    terms=[]
    for sat,o in zip(SATELLITES,out[:3]):
        lifted.append(dict(op='and',inputs=[sat,remap(o)]));terms.append(9+len(lifted))
    output=remap(out[3])
    for term in terms:
        lifted.append(dict(op='or',inputs=[output,term]));output=9+len(lifted)
    errors=[]
    for mask in range(1024):
        x=[bool(mask>>i&1) for i in range(10)]
        y=evaluate(lifted,x)[output]
        z=any(x[a] and x[b] for a,b in PETERSEN)
        if y!=z:errors.append(mask)
    not_count=sum(g['op']=='not' for g in lifted)
    return dict(core_errors=core_bad,gate_count=len(lifted),not_count=not_count,gates=lifted,output=output,errors=errors,
                valid=not core_bad and not errors and len(lifted)<=19 and not_count>=1)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('candidate',type=Path);p.add_argument('output',type=Path);a=p.parse_args()
    d=validate_and_lift(json.loads(a.candidate.read_text()));a.output.write_text(json.dumps(d,indent=2)+'\n')
    print(json.dumps({k:d[k] for k in ['valid','gate_count','not_count','core_errors','errors']}))
    if not d['valid']:raise SystemExit(1)
