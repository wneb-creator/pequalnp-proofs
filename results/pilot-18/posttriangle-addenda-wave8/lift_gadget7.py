"""A7-input11-gate subdivided-K4 implementation lifts to the full21 target."""
from pathlib import Path
import json,hashlib
from prepare_triangle589 import EDGES
H=Path('/tmp/oec/pequalnp-pilot-18/orch/S05')
MAP=[0,2,4,9,5,8,10]
GE=[(3,4),(3,5),(4,5),(0,3),(1,4),(2,5),(0,6),(1,6),(2,6)]
def lift(d):
    assert d['inputs']==7 and d['gate_wire_offset']==7
    gates=[];memo={}
    def op(kind,a,b):
        if a==b:return a
        key=(kind,*sorted((a,b)))
        if key not in memo:memo[key]=11+len(gates);gates.append(list(key))
        return memo[key]
    wires=MAP[:]
    for kind,a,b in d['gates']:wires.append(op(kind,wires[a],wires[b]))
    core=wires[d['output']]
    six=op('and',6,op('or',10,op('or',3,7)))
    seven=op('and',7,op('or',3,9))
    one=op('and',1,op('or',4,8))
    rest=op('or',six,op('or',seven,one));output=op('or',core,rest)
    return dict(inputs=11,gate_wire_offset=11,size=len(gates),gates=gates,output=output)
def main():
    p=H/'gadget7-contributor-candidate.json';d=json.loads(p.read_text());assert d['size']==12
    for m in range(128):
        v=[bool(m>>i&1) for i in range(7)]
        for kind,a,b in d['gates']:v.append(v[a]&v[b] if kind=='and' else v[a]|v[b])
        assert v[d['output']]==any(m>>a&1 and m>>b&1 for a,b in GE)
    e=lift(d);assert e['size']<=22
    mapped={tuple(sorted((MAP[a],MAP[b]))) for a,b in GE}
    residual={(3,6),(6,7),(6,10),(3,7),(7,9),(1,4),(1,8)}
    assert not mapped&residual and mapped|residual==set(EDGES)
    for m in range(2048):
        v=[bool(m>>i&1) for i in range(11)]
        for kind,a,b in e['gates']:v.append(v[a]&v[b] if kind=='and' else v[a]|v[b])
        assert v[e['output']]==any(m>>a&1 and m>>b&1 for a,b in EDGES)
    out=H/'gadget7-lift-exact22-control.json'
    with out.open('x') as f:json.dump(e,f,indent=2);f.write('\n')
    result=dict(status='PASS_EXACT_LIFT_IDENTITY_AND_22_GATE_CONTROL',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),local_candidate_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),control_sha256=hashlib.sha256(out.read_bytes()).hexdigest(),gadget_edges=sorted(mapped),residual_edges=sorted(residual),residual_expression='6*(3 OR7 OR10) OR7*(3 OR9) OR1*(4 OR8)',residual_gates=9,final_OR=1,local_size=d['size'],full_size=e['size'],checks=dict(local128=128,global2048=2048),theoretical_lift='ANY exact seven-input circuit of size<=11 yields fullsize<=21; no interface condition',exact21_found=False,Lean_proof=False)
    with (H/'gadget7-lift-result.json').open('x') as f:json.dump(result,f,indent=2);f.write('\n')
    print(json.dumps(result))
if __name__=='__main__':main()
