"""Independent prefix-set construction and sampled tail cost-DP checks."""
from pathlib import Path
import hashlib,json,random,time,resource,os
from free_E_six_gate_scan import tail,expr_value,TARGET
H=Path('/tmp/oec/pequalnp-pilot-18/orch/S05')
def main():
    os.nice(10);resource.setrlimit(resource.RLIMIT_CPU,(3,3));t=time.monotonic()
    inputs=[sum(1<<m for m in range(32) if m&(1<<i)) for i in range(5)]
    base=frozenset(inputs+[inputs[3]|inputs[4]])
    pairs={inputs[i]&inputs[j] for i in range(5) for j in range(i+1,5)}
    assert len(pairs)==10 and not pairs&base
    states={frozenset()};counts=[]
    for _ in range(3):
        nxt=set()
        for state in states:
            available=base|state
            generated={a&b for a in available for b in available}|{a|b for a in available for b in available}
            nxt.update(state|{v} for v in generated-available)
        states=nxt;counts.append(len(states))
    canonical=sorted(tuple(sorted(state)) for state in states)
    digest=hashlib.sha256(json.dumps(canonical,separators=(',',':')).encode()).hexdigest()
    original=json.load(open(H/'freeE-sixgate-complete-result.json'))
    assert counts==[25,456,7478] and digest==original['prefix_state_sha256']
    rng=random.Random(7478);sample=rng.sample(canonical,128);checks=0;records=[]
    for state in sample:
        available=base|set(state);layers=[set(available)];seen=set(available)
        for cost in range(1,4):
            new=set()
            for i in range(cost):
                j=cost-1-i
                new.update(a&b for a in layers[i] for b in layers[j]);new.update(a|b for a in layers[i] for b in layers[j])
            new-=seen;layers.append(new);seen|=new
        assert TARGET not in seen
        for target in [TARGET]+rng.sample(sorted(seen),7):
            e=tail(sorted(available),target);assert (e is not None)==(target in seen)
            if e is not None:assert expr_value(e,{x:x for x in available})==target
            checks+=1
        records.append(dict(prefix=state,reachable_layer_sizes=[len(x) for x in layers]))
    result=dict(status='PASS_INDEPENDENT_PREFIX_AND_SAMPLED_TAIL_CONTROLS',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),scan_source_sha256=hashlib.sha256((H/'free_E_six_gate_scan.py').read_bytes()).hexdigest(),prefix_counts=counts,prefix_state_sha256=digest,tail_prefixes=len(sample),tail_targets_checked=checks,padding_distinct_AND_functions=10,records=records,elapsed_seconds=time.monotonic()-t,full_independent_tail_exhaustion=False,Lean_proof=False)
    with (H/'free-E-scan-independent-result.json').open('x') as f:json.dump(result,f,indent=2);f.write('\n')
    print(json.dumps({k:v for k,v in result.items() if k!='records'}))
if __name__=='__main__':main()
