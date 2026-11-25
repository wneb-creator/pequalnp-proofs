#!/usr/bin/env python3
"""Minimize shared NOT sources over all DeMorgan phase choices of a signed circuit."""
import argparse
import json
from pathlib import Path
from signed_source import N, target

def evaluate(gates, output_sign, row):
    values=[bool((row>>i)&1) for i in range(N)]+[False]
    for op,operands in gates:
        a,b=[values[wire]^sign for wire,sign in operands]
        values.append(a and b if op=='AND' else a or b)
    return values[-1]^output_sign

def optimize(report, stop_at):
    gates=report['signed_gates']
    m=len(gates)
    assert m<=25
    signs=[]
    sources=[]
    incidents=[[] for _ in range(m)]
    for j,(_,operands) in enumerate(gates):
        for wire,sign in operands:
            eid=len(signs)
            signs.append(bool(sign)); sources.append(wire)
            incidents[j].append(eid)
            if wire>N: incidents[wire-N-1].append(eid)
    eid=len(signs)
    signs.append(bool(report['output_sign'])); sources.append(N+m)
    incidents[-1].append(eid)
    counts=[0]*(N+1+m)
    for wire,sign in zip(sources,signs): counts[wire]+=sign
    cost=sum(c>0 for c in counts)
    best,phase,best_phase=cost,0,0
    visited=1
    for t in range(1,1<<m):
        if best<=stop_at: break
        j=(t&-t).bit_length()-1
        phase ^= 1<<j
        for eid in incidents[j]:
            wire=sources[eid]
            before=counts[wire]
            counts[wire]+= -1 if signs[eid] else 1
            signs[eid]=not signs[eid]
            cost+=(counts[wire]>0)-(before>0)
        visited+=1
        if cost<best: best,best_phase=cost,phase
    adjusted=[]
    for j,(op,operands) in enumerate(gates):
        p=bool((best_phase>>j)&1)
        newop=('OR' if op=='AND' else 'AND') if p else op
        newargs=[]
        for wire,sign in operands:
            source_phase=bool((best_phase>>(wire-N-1))&1) if wire>N else False
            newargs.append([wire,bool(sign)^source_phase^p])
        newargs.sort(key=lambda x:(x[0],x[1]))
        adjusted.append([newop,newargs])
    output_sign=bool(report['output_sign'])^bool((best_phase>>(m-1))&1)
    used={wire for _,operands in adjusted for wire,sign in operands if sign}
    if output_sign: used.add(N+m)
    assert len(used)==best
    sentinel=N+m+len(used)+1
    raw={i:i for i in range(N)}; raw[N]=sentinel
    negative={}; expanded=[]
    def emit(op,args):
        expanded.append([op,args]); return N+len(expanded)-1
    for wire in sorted(used):
        if wire<=N: negative[wire]=emit('NOT',[raw[wire]])
    for j,(op,operands) in enumerate(adjusted):
        wire=N+1+j
        raw[wire]=emit(op,[negative[w] if s else raw[w] for w,s in operands])
        if wire in used: negative[wire]=emit('NOT',[raw[wire]])
    output=negative[N+m] if output_sign else raw[N+m]
    bad=[]
    for row in range(1<<N):
        old=evaluate(gates,report['output_sign'],row)
        new=evaluate(adjusted,output_sign,row)
        assert new==old, 'DeMorgan phase transformation changed the function'
        values=[bool((row>>i)&1) for i in range(N)]
        for op,args in expanded:
            ins=[values[i] if i<len(values) else False for i in args]
            values.append(all(ins) if op=='AND' else any(ins) if op=='OR' else not ins[0])
        assert values[output]==new, 'Expanded NOT circuit disagrees with signed circuit'
        if new!=target(row): bad.append(row)
    return {'signed_gates':adjusted,'output_sign':output_sign,'phase_bits':best_phase,
            'phase_assignments_visited':visited,'phase_optimum_proven':visited==(1<<m),
            'used_negative_sources':sorted(used),'used_negative_source_count':best,
            'emitted_not_count':best,'expanded_gates':expanded,'output':output,
            'binary_gate_count':m,'gate_count':len(expanded),
            'correct_all_1024':not bad,'counterexamples':bad}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--report',required=True); p.add_argument('--out',required=True)
    p.add_argument('--stop-at',type=int,default=-1)
    args=p.parse_args()
    result=optimize(json.loads(Path(args.report).read_text()),args.stop_at)
    Path(args.out).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ['binary_gate_count','emitted_not_count','gate_count','correct_all_1024','phase_assignments_visited','phase_optimum_proven']}))

if __name__=='__main__': main()
