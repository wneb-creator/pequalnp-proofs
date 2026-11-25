#!/usr/bin/env python3
"""Decode an official LinkN2 model and exhaustively check its Boolean circuit."""
import argparse
import json
from pathlib import Path


def main():
    p=argparse.ArgumentParser()
    p.add_argument('--directory',type=Path,required=True)
    p.add_argument('--solver-output',type=Path,required=True)
    p.add_argument('--edges',type=Path,required=True)
    p.add_argument('--out',type=Path,required=True)
    args=p.parse_args()
    metadata=json.loads((args.directory/'metadata.json').read_text())
    n,s=metadata['n'],metadata['gates']
    rows=json.loads((args.directory/'rows.json').read_text())
    edges=json.loads(args.edges.read_text())
    positive=set()
    sat=False
    with args.solver_output.open() as f:
        for line in f:
            if line.strip()=='s SATISFIABLE': sat=True
            if line.startswith('v '):
                for word in line.split()[1:]:
                    lit=int(word)
                    if lit>0: positive.add(lit)
    if not sat: raise ValueError('solver output does not report SATISFIABLE')
    checked=0
    with (args.directory/'official.cnf').open() as f:
        for line in f:
            if line.startswith(('c','p')): continue
            clause=list(map(int,line.split()))
            assert clause[-1]==0
            if not any((abs(lit) in positive)==(lit>0) for lit in clause[:-1]):
                raise ValueError(f'model fails clause {checked+1}')
            checked+=1
    width=2**n+n+s+2
    def ix(k,j,a): return (k*(s+1)+j)*width+a+1
    def selected(k,j,bound):
        return [a for a in range(bound) if ix(k,j,a) in positive]
    gates=[]
    raw=[]
    for j in range(s):
        ops=selected(0,j,4)
        src1=selected(1,j,n+j+1)
        src2=selected(2,j,n+j+1)
        assert ops and src1 and src2
        op=ops[0]
        a=src1[0]
        b=a if op==3 else src2[0]
        assert b in src2
        raw.append({'op':op,'a':a,'b':b,'selected_ops':ops})
        a=a if a<n+j else -1
        b=b if b<n+j else -1
        if op==2: gates.append([2,-1,-1])
        elif op==3: gates.append([2,a,-1])
        else: gates.append([op,a,b])
    outputs=selected(6,0,n+s+1)
    assert outputs
    output=outputs[0]
    total=2**n
    allbits=(1<<total)-1
    values=[sum(1<<r for r in range(total) if r>>i&1) for i in range(n)]
    for op,a,b in gates:
        av=values[a] if 0<=a<len(values) else 0
        bv=values[b] if 0<=b<len(values) else 0
        values.append(av&bv if op==0 else av|bv if op==1 else allbits^av)
    actual=values[output] if output<len(values) else 0
    expected=0
    for a,b in edges: expected|=values[a]&values[b]
    mismatch=actual^expected
    counterexamples=[r for r in range(total) if mismatch>>r&1]
    sample_errors=[r for r in rows if mismatch>>r&1]
    assert not sample_errors, f'decoding failed on certified rows: {sample_errors[:10]}'
    result={'gates':gates,'output':output,'raw_official_model':raw,
            'cnf_clauses_verified':checked,'exhaustive_inputs_verified':total,
            'mismatch_count':len(counterexamples),'counterexamples':counterexamples,
            'exact':not counterexamples}
    args.out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ['output','cnf_clauses_verified',
          'exhaustive_inputs_verified','mismatch_count','exact']},indent=2))


if __name__=='__main__': main()
