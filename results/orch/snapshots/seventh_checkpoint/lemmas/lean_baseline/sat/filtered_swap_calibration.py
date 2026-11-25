import json,time
from pathlib import Path
from grid_taps_synthesis import emit,Solver,evaluate_wires


def main():
    base=Path('results/orch/lemmas/lean_baseline/sat')
    folder=Path('/tmp/oec/pequalnp-pilot-57/full-residual-filtered-cegis')
    seed=json.loads((folder/'seed.json').read_text())
    pack=json.loads((base/'full_residual_tap.json').read_text());case=pack['cases'][0];n=case['inputs']
    qmask=sum(1<<v for v in case['tap_input_indices'])
    left={a for a,b in pack['edges']};right={b for a,b in pack['edges']}
    masks={0}|{1<<v for v in range(n)}|{(1<<a)|(1<<b) for a,b in pack['edges']}
    masks|={sum(1<<v for v in left),sum(1<<v for v in right),sum(1<<v for v in right)&~qmask}
    tests=[]
    for mask in sorted(masks):
        hit=any(mask>>a&1 and mask>>b&1 for a,b in pack['edges'])
        tests.append({'mask':mask,'targets':[int(hit),-1 if hit else int(bool(mask&qmask))]})
    rebuilt=folder/'calibration-rebuilt.cnf'
    selected,outs,nvars,nclauses=emit(rebuilt,{'inputs':n,'tests':tests},seed,sample_wires={})
    assert rebuilt.read_bytes()==(folder/'initial.cnf').read_bytes()
    answer=[gate.copy() for gate in seed['gates']]
    assert answer[8]==[1,1,12]
    answer[8]=[1,0,13]
    mask=4098;values=evaluate_wires(answer,mask,n)
    assert not values[seed['outputs'][0]] and values[seed['outputs'][1]]
    solver=Solver(57131)
    for op,sa,sb in selected:
        for literal in [op]+sa+sb:solver.freeze(literal)
    for out in outs:
        for literal in out:solver.freeze(literal)
    for path in [folder/'initial.cnf',folder/'added-clauses.txt']:
        with path.open() as source:
            for line in source:
                if not line.startswith('p'):solver.add(*map(int,line.split()[:-1]))
    for (op,sa,sb),(wanted,a,b) in zip(selected,answer):
        solver.add(op if wanted else -op)
        solver.add(sa[a]);solver.add(sb[b])
    for out,wanted in zip(outs,seed['outputs']):solver.add(out[wanted])
    begin=time.monotonic();result=solver.solve(30)
    print('FIXED ONE-GATE SWAP result',result,'seconds',time.monotonic()-begin,flush=True)
    assert result==10
    assert sum(a!=b for op,a,b in answer)==61
    print('PASS saved fullCNF plus counterexample4098 admits the explicitonegate orientation swap')
    solver.close()


if __name__=='__main__':main()
