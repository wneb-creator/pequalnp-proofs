import json,time
from pathlib import Path
from grid_taps_synthesis import emit,Solver,evaluate_wires
from incremental_cegis import LiveCNF,model
from full_residual_cegis import gate_edit_thresholds,thresholds


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
    total_clauses=0
    last_variable=1
    for path in [folder/'initial.cnf',folder/'added-clauses.txt']:
        with path.open() as source:
            for line in source:
                if not line.startswith('p'):
                    literals=list(map(int,line.split()[:-1]))
                    solver.add(*literals)
                    last_variable=max(last_variable,max(map(abs,literals),default=1))
                    total_clauses+=1
    with (folder/'bounded-calibration-added.txt').open('w') as journal:
        cnf=LiveCNF(solver,last_variable,total_clauses,journal)
        active=[]
        for (_,sa,sb),(_,a,b) in zip(selected,seed['gates']):
            copy=cnf.var(a==b)
            for x,y in zip(sa,sb):
                cnf.clause(-x,-y,copy)
                cnf.clause(-copy,-x,y)
            active.append((-copy,a!=b))
        costs=thresholds(cnf,active,61)
        for literal in costs:solver.freeze(literal)
        edits=gate_edit_thresholds(cnf,solver,selected,seed['gates'],3)
        journal.flush()
        for radius,expected in [(0,20),(1,10)]:
            solver.lib.ccadical_assume(solver.ptr,-costs[62])
            solver.lib.ccadical_assume(solver.ptr,-edits[radius+1])
            begin=time.monotonic();result=solver.solve(30)
            print('BOUND',radius,'result',result,'seconds',time.monotonic()-begin,flush=True)
            assert result==expected
        found=model(solver,selected)
        assert sum(x!=y for x,y in zip(found,seed['gates']))<=1
        assert sum(a!=b for op,a,b in found)<=61
        outputs=[]
        for out in outs:
            choices=[i for i,lit in enumerate(out) if solver.truth(lit)]
            assert len(choices)==1;outputs.append(choices[0])
        values=evaluate_wires(found,4098,n)
        assert not values[outputs[0]] and values[outputs[1]]
        (folder/'bounded-calibration-model.json').write_text(json.dumps({'gates':found,'outputs':outputs}))
        fresh=gate_edit_thresholds(cnf,solver,selected,found,3)
        solver.lib.ccadical_assume(solver.ptr,-costs[62])
        solver.lib.ccadical_assume(solver.ptr,-fresh[1])
        result=solver.solve(30)
        print('RECENTER BOUND0 result',result,flush=True)
        assert result==10 and model(solver,selected)==found
        print('PASS adaptive gate thresholds and recentering on saved fullCNF')
    solver.close()


if __name__=='__main__':main()
