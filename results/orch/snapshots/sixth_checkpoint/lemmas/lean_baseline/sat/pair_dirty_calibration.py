import json
from pathlib import Path
from grid_taps_synthesis import emit, Solver
from incremental_cegis import LiveCNF
from full_residual_cegis import require_pair_dirty


def check(folder,name,gates,outputs,expected):
    n=4
    edges=[(0,1),(2,3)]
    tap=[1]
    tests=[]
    for mask in range(16):
        h=any(mask>>a&1 and mask>>b&1 for a,b in edges)
        tests.append({'mask':mask,'targets':[int(h),-1 if h else int(bool(mask&2))]})
    seed={'gates':gates,'outputs':outputs}
    path=folder/(name+'.cnf')
    selected,outs,nvars,nclauses=emit(path,{'inputs':n,'tests':tests},seed)
    solver=Solver(5713)
    for op,sa,sb in selected:
        for literal in [op]+sa+sb: solver.freeze(literal)
    for out in outs:
        for literal in out: solver.freeze(literal)
    with path.open() as source:
        for line in source:
            if not line.startswith('p'): solver.add(*map(int,line.split()[:-1]))
    with (folder/(name+'-added.txt')).open('w') as journal:
        cnf=LiveCNF(solver,nvars,nclauses,journal)
        for (op,sa,sb),(wanted,a,b) in zip(selected,gates):
            cnf.clause(op if wanted else -op)
            cnf.clause(sa[a])
            cnf.clause(sb[b])
        for out,wanted in zip(outs,outputs): cnf.clause(out[wanted])
        proper=[(1 if op==0 and a!=b else -1,op==0 and a!=b) for op,a,b in gates]
        bits=require_pair_dirty(cnf,solver,selected,outs,proper,seed,n,edges,tap)
        journal.flush()
        result=solver.solve(5)
        assert result==expected,(name,result)
        mask=sum(1<<i for i,lit in enumerate(bits) if solver.truth(lit)) if result==10 else None
        print(json.dumps({'case':name,'result':result,'witness':mask}),flush=True)
    solver.close()


def main():
    folder=Path('/tmp/oec/pequalnp-pilot-57/pair-dirty-calibration')
    folder.mkdir(exist_ok=True)
    clean=[[0,0,1],[0,2,3],[1,4,5]]
    dirty=[[1,0,2],[1,1,3],[0,4,5],[0,0,1],[0,2,3],[1,7,8],[0,6,9]]
    check(folder,'clean',clean,[6,1],20)
    check(folder,'copy_only_dirty',clean+[[0,1,1]],[6,7],20)
    check(folder,'absorbed_dirty',dirty,[10,1],10)
    print('PASS symbolic pair-dirty calibration')


if __name__=='__main__': main()
