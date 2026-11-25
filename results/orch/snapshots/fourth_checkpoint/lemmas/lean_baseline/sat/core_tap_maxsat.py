import argparse
import json
from pathlib import Path

from core_tap_synthesis import validate, truth_columns
from grid_taps_synthesis import emit, stamp, Solver, model, evaluate_wires, canonical_seed
from incremental_cegis import LiveCNF


def cone(gates,output,n):
    active=set()
    def visit(wire):
        if wire<n or wire-n in active: return
        i=wire-n
        active.add(i)
        visit(gates[i][1])
        visit(gates[i][2])
    visit(output)
    mapping={i:i for i in range(n)}
    answer=[]
    for i in sorted(active):
        op,a,b=gates[i]
        answer.append([op,mapping[a],mapping[b]])
        mapping[n+i]=n+len(answer)-1
    return answer,mapping[output]


def thresholds(cnf,errors,maximum):
    row=[1]+[-1]*(maximum+1)
    hint_total=0
    for error,hint in errors:
        hint_total+=hint
        next_row=[1]
        for j in range(1,maximum+2):
            old,previous=row[j],row[j-1]
            z=cnf.var(hint_total>=j)
            cnf.clause(-old,z)
            cnf.clause(-previous,-error,z)
            cnf.clause(old,previous,-z)
            cnf.clause(old,error,-z)
            next_row.append(z)
        row=next_row
    return row


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('problem',type=Path)
    parser.add_argument('output',type=Path)
    parser.add_argument('--case',default='outside9_pair6_11')
    parser.add_argument('--seconds',type=int,default=180)
    parser.add_argument('--wire-rank',type=int,default=0)
    parser.add_argument('--order-max',action='store_true')
    args=parser.parse_args()
    pack=json.loads(args.problem.read_text())
    case=next(c for c in pack['cases'] if c['name']==args.case)
    data={'inputs':case['inputs'],'tests':[
        {'mask':c['input'],'targets':[int(c['residual']),-1 if c['tap'] is None else int(c['tap'])]}
        for c in case['constraints']]}
    n=case['inputs']
    gates=[[op,*sorted((a,b))] for op,a,b in case['seed']['gates'][:-1]]
    assert len(gates)==case['max_gates']
    ranked=sorted((sum(evaluate_wires(gates,c['input'],n)[wire]!=bool(c['tap'])
                       for c in case['constraints'] if c['tap'] is not None),wire)
                  for wire in range(n+len(gates)))
    maximum,tap=ranked[args.wire_rank]
    seed={'gates':gates,'outputs':[case['seed']['residual_output'],tap]}
    if args.order_max:
        seed=canonical_seed(seed,n)
    args.output.mkdir(parents=True,exist_ok=True)
    selected,outs,nvars,nclauses,errors=emit(args.output/'initial.cnf',data,seed,
                                          soft_outputs=(1,),order_max=args.order_max)
    assert sum(hint for _,hint in errors)==maximum
    solver=Solver(5773+args.wire_rank)
    for op,sa,sb in selected:
        for lit in [op]+sa+sb: solver.freeze(lit)
    for out in outs:
        for lit in out: solver.freeze(lit)
    for error,_ in errors: solver.freeze(error)
    with (args.output/'initial.cnf').open() as source:
        for line in source:
            if not line.startswith('p'):
                solver.add(*[int(word) for word in line.split()[:-1]])
    journal=(args.output/'bound-clauses.txt').open('w')
    cnf=LiveCNF(solver,nvars,nclauses,journal)
    row=thresholds(cnf,errors,maximum)
    for lit in row: solver.freeze(lit)
    journal.flush()
    stamp('START',case['name'],'maximum-errors',maximum,'vars',cnf.variables,'clauses',cnf.clauses)
    bound=maximum
    while bound>=0:
        solver.lib.ccadical_assume(solver.ptr,-row[bound+1])
        result=solver.solve(args.seconds)
        stamp('BOUND',bound,'SOLVER',result)
        if result!=10: break
        answer=model(solver,selected)
        assert len(answer)<=case['max_gates']
        assert all(op in (0,1) and 0<=a<n+i and 0<=b<n+i
                   for i,(op,a,b) in enumerate(answer))
        outputs=[]
        for out in outs:
            choices=[i for i,lit in enumerate(out) if solver.truth(lit)]
            assert len(choices)==1
            outputs.append(choices[0])
        actual=sum(evaluate_wires(answer,c['input'],n)[outputs[1]]!=bool(c['tap'])
                   for c in case['constraints'] if c['tap'] is not None)
        assert actual<=bound
        assert all(evaluate_wires(answer,c['input'],n)[outputs[0]]==c['residual']
                   for c in case['constraints'])
        allones=(1<<(1<<n))-1
        wires=truth_columns(n)
        expected=0
        for a,b in pack['edges']: expected|=wires[a]&wires[b]
        for op,a,b in answer: wires.append((wires[a]|wires[b]) if op else (wires[a]&wires[b]))
        assert wires[outputs[0]]==expected
        residual,residual_output=cone(answer,outputs[0],n)
        witness={'gates':answer,'outputs':outputs,'case':case['name'],
                 'tap_input_indices':case['tap_input_indices'],'tap_errors':actual,
                 'tap_is_correct':actual==0,
                 'outside_original_point':case['outside_original_point'],
                 'input_original':pack['input_original'],'calibration':False,
                 'residual_gates':residual,'residual_output':residual_output,
                 'full_graph_gate_count':len(answer)+case.get('completion_additional_gates',36-len(case['tap_input_indices']))}
        (args.output/f'candidate-errors-{actual}.json').write_text(json.dumps(witness))
        stamp('CANDIDATE','tap-errors',actual,'residual-size',len(residual),
              'residual-ANDs',sum(op==0 for op,_,_ in residual))
        if len(residual)<=case.get('residual_target_gates',28):
            (args.output/'EXACT-CORE-WITNESS.json').write_text(json.dumps(witness))
            stamp('TARGET CORE WITNESS',len(residual))
            break
        if actual==0:
            assert validate(pack,case,answer,outputs)
            (args.output/'EXACT-CORE-TAP.json').write_text(json.dumps(witness))
            stamp('TARGET CORE TAP',len(answer))
            break
        bound=actual-1
    journal.close()
    solver.close()


if __name__=='__main__':
    main()
