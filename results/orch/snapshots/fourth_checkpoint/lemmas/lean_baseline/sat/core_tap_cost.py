import argparse
import json
from pathlib import Path

from core_tap_synthesis import validate
from core_tap_maxsat import cone
from grid_taps_synthesis import emit, stamp, Solver, model, canonical_seed
from incremental_cegis import LiveCNF


def compact(gates,outputs,n):
    aliases={i:i for i in range(n)}
    copied=[]
    for i,(op,a,b) in enumerate(gates):
        a,b=aliases[a],aliases[b]
        if a==b:
            aliases[n+i]=a
        else:
            aliases[n+i]=n+len(copied)
            copied.append([op,a,b])
    outputs=[aliases[o] for o in outputs]
    active=set()
    def visit(wire):
        if wire<n or wire-n in active: return
        i=wire-n
        active.add(i)
        visit(copied[i][1])
        visit(copied[i][2])
    for output in outputs: visit(output)
    mapping={i:i for i in range(n)}
    answer=[]
    for i in sorted(active):
        op,a,b=copied[i]
        mapping[n+i]=n+len(answer)
        answer.append([op,mapping[a],mapping[b]])
    return answer,[mapping[o] for o in outputs]


def thresholds(cnf,active,maximum):
    row=[1]+[-1]*(maximum+1)
    hints=0
    for literal,hint in active:
        hints+=hint
        next_row=[1]
        for j in range(1,maximum+2):
            old,previous=row[j],row[j-1]
            z=cnf.var(hints>=j)
            cnf.clause(-old,z)
            cnf.clause(-previous,-literal,z)
            cnf.clause(old,previous,-z)
            cnf.clause(old,literal,-z)
            next_row.append(z)
        row=next_row
    return row


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('problem',type=Path)
    parser.add_argument('output',type=Path)
    parser.add_argument('--case',default='outside4_triple13_14_16')
    parser.add_argument('--seconds',type=int,default=300)
    parser.add_argument('--pads',type=int,default=2)
    parser.add_argument('--attempts',type=int,default=1)
    parser.add_argument('--order-max',action='store_true')
    args=parser.parse_args()
    pack=json.loads(args.problem.read_text())
    case=next(c for c in pack['cases'] if c['name']==args.case)
    n=case['inputs']
    data={'inputs':n,'tests':[
        {'mask':c['input'],'targets':[int(c['residual']),-1 if c['tap'] is None else int(c['tap'])]}
        for c in case['constraints']]}
    original=case['seed']
    seed={'gates':[[op,*sorted((a,b))] for op,a,b in original['gates']],
          'outputs':[original['residual_output'],original['tap_output']]}
    maximum=len(seed['gates'])
    for i in range(args.pads):
        side=i%2
        output=seed['outputs'][side]
        seed['gates'].append([0,output,output])
        seed['outputs'][side]=n+len(seed['gates'])-1
    if args.order_max: seed=canonical_seed(seed,n)
    assert validate(pack,case,seed['gates'],seed['outputs'])
    args.output.mkdir(parents=True,exist_ok=True)
    (args.output/'seed.json').write_text(json.dumps(seed))
    selected,outs,nvars,nclauses=emit(args.output/'initial.cnf',data,seed,
                                    order_max=args.order_max)
    solver=Solver(5789+args.pads)
    for op,sa,sb in selected:
        for lit in [op]+sa+sb: solver.freeze(lit)
    for out in outs:
        for lit in out: solver.freeze(lit)
    with (args.output/'initial.cnf').open() as source:
        for line in source:
            if not line.startswith('p'):
                solver.add(*[int(word) for word in line.split()[:-1]])
    journal=(args.output/'cost-clauses.txt').open('w')
    cnf=LiveCNF(solver,nvars,nclauses,journal)
    active=[]
    for (_,sa,sb),(_,a,b) in zip(selected,seed['gates']):
        copy=cnf.var(a==b)
        solver.freeze(copy)
        for left,right in zip(sa,sb):
            cnf.clause(-left,-right,copy)
            cnf.clause(-copy,-left,right)
        active.append((-copy,a!=b))
    row=thresholds(cnf,active,maximum)
    for lit in row: solver.freeze(lit)
    journal.flush()
    stamp('START',case['name'],'slots',len(seed['gates']),'cost',maximum,
          'target',case['max_gates'],'vars',cnf.variables,'clauses',cnf.clauses)
    bound=maximum
    while bound>=case['max_gates']:
        result=0
        for attempt in range(args.attempts):
            solver.lib.ccadical_assume(solver.ptr,-row[bound+1])
            result=solver.solve(args.seconds)
            stamp('COST',bound,'ATTEMPT',attempt,'SOLVER',result)
            if result!=0: break
        if result!=10: break
        answer=model(solver,selected)
        outputs=[]
        for out in outs:
            choices=[i for i,lit in enumerate(out) if solver.truth(lit)]
            assert len(choices)==1
            outputs.append(choices[0])
        actual=sum(a!=b for _,a,b in answer)
        assert actual<=bound
        assert validate(pack,case,answer,outputs)
        reduced,reduced_outputs=compact(answer,outputs,n)
        assert len(reduced)<=actual
        assert validate(pack,case,reduced,reduced_outputs)
        residual,residual_output=cone(reduced,reduced_outputs[0],n)
        witness={'gates':reduced,'outputs':reduced_outputs,'case':case['name'],
                 'tap_input_indices':case['tap_input_indices'],'tap_is_correct':True,
                 'outside_original_point':case['outside_original_point'],
                 'input_original':pack['input_original'],
                 'target_met':len(reduced)<=case['max_gates'],
                 'full_graph_gate_count':len(reduced)+case.get('completion_additional_gates',36-len(case['tap_input_indices'])),
                 'residual_gates':residual,'residual_output':residual_output}
        (args.output/f'exact-size-{len(reduced)}.json').write_text(json.dumps(witness))
        stamp('EXACT BOTH OUTPUTS','joint-size',len(reduced),'H-size',len(residual),
              'ANDs',sum(op==0 for op,_,_ in reduced))
        if len(residual)<=case.get('residual_target_gates',28):
            (args.output/'EXACT-CORE-WITNESS.json').write_text(json.dumps(witness))
            stamp('TARGET CORE WITNESS',len(residual))
            break
        if len(reduced)<=case['max_gates']:
            (args.output/'EXACT-CORE-TAP.json').write_text(json.dumps(witness))
            stamp('TARGET CORE TAP',len(reduced))
            break
        bound=min(bound-1,len(reduced)-1)
    journal.close()
    solver.close()


if __name__=='__main__':
    main()
