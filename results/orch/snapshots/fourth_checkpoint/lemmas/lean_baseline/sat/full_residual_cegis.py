import argparse
import json
import random
from pathlib import Path

from core_tap_synthesis import validate, truth_columns
from core_tap_cost import compact, thresholds
from core_tap_maxsat import cone
from grid_taps_synthesis import emit, stamp, Solver, model, canonical_seed, evaluate_wires
from incremental_cegis import LiveCNF


def add_sample(cnf,selected,outs,n,case,hint):
    mask,targets=case['mask'],case['targets']
    values=evaluate_wires(hint,mask,n)
    wires=[1 if mask>>i&1 else -1 for i in range(n)]
    for i,(op,sa,sb) in enumerate(selected):
        a=cnf.var(values[hint[i][1]])
        b=cnf.var(values[hint[i][2]])
        for selectors,z in ((sa,a),(sb,b)):
            for wire,literal in enumerate(selectors):
                cnf.clause(-literal,-z,wires[wire])
                cnf.clause(-literal,z,-wires[wire])
        wires.append(cnf.ao_gate(op,a,b,values[n+i]))
    for target,selectors in zip(targets,outs):
        if target<0: continue
        for wire,literal in enumerate(selectors):
            cnf.clause(-literal,wires[wire] if target else -wires[wire])
    cnf.journal.flush()


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('problem',type=Path)
    parser.add_argument('output',type=Path)
    parser.add_argument('--case',default='full_point0_residual_tap')
    parser.add_argument('--seconds',type=int,default=120)
    parser.add_argument('--rounds',type=int,default=50)
    parser.add_argument('--pads',type=int,default=2)
    parser.add_argument('--add',type=int,default=8)
    parser.add_argument('--order-max',action='store_true')
    parser.add_argument('--start',type=Path)
    parser.add_argument('--pad-after',type=int,nargs='+')
    parser.add_argument('--pair-tests',action='store_true')
    args=parser.parse_args()
    pack=json.loads(args.problem.read_text())
    case=next(c for c in pack['cases'] if c['name']==args.case)
    n=case['inputs']
    qmask=sum(1<<i for i in case['tap_input_indices'])
    def labelled(mask):
        hit=any(mask>>a&1 and mask>>b&1 for a,b in pack['edges'])
        return {'mask':mask,'targets':[int(hit),-1 if hit else int(bool(mask&qmask))]}
    full=[labelled(c['input']) for c in case['constraints']]
    assert all(t['targets']==[int(c['residual']),-1 if c['tap'] is None else int(c['tap'])]
               for t,c in zip(full,case['constraints']))
    left={a for a,b in pack['edges']}
    right={b for a,b in pack['edges']}
    masks={0}|{1<<i for i in range(n)}|{1<<a|1<<b for a,b in pack['edges']}
    masks|={sum(1<<i for i in left),sum(1<<i for i in right)}
    if args.pair_tests:
        masks|={1<<a|1<<b for a in left for b in right}
    samples=[labelled(mask) for mask in sorted(masks)]
    original=case['seed']
    source=json.loads(args.start.read_text()) if args.start else {
        'gates':original['gates'],
        'outputs':[original['residual_output'],original['tap_output']]}
    seed={'gates':[[op,*sorted((a,b))] for op,a,b in source['gates']],
          'outputs':source['outputs'].copy()}
    maximum=case['max_gates'] if args.start else len(seed['gates'])
    slots=max(len(seed['gates']),len(original['gates']))+args.pads
    if args.pad_after:
        assert len(args.pad_after)==slots-len(seed['gates'])
        assert all(0<=i<len(seed['gates']) for i in args.pad_after)
        mapped={i:i for i in range(n)}
        new=[]
        for i,(op,a,b) in enumerate(seed['gates']):
            new.append([op,mapped[a],mapped[b]])
            mapped[n+i]=n+len(new)-1
            for _ in range(args.pad_after.count(i)):
                wire=mapped[n+i]
                new.append([0,wire,wire])
                mapped[n+i]=n+len(new)-1
        seed={'gates':new,'outputs':[mapped[o] for o in seed['outputs']]}
    else:
        for i in range(slots-len(seed['gates'])):
            side=i%2
            output=seed['outputs'][side]
            seed['gates'].append([0,output,output])
            seed['outputs'][side]=n+len(seed['gates'])-1
    if args.order_max: seed=canonical_seed(seed,n)
    if not args.start:
        assert validate(pack,case,seed['gates'],seed['outputs'])
    assert all(op in (0,1) and 0<=a<n+i and 0<=b<n+i
               for i,(op,a,b) in enumerate(seed['gates']))
    for test in samples:
        values=evaluate_wires(seed['gates'],test['mask'],n)
        assert all(target<0 or values[output]==bool(target)
                   for output,target in zip(seed['outputs'],test['targets']))
    args.output.mkdir(parents=True,exist_ok=True)
    data={'inputs':n,'tests':samples}
    selected,outs,nvars,nclauses=emit(args.output/'initial.cnf',data,seed,order_max=args.order_max)
    solver=Solver(5791)
    for op,sa,sb in selected:
        for lit in [op]+sa+sb: solver.freeze(lit)
    for out in outs:
        for lit in out: solver.freeze(lit)
    with (args.output/'initial.cnf').open() as source:
        for line in source:
            if not line.startswith('p'):
                solver.add(*[int(word) for word in line.split()[:-1]])
    journal=(args.output/'added-clauses.txt').open('w')
    cnf=LiveCNF(solver,nvars,nclauses,journal)
    active=[]
    for (_,sa,sb),(_,a,b) in zip(selected,seed['gates']):
        copy=cnf.var(a==b)
        solver.freeze(copy)
        for x,y in zip(sa,sb):
            cnf.clause(-x,-y,copy)
            cnf.clause(-copy,-x,y)
        active.append((-copy,a!=b))
    row=thresholds(cnf,active,maximum)
    for lit in row: solver.freeze(lit)
    journal.flush()
    stamp('START',case['name'],'samples',len(samples),'full-care',len(full),
          'slots',len(seed['gates']),'cost',maximum,'target',case['max_gates'],
          'variables',cnf.variables,'clauses',cnf.clauses)
    bound=maximum
    rng=random.Random(5700)
    for round_no in range(args.rounds):
        solver.lib.ccadical_assume(solver.ptr,-row[bound+1])
        result=solver.solve(args.seconds)
        stamp('ROUND',round_no,'COST',bound,'SOLVER',result)
        if result!=10: break
        answer=model(solver,selected)
        outputs=[]
        for out in outs:
            choices=[i for i,lit in enumerate(out) if solver.truth(lit)]
            assert len(choices)==1
            outputs.append(choices[0])
        assert sum(a!=b for _,a,b in answer)<=bound
        assert all(op in (0,1) and 0<=a<n+i and 0<=b<n+i
                   for i,(op,a,b) in enumerate(answer))
        def wrong_at(test):
            wires=evaluate_wires(answer,test['mask'],n)
            return [side for side,(out,target) in enumerate(zip(outputs,test['targets']))
                    if target>=0 and wires[out]!=bool(target)]
        assert not any(wrong_at(test) for test in samples)
        failures=[(test,wrong_at(test)) for test in full if wrong_at(test)]
        reduced,reduced_outputs=compact(answer,outputs,n)
        residual,residual_output=cone(reduced,reduced_outputs[0],n)
        h_errors=sum(0 in sides for _,sides in failures)
        tap_errors=sum(1 in sides for _,sides in failures)
        witness={'gates':reduced,'outputs':reduced_outputs,'case':case['name'],
                 'tap_input_indices':case['tap_input_indices'],
                 'outside_original_point':case['outside_original_point'],
                 'input_original':pack['input_original'],'full_care_verified':not failures,
                 'residual_errors':h_errors,'tap_errors':tap_errors,
                 'target_met':not failures and len(reduced)<=case['max_gates'],
                 'full_graph_gate_count':len(reduced)+case.get('completion_additional_gates',36-len(case['tap_input_indices'])),
                 'residual_gates':residual,'residual_output':residual_output}
        (args.output/f'candidate-{round_no}.json').write_text(json.dumps(witness))
        stamp('CANDIDATE','joint-size',len(reduced),'H-size',len(residual),
              'H-errors',h_errors,'tap-errors',tap_errors)
        if not h_errors and len(residual)<=case.get('residual_target_gates',28):
            wires=truth_columns(n)
            expected=0
            for a,b in pack['edges']: expected|=wires[a]&wires[b]
            for op,a,b in residual: wires.append((wires[a]|wires[b]) if op else (wires[a]&wires[b]))
            assert wires[residual_output]==expected
            (args.output/'EXACT-RESIDUAL-WITNESS.json').write_text(json.dumps(witness))
            stamp('TARGET RESIDUAL WITNESS',len(residual))
            break
        if not failures:
            assert validate(pack,case,answer,outputs)
            assert validate(pack,case,reduced,reduced_outputs)
            if len(reduced)<=case['max_gates']:
                (args.output/'EXACT-RESIDUAL-TAP.json').write_text(json.dumps(witness))
                stamp('TARGET RESIDUAL TAP',len(reduced))
                break
            bound=min(bound-1,len(reduced)-1)
            continue
        counterexamples=set()
        for test,sides in failures:
            side=sides[0]
            assert test['targets'][side]==0
            mask=test['mask']
            order=list(range(n))
            rng.shuffle(order)
            for i in order:
                small=mask&~(1<<i)
                if evaluate_wires(answer,small,n)[outputs[side]]: mask=small
            new=labelled(mask)
            assert new['targets'][side]==0 and wrong_at(new)
            assert mask not in masks
            counterexamples.add(mask)
        chosen=sorted(counterexamples,key=lambda mask:(mask.bit_count(),mask))[:args.add]
        assert chosen
        stamp('ADD',[(mask,mask.bit_count()) for mask in chosen])
        for mask in chosen:
            new=labelled(mask)
            add_sample(cnf,selected,outs,n,new,answer)
            samples.append(new)
            masks.add(mask)
        (args.output/'samples.json').write_text(json.dumps(samples))
    journal.close()
    solver.close()


if __name__=='__main__':
    main()
