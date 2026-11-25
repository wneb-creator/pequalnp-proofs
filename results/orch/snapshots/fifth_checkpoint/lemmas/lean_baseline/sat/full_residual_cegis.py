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



def and_depths(gates,n):
    has_and=[False]*n
    has_nested=[False]*n
    for op,a,b in gates:
        proper=op==0 and a!=b
        parents=has_and[a] or has_and[b]
        has_and.append(proper or parents)
        has_nested.append(has_nested[a] or has_nested[b] or (proper and parents))
    return has_and,has_nested


def require_assembled_nested(cnf,selected,outs,active_ands,seed,n):
    hint_d,hint_e=and_depths(seed['gates'],n)
    d=[-1]*n
    e=[-1]*n
    def select(selectors,wires,hint):
        z=cnf.var(hint)
        for literal,value in zip(selectors,wires):
            cnf.clause(-literal,-z,value)
            cnf.clause(-literal,z,-value)
        return z
    for i,((_,sa,sb),(proper,hint_proper),(_,a,b)) in enumerate(
            zip(selected,active_ands,seed['gates'])):
        da=select(sa,d,hint_d[a])
        db=select(sb,d,hint_d[b])
        ea=select(sa,e,hint_e[a])
        eb=select(sb,e,hint_e[b])
        parents=cnf.ao_gate(1,da,db,hint_d[a] or hint_d[b])
        nested=cnf.ao_gate(-1,proper,parents,hint_proper and (hint_d[a] or hint_d[b]))
        earlier=cnf.ao_gate(1,ea,eb,hint_e[a] or hint_e[b])
        d.append(cnf.ao_gate(1,proper,parents,hint_d[n+i]))
        e.append(cnf.ao_gate(1,nested,earlier,hint_e[n+i]))
    nested_h=select(outs[0],e,hint_e[seed['outputs'][0]])
    and_tap=select(outs[1],d,hint_d[seed['outputs'][1]])
    cnf.clause(nested_h,and_tap)


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
    parser.add_argument('--require-nonstar-and',action='store_true')
    parser.add_argument('--require-assembled-nested-and',action='store_true')
    parser.add_argument('--forbid-raw-absorption',action='store_true')
    parser.add_argument('--minimum-noncopy-ands',type=int,default=0)
    parser.add_argument('--exact-noncopy-ands',type=int)
    parser.add_argument('--attempts',type=int,default=1)
    args=parser.parse_args()
    if args.exact_noncopy_ands is not None:
        assert args.exact_noncopy_ands>0
        assert args.exact_noncopy_ands>=args.minimum_noncopy_ands
        args.minimum_noncopy_ands=args.exact_noncopy_ands
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
    masks.add(sum(1<<i for i in right)&~qmask)
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
    (args.output/'seed.json').write_text(json.dumps(seed))
    (args.output/'run.json').write_text(json.dumps({
        key:str(value) if isinstance(value,Path) else value
        for key,value in vars(args).items()}))
    data={'inputs':n,'tests':samples}
    sample_wires={} if args.require_nonstar_and or args.forbid_raw_absorption else None
    selected,outs,nvars,nclauses=emit(args.output/'initial.cnf',data,seed,order_max=args.order_max,
                                    sample_wires=sample_wires)
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
    if args.forbid_raw_absorption:
        assert all(1<<v in sample_wires for v in range(n))
        for i,(_,sa,sb) in enumerate(selected):
            for vertex in range(n):
                for source in range(n,n+i):
                    cnf.clause(-sa[vertex],-sb[source],-sample_wires[1<<vertex][source])
    if args.require_nonstar_and:
        positives=[(1<<a)|(1<<b) for a,b in pack['edges']]
        assert all(mask in sample_wires for mask in positives)
        hints={mask:evaluate_wires(seed['gates'],mask,n) for mask in positives}
        witnesses=[]
        for i,((op,sa,sb),(hint_op,a,b)) in enumerate(zip(selected,seed['gates'])):
            common=(1<<n)-1
            for mask in positives:
                if hints[mask][n+i]: common&=mask
            witness=cnf.var(hint_op==0 and a!=b and common==0)
            witnesses.append(witness)
            cnf.clause(-witness,-op)
            for left,right in zip(sa,sb): cnf.clause(-witness,-left,-right)
            for vertex in range(n):
                cnf.clause(-witness,*[sample_wires[mask][n+i]
                                     for mask in positives if not (mask>>vertex&1)])
        cnf.clause(*witnesses)
    active=[]
    active_ands=[]
    for (op,sa,sb),(hint_op,a,b) in zip(selected,seed['gates']):
        copy=cnf.var(a==b)
        solver.freeze(copy)
        for x,y in zip(sa,sb):
            cnf.clause(-x,-y,copy)
            cnf.clause(-copy,-x,y)
        active.append((-copy,a!=b))
        if args.minimum_noncopy_ands or args.require_assembled_nested_and:
            conjunction=cnf.var(hint_op==0 and a!=b)
            cnf.clause(-conjunction,-op)
            cnf.clause(-conjunction,-copy)
            cnf.clause(op,copy,conjunction)
            active_ands.append((conjunction,hint_op==0 and a!=b))
    if args.require_assembled_nested_and:
        require_assembled_nested(cnf,selected,outs,active_ands,seed,n)
    if args.minimum_noncopy_ands:
        assert 0<args.minimum_noncopy_ands<=len(seed['gates'])
        and_row=thresholds(cnf,active_ands,args.minimum_noncopy_ands)
        cnf.clause(and_row[args.minimum_noncopy_ands])
        if args.exact_noncopy_ands is not None:
            cnf.clause(-and_row[args.exact_noncopy_ands+1])
    row=thresholds(cnf,active,maximum)
    for lit in row: solver.freeze(lit)
    journal.flush()
    stamp('START',case['name'],'samples',len(samples),'full-care',len(full),
          'slots',len(seed['gates']),'cost',maximum,'target',case['max_gates'],
          'minimum-noncopy-ands',args.minimum_noncopy_ands,
          'exact-noncopy-ands',args.exact_noncopy_ands,
          'require-nonstar-and',args.require_nonstar_and,
          'require-assembled-nested-and',args.require_assembled_nested_and,
          'forbid-raw-absorption',args.forbid_raw_absorption,
          'variables',cnf.variables,'clauses',cnf.clauses)
    bound=maximum
    rng=random.Random(5700)
    for round_no in range(args.rounds):
        result=0
        for attempt in range(args.attempts):
            solver.lib.ccadical_assume(solver.ptr,-row[bound+1])
            result=solver.solve(args.seconds)
            stamp('ROUND',round_no,'ATTEMPT',attempt,'COST',bound,'SOLVER',result)
            if result!=0: break
        if result!=10: break
        answer=model(solver,selected)
        outputs=[]
        for out in outs:
            choices=[i for i,lit in enumerate(out) if solver.truth(lit)]
            assert len(choices)==1
            outputs.append(choices[0])
        if args.require_assembled_nested_and:
            has_and,has_nested=and_depths(answer,n)
            assert has_nested[outputs[0]] or has_and[outputs[1]]
        assert sum(a!=b for _,a,b in answer)<=bound
        assert sum(op==0 and a!=b for op,a,b in answer)>=args.minimum_noncopy_ands
        if args.exact_noncopy_ands is not None:
            assert sum(op==0 and a!=b for op,a,b in answer)==args.exact_noncopy_ands
        assert all(op in (0,1) and 0<=a<n+i and 0<=b<n+i
                   for i,(op,a,b) in enumerate(answer))
        if args.forbid_raw_absorption:
            singleton_values={v:evaluate_wires(answer,1<<v,n) for v in range(n)}
            assert all(not singleton_values[a][b] for _,a,b in answer if a<n<=b)
        if args.require_nonstar_and:
            common=[(1<<n)-1]*len(answer)
            for a,b in pack['edges']:
                mask=(1<<a)|(1<<b)
                values=evaluate_wires(answer,mask,n)
                for i in range(len(answer)):
                    if values[n+i]: common[i]&=mask
            assert any(op==0 and a!=b and common[i]==0
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
