import argparse
import json
from pathlib import Path

from grid_taps_synthesis import emit, stamp, Solver, model, evaluate_wires


def validate(pack,case,gates,outputs):
    n=case['inputs']
    assert all(op in (0,1) and 0<=a<n+i and 0<=b<n+i
               for i,(op,a,b) in enumerate(gates))
    assert len(outputs)==2 and all(0<=i<n+len(gates) for i in outputs)
    qmask=sum(1<<i for i in case['tap_input_indices'])
    allones=(1<<(1<<n))-1
    wires=[(allones//((1<<(1<<i))+1))<<(1<<i) for i in range(n)]
    expected=0
    for a,b in pack['edges']: expected |= wires[a]&wires[b]
    expected_tap=0
    for i in case['tap_input_indices']: expected_tap |= wires[i]
    for op,a,b in gates:
        wires.append((wires[a]|wires[b]) if op else (wires[a]&wires[b]))
    return (wires[outputs[0]]==expected and
            ((wires[outputs[1]]^expected_tap)&(allones^expected))==0)


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('problem',type=Path)
    parser.add_argument('output',type=Path)
    parser.add_argument('--case',default='outside9_pair6_11')
    parser.add_argument('--seconds',type=int,default=120)
    parser.add_argument('--count',type=int,default=4)
    parser.add_argument('--offset',type=int,default=0)
    parser.add_argument('--and-count',type=int)
    parser.add_argument('--calibrate',action='store_true')
    args=parser.parse_args()
    pack=json.loads(args.problem.read_text())
    case=next(case for case in pack['cases'] if case['name']==args.case)
    data={'inputs':case['inputs'],'tests':[
        {'mask':c['input'],'targets':[int(c['residual']),-1 if c['tap'] is None else int(c['tap'])]}
        for c in case['constraints']]}
    original=case['seed']
    n=data['inputs']
    base_gates=[[op,*sorted((a,b))] for op,a,b in original['gates'][:-1]]
    assert len(base_gates)==case['max_gates']
    ranked=[]
    for wire in range(n+len(base_gates)):
        errors=sum(evaluate_wires(base_gates,c['input'],n)[wire]!=bool(c['tap'])
                   for c in case['constraints'] if c['tap'] is not None)
        ranked.append((errors,wire))
    ranked.sort()
    seeds=[{'gates':base_gates,'outputs':[original['residual_output'],wire],
            'tap_care_errors':errors} for errors,wire in ranked]
    if args.calibrate:
        seeds=[{'gates':[[op,*sorted((a,b))] for op,a,b in original['gates']],
                'outputs':[original['residual_output'],original['tap_output']],
                'tap_care_errors':0}]
    args.output.mkdir(parents=True,exist_ok=True)
    for index in range(args.offset,min(len(seeds),args.offset+args.count)):
        seed=seeds[index]
        folder=args.output/f'seed-{index}'
        folder.mkdir(exist_ok=True)
        (folder/'seed.json').write_text(json.dumps(seed))
        assert args.calibrate or len(seed['gates'])<=case['max_gates']
        selected,outs,nvars,nclauses=emit(folder/'initial.cnf',data,seed,args.and_count)
        solver=Solver(5700+index)
        for op,sa,sb in selected:
            for lit in [op]+sa+sb: solver.freeze(lit)
        for out in outs:
            for lit in out: solver.freeze(lit)
        with (folder/'initial.cnf').open() as source:
            for line in source:
                if not line.startswith('p'):
                    solver.add(*[int(word) for word in line.split()[:-1]])
        stamp('CASE',case['name'],'SEED',index,'gates',len(seed['gates']),
              'initial-tap-errors',seed['tap_care_errors'],'vars',nvars,'clauses',nclauses)
        result=solver.solve(args.seconds)
        stamp('SOLVER',result)
        if result==10:
            answer=model(solver,selected)
            outputs=[]
            for out in outs:
                choices=[i for i,lit in enumerate(out) if solver.truth(lit)]
                assert len(choices)==1
                outputs.append(choices[0])
            assert args.calibrate or len(answer)<=case['max_gates']
            if args.and_count is not None:
                assert sum(op==0 for op,_,_ in answer)==args.and_count
            assert validate(pack,case,answer,outputs)
            witness={'gates':answer,'outputs':outputs,'case':case['name'],
                     'tap_input_indices':case['tap_input_indices'],
                     'outside_original_point':case['outside_original_point'],
                     'input_original':pack['input_original'],'calibration':args.calibrate,
                     'full_graph_gate_count':len(answer)+36-len(case['tap_input_indices'])}
            name='BASELINE-WITNESS.json' if args.calibrate else 'EXACT-CORE-TAP.json'
            (folder/name).write_text(json.dumps(witness))
            stamp('BASELINE' if args.calibrate else 'TARGET CORE TAP',len(answer),
                  'gates','validated-all-inputs',1<<n)
            solver.close()
            return
        solver.close()


if __name__=='__main__':
    main()
