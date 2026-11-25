import argparse
import itertools
import json
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'lower_bound' / 'sat'))
from global_synthesis import CNF, evaluate_wires
from incremental_cegis import Solver, model


def stamp(*items):
    print(datetime.now(timezone.utc).isoformat(), *items, flush=True)


def partitions(items):
    if not items:
        yield []
        return
    first,*rest=items
    for tail in partitions(rest):
        yield [[first]]+tail
        for i in range(len(tail)):
            yield tail[:i]+[[first]+tail[i]]+tail[i+1:]


def make_seed(data, blocks, taps_first=False):
    n=data['inputs']
    gates=[]
    cache={}
    def add(op,a,b):
        key=(op,*sorted((a,b)))
        if key not in cache:
            gates.append(list(key))
            cache[key]=n+len(gates)-1
        return cache[key]
    def join(wires):
        answer=wires[0]
        for wire in wires[1:]: answer=add(1,answer,wire)
        return answer
    if taps_first:
        a=join([0,1,2])
        b=join([3,4,5])
    stars=[]
    for block in blocks:
        neighbors=sorted({v for u,v in data['edges'] if u in block})
        stars.append(add(0,join(block),join(neighbors)))
    h=join(stars)
    if not taps_first:
        a=join([0,1,2])
        b=join([3,4,5])
    return {'blocks':blocks,'gates':gates,'outputs':[h,a,b],
            'taps_first':taps_first}


def pad_seed(seed,n,count):
    gates=[[op,*sorted((a,b))] for op,a,b in seed['gates']]
    outputs=seed['outputs'].copy()
    while len(gates)<count:
        side=(len(gates)-len(seed['gates']))%3
        gates.append([0,outputs[side],outputs[side]])
        outputs[side]=n+len(gates)-1
    assert len(gates)==count
    return {'gates':gates,'outputs':outputs,'blocks':seed.get('blocks'),
            'taps_first':seed.get('taps_first')}


def canonical_seed(seed,ninputs):
    mapping={i:i for i in range(ninputs)}
    remaining=set(range(len(seed['gates'])))
    answer=[]
    while remaining:
        choices=[]
        for i in remaining:
            op,a,b=seed['gates'][i]
            if a in mapping and b in mapping:
                a,b=sorted((mapping[a],mapping[b]))
                choices.append((b,a,op,i))
        assert choices
        b,a,op,i=min(choices)
        remaining.remove(i)
        mapping[ninputs+i]=ninputs+len(answer)
        answer.append([op,a,b])
    return dict(seed,gates=answer,outputs=[mapping[o] for o in seed['outputs']])


def emit(path,data,seed,and_count=None,soft_outputs=(),order_max=False):
    n=data['inputs']
    gates=seed['gates']
    cnf=CNF(path)
    selected=[]
    bprefixes=[]
    for i,(hint_op,hint_a,hint_b) in enumerate(gates):
        op=cnf.var(bool(hint_op))
        sa=[cnf.var(j==hint_a) for j in range(n+i)]
        sb=[cnf.var(j==hint_b) for j in range(n+i)]
        prefix=cnf.exactly_one(sa,hint_a)
        bprefixes.append(cnf.exactly_one(sb,hint_b))
        for j in range(len(sb)-1): cnf.clause(-sb[j],prefix[j])
        selected.append((op,sa,sb))
    if order_max:
        for i in range(1,len(gates)):
            for j in range(1,len(selected[i-1][2])):
                cnf.clause(-selected[i-1][2][j],-bprefixes[i][j-1])
    if and_count is not None:
        row=[1]+[-1]*(and_count+1)
        hint_count=0
        for (op,_,_),gate in zip(selected,gates):
            hint_count += gate[0]==0
            next_row=[1]
            for j in range(1,and_count+2):
                old,previous=row[j],row[j-1]
                z=cnf.var(hint_count>=j)
                cnf.clause(-old,z)
                cnf.clause(-previous,op,z)
                cnf.clause(old,previous,-z)
                cnf.clause(old,-op,-z)
                next_row.append(z)
            row=next_row
        cnf.clause(row[and_count])
        cnf.clause(-row[and_count+1])
    outputs=[]
    for hint in seed['outputs']:
        selectors=[cnf.var(j==hint) for j in range(n+len(gates))]
        cnf.exactly_one(selectors,hint)
        outputs.append(selectors)
    for wire in range(n+len(gates)):
        uses=[side[wire] for i,(_,sa,sb) in enumerate(selected) if wire<n+i
              for side in (sa,sb)]
        uses += [out[wire] for out in outputs]
        cnf.clause(*uses)
    soft_errors=[]
    for case in data['tests']:
        mask,targets=case['mask'],case['targets']
        hints=evaluate_wires(gates,mask,n)
        wires=[1 if mask>>j&1 else -1 for j in range(n)]
        for i,(op,sa,sb) in enumerate(selected):
            a=cnf.var(hints[gates[i][1]])
            b=cnf.var(hints[gates[i][2]])
            for selectors,z in ((sa,a),(sb,b)):
                for wire,literal in enumerate(selectors):
                    cnf.clause(-literal,-z,wires[wire])
                    cnf.clause(-literal,z,-wires[wire])
            wires.append(cnf.ao_gate(op,a,b,hints[n+i]))
        for side,(label,selectors) in enumerate(zip(targets,outputs)):
            if label<0: continue
            if side in soft_outputs:
                hint=hints[seed['outputs'][side]]!=bool(label)
                error=cnf.var(hint)
                soft_errors.append((error,hint))
                for wire,literal in enumerate(selectors):
                    correct=wires[wire] if label else -wires[wire]
                    cnf.clause(-literal,error,correct)
                    cnf.clause(-literal,-error,-correct)
                continue
            for wire,literal in enumerate(selectors):
                cnf.clause(-literal,wires[wire] if label else -wires[wire])
    cnf.finish()
    result=(selected,outputs,cnf.variables,cnf.clauses)
    return result+(soft_errors,) if soft_outputs else result


def validate(data,gates,outputs):
    n=data['inputs']
    assert all(op in (0,1) and 0<=a<n+i and 0<=b<n+i
               for i,(op,a,b) in enumerate(gates))
    assert len(outputs)==3 and all(0<=o<n+len(gates) for o in outputs)
    for mask in range(1<<n):
        wires=evaluate_wires(gates,mask,n)
        h=any(mask>>u&1 and mask>>v&1 for u,v in data['edges'])
        if wires[outputs[0]]!=h: return False
        if not h:
            if wires[outputs[1]]!=bool(mask&7): return False
            if wires[outputs[2]]!=bool(mask&56): return False
    return True


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('problem',type=Path)
    parser.add_argument('output',type=Path)
    parser.add_argument('--gates',type=int,default=26)
    parser.add_argument('--seconds',type=int,default=120)
    parser.add_argument('--count',type=int,default=8)
    parser.add_argument('--offset',type=int,default=0)
    parser.add_argument('--and-count',type=int)
    parser.add_argument('--calibrate',action='store_true')
    args=parser.parse_args()
    data=json.loads(args.problem.read_text())
    args.output.mkdir(parents=True,exist_ok=True)
    seeds=[make_seed(data,blocks,early) for blocks in partitions(list(range(6)))
           for early in (True,False)]
    seeds=[s for s in seeds if len(s['gates'])<=args.gates]
    seeds.sort(key=lambda s:(len(s['gates']),s['blocks']))
    representatives={}
    for seed in seeds:
        shape=sorted((sum(x<3 for x in block),sum(x>=3 for x in block))
                     for block in seed['blocks'])
        shape=min(tuple(shape),tuple(sorted((b,a) for a,b in shape)))
        representatives.setdefault((shape,seed['taps_first']),seed)
    seeds=list(representatives.values())
    for seed in seeds:
        seed['basis_errors']=sum(
            evaluate_wires(seed['gates'],case['mask'],data['inputs'])[out]!=bool(target)
            for case in data['tests'] for out,target in zip(seed['outputs'],case['targets'])
            if target>=0)
    seeds.sort(key=lambda s:(s['basis_errors'],len(s['gates']),s['blocks']))
    if args.calibrate:
        seeds=[data['baseline']]
        assert args.gates==len(seeds[0]['gates'])
    for index in range(args.offset,min(len(seeds),args.offset+args.count)):
        original=seeds[index]
        seed=pad_seed(original,data['inputs'],args.gates)
        folder=args.output/f'seed-{index}'
        folder.mkdir(exist_ok=True)
        (folder/'seed.json').write_text(json.dumps(seed))
        selected,outputs,nvars,nclauses=emit(folder/'initial.cnf',data,seed,args.and_count)
        solver=Solver(5700+index)
        for op,sa,sb in selected:
            for lit in [op]+sa+sb: solver.freeze(lit)
        for out in outputs:
            for lit in out: solver.freeze(lit)
        with (folder/'initial.cnf').open() as source:
            for line in source:
                if not line.startswith('p'):
                    solver.add(*[int(word) for word in line.split()[:-1]])
        stamp('SEED',index,seed.get('blocks'),'gates',args.gates,'vars',nvars,'clauses',nclauses)
        begin=time.monotonic()
        result=solver.solve(args.seconds)
        stamp('SOLVER',result,'seconds',round(time.monotonic()-begin,3))
        if result==10:
            answer=model(solver,selected)
            if args.and_count is not None:
                assert sum(op==0 for op,_,_ in answer)==args.and_count
            answer_outputs=[]
            for out in outputs:
                chosen=[i for i,lit in enumerate(out) if solver.truth(lit)]
                assert len(chosen)==1
                answer_outputs.append(chosen[0])
            assert len(answer)<=args.gates
            assert validate(data,answer,answer_outputs)
            result={'gates':answer,'outputs':answer_outputs,'calibration':args.calibrate,
                    'full_core_gate_count':len(answer)+data['completion_gate_cost']}
            name='BASELINE-WITNESS.json' if args.calibrate else 'EXACT-GRID-TAPS.json'
            (folder/name).write_text(json.dumps(result))
            stamp('VALIDATED GRID TAPS',len(answer),'gates','full-core',result['full_core_gate_count'])
            solver.close()
            return
        solver.close()


if __name__=='__main__':
    main()
