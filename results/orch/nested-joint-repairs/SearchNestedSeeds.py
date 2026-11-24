"""Generate explicitly INVALID positive-complete nested dirty Alternative6 seeds."""
import argparse
import itertools
import json
from pathlib import Path
import SearchAlternative6PairProblem as problem
from SearchPhysicalRepairPairs import evaluate, scalar_artifact


def generate(a, b):
    neighbors={i:sorted(v for u,v in problem.EDGES if u==i) for i in range(6)}
    gates=[]
    def gate(operation,u,v):
        gates.append([operation,sorted([u,v])])
        return problem.N+len(gates)-1
    def ors(wires):
        wires=list(wires)
        result=wires[0]
        for wire in wires[1:]:
            result=gate('or',result,wire)
        return result
    shared=gate('or',a,b)
    h0=gate('and',shared,ors(neighbors[a]))
    h1=gate('and',shared,ors(neighbors[b]))
    top0=gate('and',a,h0)
    top1=gate('and',b,h1)
    rest=[i for i in range(6) if i not in (a,b)]
    right=sorted(set().union(*(set(neighbors[i]) for i in rest)))
    dirty=gate('and',ors(rest),ors(right))
    output=ors([top0,top1,dirty])
    original_size=len(gates)
    assert original_size==32-(16-len(right)) and original_size in (26,27)
    while len(gates)<28:
        operation,(u,v)=gates[-1]
        output=gate(operation,output,u)
    state=tuple((operation,tuple(pair)) for operation,pair in gates)
    ev=evaluate(problem,state)
    assert ev[0]==0 and ev[1]>0 and output==problem.N+27
    singles=[1<<i for i in range(problem.N)]
    for operation,(u,v) in gates:
        singles.append(singles[u]&singles[v] if operation=='and' else singles[u]|singles[v])
    assert singles[output]==0
    artifact=scalar_artifact(problem,state,'INVALID nested-dirty positive-complete repair seed')
    artifact.update({'selected_clean_points':[a,b],'merged_points':rest,
                     'original_size':original_size,'augmented_negative_errors':ev[1]})
    return artifact


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--output-dir',type=Path,required=True)
    args=parser.parse_args()
    args.output_dir.mkdir(parents=True,exist_ok=True)
    for a,b in itertools.combinations(range(6),2):
        artifact=generate(a,b)
        name='points-'+str(a)+'-'+str(b)+'.json'
        (args.output_dir/name).write_text(json.dumps(artifact,indent=2)+'\n')
        print(json.dumps({'file':name,'size':artifact['size'],'original_size':artifact['original_size'],
                          'raw_errors':artifact['wrong_raw_tests'],
                          'augmented_errors':artifact['augmented_negative_errors'],
                          'singleton_errors':0}),flush=True)
    print('PASS15nested seeds, complete88scalar verification each')


if __name__=='__main__':
    main()
