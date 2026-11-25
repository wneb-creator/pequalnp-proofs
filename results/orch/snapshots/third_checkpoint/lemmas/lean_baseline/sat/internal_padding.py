import argparse
import itertools
import json
from pathlib import Path

from resynthesize import evaluate
from subset_search import validate_basis


def padded(gates, ninputs, locations):
    mapping = {i:i for i in range(ninputs)}
    answer = []
    for wire in range(ninputs):
        for _ in range(locations.count(wire)):
            answer.append([0,mapping[wire],mapping[wire]])
            mapping[wire] = ninputs+len(answer)-1
    for i,(op,a,b) in enumerate(gates):
        answer.append([op,*sorted((mapping[a],mapping[b]))])
        wire = ninputs+i
        mapping[wire] = ninputs+len(answer)-1
        for _ in range(locations.count(wire)):
            answer.append([0,mapping[wire],mapping[wire]])
            mapping[wire] = ninputs+len(answer)-1
    assert mapping[ninputs+len(gates)-1] == ninputs+len(answer)-1
    return answer


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('problem',type=Path)
    parser.add_argument('seeds',type=Path)
    parser.add_argument('output',type=Path)
    parser.add_argument('--index',type=int,default=15)
    args=parser.parse_args()
    data=json.loads(args.problem.read_text())
    seed=json.loads(args.seeds.read_text())[args.index]
    tests=validate_basis(data)
    n=data['inputs']
    count=data['max_gates']-len(seed['gates'])
    assert count==2
    places=[(wire,wire) for wire in range(n+len(seed['gates']))]
    places += list(itertools.combinations([17,18,19,26,27,30,31,34,35,38,39,40,41],2))
    result=[]
    for location in places:
        gates=padded(seed['gates'],n,location)
        assert len(gates)==data['max_gates']
        assert all(op in (0,1) and 0<=a<n+i and 0<=b<n+i
                   for i,(op,a,b) in enumerate(gates))
        assert all(evaluate(gates,mask,n)[-1]==evaluate(seed['gates'],mask,n)[-1]
                   for mask,_ in tests)
        result.append({'group':seed['group'],'padding':location,'gates':gates,
                       'output':n+len(gates)-1,'size':len(gates),
                       'positive_errors':seed['positive_errors'],
                       'negative_errors':seed['negative_errors']})
    args.output.write_text(json.dumps(result))
    print('EQUIVALENT INTERNAL PADDING SEEDS',len(result),flush=True)


if __name__=='__main__':
    main()
