import argparse
import json
import random
from pathlib import Path
from resynthesize import evaluate
from subset_search import validate_basis


def cleanup(gates, output, n):
    used = {output}
    for i in reversed(range(len(gates))):
        if n+i in used:
            used.update(gates[i][1:])
    mapping = {i:i for i in range(n)}
    answer = []
    for i, (op,a,b) in enumerate(gates):
        if n+i in used:
            mapping[n+i] = n+len(answer)
            answer.append([op,mapping[a],mapping[b]])
    return answer, mapping[output]


def prune(gates, tests, n, rng):
    gates, output = cleanup(gates, n+len(gates)-1,n)
    pos = sum(1<<i for i,(_,label) in enumerate(tests) if label)
    neg = ((1<<len(tests))-1)^pos
    while True:
        values = [sum(1<<t for t,(mask,_) in enumerate(tests) if mask>>i&1) for i in range(n)]
        for op,a,b in gates:
            values.append((values[a]|values[b]) if op else (values[a]&values[b]))
        choices = []
        for i in range(len(gates)):
            v=values[n+i]
            for j in range(n+i):
                u=values[j]
                if v&pos&~u == 0 and u&neg&~v == 0:
                    choices.append((i,j))
        if not choices:
            return cleanup(gates,output,n)
        i,j = rng.choice(choices)
        oldwire=n+i
        def shift(w):
            return j if w==oldwire else w-1 if w>oldwire else w
        gates = [[op,shift(a),shift(b)] for k,(op,a,b) in enumerate(gates) if k!=i]
        output=shift(output)
        gates,output=cleanup(gates,output,n)


def complete(gates, output, data):
    n=data['inputs'];k=len(data['original_rows'])
    missing=[(a,b) for a,b in data['edges'] if not evaluate(gates,1<<a|1<<b,n)[output]]
    best=None
    for owners in range(1<<k):
        points={u for u in range(k) if owners>>u&1}
        lines={b for a,b in missing if a not in points}
        relevant_points={a for a,b in missing if a in points}
        cover=relevant_points|lines
        if best is None or len(cover)<len(best):best=cover
    blocks={u:[] for u in best}
    for a,b in missing:
        if a in best:blocks[a].append(b)
        else:blocks[b].append(a)
    result=[list(g) for g in gates]
    for u,neighbors in sorted(blocks.items()):
        w=neighbors[0]
        for v in neighbors[1:]:
            result.append([1,w,v]);w=n+len(result)-1
        result.append([0,u,w]);w=n+len(result)-1
        result.append([1,output,w]);output=n+len(result)-1
    return result,output,len(missing),len(best)


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('case',type=Path)
    parser.add_argument('pool',type=Path)
    parser.add_argument('output',type=Path)
    parser.add_argument('--rounds',type=int,default=100)
    args=parser.parse_args()
    data=json.loads(args.case.read_text());tests=validate_basis(data)
    pool=json.loads(args.pool.read_text());rng=random.Random(65057)
    args.output.mkdir(exist_ok=True,parents=True)
    record=1000
    for index,item in enumerate(pool):
        gs=item['gates']
        for trial in range(args.rounds):
            pruned,out=prune(gs,tests,data['inputs'],rng)
            if any(evaluate(pruned,m,data['inputs'])[out] and not y for m,y in tests):continue
            result,output,missing,cover=complete(pruned,out,data)
            assert all(evaluate(result,m,data['inputs'])[output]==bool(y) for m,y in tests)
            if len(result)<record:
                record=len(result)
                print('BEST',record,'entry',index,'trial',trial,'pruned',len(pruned),'missing',missing,'cover',cover,flush=True)
                (args.output/'best.json').write_text(json.dumps({'gates':result,'output':output,'input_original':data['input_original'],'original_rows':data['original_rows']}))
            if len(result)<=data['max_gates']:
                assert all(evaluate(result,m,data['inputs'])[output]==any(m>>a&1 and m>>b&1 for a,b in data['edges']) for m in range(1<<data['inputs']))
                (args.output/'FULL-SUBSET-WITNESS.json').write_text(json.dumps({'gates':result,'output':output,'input_original':data['input_original'],'original_rows':data['original_rows']}))
                print('FULL SUBSET WITNESS',flush=True)
                return
    print('FINISHED best',record,flush=True)


if __name__=='__main__':main()
