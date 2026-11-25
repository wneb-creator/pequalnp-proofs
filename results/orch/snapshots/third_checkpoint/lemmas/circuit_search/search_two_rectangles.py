import collections
import itertools
import json
import pathlib
import time

HERE = pathlib.Path(__file__).resolve().parent
case = json.loads((HERE/'subsets/k6_p3.json').read_text())
edges = set(map(tuple, case['edges']))
neighbors = [{l for p,l in edges if p==i} for i in range(6)]
allpairs = [(p,l) for p in range(6) for l in range(6,17)]
number = {e:i for i,e in enumerate(allpairs)}
edge_mask = sum(1<<number[e] for e in edges)
rectangles = []
for k in (2,3):
    for owners in itertools.combinations(range(6),k):
        available = sorted(set().union(*(neighbors[p] for p in owners)))
        for count in range(2,min(7,len(available)+1)):
            for lines in itertools.combinations(available,count):
                mask = sum(1<<number[p,l] for p in owners for l in lines)
                added = mask & ~edge_mask
                if added.bit_count()<=3:
                    rectangles.append((owners,set(lines),mask,added))


def build(r,s):
    terms = [(r[0],r[1]),(s[0],s[1])]
    covered = r[2]|s[2]
    for p in range(6):
        residual={l for l in neighbors[p] if not(covered>>number[p,l]&1)}
        if residual:terms.append(((p,),residual))
    gates=[]
    sets=[ls.copy() for _,ls in terms]
    while True:
        counts=collections.Counter(pair for ls in sets for pair in itertools.combinations(sorted(ls),2))
        if not counts or max(counts.values())<=1:break
        pair=max(counts,key=counts.get);wire=17+len(gates);gates.append([1,*pair])
        pairset=set(pair)
        for ls in sets:
            if pairset<=ls:ls.difference_update(pair);ls.add(wire)
    cache={}
    def gate(op,a,b):
        if a==b:return a
        key=(op,*sorted((a,b)))
        if key not in cache:cache[key]=17+len(gates);gates.append(list(key))
        return cache[key]
    outputs=[]
    for (owners,_),ls in zip(terms,sets):
        owner=owners[0]
        for p in owners[1:]:owner=gate(1,owner,p)
        ordered=sorted(ls);line=ordered[0]
        for l in ordered[1:]:line=gate(1,line,l)
        outputs.append(gate(0,owner,line))
    output=outputs[0]
    for w in outputs[1:]:output=gate(1,output,w)
    return gates


start=time.monotonic();checked=0;best=100;pool=[];seen=set()
for i,r in enumerate(rectangles):
    for s in rectangles[i+1:]:
        if (r[3]|s[3]).bit_count()>3:continue
        if r[2]&~s[2]==0 or s[2]&~r[2]==0:continue
        checked+=1
        gates=build(r,s)
        if len(gates)>28:continue
        graph=r[2]|s[2]|edge_mask
        if graph in seen:continue
        seen.add(graph)
        bad=0
        for x,y in case['tests']:
            values=[x>>j&1 for j in range(17)]
            for op,a,b in gates:values.append(values[a]|values[b] if op else values[a]&values[b])
            assert not y or values[-1]
            bad+=not y and values[-1]
        pool.append(dict(gates=gates,false=bad,added=[e for e in allpairs if graph>>number[e]&1 and e not in edges]))
        if bad<best:
            best=bad
            print('BEST',bad,'size',len(gates),'added',pool[-1]['added'],'seconds',time.monotonic()-start,flush=True)
            (HERE/'k6-two-rectangle-best.json').write_text(json.dumps(gates))
print('DONE','rectangles',len(rectangles),'pairs',checked,'best',best,'pool',len(pool),'seconds',time.monotonic()-start,flush=True)
(HERE/'k6-two-rectangle-pool.json').write_text(json.dumps(pool))
