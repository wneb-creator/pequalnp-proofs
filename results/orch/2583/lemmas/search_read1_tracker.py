import json
import random
from pathlib import Path

DATA=json.loads(Path('results/orch/2583/lemmas/search_fano_baseline.json').read_text())
EDGES=[tuple(e) for e in DATA['edges']]

def tracked(circ):
    linear=[1<<i for i in range(14)]
    pairs=[0]*14
    for op,a,b in circ:
        if op==1:
            linear.append(linear[a]|linear[b])
            pairs.append(pairs[a]|pairs[b])
        else:
            pairs.append(sum(int(bool((linear[a]>>p&1 and linear[b]>>l&1) or
                                      (linear[b]>>p&1 and linear[a]>>l&1)))<<k
                             for k,(p,l) in enumerate(EDGES)))
            linear.append(0)
    return linear[-1],pairs[-1]

def exact_read1(circ,p,l):
    vectors=[{(1,0)} if i==p else {(0,1)} if i==l else set() for i in range(14)]
    for op,a,b in circ:
        if op==1:vectors.append(vectors[a]|vectors[b])
        else:vectors.append({(min(x+z,2),min(y+w,2))
                             for x,y in vectors[a] for z,w in vectors[b]})
    return any(x<=1 and y<=1 for x,y in vectors[-1])

def check(circ):
    linear,pairs=tracked(circ)
    for k,(p,l) in enumerate(EDGES):
        prediction=bool((linear>>p&1) or (linear>>l&1) or (pairs>>k&1))
        assert prediction==exact_read1(circ,p,l)

if __name__=='__main__':
    check(DATA['gates'])
    plant=[(0,0,7),(1,0,7),(0,14,15)]
    check(plant)
    assert not exact_read1(plant,0,7)
    rng=random.Random(2583)
    for iteration in range(1000):
        count=rng.randrange(1,28)
        circ=[(rng.randrange(2),rng.randrange(14+j),rng.randrange(14+j)) for j in range(count)]
        check(circ)
    print('PASS: tracker matches exact joint capped-vector recursion on 1002 circuits and 21042 edge tests; planted repeated-edge witness rejected')
