import argparse
import heapq
import json
import random
import time
from pathlib import Path


def basis(q=3):
    n = 13
    offsets = {0, 1, 3, 9}
    neighbors = [sum(1 << l for l in range(n) if (p-l) % n in offsets) for p in range(n)]
    edges = [(p, 13+l) for p in range(n) for l in range(n) if (neighbors[p] >> l) & 1]
    independent = []
    for points in range(1 << n):
        adjacent = 0
        for p in range(n):
            if (points >> p) & 1:
                adjacent |= neighbors[p]
        lines = ((1 << n)-1) ^ adjacent
        closure = sum(1 << p for p in range(n) if neighbors[p] & lines == 0)
        if closure == points:
            independent.append(points | (lines << n))
    samples = [(1 << a) | (1 << b) for a,b in edges] + independent + [1, 1 << 13]
    inputs = [sum(((sample >> i) & 1) << j for j,sample in enumerate(samples)) for i in range(26)]
    wanted = (1 << len(edges))-1
    return neighbors, edges, independent, inputs, wanted, len(samples)-2, len(samples)-1


NEIGHBORS, EDGES, INDEPENDENT, INPUTS, WANTED, PX, PY = basis()


def evaluate(gates):
    vals = INPUTS.copy()
    dy = [int(i == 13) for i in range(26)]
    dx = [int(i == 0) for i in range(26)]
    for op,a,b in gates:
        va,vb = vals[a],vals[b]
        if op == 0:
            vals.append(va | vb)
            dy.append(dy[a] | dy[b])
            dx.append(dx[a] | dx[b])
        else:
            vals.append(va & vb)
            dy.append(((va >> PX) & 1 & dy[b]) | (dy[a] & (vb >> PX) & 1))
            dx.append(((va >> PY) & 1 & dx[b]) | (dx[a] & (vb >> PY) & 1))
    mismatch = (vals[-1] ^ WANTED).bit_count()
    derivatives = dy[-1] + dx[-1]
    return mismatch + 16*int((vals[-1] & 1) == 0) + 4*derivatives, mismatch, derivatives


def star(rng, doubled=False, transpose=False):
    gates = []
    def gate(op,a,b):
        assert a != b
        gates.append((op,min(a,b),max(a,b)))
        return 25+len(gates)
    replacement = 13
    if doubled:
        replacement = gate(1,13,gate(1,0,13))
    centers = list(range(13))
    rng.shuffle(centers)
    outputs = []
    for p in centers:
        leaves = [13+l for l in range(13) if (NEIGHBORS[p] >> l) & 1]
        rng.shuffle(leaves)
        if p == 0 and doubled:
            leaves = [replacement if l == 13 else l for l in leaves]
        while len(leaves)>1:
            a = leaves.pop(rng.randrange(len(leaves)))
            b = leaves.pop(rng.randrange(len(leaves)))
            leaves.append(gate(0,a,b))
        outputs.append(gate(1,p,leaves[0]))
    while len(outputs)>1:
        a = outputs.pop(rng.randrange(len(outputs)))
        b = outputs.pop(rng.randrange(len(outputs)))
        outputs.append(gate(0,a,b))
    if transpose:
        # p maps to line -p and line l maps to point -l.
        def trans(i):
            if i < 13: return 13+((-i) % 13)
            if i < 26: return (13-i) % 13
            return i
        gates = [(op,min(trans(a),trans(b)),max(trans(a),trans(b))) for op,a,b in gates]
    return tuple(gates)


def distributed_star(rng, transpose=False):
    gates=[]
    def gate(op,a,b):
        assert a != b
        gates.append((op,min(a,b),max(a,b)))
        return 25+len(gates)
    chosen=rng.choice([p for p in range(1,13) if not (NEIGHBORS[p]&1)])
    centers=list(range(13))
    rng.shuffle(centers)
    outputs=[]
    for p in centers:
        leaves=[13+l for l in range(13) if (NEIGHBORS[p]>>l)&1]
        while len(leaves)>1:
            a=leaves.pop(rng.randrange(len(leaves)))
            b=leaves.pop(rng.randrange(len(leaves)))
            leaves.append(gate(0,a,b))
        if p==chosen:
            chosen_leaves=leaves[0]
        else:
            outputs.append(gate(1,p,leaves[0]))
    while len(outputs)>1:
        a=outputs.pop(rng.randrange(len(outputs)))
        b=outputs.pop(rng.randrange(len(outputs)))
        outputs.append(gate(0,a,b))
    a=outputs[0]
    gate(1,gate(0,a,chosen),gate(0,a,chosen_leaves))
    if transpose:
        def trans(i):
            if i<13:return 13+((-i)%13)
            if i<26:return (13-i)%13
            return i
        gates=[(op,min(trans(a),trans(b)),max(trans(a),trans(b))) for op,a,b in gates]
    assert len(gates)==65
    assert evaluate(gates)==(0,0,0)
    return tuple(gates)


def remove_gate(gates,j,side):
    dead = 26+j
    replacement = gates[j][side]
    def ren(i):
        if i == dead: return replacement
        return i-1 if i>dead else i
    result = []
    for k,(op,a,b) in enumerate(gates):
        if k == j: continue
        a,b = ren(a),ren(b)
        if a == b:
            # A duplicated read is repaired by an arbitrary earlier distinct wire.
            b = 0 if a else 1
        result.append((op,min(a,b),max(a,b)))
    return tuple(result)


def mutate(gates,rng):
    g = list(gates)
    steps = rng.choices([1,2,3,5,8], [65,23,8,3,1])[0]
    for _ in range(steps):
        j = rng.randrange(len(g))
        op,a,b = g[j]
        kind = rng.randrange(10)
        if kind == 0:
            op ^= 1
        elif kind == 1:
            op = rng.randrange(2)
            a,b = rng.sample(range(26+j),2)
        else:
            v = rng.randrange(26+j)
            if rng.randrange(2): a = v
            else: b = v
        if a == b:
            b = (a+1) % (26+j)
        g[j] = (op,min(a,b),max(a,b))
    return tuple(g)


def run(seconds,seed,out):
    rng = random.Random(seed)
    began = time.monotonic()
    population = []
    seen = set()
    serial = 0
    best = (10**9,10**9,10**9)
    iterations = 0
    accepted = 0
    def submit(gates):
        nonlocal serial,best,accepted
        if gates in seen: return
        seen.add(gates)
        if len(seen)>200000: seen.clear()
        fitness = evaluate(gates)
        if fitness<best:
            best=fitness
            payload = dict(seed=seed,seconds=time.monotonic()-began,iterations=iterations,
                           score=fitness[0],mismatches=fitness[1],derivatives=fitness[2],gates=gates,
                           negative_basis=len(INDEPENDENT))
            out.write_text(json.dumps(payload)+'\n')
            print(json.dumps({k:v for k,v in payload.items() if k!='gates'}),flush=True)
        serial += 1
        # Max-heap encoded through negated objective; maintain a modest diverse beam.
        item=(-fitness[0],-fitness[1],rng.random(),serial,gates)
        if len(population)<256:
            heapq.heappush(population,item)
            accepted += 1
        elif item>population[0]:
            heapq.heapreplace(population,item)
            accepted += 1
        return fitness == (0,0,0)
    for _ in range(256):
        if rng.randrange(3):
            gates=distributed_star(rng,rng.randrange(2)==0)
        else:
            doubled = rng.randrange(2) == 0
            gates = star(rng,doubled,rng.randrange(2)==0)
        while len(gates)>64:
            gates = remove_gate(gates,rng.randrange(len(gates)-1),rng.choice([1,2]))
        submit(gates)
    next_report = time.monotonic()+30
    while time.monotonic()-began<seconds:
        iterations += 1
        if iterations % 5000 == 0:
            gates=distributed_star(rng,rng.randrange(2)==0)
            while len(gates)>64:
                gates=remove_gate(gates,rng.randrange(len(gates)-1),rng.choice([1,2]))
        else:
            # Tournament selection plus one uniform draw prevents a single ancestry.
            candidates=rng.sample(population,3)
            parent=max(candidates)[-1] if rng.randrange(5) else rng.choice(population)[-1]
            gates=mutate(parent,rng)
        if submit(gates):
            print(json.dumps(dict(found=True,iterations=iterations,seed=seed)),flush=True)
            return
        if time.monotonic()>next_report:
            print(json.dumps(dict(progress=True,iterations=iterations,accepted=accepted,
                                  best=best,seconds=time.monotonic()-began,seed=seed)),flush=True)
            next_report=time.monotonic()+30
    print(json.dumps(dict(finished=True,iterations=iterations,accepted=accepted,best=best,
                         seconds=time.monotonic()-began,seed=seed)),flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--seconds',type=int,default=1200)
    p.add_argument('--seed',type=int,default=64)
    p.add_argument('--out',type=Path,required=True)
    a=p.parse_args()
    print(json.dumps(dict(positive_basis=len(EDGES),negative_basis=len(INDEPENDENT),seed=a.seed)),flush=True)
    run(a.seconds,a.seed,a.out)
