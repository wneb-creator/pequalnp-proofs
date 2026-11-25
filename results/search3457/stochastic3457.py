import argparse, itertools, json, math, random, resource, time
from pathlib import Path

ap = argparse.ArgumentParser(description="Bounded heuristic full-truth-table circuit search; no UNSAT claims")
ap.add_argument("--N", type=int, default=4)
ap.add_argument("--mask", type=int, required=True)
ap.add_argument("--gates", type=int, required=True)
ap.add_argument("--seconds", type=int, default=120)
ap.add_argument("--seed", type=int, default=0)
ap.add_argument("--temperature", type=float, default=10.0)
ap.add_argument("--restart-steps", type=int, default=10000)
ap.add_argument("--out", type=Path, required=True)
a = ap.parse_args()
assert a.seconds > 0 and 1 <= a.N <= 5 and a.gates > 0
assert a.temperature > 0 and a.restart_steps > 0
assert a.mask > 0 and a.mask < (1 << (a.N*a.N))
for p in range(a.N):
    for q in range(p):
        assert sum(bool(a.mask >> (p*a.N+l) & 1) and bool(a.mask >> (q*a.N+l) & 1) for l in range(a.N)) <= 1, "graph is not C4-free"
resource.setrlimit(resource.RLIMIT_AS, (256 * 1024 * 1024, 256 * 1024 * 1024))
rng = random.Random(a.seed)
n = 2 * a.N
assignments = range(1 << n)
full = (1 << (1 << n)) - 1
inputs = [sum(1 << r for r in assignments if r >> i & 1) for i in range(n)]
edges = [(p, a.N+l) for p in range(a.N) for l in range(a.N) if a.mask >> (p*a.N+l) & 1]
def expected(r):
    return any(r >> p & 1 and r >> l & 1 for p,l in edges)
target = sum(1 << r for r in assignments if expected(r))
singletons = sum(1 << (1 << i) for i in range(n))
edge_rows = sum(1 << ((1 << p) | (1 << l)) for p,l in edges)
mis_rows = sum(1 << r for r in assignments if not expected(r) and all(expected(r | (1 << i)) for i in range(n) if not r >> i & 1))

def evaluate(c):
    wires = inputs.copy()
    bad = 0
    for op,p,q in c:
        t = (wires[p] & wires[q]) if op else (wires[p] | wires[q])
        if op:
            bad += (t & singletons).bit_count()
        wires.append(t)
    err = wires[-1] ^ target
    score = err.bit_count() + 16 * (err & edge_rows).bit_count() + 32 * (err & mis_rows).bit_count() + 256 * bad
    return score, err.bit_count(), bad

covers = []
for size in range(1,n+1):
    covers = [set(c) for c in itertools.combinations(range(n),size) if all(p in c or l in c for p,l in edges)]
    if covers:
        break

def canonical():
    c = []
    def add(op,p,q):
        c.append((op,min(p,q),max(p,q)))
        return n + len(c)-1
    def or_tree(ws):
        ws = list(ws)
        while len(ws) > 1:
            p = ws.pop(rng.randrange(len(ws)))
            q = ws.pop(rng.randrange(len(ws)))
            ws.append(add(0,p,q))
        return ws[0]
    cover = rng.choice(covers)
    stars = {v: [] for v in cover}
    for p,l in edges:
        owners = [v for v in (p,l) if v in cover]
        v = rng.choice(owners)
        stars[v].append(l if v == p else p)
    order = list(cover)
    rng.shuffle(order)
    terms = []
    for v in order:
        assert stars[v]
        terms.append(add(1,v,or_tree(stars[v])))
    or_tree(terms)
    return c
base = canonical()
assert evaluate(base) == (0,0,0)
assert len(base) == a.gates + 1

def initial():
    c = canonical()
    pos = rng.randrange(len(c)-1)
    replacement = c[pos][rng.randrange(1,3)]
    c.pop(pos)
    removed_wire = n + pos
    def fix(w):
        if w == removed_wire:
            w = replacement
        return w - (w > removed_wire)
    return [(op,*sorted((fix(p),fix(q)))) for op,p,q in c]

start = time.monotonic()
end = start + a.seconds
best_score = 10**9
best = None
steps = 0
restarts = 0
while time.monotonic() < end:
    c = initial()
    score,err,bad = evaluate(c)
    restarts += 1
    if score < best_score:
        best_score = score
        best = c.copy()
        print(json.dumps({"elapsed": round(time.monotonic()-start,3), "score": score, "truth_errors": err, "singleton_violations": bad, "steps": steps, "circuit": c}),flush=True)
    if score == 0:
        break
    for step in range(a.restart_steps):
        if step % 256 == 0 and time.monotonic() >= end:
            break
        i = rng.randrange(a.gates)
        old = c[i]
        op,p,q = old
        choice = rng.randrange(5)
        if choice == 0:
            op ^= 1
        elif choice < 3:
            p = rng.randrange(n+i)
        else:
            q = rng.randrange(n+i)
        c[i] = (op,min(p,q),max(p,q))
        new_score,new_err,new_bad = evaluate(c)
        steps += 1
        temp = a.temperature * (1.0 - step/a.restart_steps) + 0.25
        if new_score <= score or rng.random() < math.exp((score-new_score)/temp):
            score,err,bad = new_score,new_err,new_bad
        else:
            c[i] = old
        if score < best_score:
            best_score = score
            best = c.copy()
            print(json.dumps({"elapsed": round(time.monotonic()-start,3), "score": score, "truth_errors": err, "singleton_violations": bad, "steps": steps, "circuit": c}),flush=True)
        if score == 0:
            break
    if best_score == 0:
        break

# Independent scalar evaluation, including every AND's singleton behavior.
def verify(c):
    mistakes = []
    bad_and = []
    for r in assignments:
        ws = [bool(r >> i & 1) for i in range(n)]
        for i,(op,p,q) in enumerate(c):
            ws.append((ws[p] and ws[q]) if op else (ws[p] or ws[q]))
            if op and r.bit_count() == 1 and ws[-1]:
                bad_and.append((i,r))
        if ws[-1] != expected(r):
            mistakes.append(r)
    return mistakes,bad_and
mistakes,bad_and = verify(best)
assert (len(mistakes),len(bad_and)) == evaluate(best)[1:]
result = {"N":a.N,"mask":a.mask,"gates":a.gates,"seed":a.seed,"temperature":a.temperature,"restart_steps":a.restart_steps,"seconds_requested":a.seconds,"elapsed":time.monotonic()-start,"steps":steps,"restarts":restarts,"best_score":best_score,"truth_error_count":len(mistakes),"singleton_violation_count":len(bad_and),"status":"verified witness" if not mistakes and not bad_and else "no witness found; heuristic search only","circuit":[["and" if op else "or",p,q] for op,p,q in best],"truth_error_assignments":mistakes,"singleton_violations":bad_and}
a.out.write_text(json.dumps(result,indent=2)+"\n")
print(json.dumps(result),flush=True)
