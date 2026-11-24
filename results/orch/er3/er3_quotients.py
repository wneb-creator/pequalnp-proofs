import functools, itertools, json, sys, time
from pathlib import Path

source = json.loads(Path(sys.argv[1]).read_text())
limit = int(sys.argv[2])
out = Path(sys.argv[3])
n = source['n']
original_edges = [tuple(e) for e in source['edges']]
adj = [0] * n
for i,j in original_edges:
    adj[i] |= 1 << j
    adj[j] |= 1 << i

def independent_block(s):
    return all(not (adj[i] & s) for i in range(n) if s >> i & 1)

@functools.lru_cache(None)
def inputs(q):
    return [sum(1 << x for x in range(1 << q) if x >> i & 1) for i in range(q)]

def test(partition):
    q=len(partition)
    m={i:j for j,b in enumerate(partition) for i in range(n) if b>>i&1}
    es={tuple(sorted((m[i],m[j]))) for i,j in original_edges}
    assert all(i!=j for i,j in es)
    masks=[0]*q
    for i,j in es:
        masks[i]|=1<<j; masks[j]|=1<<i
    if any((masks[i]&masks[j]).bit_count()>=2 for i in range(q) for j in range(i)):
        return None
    @functools.lru_cache(None)
    def alpha(s):
        if not s:return 0
        v=(s&-s).bit_length()-1
        return max(alpha(s&~(1<<v)),1+alpha(s&~((1<<v)|masks[v])))
    tau=q-alpha((1<<q)-1)
    vals=inputs(q).copy();lookup={v:i for i,v in enumerate(vals)}
    rename=[m[i] for i in range(n)];gates=[]
    for op,a,b in source['gates']:
        a,b=rename[a],rename[b]
        value=vals[a]&vals[b] if op=='and' else vals[a]|vals[b]
        if value not in lookup:
            lookup[value]=len(vals); vals.append(value);gates.append([op,a,b])
        rename.append(lookup[value])
    output=rename[source['output']]
    used=set()
    def visit(w):
        if w<q or w in used:return
        used.add(w);_,a,b=gates[w-q];visit(a);visit(b)
    visit(output)
    expected=0
    for i,j in es:expected|=vals[i]&vals[j]
    assert expected==vals[output]
    bound=len(es)+tau-1;size=len(used)
    if size<bound:
        names={i:i for i in range(q)};pruned=[]
        for w in sorted(used):
            op,a,b=gates[w-q];names[w]=q+len(pruned)
            pruned.append([op,names[a],names[b]])
        witness={'n':q,'edges':sorted(es),'tau':tau,'bound':bound,'size':size,
                 'gates':pruned,'output':names[output],'partition':partition,
                 'full_truth_rows':1<<q}
        out.write_text(json.dumps(witness,indent=2))
        print('WITNESS',json.dumps(witness),flush=True)
        sys.exit(0)
    return (len(es),tau,size,bound)

parts={tuple(1<<i for i in range(n))}
start=time.monotonic();total=0;eligible=0;best=None
for depth in range(limit+1):
    count=0;local=[]
    for p in parts:
        total+=1;r=test(p)
        if r is not None:
            eligible+=1;count+=1;local.append(r)
            if best is None or r[2]-r[3]<best[2]-best[3]:best=r
    print(json.dumps({'merges':depth,'partitions':len(parts),'eligible':count,
                      'best_excess':None if not local else min(r[2]-r[3] for r in local),
                      'elapsed':time.monotonic()-start}),flush=True)
    if depth==limit:break
    nxt=set()
    for p in parts:
        for i in range(len(p)):
            for j in range(i):
                b=p[i]|p[j]
                if independent_block(b):
                    nxt.add(tuple(sorted([b]+[v for k,v in enumerate(p) if k not in (i,j)])))
    parts=nxt
print(json.dumps({'total':total,'eligible':eligible,'best':best,'elapsed':time.monotonic()-start}),flush=True)
