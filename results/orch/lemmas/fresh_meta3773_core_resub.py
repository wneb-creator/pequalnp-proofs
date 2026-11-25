from pathlib import Path
import json, itertools, time
job = Path(__file__).resolve().parent
d = json.loads((job / 'geometry-meta3773-core-data.json').read_text())
s = json.loads((job / 'geometry-core-search7901-best.json').read_text())
def pack(words): return sum(x << (64*i) for i,x in enumerate(words))
inputs = list(map(pack,d['inputs']))
truth = list(map(pack,d['truth']))
care = list(map(pack,d['care']))
mask = (1 << len(d['rows']))-1
gates = s['gates']; outs = s['outputs']; n = len(inputs)
def simulate(force=None):
    result = inputs.copy()
    for i,(op,a,b) in enumerate(gates,n):
        result.append(force[i] if force and i in force else result[a]&result[b] if op else result[a]|result[b])
    return result
original = simulate()
errors = [[i for i in range(len(d['rows'])) if ((original[o]^t)&c)>>i&1] for o,t,c in zip(outs,truth,care)]
print('errors', errors)
sc = []; sol=[]; improved=[]; checks=0
for w in range(n+1,n+len(gates)):
    low = simulate({w:0}); high=simulate({w:mask})
    z=o=0; static=0
    for out,t,c in zip(outs,truth,care):
        delta=low[out]^high[out]; static+=((~delta)&(t^low[out])&c).bit_count(); z |= delta & ~t & c; o |= delta & t & c
    vals=original[:w]
    localmin=10000
    for b in range(w):
        for a in range(b+1):
            for op,v in [(0,vals[a]|vals[b]),(1,vals[a]&vals[b])]:
                checks+=1
                if v==original[w]: continue
                # z/o unions allow each distinct row to be counted once; recalc full scores for answers
                e=static+(v&z).bit_count()+(~v&o).bit_count()
                localmin=min(localmin,e)
                if e<=1:
                    total=sum(((simulate({w:v})[out]^t)&c).bit_count() for out,t,c in zip(outs,truth,care))
                    if total<=1: improved.append([w,op,a,b,total])
                    if total==0:sol.append(improved[-1])
    sc.append([w,static,localmin]);
print('single-gate-replacements',checks,'improved',len(improved),'solutions',sol,'examples',improved[:20]); print('range',sc)
# Any raw existing output replacement. Core truth masks contain complete monotone separating tests.
print('any-existing-output', [[(i,((v^t)&c).bit_count()) for i,v in enumerate(original) if ((v^t)&c).bit_count()<=2] for t,c in zip(truth,care)])
