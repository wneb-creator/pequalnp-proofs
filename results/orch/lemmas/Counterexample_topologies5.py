import itertools,json,time
from collections import Counter
from pathlib import Path
n=5
inputs=tuple(sum(1<<x for x in range(1<<n) if x>>i&1) for i in range(n))
rows=json.loads(Path('/tmp/oec/pequalnp-pilot-63/Counterexample_graph_minima5.json').read_text())
mins={r['circuit'][-1][-1]:r['depth'] for r in rows}
counts=Counter();examples={}
def analyze(circuit,fs,ancestors,orleaves):
    f=fs[-1];d=len(circuit)
    if mins.get(f)!=d:return
    counts['minimal_graph_circuits']+=1
    junk={j for j,(op,a,b) in enumerate(circuit) if op=='and' and fs[n+j]&~f}
    tops={j for j,(op,a,b) in enumerate(circuit) if op=='and' and not fs[n+j]&~f}
    istop=not any(t in ancestors[n+j] for t in tops for j,(op,a,b) in enumerate(circuit) if op=='and')
    if not istop:return
    counts['topform_minimal']+=1
    deep={j for j in junk if ancestors[n+j]&junk}
    if junk:
        counts['with_junk']+=1
        examples.setdefault('junk',dict(circuit=circuit,functions=fs,junk=list(junk),deep=list(deep)))
    if deep:
        counts['with_deep_junk']+=1
        examples.setdefault('deep',dict(circuit=circuit,functions=fs,junk=list(junk),deep=list(deep)))
    if any((orleaves[a]&{n+j for j in junk}) and (orleaves[b]&{n+j for j in junk}) for j,(op,a,b) in enumerate(circuit) if j in tops):
        counts['with_double_junk']+=1
        examples.setdefault('double',dict(circuit=circuit,functions=fs,junk=list(junk),deep=list(deep)))
def visit(circuit,fs,anc,ors):
    if circuit:analyze(circuit,fs,anc,ors)
    if len(circuit)==5:return
    counts['prefixes']+=1
    for a,b in itertools.combinations(range(len(fs)),2):
        for op in ['and','or']:
            f=fs[a]&fs[b] if op=='and' else fs[a]|fs[b]
            if f in fs:continue
            j=len(circuit)
            an=anc[a]|anc[b]|({a-n} if a>=n else set())|({b-n} if b>=n else set())
            ol=(ors[a]|ors[b]|{n+j}) if op=='or' else {n+j}
            visit(circuit+[(op,a,b)],fs+[f],anc+[an],ors+[ol])
visit([],list(inputs),[set() for _ in inputs],[{i} for i in range(n)])
print(json.dumps(dict(counts=counts,examples=examples),indent=2))
