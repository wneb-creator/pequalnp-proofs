import json,sys
from pathlib import Path
BASE=Path('/tmp/oec/pequalnp-pilot-132/circuit-search')
CASES=json.loads((BASE/'cases.json').read_text())
EXAMPLES=CASES['positive']+CASES['negative']
POSITIVES=(1<<len(CASES['positive']))-1

def prune(g):
    v=[sum(((a>>i)&1)<<j for j,a in enumerate(EXAMPLES)) for i in range(26)]
    one=[1<<i for i in range(26)]
    new=[];ids=list(range(26));seen={x:i for i,x in enumerate(v)}
    singleton_rewrites=[];duplicate_rewrites=[]
    for old,(op,a,b) in enumerate(g,26):
        aa,bb=ids[a],ids[b]
        sig=(v[aa]|v[bb]) if op else (v[aa]&v[bb])
        ss=(one[aa]|one[bb]) if op else (one[aa]&one[bb])
        literal=next((i for i in range(26) if ss>>i&1 and (sig&POSITIVES)==(v[i]&POSITIVES)),None)
        if literal is not None:
            ids.append(literal);singleton_rewrites.append((old,literal))
        elif sig in seen:
            ids.append(seen[sig]);duplicate_rewrites.append((old,seen[sig]))
        else:
            index=26+len(new);new.append([op,aa,bb]);ids.append(index);v.append(sig);one.append(ss);seen[sig]=index
    output=ids[-1];used=set();todo=[output]
    while todo:
        i=todo.pop()
        if i<26 or i in used:continue
        used.add(i);todo.extend(new[i-26][1:])
    mapping={i:i for i in range(26)};clean=[]
    for i,(op,a,b) in enumerate(new,26):
        if i in used:
            mapping[i]=26+len(clean);clean.append([op,mapping[a],mapping[b]])
    assert mapping[output]==26+len(clean)-1
    wrong=0
    for j,a in enumerate(EXAMPLES):
        values=[bool(a>>i&1) for i in range(26)]
        for op,b,c in clean:values.append((values[b] or values[c]) if op else(values[b] and values[c]))
        wrong+=values[-1]!=(j<len(CASES['positive']))
    return clean,{'before':len(g),'after':len(clean),'wrong':wrong,'singleton':singleton_rewrites,'duplicates':duplicate_rewrites}

if __name__=='__main__':
    for arg in sys.argv[1:]:
        path=Path(arg);clean,report=prune(json.loads(path.read_text()));print(path.name,json.dumps(report))
        path.with_name(path.stem+'-pruned.json').write_text(json.dumps(clean))
