import ast,json,re,sys
from pathlib import Path

log=Path(sys.argv[1]);prefix=Path(sys.argv[2]);elastic=bool(int(sys.argv[3]))
data=json.loads((Path(__file__).resolve().parent/'data.json').read_text())
inputs=[sum(((m>>v)&1)<<m for m in range(256)) for v in range(8)]
target=0
for a,b in data['edges']:target|=inputs[a]&inputs[b]

def evaluate(gates,output):
    w=inputs.copy()
    for op,a,b in gates:
        assert op in (0,1) and 0<=a<len(w) and 0<=b<len(w)
        w.append(w[a]&w[b] if op==0 else w[a]|w[b])
    return w[output]

def live_count(gates):
    live={7+len(gates)}
    for i in range(len(gates)-1,-1,-1):
        if 8+i in live:live.update(gates[i][1:])
    return sum(8+i in live for i in range(len(gates)))

reports=[]
for line in log.read_text().splitlines():
    if line.startswith('best '):
        m=re.fullmatch(r'best (\d+) trial (\d+) gates (\[.*\])',line);assert m
        gates=ast.literal_eval(m[3]);assert len(gates)==(14 if elastic else 10)
        actual=evaluate(gates,7+len(gates));fp=(actual&~target).bit_count();fn=(target&~actual).bit_count()
        sfp=sum(bool(actual>>r&1) and not bool(target>>r&1) for r in data['rows'])
        sfn=sum(bool(target>>r&1) and not bool(actual>>r&1) for r in data['rows'])
        score=128*(sfp+sfn)+live_count(gates) if elastic else 4*sfp+sfn
        assert score==int(m[1])
        if elastic:assert fp==fn==0
        report=dict(score=score,trial=int(m[2]),sample_false_positive=sfp,sample_false_negative=sfn,
                    full_false_positive=fp,full_false_negative=fn,live_gates=live_count(gates),
                    false_positive_masks=[r for r in range(256) if actual>>r&1 and not target>>r&1],
                    false_negative_masks=[r for r in range(256) if target>>r&1 and not actual>>r&1])
        reports.append(report)
        prefix.with_name(prefix.name+'-best.json').write_text(json.dumps(dict(inputs=8,gates=gates,output=7+len(gates),validation=report),indent=2)+'\n')
    elif line.startswith('WITNESS '):
        candidate=json.loads(line[8:]);assert candidate['inputs']==8 and len(candidate['gates'])<=10
        assert evaluate(candidate['gates'],candidate['output'])==target
        candidate['full_assignments_checked']=256
        prefix.with_name(prefix.name+'-witness.json').write_text(json.dumps(candidate,indent=2)+'\n')
prefix.with_name(prefix.name+'-validation.json').write_text(json.dumps(reports,indent=2)+'\n')
print(json.dumps(reports))
