import json
from pathlib import Path
from fano_sat import verify

P=Path(__file__).resolve().parent
c=json.loads((P/'upper27.json').read_text())
gs=c['gates']
mapping={i:7+(1-i)%7 for i in range(7)}
mapping.update({7+j:(1-j)%7 for j in range(7)})
edges={tuple(sorted(e)) for e in json.loads((P/'fano.json').read_text())['edges']}
assert {tuple(sorted((mapping[a],mapping[b]))) for a,b in edges}==edges
todo=set(range(27));out=[]
while todo:
    ready=[j for j in todo if gs[j][1] in mapping and gs[j][2] in mapping]
    j=min(ready,key=lambda j:(max(mapping[gs[j][1]],mapping[gs[j][2]]),min(mapping[gs[j][1]],mapping[gs[j][2]]),j))
    op,a,b=gs[j];a,b=sorted((mapping[a],mapping[b]))
    mapping[14+j]=14+len(out);out.append([op,a,b]);todo.remove(j)
assert out[0]==[1,0,1] and not verify(out)
(P/'upper27-firstOR.json').write_text(json.dumps({'gates':out,'output':40,'bad':[]},indent=2)+'\n')
(P/'upper27-firstOR-fix.json').write_text(json.dumps(dict(enumerate(out)),indent=2)+'\n')
(P/'fano26-firstOR-fix.json').write_text(json.dumps({'0':[1,0,1]})+'\n')
print('Prepared same-side first-OR27 control; all16384 inputs pass.')
