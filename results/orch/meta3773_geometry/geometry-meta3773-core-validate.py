from pathlib import Path
import json,resource
resource.setrlimit(resource.RLIMIT_CORE,(0,0))
p=Path(__file__).resolve().parent
d=json.loads((p/'geometry-meta3773-core-data.json').read_text())
assert d['n']==24 and d['positive_count']==45 and len(d['rows'])==737
for i,row in enumerate(d['inputs']):
 assert sum(v<<(64*k)for k,v in enumerate(row))==sum(((m>>i)&1)<<k for k,m in enumerate(d['rows']))
report=[]
for f in sorted(p.glob('geometry-core-search*.json')):
 c=json.loads(f.read_text())
 if 'gates' not in c:continue
 assert c['inputs']==24 and c['gates'][0]==[0,0,1]
 vals=[sum(v<<(64*k)for k,v in enumerate(row))for row in d['inputs']]
 for i,(op,a,b)in enumerate(c['gates']):
  assert op in (0,1)and 0<=a<24+i and 0<=b<24+i
  vals.append(vals[a]&vals[b]if op else vals[a]|vals[b])
 errors=[]
 for o,w in enumerate(c['outputs']):
  assert 0<=w<len(vals)
  care=sum(v<<(64*k)for k,v in enumerate(d['care'][o]));truth=sum(v<<(64*k)for k,v in enumerate(d['truth'][o]));bits=(vals[w]^truth)&care
  errors.extend([o,k]for k in range(len(d['rows']))if bits>>k&1)
 assert len(errors)==c['errors']and len(c['gates'])==c['active']
 report.append({'file':f.name,'gates':len(c['gates']),'errors':len(errors),'wrong_output_rows':errors,'witness':not errors and len(c['gates'])<=58})
print(json.dumps(report,indent=2))
