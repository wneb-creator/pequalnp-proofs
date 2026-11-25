from pathlib import Path
import json,hashlib,resource,time
resource.setrlimit(resource.RLIMIT_CORE,(0,0));resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(20,20))
job=Path('/tmp/oec/pequalnp-pilot-79');source=job/'meta3773-six-dense-patch-data.json';digest=hashlib.sha256(source.read_bytes()).hexdigest();d=json.loads(source.read_text());R=d['raw_inputs'];N=d['inputs_with_free_or_signals'];K=len(d['point_inputs']);free=[x['inputs'] for x in d['default_free_ors']];gates=[]
def gate(op,a,b):
    gates.append([op,a,b]);return N+len(gates)-1
def union(xs):
    out=xs[0]
    for x in xs[1:]:out=gate(1,out,x)
    return out
stars=[]
for i in range(K):stars.append(gate(0,i,union([b for a,b in d['edges'] if a==i])))
output=union(stars);assert len(gates)==29
start=time.monotonic()
for raw in range(1<<R):
    values=[bool(raw>>i&1) for i in range(R)]
    for a,b in free:assert a<len(values) and b<len(values);values.append(values[a] or values[b])
    assert len(values)==N
    for op,a,b in gates:assert a<len(values) and b<len(values);values.append((values[a] or values[b]) if op else (values[a] and values[b]))
    assert values[output]==any(values[a] and values[b] for a,b in d['edges'])
assert hashlib.sha256(source.read_bytes()).hexdigest()==digest
result={'scope':'Positive baseline29 local circuit control, not target28 or global63 witness','source_model_sha256':digest,'gates':gates,'free_ors':free,'output':output,'size':len(gates),'physical_truth_table_verified':True,'physical_inputs':1<<R,'seconds':time.monotonic()-start}
(job/'meta3773-six-dense-baseline29.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k not in ['gates','free_ors']}))
