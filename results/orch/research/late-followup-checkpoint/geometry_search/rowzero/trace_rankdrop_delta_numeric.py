from pathlib import Path
from collections import Counter
import json,hashlib
import numpy as np
base=Path('/tmp/oec/pequalnp-pilot-78/construct_search')
output=Path('/tmp/oec/pequalnp-pilot-78/geometry_search/rowzero')
source=base/'tracezero-numeric-candidates.json'
raw=source.read_bytes();data=json.loads(raw)
names=json.loads((base/'tracezero-hadamard.json').read_text())['variables']
assert names==['p0','p1','p2','p3','p4','p5','b0','b1','b2','b3','k','l']
records=[]
for i,record in enumerate(data):
 point={name:complex(a,b) for name,a,b in zip(names,record['real'],record['imag'])}
 b0,b1,b2,b3=[point[name] for name in ['b0','b1','b2','b3']]
 delta=b0*b3-b1*b2
 product_scale=abs(b0*b3)+abs(b1*b2)
 B=np.array([[b0,b2],[b1,b3]],dtype=complex)
 sv=np.linalg.svd(B,compute_uv=False)
 norm2=sum(abs(x)**2 for x in [b0,b1,b2,b3])
 records.append({'candidate_index':i,'delta_real':delta.real,'delta_imag':delta.imag,'absolute_delta':abs(delta),'delta_scaled_by_max_one_products':abs(delta)/max(1,product_scale),'delta_scaled_by_B_squared_norm':abs(delta)/max(norm2,1e-300),'B_singular_values':sv.tolist(),'B_singular_value_ratio':float(sv[1]/max(sv[0],1e-300)),'original_residual':record['record']['residual_max'],'stabilizer_size':len(record['stabilizer'])})
thresholds=[1e-12,1e-10,1e-8,1e-6]
counts={str(t):sum(r['delta_scaled_by_max_one_products']<t for r in records) for t in thresholds}
small=[r for r in records if r['delta_scaled_by_max_one_products']<1e-8]
summary={'candidate_count':len(records),'input_sha256':hashlib.sha256(raw).hexdigest(),'threshold_counts':counts,'small_candidate_indices':[r['candidate_index'] for r in small],'small_stabilizer_histogram':dict(Counter(r['stabilizer_size'] for r in small)),'minimum_absolute_delta':min(r['absolute_delta'] for r in records),'minimum_scaled_delta':min(r['delta_scaled_by_max_one_products'] for r in records),'minimum_B_singular_value_ratio':min(r['B_singular_value_ratio'] for r in records),'maximum_input_residual':max(r['original_residual'] for r in records),'smallest_records':sorted(records,key=lambda r:r['delta_scaled_by_max_one_products'])[:8],'scope':'Numerical evidence only. Small nonzero floating-point values do not establish exact vanishing; non-small values do not prove global coverage.'}
(output/'trace-rankdrop-delta-numeric.json').write_text(json.dumps({'summary':summary,'records':records},indent=2)+'\n')
print(json.dumps(summary),flush=True)
