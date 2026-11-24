from pathlib import Path
from itertools import permutations
import hashlib,json
H=Path('/tmp/oec/pequalnp-pilot-18/orch/S05')
# Canonical order a,b,c,x,y,z,t maps to full0,2,4,9,5,8,10.
E=[(6,0),(6,1),(6,2),(0,3),(1,4),(2,5),(3,4),(3,5),(4,5)]
records=[]
for perm in permutations(range(3)):
 a,b,c=perm;x,y,z=[v+3 for v in perm];t=6;gates=[];memo={}
 def gate(op,u,v):
  key=(op,*sorted((u,v)))
  if key not in memo:memo[key]=7+len(gates);gates.append(list(key))
  return memo[key]
 left=gate('and',a,gate('or',x,t))
 right=gate('and',t,gate('or',b,c))
 dirty=gate('and',gate('or',b,z),gate('or',c,y))
 triangle=gate('and',gate('or',y,z),gate('or',x,dirty))
 output=gate('or',gate('or',left,right),triangle)
 assert len(gates)==12
 wrong=[];junk=set()
 for m in range(128):
  v=[bool(m>>i&1) for i in range(7)];want=any(v[u] and v[w] for u,w in E)
  for i,(op,u,w) in enumerate(gates):
   v.append(v[u]&v[w] if op=='and' else v[u]|v[w])
   if not want and op=='and' and v[-1]:junk.add(i)
  assert v[output]==want
  # Equivalent symmetric upper-factor identity, used only as an algebra check.
  va,vb,vc,vx,vy,vz,vt=[bool(m>>i&1) for i in [a,b,c,x,y,z,t]]
  D=(va or vy or vz) and (vx or ((vb or vz) and (vc or vy)))
  assert D==(want or (va and vb and vc)) if not vt else True
  unguarded=D or (vt and (va or vb or vc))
  assert unguarded==(want or (va and vb and vc))
  assert (unguarded and (vt or vx or vy or vz))==want
 records.append(dict(permutation=perm,inputs=7,gate_wire_offset=7,gates=gates,output=output,gate_count=12,junk_ANDs=sorted(junk),all128_inputs=True))
result=dict(status='VERIFIED_SYMMETRIC_12_GATE_IDENTITY_NO11_FOUND',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),identity='a(x+t) + t(b+c) + (y+z)[x+(b+z)(c+y)]',operator_convention='+=OR,multiplication=AND',cost='2+2+6+2=12',six_S3_images=records,total_input_checks=768,known_dirty11='D+t(a+b+c) = F+abc',exact_filter_identity='F=(D+t(a+b+c))(t+x+y+z)',scope='Simple symbolic identities verified scalarly. No generic search/solver/Lean/lowerbound or11-gate witness.')
with (H/'gadget7-symmetric-identity-result.json').open('x') as f:json.dump(result,f,indent=2);f.write('\n')
print(json.dumps({k:v for k,v in result.items() if k!='six_S3_images'}))
