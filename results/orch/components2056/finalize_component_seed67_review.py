from pathlib import Path
import json,hashlib
b=Path('/tmp/oec/pequalnp-pilot-121/components2056');prefix='v5-nonread-control67-seed67warm-checked';phase=json.loads((b/'v5-nonread-control67-seed67warm.phase.json').read_text());mask=(b/phase['mask_name']).read_bytes();N=phase['variables']
def model(p):
 a={};sat=False
 for line in p.read_text().splitlines():
  if line.startswith('s '):sat=line=='s SATISFIABLE'
  if line.startswith('v '):
   for v in map(int,line.split()[1:]):
    if v:assert abs(v) not in a or a[abs(v)]==(v>0);a[abs(v)]=v>0
 assert sat and len(a)==N and set(a)==set(range(1,N+1));return a
warm=model(b/(prefix+'.sol'));orig=model(b/(prefix+'.unrenamed.sol'))
assert all(orig[i]==bool(warm[i]^((mask[(i-1)//8]>>((i-1)%8))&1)) for i in range(1,N+1))
candidate=b/(prefix+'.candidate.json');cold=b/'v5-nonread-control67-circuit.json';assert candidate.read_bytes()==cold.read_bytes()
p=Path('/tmp/oec/pequalnp-pilot-121/component-seed67-phase-independent-review.json');a=json.loads(p.read_text());a['actual_inverse_file_matches_every_variable']=True;a['actual_inverse_sha256']=hashlib.sha256((b/(prefix+'.unrenamed.sol')).read_bytes()).hexdigest();a['decoded_candidate_byte_identical_to_independently_checked_cold67']=True;a['candidate_sha256']=hashlib.sha256(candidate.read_bytes()).hexdigest();a['scope']='Optional67-preferred component preparation approved with exact actual inverse and decoded candidate;67-gate control only, no63 target result';p.write_text(json.dumps(a,indent=2)+'\n');print('review_sha256',hashlib.sha256(p.read_bytes()).hexdigest());print(p.read_text())
