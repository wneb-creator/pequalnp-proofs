from pathlib import Path
import json,hashlib
p=Path('/tmp/oec/pequalnp-pilot-121/plane2056-cegis');old=p/'warm-dirty2-near63-query';new=p/'warm-dirty2-nested63-query';om=json.loads(old.with_suffix('.mapping.json').read_text());nm=json.loads(new.with_suffix('.mapping.json').read_text());meta=json.loads(new.with_suffix('.json').read_text());semantic=json.loads(Path('/tmp/oec/pequalnp-pilot-121/nested63-phase-semantics-independent-review.json').read_text());n=meta['variables'];assert n==164672
for k in om:
 if k not in ['warm_gates','flipped_variables']:assert om[k]==nm[k],k
assert nm['warm_gates']==json.loads((p/'nested-near63-gates.json').read_text());diff=set(om['flipped_variables'])^set(nm['flipped_variables']);translate={b'0':b'0'}
for i in range(1,n+1):
 for s in [-1,1]:translate[str(s*i).encode()]=str((-s if i in diff else s)*i).encode()
failures=[];count=0
with old.with_suffix('.cnf').open('rb') as a,new.with_suffix('.cnf').open('rb') as b:
 assert a.readline()==b.readline()
 for i,line in enumerate(a,1):
  aa=line.split();bb=b.readline().split();assert len(aa)==len(bb) and all(translate[x]==y for x,y in zip(aa,bb)),i
  if not any(x.startswith(b'-') for x in bb[:-1]):failures.append({'index':i,'clause':[int(x) for x in bb[:-1]]})
  count+=1
 assert not b.read(1)
assert count==meta['clauses']==8860275
badrows=set(semantic['missing_positive_rows']);expected=[nm['outputs'][k] for k,r in enumerate(nm['rows']) if r in badrows];assert len(expected)==6
assert all(v not in nm['flipped_variables'] for v in expected)
assert sorted([x['clause'] for x in failures])==sorted([[x] for x in expected])
assert nm['dirty_at_least_two_variable'] in nm['flipped_variables']
r={'scope':'Equivalent CNF with complementary nested63 preference; no native target result','source_sha256':hashlib.sha256((p/'direct_cnf_warm_dirty2.py').read_bytes()).hexdigest(),'clauses_compared':count,'variables':n,'all_clauses_exact_after_polarity_translation':True,'mapping_fields_identical_except_warm_and_mask':True,'changed_polarity_variables':len(diff),'old_cnf_sha256':hashlib.sha256(old.with_suffix('.cnf').read_bytes()).hexdigest(),'new_cnf_sha256':hashlib.sha256(new.with_suffix('.cnf').read_bytes()).hexdigest(),'phase_failures':failures,'only_six_expected_positive_failures':True,'dirty2_unit_satisfied':True,'native_control_basis':'Same underlying formula as previously independently checked69-positive/67-negative controls; no new native control claimed','verdict':'APPROVED phase equivalence'}
q=Path('/tmp/oec/pequalnp-pilot-121/nested63-phase-equivalence-independent-review.json');q.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
