from pathlib import Path
import importlib.util,itertools,json,hashlib
B=Path('/tmp/oec/pequalnp-pilot-21/search')
spec=importlib.util.spec_from_file_location('canonical_five_test',B/'cegis-general-five-canonical.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
c=m.f.b.CNF();ops,aa,bb,labels=m.encode(c,[])
labelvars={v for row in labels for v in row};clauses=[clause for clause in c.cs if all(abs(v) in labelvars for v in clause)]
accepted=[]
for a,b,d in itertools.product(range(13),repeat=3):
 choices=[0,1,a,b,d];values={v:w==choice for row,choice in zip(labels,choices) for w,v in enumerate(row)}
 actual=all(any(values[abs(v)]==(v>0) for v in clause) for clause in clauses)
 wanted=a==2 and b==3 and d in (4,7,9)
 assert actual==wanted
 if actual:accepted.append(choices)
cert=json.loads((B/'five-line-orbit-maps.json').read_text());lines=[set(L) for L in m.f.LINES]
assert len(cert)==1287
for key,item in cert.items():
 subset=list(map(int,key.split(',')));permutation=item['point_map'];representative=item['representative']
 assert sorted(permutation)==list(range(13)) and representative in accepted
 images=[{permutation[p] for p in line} for line in lines]
 assert {frozenset(x) for x in images}=={frozenset(x) for x in lines}
 assert {frozenset(images[w]) for w in subset}=={frozenset(lines[w]) for w in representative}
class Count(m.f.b.CNF):
 def __init__(self):self.n=0;self.count=0
 def add(self,*xs):self.count+=1
cc=Count();m.encode(cc,m.f.ROWS)
assert cc.n==129594 and cc.count==2680566
report={'status':'PASS','tested_remaining_label_assignments':13**3,'accepted_label_assignments':accepted,'verified_five_subset_maps':len(cert),'full_variables':cc.n,'full_clauses':cc.count,'solver_launched':False,'runner_sha256':hashlib.sha256((B/'cegis-general-five-canonical.py').read_bytes()).hexdigest()}
(B/'general-five-canonical-test.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
