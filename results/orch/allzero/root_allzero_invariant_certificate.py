from pathlib import Path
import importlib.util,json,itertools,collections,sys,math
job=Path('/tmp/oec/pequalnp-pilot-79');base='root-allzero-d8';meta=json.loads((job/(base+'-metadata.json')).read_text());invmeta=json.loads((job/(base+'-invariant-metadata.json')).read_text());cert=json.loads((job/(base+'-invariant-exact-certificate.json')).read_text())
spec=importlib.util.spec_from_file_location('ng',job/'neogb-run-rational.py');ng=importlib.util.module_from_spec(spec);spec.loader.exec_module(ng)
names,prime,polys=ng.parse_input(job/'fresh_top_allzero_0.msolve');assert prime==0
pairs=[(0,1),(0,2),(1,2)];perms=list(itertools.permutations(range(3)))
def action(m,p):
 out=[0]*7;sign=1;out[-1]=m[-1]
 for i in range(3):out[p[i]]=m[i]
 for k,(i,j) in enumerate(pairs):
  ii,jj=p[i],p[j]
  if ii>jj:ii,jj=jj,ii;sign*=(-1)**m[k+3]
  out[3+pairs.index((ii,jj))]=m[k+3]
 return tuple(out),sign
def actpoly(poly,p):
 out=collections.defaultdict(int)
 for e,c in poly.items():
  m,s=action(e,p);out[m]+=s*c
 return {m:c for m,c in out.items() if c}
def reduce(poly):
 out=collections.defaultdict(int)
 for m,c in poly.items():out[m[:-1]+(m[-1]%2,)]+=c*24**(m[-1]//2)
 return {m:int(c) for m,c in out.items() if c}
reduced=[reduce(p) for p in polys];multipliers=[collections.defaultdict(int) for _ in polys];origins=meta['row_origins'];maps=[]
for p in perms:
 mapping=[]
 for i,poly in enumerate(reduced):
  acted=actpoly(poly,p)
  candidates=[j for j,q in enumerate(reduced) if q==acted]
  assert candidates,(p,i)
  mapping.append(candidates[0])
 maps.append(mapping)
for invrow,weight in enumerate(cert['coefficients']):
 if not weight:continue
 source=invmeta['source_rows'][invrow];i,m=origins[source]
 for p,mapping in zip(perms,maps):
  e,sign=action(m,p);multipliers[mapping[i]][e]+=weight*sign
multipliers=[{m:int(c) for m,c in poly.items() if c} for poly in multipliers]
# Independent multiplication against the original characteristic-zero input, then exact division by h²−24.
total=collections.defaultdict(int)
for multiplier,poly in zip(multipliers,polys):
 for m,c in multiplier.items():
  for e,b in poly.items():total[tuple(x+y for x,y in zip(m,e))]+=c*int(b)
zero=(0,)*7;total[zero]-=cert['denominator'];total={m:c for m,c in total.items() if c}
quotient=collections.defaultdict(int)
while total:
 m=max(total,key=lambda e:e[-1]);c=total[m]
 assert m[-1]>=2,(m,c)
 q=m[:-1]+(m[-1]-2,);quotient[q]+=c
 total[m]-=c;total[q]=total.get(q,0)+24*c
 total={e:v for e,v in total.items() if v}
assert not multipliers[0]
multipliers[0]={m:-c for m,c in quotient.items() if c}
# Final exact no-quotient verification.
final=collections.defaultdict(int)
for multiplier,poly in zip(multipliers,polys):
 for m,c in multiplier.items():
  for e,b in poly.items():final[tuple(x+y for x,y in zip(m,e))]+=c*int(b)
final={m:c for m,c in final.items() if c};assert final=={zero:cert['denominator']}
out={'classification':'Exact characteristic-zero polynomial unit identity checked against original input; not Lean checked','variables':names,'denominator':cert['denominator'],'multipliers':[[[list(m),c] for m,c in sorted(p.items())] for p in multipliers],'terms':[len(p) for p in multipliers],'permutation_generator_maps':maps}
(job/'root-allzero-original-exact-certificate.json').write_text(json.dumps(out,separators=(',',':'))+'\n')
print(json.dumps({'verified':True,'terms':out['terms'],'total_terms':sum(out['terms']),'constant_bits':cert['denominator'].bit_length(),'distinct_coefficients':len(set(abs(c) for p in multipliers for c in p.values()))}),flush=True)
