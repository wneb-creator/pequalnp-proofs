from pathlib import Path
from fractions import Fraction as Q
import hashlib,json,math,resource,time
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
out=Path(__file__).parent;start=time.monotonic()
meta=json.loads((out/'star-linear-compress.json').read_text())
data=json.loads((out/'star-r-flat-certificate.json').read_text())
basis=json.loads((out/'star-linear-compress.basis.json').read_text())
assert basis['characteristic']==0 and basis['nvars']==len(meta['tags'])
linear=[];pivots=set()
for poly in basis['basis']:
 row={};constant=Q(0)
 for coefficient,exponents in poly:
  assert sum(exponents)<=1
  if any(exponents):
   variable=exponents.index(1);row[variable]=Q(coefficient)
  else:constant=Q(coefficient)
 assert row
 pivot=min(row);assert pivot not in pivots;pivots.add(pivot)
 linear.append((pivot,row,constant))
del basis
solution=[Q(0)]*len(meta['tags'])
for pivot,row,constant in linear:
 assert all(i==pivot or i not in pivots for i in row)
 solution[pivot]=-constant/row[pivot]
new=[{} for _ in data['generators']]
for c,(i,mon) in zip(solution,meta['tags']):
 if c:new[i][tuple(mon)]=c
total={}
for terms,mult in zip(data['generators'],new):
 for mon,coefficient in terms:
  for shift,c in mult.items():
   key=tuple(a+b for a,b in zip(mon,shift));total[key]=total.get(key,Q(0))+Q(coefficient)*c
   if not total[key]:del total[key]
assert total=={(0,0,1,0,0):Q(1)}
D=1
for poly in new:
 for c in poly.values():D=math.lcm(D,c.denominator)
result={**data,'multipliers':[[[list(mon),str(c)] for mon,c in sorted(poly.items())] for poly in new],
 'compression':'Exact solution of known-support linear system, independently verified by direct Fraction polynomial convolution.',
 'common_denominator':str(D),'compression_seconds':time.monotonic()-start,
 'linear_basis_sha256':hashlib.sha256((out/'star-linear-compress.basis.json').read_bytes()).hexdigest()}
(out/'star-r-native-compressed-certificate.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS terms',[len(poly) for poly in new],'denominator_digits',len(str(D)),'max_coefficient_chars',max(len(str(c)) for poly in new for c in poly.values()),'seconds',time.monotonic()-start,flush=True)
