from pathlib import Path
from fractions import Fraction as Q
import argparse,hashlib,json,math,resource,sys,time
p=argparse.ArgumentParser();p.add_argument('mode',choices=['prepare','extract']);p.add_argument('case',choices=['equal','different']);a=p.parse_args()
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CORE,(0,0));sys.set_int_max_str_digits(0)
out=Path(__file__).parent;stem='axis-four-'+a.case;data=json.loads((out/(stem+'-flat-certificate.json')).read_text());zero=(0,)*4
gens=[{tuple(mon):Q(c) for mon,c in terms} for terms in data['generators']]
assert gens[-1]=={zero:Q(-2),(0,0,0,2):Q(1)}
assert all(mon[-1]<=1 for g in gens[:-1] for mon in g)
def add(dst,key,c):
 dst[key]=dst.get(key,Q(0))+c
 if not dst[key]:del dst[key]
def reduce_monomial(mon):
 return mon[:-1]+(mon[-1]%2,),Q(2)**(mon[-1]//2)
if a.mode=='prepare':
 tags=[]
 for i,terms in enumerate(data['multipliers'][:-1]):
  reduced={}
  for mon,c in terms:
   key,factor=reduce_monomial(tuple(mon));add(reduced,key,Q(c)*factor)
  tags.extend((i,mon) for mon in reduced)
 tags.sort(key=lambda z:(sum(z[1])+max(map(sum,gens[z[0]])),sum(z[1]),z[0],z[1]))
 n=len(tags);assert 0<n<=1000, n
 rows={}
 for column,(i,mult) in enumerate(tags):
  for mon,c in gens[i].items():
   key,factor=reduce_monomial(tuple(x+y for x,y in zip(mon,mult)))
   add(rows.setdefault(key,{}),column,c*factor)
 rows={mon:r for mon,r in rows.items() if r};rows.setdefault(zero,{})[n]=Q(-1)
 ordered=sorted(rows,key=lambda m:(sum(m),m));lengths=[len(rows[m]) for m in ordered]
 path=out/(stem+'-quotient-linear.in')
 with path.open('w') as f:
  f.write(f'{n} {len(rows)} 0 {sum(lengths)}\n'+' '.join(map(str,lengths))+'\n')
  for mon in ordered:
   for column,c in sorted(rows[mon].items()):
    exponents=['0']*n
    if column<n:exponents[column]='1'
    f.write(str(c.numerator)+' '+str(c.denominator)+' '+' '.join(exponents)+'\n')
 (out/(stem+'-quotient-linear.json')).write_text(json.dumps({'tags':[[i,list(mon)] for i,mon in tags],'shape':[len(rows),n],'quotient_relation':'u^2=2','input_sha256':hashlib.sha256(path.read_bytes()).hexdigest()},indent=2)+'\n')
 print('PREPARED',len(rows),n,'terms',sum(lengths),flush=True)
else:
 meta=json.loads((out/(stem+'-quotient-linear.json')).read_text());basis=json.loads((out/(stem+'-quotient-linear.basis.json')).read_text());assert basis['characteristic']==0
 linear=[];pivots=set()
 for poly in basis['basis']:
  row={};constant=Q(0)
  for coefficient,exponents in poly:
   assert sum(exponents)<=1
   if any(exponents):row[exponents.index(1)]=Q(coefficient)
   else:constant=Q(coefficient)
  assert row,'linear support system inconsistent'
  pivot=min(row);assert pivot not in pivots;pivots.add(pivot);linear.append((pivot,row,constant))
 solution=[Q(0)]*len(meta['tags'])
 for pivot,row,constant in linear:
  assert all(i==pivot or i not in pivots for i in row)
  solution[pivot]=-constant/row[pivot]
 mults=[{} for _ in gens]
 for c,(i,mon) in zip(solution,meta['tags']):
  if c:mults[i][tuple(mon)]=c
 total={}
 for g,mult in zip(gens[:-1],mults[:-1]):
  for mon,c in g.items():
   for shift,d in mult.items():add(total,tuple(x+y for x,y in zip(mon,shift)),c*d)
 assert all(mon[-1]<=2 for mon in total)
 for mon,c in list(total.items()):
  if mon[-1]==2:mults[-1][mon[:-1]+(0,)]=-c
 for mon,c in gens[-1].items():
  for shift,d in mults[-1].items():add(total,tuple(x+y for x,y in zip(mon,shift)),c*d)
 assert total=={zero:Q(1)}
 D=1
 for mult in mults:
  for c in mult.values():D=math.lcm(D,c.denominator)
 result={**data,'multipliers':[[[list(mon),str(c)] for mon,c in sorted(mult.items())] for mult in mults],'integer_denominator':str(D),'compression':'Exact linear solution modulo u^2-2 followed by explicit relation multiplier and direct rational polynomial verification.'}
 (out/(stem+'-quotient-compressed-certificate.json')).write_text(json.dumps(result,indent=2)+'\n')
 print('PASS terms',[len(x) for x in mults],'denominator_digits',len(str(D)),flush=True)
