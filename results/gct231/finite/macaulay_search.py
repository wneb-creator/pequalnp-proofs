from pathlib import Path
import sympy as s,json,itertools,time,sys,math
base=Path(__file__).parent
stem=sys.argv[1];D=int(sys.argv[2]);prime=int(sys.argv[3]);limit=float(sys.argv[4])
data=json.loads((base/(stem+'-equations.json')).read_text());u=s.symbols(' '.join(data['unknowns']));N=len(u)
polys=[s.Poly(s.sympify(r['coefficient']),*u) for r in data['equations']]
def monomials(maxdeg):
 out=[]
 for degree in range(maxdeg+1):
  level=[]
  for comb in itertools.combinations_with_replacement(range(N),degree):
   e=[0]*N
   for j in comb:e[j]+=1
   level.append(tuple(e))
  out.extend(sorted(level))
 return out
mons=monomials(D);index={m:i for i,m in enumerate(mons)};zero=(0,)*N
basis={};rows=0;start=time.monotonic();status='NO_CERTIFICATE_AT_THIS_DEGREE';stop=False
print('MODEL',stem,'D',D,'PRIME',prime,'COLS',len(mons),flush=True)
for eqnum,f in sorted(enumerate(polys),key=lambda item:item[1].total_degree()):
 for mul in monomials(D-f.total_degree()):
  row={index[tuple(a+b for a,b in zip(exp,mul))]:int(coef)%prime for exp,coef in f.terms() if int(coef)%prime}
  rows+=1;steps=0
  while row:
   lead=max(row)
   if lead not in basis:break
   factor=row[lead];previous=basis[lead]
   for col,value in previous.items():
    new=(row.get(col,0)-factor*value)%prime
    if new:row[col]=new
    elif col in row:del row[col]
   steps+=1
   if steps%100==0 and time.monotonic()-start>limit:
    status='UNKNOWN_TIME_LIMIT';stop=True;break
  if stop:break
  if row:
   lead=max(row);inv=pow(row[lead],prime-2,prime)
   row={col:(value*inv)%prime for col,value in row.items()}
   basis[lead]=row
   if lead==index[zero]:status='MODULAR_UNIT_CERTIFICATE_EXISTS';stop=True;break
  if rows%100==0:print('PROGRESS',rows,'RANK',len(basis),'ENTRIES',sum(map(len,basis.values())),'SECONDS',time.monotonic()-start,flush=True)
  if time.monotonic()-start>limit:status='UNKNOWN_TIME_LIMIT';stop=True;break
 if stop:break
result={'model':stem,'degree_bound':D,'prime':prime,'status':status,'rows_processed':rows,'rank':len(basis),'columns':len(mons),'wall_seconds':time.monotonic()-start,'basis_entries':sum(map(len,basis.values())),'scope':'Modular low-degree certificate search only; no characteristic-zero nonexistence conclusion.'}
(base/(stem+'-macaulay-d'+str(D)+'-p'+str(prime)+'.json')).write_text(json.dumps(result,indent=2)+'\n')
print('RESULT',json.dumps(result),flush=True)
