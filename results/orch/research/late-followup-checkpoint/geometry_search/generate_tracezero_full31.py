import json,itertools,math,time
from pathlib import Path
from sympy.polys.rings import ring
from sympy.polys.domains import QQ
import sympy as s
base=Path('/tmp/oec/pequalnp-pilot-78');job=base/'geometry_search/tracezero_rankdrop';start=time.monotonic()
data=json.loads((base/'construct_search/tracezero-hadamard.json').read_text());old=json.loads((job/'matrix.json').read_text());shifted=json.loads((job/'shifted-matrix.json').read_text())
names=data['variables']+['w'+str(i) for i in range(6)];R,*xs=ring(','.join(names),QQ)
p=xs[:6];bs=xs[6:10];k,l=xs[10:12];ws=xs[12:]
D=[(R.one,R.zero,R.zero),(R.zero,R.one,R.zero),(k,l,R.one)]
RR=[(p[2*i],p[2*i+1],ws[i]) for i in range(3)]
P=[tuple(RR[i][v]+3*D[i][v] for v in range(3)) for i in range(3)]
B=[(bs[0],bs[1],ws[3]),(bs[2],bs[3],ws[4]),(-bs[0]-bs[2],-bs[1]-bs[3],ws[5])]
zero=(R.zero,)*3;Tp=[[zero for j in range(4)] for i in range(4)]
for i in range(3):
 Tp[i+1][i+1]=B[i];Tp[0][i+1]=Tp[i+1][0]=tuple((P[i][v]-D[i][v])/2 for v in range(3))
for i,(a,b) in enumerate([(2,3),(1,3),(1,2)]):Tp[a][b]=Tp[b][a]=tuple((3*D[i][v]-P[i][v])/2 for v in range(3))
H=[[1,1,1,1],[1,1,-1,-1],[1,-1,1,-1],[1,-1,-1,1]]
T=[[tuple(sum(H[i][a]*H[j][b]*Tp[a][b][v] for a in range(4) for b in range(4))/4 for v in range(3)) for j in range(4)] for i in range(4)]
def mul(a,b):
 out={}
 for ea,ca in a.items():
  for eb,cb in b.items():
   e=tuple(x+y for x,y in zip(ea,eb));out[e]=out.get(e,R.zero)+ca*cb
 return out
coeff={}
for perm in itertools.permutations(range(4)):
 term={(0,0,0):R.one}
 for i in range(4):term=mul(term,{(0,0,0):R.one,(1,0,0):T[i][perm[i]][0],(0,1,0):T[i][perm[i]][1],(0,0,1):T[i][perm[i]][2]})
 for e,c in term.items():coeff[e]=coeff.get(e,R.zero)+c
assert coeff[(0,0,0)]==24 and all(coeff[e]==0 for e in [(1,0,0),(0,1,0),(0,0,1)])
parse=lambda text:R.from_expr(s.sympify(text.replace('^','**')))
for f,meta in zip(shifted['flat_generators'],data['metadata']):
 e=(meta['degree']-meta['t_power'],meta['t_power'],0)
 assert coeff[e]==parse(f)*QQ(meta['content'])/QQ(meta['denominator'])
for row,exp,scale in zip(shifted['matrix'],old['parameter_exponents'],old['row_scale_to_actual_derivative']):
 expr=sum(parse(row[i])*ws[i] for i in range(6))+parse(row[6])
 assert coeff[tuple(exp)+(1,)]==expr*QQ(scale)
exps=[(a,b,d-a-b) for d in (2,3,4) for a in range(d+1) for b in range(d-a+1)]
polys=[];scales=[]
for e in exps:
 f=coeff[e];den=1
 for c in f.values():den=math.lcm(den,int(c.denominator))
 f=f*den;content=0
 for c in f.values():content=math.gcd(content,abs(int(c)))
 assert content;polys.append(f/content);scales.append(str(QQ(content,den)))
fmt=lambda x:str(x).replace('**','^')
script='ring r=0,('+','.join(names)+'),dp;\noption(redSB);\noption(prot);\nideal I='+','.join(fmt(x) for x in polys)+';\nideal G=slimgb(I);\nprint("SIZE");size(G);print("DIMENSION");dim(G);print("BASIS");short=0;G;print("COMPLETED_EXACT_RUN");quit;\n'
(job/'rank3-full31-shifted-Q.sing').write_text(script)
report={'status':'PASS','variables':names,'parameter_exponents':exps,'generators':list(map(str,polys)),'scales_to_actual_permanent_coefficients':scales,'term_counts':[len(x) for x in polys],'total_terms':sum(len(x) for x in polys),'all21_incidence_coefficients_independently_matched':True,'source':'Direct24-term permanent expansion in three plane parameters, using explicit Hadamard matrices.','scope':'All31 homogeneous coefficients for a full diagonal-rank-three candidate in the tracezero two-plane normalization. Constant-diagonal obstruction supplies complete D-rank-three coverage. No algebraic conclusion yet.','seconds':time.monotonic()-start}
(job/'full31-shifted.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k not in ('generators',)},indent=2))
