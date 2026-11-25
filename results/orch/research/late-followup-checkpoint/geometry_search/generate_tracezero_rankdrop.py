import json,itertools,time
from pathlib import Path
from sympy.polys.rings import ring
from sympy.polys.domains import QQ
base=Path('/tmp/oec/pequalnp-pilot-78');job=base/'geometry_search/tracezero_rankdrop';job.mkdir(exist_ok=True);start=time.monotonic()
data=json.loads((base/'construct_search/tracezero-hadamard.json').read_text());R,*xs=ring(','.join(data['variables']),QQ)
p=xs[:6];bs=xs[6:10];k,l=xs[10:];D=[(R.one,R.zero),(R.zero,R.one),(k,l)];P=[tuple(p[2*i:2*i+2]) for i in range(3)];B=[tuple(bs[:2]),tuple(bs[2:]),(-bs[0]-bs[2],-bs[1]-bs[3])]
H=[[1,1,1,1],[1,1,-1,-1],[1,-1,1,-1],[1,-1,-1,1]]
def transform(B,P,D):
 M=[[R.zero for j in range(4)] for i in range(4)]
 for i in range(3):M[i+1][i+1]=B[i];M[0][i+1]=M[i+1][0]=(P[i]-D[i])/2
 for i,(a,b) in enumerate([(2,3),(1,3),(1,2)]):M[a][b]=M[b][a]=(3*D[i]-P[i])/2
 return [[sum(H[i][a]*H[j][b]*M[a][b] for a in range(4) for b in range(4))/4 for j in range(4)] for i in range(4)]
AB=[transform([x[v] for x in B],[x[v] for x in P],[x[v] for x in D]) for v in range(2)]
W=[]
for v in range(7):
 bw=[R.one if v==i+3 else R.zero for i in range(3)]
 pw=[R.one if v==i else R.zero for i in range(3)]
 dw=[R.zero,R.zero,R.one if v==6 else R.zero]
 W.append(transform(bw,pw,dw))
exps=[(d-i,i) for d in (1,2,3) for i in range(d+1)]
def mul(a,b):
 out={}
 for ea,ca in a.items():
  for eb,cb in b.items():
   e=(ea[0]+eb[0],ea[1]+eb[1]);out[e]=out.get(e,R.zero)+ca*cb
 return out
coeff=[{} for v in range(7)]
for perm in itertools.permutations(range(4)):
 for slot in range(4):
  term={(0,0):R.one}
  for i in range(4):
   if i!=slot:term=mul(term,{(0,0):R.one,(1,0):AB[0][i][perm[i]],(0,1):AB[1][i][perm[i]]})
  for v in range(7):
   w=W[v][slot][perm[slot]]
   if w:
    for e,c in term.items():coeff[v][e]=coeff[v].get(e,R.zero)+w*c
assert all(coeff[v].get((0,0),R.zero)==0 for v in range(7))
raw=[[coeff[v].get(e,R.zero) for v in range(7)] for e in exps]
matrix=[];scales=[]
for row in raw:
 den=1
 for entry in row:
  for c in entry.values():den=__import__('math').lcm(den,int(c.denominator))
 row=[den*x for x in row];g=0
 for entry in row:
  for c in entry.values():g=__import__('math').gcd(g,abs(int(c)))
 assert g;matrix.append([x/g for x in row]);scales.append(str(QQ(g,den)))
report={'variables':data['variables'],'kernel_coordinates':['P_W0','P_W1','P_W2','B_W0','B_W1','B_W2','D_W2'],'parameter_exponents':exps,'matrix':[[str(x) for x in row] for row in matrix],'row_scale_to_actual_derivative':scales,'AB_matrices':[[[str(x) for x in row] for row in A] for A in AB],'W_basis':[[[str(x) for x in row] for row in A] for A in W],'term_counts':[[len(x) for x in row] for row in matrix],'scope':'Necessary first-variation equations for a third direction modulo the given trace-zero two-plane. No division or pivot assumptions: subtract D_W0*A+D_W1*B so D_W0=D_W1=0. The complementary seven coordinates are free. A nonzero extension forces rank(matrix)<=6. If the full three-plane has diagonal rank3, D_W2 is nonzero and may be normalized to1, giving six unknowns andnine affine linear equations. This is necessary, not sufficient, for a permanent-flat extension.','seconds':time.monotonic()-start}
(job/'matrix.json').write_text(json.dumps(report,indent=2)+'\n')
variables=data['variables']+['w'+str(i) for i in range(6)]
def fmt(x):return str(x).replace('**','^')
incidence=['+'.join('('+fmt(row[i])+')*w'+str(i) for i in range(6))+'+('+fmt(row[6])+')' for row in matrix]
script='ring r=0,('+','.join(variables)+'),dp;\noption(redSB);\noption(prot);\nideal I='+','.join(data['equations']+incidence)+';\nideal G=std(I);\nprint("SIZE");size(G);print("DIMENSION");dim(G);print("BASIS");G;quit;\n'
(job/'rank3-incidence-Q.sing').write_text(script)
print(json.dumps({'status':'GENERATED','shape':[9,7],'matrix_terms':sum(sum(row) for row in report['term_counts']),'seconds':report['seconds'],'scope':report['scope']},indent=2))
