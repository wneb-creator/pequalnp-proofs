from pathlib import Path
from itertools import permutations
from sympy.polys.rings import ring
from sympy.polys.domains import QQ
import json,math,time
start=time.monotonic()
base=Path('/tmp/oec/pequalnp-pilot-78/geometry_search/rowzero')
names=['p0','p1','p2','p3','p4','p5','d0','d1','d2','d3','tau']
R,*v=ring(','.join(names),QQ)
p0,p1,p2,p3,p4,p5,d0,d1,d2,d3,tau=v
H=[[1,1,1,1],[1,1,-1,-1],[1,-1,1,-1],[1,-1,-1,1]]
def add(A,B):
 out=dict(A)
 for k,x in B.items():out[k]=out.get(k,R.zero)+x
 return {k:x for k,x in out.items() if x}
def scale(A,c):return {k:x*c for k,x in A.items() if x*c}
def mul(A,B):
 out={}
 for (i,j),a in A.items():
  for (k,l),b in B.items():out[i+k,j+l]=out.get((i+k,j+l),R.zero)+a*b
 return {k:x for k,x in out.items() if x}
def lin(pair):return {(1,0):pair[0],(0,1):pair[1]}
def product(polys):
 result={(0,0):R.one}
 for p in polys:result=mul(result,p)
 return result
cases={}
for pivot,name in [(0,'same-index'),(1,'other-index')]:
 D=[None]*3;D[pivot]=(R.zero,R.one)
 remaining=[i for i in range(3) if i!=pivot]
 D[remaining[0]]=(d0,d1);D[remaining[1]]=(d2,d3)
 P=[(p0,p1),(p2,p3),(p4,p5)]
 B=[(R.one,R.zero),(tau,R.zero),(-1-tau,R.zero)]
 Tp=[[(R.zero,R.zero) for _ in range(4)] for _ in range(4)]
 for i in range(3):
  Tp[i+1][i+1]=B[i]
  Tp[0][i+1]=Tp[i+1][0]=tuple((P[i][j]+2*D[i][j])/2 for j in range(2))
 for i,(i0,i1) in enumerate([(2,3),(1,3),(1,2)]):Tp[i0][i1]=Tp[i1][i0]=tuple(-P[i][j]/2 for j in range(2))
 T=[[tuple(sum(H[i][a]*H[j][b]*Tp[a][b][z] for a in range(4) for b in range(4))/4 for z in range(2)) for j in range(4)] for i in range(4)]
 assert all(sum(T[i][i][j] for i in range(4))==0 for j in range(2))
 assert all(sum(T[i][k][j] for i in range(4) for k in range(4))==0 for j in range(2))
 assert [tuple(T[0][1][j]+T[2][3][j] for j in range(2)),tuple(T[0][2][j]+T[1][3][j] for j in range(2)),tuple(T[0][3][j]+T[1][2][j] for j in range(2))]==B
 coefficients={}
 for perm in permutations(range(4)):
  term={(0,0):R.one}
  for i,j in enumerate(perm):term=mul(term,{(0,0):R.one,(1,0):T[i][j][0],(0,1):T[i][j][1]})
  coefficients=add(coefficients,term)
 assert coefficients[(0,0)]==24 and coefficients.get((1,0),R.zero)==coefficients.get((0,1),R.zero)==0
 pp=list(map(lin,P));dd=list(map(lin,D));bb=list(map(lin,B))
 q={}
 for i in range(3):
  q=add(q,mul(bb[i],bb[i]));q=add(q,scale(mul(pp[i],pp[i]),-1))
  q=add(q,scale(mul(pp[i],dd[i]),-6));q=add(q,scale(mul(dd[i],dd[i]),-6))
 C=add(product(bb),scale(product(pp),-1))
 for i in range(3):C=add(C,mul(bb[i],mul(dd[i],dd[i])))
 for i,j,k in [(0,1,2),(0,2,1),(1,2,0)]:C=add(C,scale(mul(mul(dd[i],dd[j]),pp[k]),2))
 C=add(C,scale(product(dd),6))
 assert all(coefficients.get((2-j,j),R.zero)==q.get((2-j,j),R.zero) for j in range(3))
 assert all(coefficients.get((3-j,j),R.zero)==C.get((3-j,j),R.zero) for j in range(4))
 polys=[];scales=[]
 for degree in (2,3,4):
  for j in range(degree+1):
   g=coefficients[(degree-j,j)];den=1
   for c in g.values():den=math.lcm(den,int(c.denominator))
   g=g*den;content=0
   for c in g.values():content=math.gcd(content,abs(int(c)))
   assert content;polys.append(g/content);scales.append(str(QQ(content,den)))
 script='ring r=0,('+','.join(names)+'),dp;\noption(redSB);\nideal I='+','.join(str(g).replace('**','^') for g in polys)+';\nideal G=std(I);\nshort=0;print("BASIS_SIZE");size(G);print("DIMENSION");dim(G);print("BASIS");G;quit;\n'
 (base/f'trace-Bone-{name}.sing').write_text(script)
 cases[name]={'variables':names,'B_forms':[[str(x) for x in row] for row in B],'D_forms':[[str(x) for x in row] for row in D],'R_forms':[[str(x) for x in row] for row in P],'generators':list(map(str,polys)),'scales_to_actual_permanent_coefficients':scales,'term_counts':[len(g) for g in polys],'D_rank_two_guard':'d0 != 0 or d2 != 0','B_rank_one_exact':True,'matrix_symmetry_trace_and_tangent_verified':True,'opposite_edge_sum_B_coordinates_verified':True,'quadratic_and_cubic_independently_reconstructed':True,'scope':'Full tracezero permanent-flat equations in the B-rank-one normalization. The native input does not impose the displayed D-rank guard; a nonunit ideal may include only guard-failing planes and requires further analysis.'}
 print(name,json.dumps({'terms':cases[name]['term_counts'],'total_terms':sum(cases[name]['term_counts'])}),flush=True)
report={'cases':cases,'coverage':'Choose a plane basis with B(A)=(1,tau,-1-tau),B(B)=0 using a nonzero B coordinate and simultaneous S3 permutation. Because D has rank2, choose nonzero D(B)_j, scale B to make it1, and subtract D(A)_j*B from A to make D(A)_j0. The stabilizer of B coordinate0 leaves two choices j=0 orj=1. Remaining D coefficients are free; rank2 is exactly d0!=0 or d2!=0.','seconds':time.monotonic()-start}
(base/'trace-Bone-systems.json').write_text(json.dumps(report,indent=2)+'\n')
