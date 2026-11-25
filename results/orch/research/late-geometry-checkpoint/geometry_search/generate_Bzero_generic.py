import itertools,json,math,time
from pathlib import Path
from sympy.polys.rings import ring
from sympy.polys.domains import QQ
base=Path('/tmp/oec/pequalnp-pilot-78/geometry_search/tracezero_Bzero_generic');start=time.monotonic()
R,a,b,x,y,z=ring('a,b,x,y,z',QQ);lam=[x,y,z];product=x*y*z-2
H=[[1,1,1,1],[1,1,-1,-1],[1,-1,1,-1],[1,-1,-1,1]]
cases=[('identity',(0,1,2),(0,1)),('swap-pair',(1,0,2),(0,1)),('swap-cross',(1,0,2),(0,2)),('cycle',(1,2,0),(0,1))]
def mul(A,B):
 out={}
 for ea,ca in A.items():
  for eb,cb in B.items():
   e=tuple(x+y for x,y in zip(ea,eb));out[e]=out.get(e,R.zero)+ca*cb
 return out
reports=[]
for name,perm,pair in cases:
 V=[None]*3;V[pair[0]]=(R.one,R.zero);V[pair[1]]=(R.zero,R.one);V[next(i for i in range(3) if i not in pair)]=(a,b)
 U=[tuple(lam[i]*v for v in V[perm[i]]) for i in range(3)]
 D=[tuple(U[i][j]-V[i][j] for j in range(2)) for i in range(3)]
 Tp=[[(R.zero,R.zero) for j in range(4)] for i in range(4)]
 for i in range(3):Tp[0][i+1]=Tp[i+1][0]=tuple(v/2 for v in U[i])
 for i,(i0,i1) in enumerate([(2,3),(1,3),(1,2)]):Tp[i0][i1]=Tp[i1][i0]=tuple((U[i][j]-2*V[i][j])/2 for j in range(2))
 T=[[tuple(sum(H[i][aa]*H[j][bb]*Tp[aa][bb][v] for aa in range(4) for bb in range(4))/4 for v in range(2)) for j in range(4)] for i in range(4)]
 coeff={}
 for p in itertools.permutations(range(4)):
  term={(0,0):R.one}
  for i in range(4):term=mul(term,{(0,0):R.one,(1,0):T[i][p[i]][0],(0,1):T[i][p[i]][1]})
  for e,c in term.items():coeff[e]=coeff.get(e,R.zero)+c
 assert coeff[(0,0)]==24 and coeff[(1,0)]==coeff[(0,1)]==0
 vprod={(0,0):R.one}
 for row in V:vprod=mul(vprod,{(1,0):row[0],(0,1):row[1]})
 for i in range(4):assert coeff[(3-i,i)]==product*vprod.get((3-i,i),R.zero)
 exps=[(d-i,i) for d in (2,4) for i in range(d+1)]
 polys=[product];scales=['1']
 for e in exps:
  f=coeff[e];den=1
  for c in f.values():den=math.lcm(den,int(c.denominator))
  f=f*den;content=0
  for c in f.values():content=math.gcd(content,abs(int(c)))
  assert content;polys.append(f/content);scales.append(str(QQ(content,den)))
 script='ring r=0,(a,b,x,y,z),dp;\noption(redSB);\nideal I='+','.join(str(f).replace('**','^') for f in polys)+';\nideal G=std(I);\nprint("SIZE");size(G);print("DIMENSION");dim(G);print("BASIS");short=0;G;print("COMPLETED_EXACT_RUN");quit;\n'
 (base/(name+'.sing')).write_text(script)
 record={'name':name,'permutation':perm,'independent_r_coordinate_pair':pair,'r':[[str(v) for v in row] for row in V],'U':[[str(v) for v in row] for row in U],'D':[[str(v) for v in row] for row in D],'generators':list(map(str,polys)),'scales_to_permanent_coefficients':scales,'term_counts':[len(f) for f in polys],'cubic_identity_exact':True,'scope':'Generic UFD branch. Allr_i are assumed nonzero asbinaryforms incoverage, but thispolynomialsystem deliberately doesnotexclude(a,b)=(0,0); any extra boundary component mustbehandled separately. No D-rank guard imposed; a unit ideal wouldprove the stronger emptiness.'}
 reports.append(record);print(json.dumps({k:record[k] for k in ('name','term_counts','cubic_identity_exact')}),flush=True)
(base/'systems.json').write_text(json.dumps({'variables':['a','b','x','y','z'],'cases':reports,'coverage':'Nonzero binary factors pair underUFD: U_i=lam_i*r_perm(i), productlam=2. D-rank2forcesr-rank2. SimultaneousS3conjugacy leavesidentity,transposition,3cycle; centralizers actoncoordinatepairs withorbitcounts1,2,1. Zero-factor boundaries areseparate.','seconds':time.monotonic()-start},indent=2)+'\n')
