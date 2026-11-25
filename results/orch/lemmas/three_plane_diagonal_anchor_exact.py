from pathlib import Path
import itertools as it,json,math,functools,time,resource,hashlib,sympy as s
resource.setrlimit(resource.RLIMIT_CORE,(0,0));resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(110,110));job=Path('/tmp/oec/pequalnp-pilot-79');start=time.monotonic();idx=range(4);zero=(0,)*4
powers=[4,16,112,928,8224]
for n in range(5,32):powers.append(16*powers[-1]-72*powers[-2]+96*powers[-3]-24*powers[-4])
def partitions(items):
 if not items:yield [];return
 first,*rest=items
 for p in partitions(rest):
  yield [(first,)]+p
  for i in range(len(p)):yield p[:i]+[(first,)+p[i]]+p[i+1:]
parts=list(partitions(list(idx)));assert len(parts)==15
@functools.lru_cache(None)
def average_numerator(exponents):
 return sum(math.prod((-1)**(len(block)-1)*math.factorial(len(block)-1)*powers[sum(exponents[i] for i in block)] for block in partition) for partition in parts)
def avgnum(e):return average_numerator(tuple(sorted(e)))
def add(*exps):return tuple(map(sum,zip(*exps)))
basis=[]
for k in range(10):
 entries={}
 for i in idx:
  for j in idx:
   terms=[]
   if k<4 and i==j:
    mon=[0]*4;mon[i]=k;terms=[(tuple(mon),1)]
   elif k>=4 and i!=j:
    degree=k-4
    for e in range(degree+1):
     mon=[0]*4;mon[i]=e;mon[j]=degree-e;terms.append((tuple(mon),math.comb(degree,e)))
   entries[i,j]=terms
 basis.append(entries)
Gnum=[[0]*10 for _ in idx];Hnum=[[[0]*10 for _ in range(10)] for _ in range(3)]
for perm in it.permutations(idx):
 for i in idx:
  fixed=[k for k in idx if k!=i and perm[k]==k]
  for size in range(len(fixed)+1):
   for selected in it.combinations(fixed,size):
    mon=tuple(int(k in selected) for k in idx);degree=3-size
    for b in range(10):
     for e,c in basis[b][i,perm[i]]:Gnum[degree][b]+=c*avgnum(add(e,mon))
 for i,j in it.combinations(idx,2):
  fixed=[k for k in idx if k not in [i,j] and perm[k]==k]
  for size in range(len(fixed)+1):
   for selected in it.combinations(fixed,size):
    mon=tuple(int(k in selected) for k in idx);degree=2-size
    for b in range(10):
     for c in range(b,10):
      total=0
      for e,ce in basis[b][i,perm[i]]:
       for f,cf in basis[c][j,perm[j]]:total+=ce*cf*avgnum(add(e,f,mon))
      for e,ce in basis[c][i,perm[i]]:
       for f,cf in basis[b][j,perm[j]]:total+=ce*cf*avgnum(add(e,f,mon))
      Hnum[degree][b][c]+=total
assert all(x%24==0 for row in Gnum for x in row);Gcoef=s.Matrix([[x//24 for x in row] for row in Gnum]);Hs=[]
for H in Hnum:
 for i in range(10):
  for j in range(i,10):assert H[i][j]%24==0;H[j][i]=H[i][j]
 Hs.append(s.Matrix([[x//24 for x in row] for row in H]))
Geval=s.Matrix([[sum(j**k*Gcoef[k,b] for k in idx) for b in range(10)] for j in idx]);gauge=s.Matrix([[int(i==4) for i in range(10)]]);reduced,pivots=Geval.col_join(gauge).rref();free=[i for i in range(10) if i not in pivots];assert len(free)==5;C=s.zeros(5,10)
for i,j in enumerate(free):
 C[i,j]=1
 for row,pivot in enumerate(pivots):C[i,pivot]=-reduced[row,j]
assert C*Geval.T==s.zeros(5,4) and C[:,4]==s.zeros(5,1)
Q=[C*Hs[i]*C.T for i in [2,1,0]]
mod=lambda x,p:int(s.numer(x))%p*pow(int(s.denom(x))%p,-1,p)%p
finite_path=job/'fresh_diagonal_anchor.json';finite_sha=hashlib.sha256(finite_path.read_bytes()).hexdigest();finite=json.loads(finite_path.read_text());assert hashlib.sha256(finite_path.read_bytes()).hexdigest()==finite_sha;p=finite['p'];assert list(pivots)==finite['pivots'] and free==finite['free'];assert [[mod(v,p) for v in Geval.row(i)] for i in idx]==finite['G'];assert [[mod(v,p) for v in C.row(i)] for i in range(5)]==finite['coords'];assert [[[mod(v,p) for v in q.row(i)] for i in range(5)] for q in Q]==finite['Q']
H0,H1,H2=Q[::-1];P=H0.inv()*H1;R=H0.inv()*H2;commutator=P*R-R*P
L=[H0,H1,H1*P,P.T*H1*P,H2,H2*P,P.T*H2*P];m2=list(it.combinations_with_replacement(range(5),2));m3=list(it.combinations_with_replacement(range(5),3));ind={m:i for i,m in enumerate(m3)};M=s.zeros(35,35)
for q,mat in enumerate(L):
 for x in range(5):
  for i,j in m2:M[5*q+x,ind[tuple(sorted((i,j,x)))]]+=mat[i,j] if i==j else mat[i,j]+mat[j,i]
assert [[mod(v,p) for v in M.row(i)] for i in range(35)]==finite['matrix']
serialize=lambda mat:[[[int(v.p),int(v.q)] for v in mat.row(i)] for i in range(mat.rows)]
result={'classification':'Exact rational diagonal-anchor gradient and Hessian net, independently matched to finite-field computation; not Lean checked','power_sums':powers,'gradient_coefficients':serialize(Gcoef),'gradient_evaluations':serialize(Geval),'pivots':list(pivots),'free':free,'kernel_coordinates':serialize(C),'Q_j2_j1_j0':[serialize(q) for q in Q],'H0det':[int(H0.det().p),int(H0.det().q)],'commutator_zero':commutator==s.zeros(5),'P':serialize(P),'R':serialize(R),'moment35':serialize(M),'modular_crosscheck':{'prime':p,'H0det':mod(H0.det(),p),'moment35_det':finite['det35'],'all_gradient_kernel_hessian_and_moment_entries_match':True},'seconds':time.monotonic()-start}
assert hashlib.sha256(finite_path.read_bytes()).hexdigest()==finite_sha;result['finite_input_sha256']=finite_sha
(job/'three-plane-diagonal-anchor-exact.json').write_text(json.dumps(result,separators=(',',':'))+'\n');print(json.dumps({'seconds':result['seconds'],'moment_entries':1225,'H0det':result['H0det'],'commutator_zero':result['commutator_zero'],'modular_crosscheck':result['modular_crosscheck'],'finite_input_sha256':finite_sha}),flush=True)
