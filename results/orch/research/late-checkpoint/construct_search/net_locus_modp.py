import itertools,json,sys,time
from pathlib import Path
p=int(sys.argv[1]) if len(sys.argv)>1 else 11
job=Path('/tmp/oec/pequalnp-pilot-78/construct_search')
coords=list(itertools.combinations_with_replacement(range(4),2));edgeids=[i for i,(a,b) in enumerate(coords) if a<b];diagids=[0,4,7,9];edges=[coords[i] for i in edgeids]
def rref(M,aug=False):
 M=[[x%p for x in row] for row in M];n=len(M);m=len(M[0]) if n else 0;row=0;piv=[]
 for c in range(m-int(aug)):
  sel=next((k for k in range(row,n) if M[k][c]),None)
  if sel is None:continue
  M[row],M[sel]=M[sel],M[row];iv=pow(M[row][c],-1,p);M[row]=[(x*iv)%p for x in M[row]]
  for k in range(n):
   if k!=row and M[k][c]:
    mul=M[k][c];M[k]=[(x-mul*y)%p for x,y in zip(M[k],M[row])]
  piv.append(c);row+=1
  if row==n:break
 return M,piv
def rank(M):return len(rref(M)[1])
def kernel(M,n=None):
 if not M:return [[int(i==j) for i in range(n)] for j in range(n)]
 A,piv=rref(M);n=len(M[0]);free=[i for i in range(n) if i not in piv];out=[]
 for f in free:
  v=[0]*n;v[f]=1
  for i,c in enumerate(piv):v[c]=-A[i][f]%p
  out.append(v)
 return out
def solve(M,b):
 A,piv=rref([row+[bb] for row,bb in zip(M,b)],True);n=len(M[0]);v=[0]*n
 if any(not any(row[:n]) and row[n] for row in A):return None
 for i,c in enumerate(piv):v[c]=A[i][n]
 return v
def dot(a,b):return sum(x*y for x,y in zip(a,b))%p
def add(a,b):return [(x+y)%p for x,y in zip(a,b)]
def lincomb(cols,v):return [sum(x*c[i] for x,c in zip(v,cols))%p for i in range(len(cols[0]))]
def qform(V):
 rows=[0]*4;ds=[V[i] for i in diagids];O=[V[i] for i in edgeids]
 for (i,j),x in zip(edges,O):rows[i]+=x;rows[j]+=x
 S=sum(O);R=O[0]*O[5]+O[1]*O[4]+O[2]*O[3]
 return (4*R-sum(x*x for x in ds)-sum(ds)**2*pow(2,-1,p)-4*sum(x*y for x,y in zip(ds,rows)))%p
def cform(H,V):
 hv=[0]*10
 for i,x in zip(edgeids,H):hv[i]=x
 D=[V[i] for i in diagids];O=[V[i] for i in edgeids];hr=[0]*4;vr=[0]*4
 for (i,j),h,v in zip(edges,H,O):hr[i]+=h;hr[j]+=h;vr[i]+=v;vr[j]+=v
 term=sum(D[i]*D[j]*H[edges.index(tuple(k for k in range(4) if k not in (i,j)))] for i,j in edges)
 term+=sum(D[i]*hr[i]*vr[i] for i in range(4))
 for tri in itertools.combinations(range(4),3):
  ix=[edges.index(e) for e in itertools.combinations(tri,2)]
  term+=sum(H[ix[k]]*O[ix[(k+1)%3]]*O[ix[(k+2)%3]] for k in range(3))
 return 2*term%p
def pform(H,V):
 D=[V[i] for i in diagids];O=[V[i] for i in edgeids];hr=[0]*4
 for (i,j),h in zip(edges,H):hr[i]+=h;hr[j]+=h
 term=sum(x*y for x,y in zip(hr,D))**2
 for omit in range(4):
  ix=[edges.index(e) for e in itertools.combinations([i for i in range(4) if i!=omit],2)]
  term+=2*D[omit]*sum(O[ix[k]]*H[ix[(k+1)%3]]*H[ix[(k+2)%3]] for k in range(3))
 term+=sum(D[i]*D[j]*H[edges.index(tuple(k for k in range(4) if k not in (i,j)))]**2 for i,j in edges)
 return term%p
def gram(form,cols):
 values=[form(x) for x in cols];return [[values[i] if i==j else (form(add(cols[i],cols[j]))-values[i]-values[j])*pow(2,-1,p)%p for j in range(len(cols))] for i in range(len(cols))]
def bil(G,x,y):return sum(x[i]*G[i][j]*y[j] for i in range(len(x)) for j in range(len(y)))%p
mons=[m for d in range(4) for m in itertools.product(range(d+1),repeat=3) if sum(m)==d];mi={m:i for i,m in enumerate(mons)};units=[(0,0,0),(1,0,0),(0,1,0),(0,0,1)]
def polyquad(form,cols):
 G=gram(form,cols);ans={(0,0,0):G[0][0]}
 for i in range(3):
  exp=[0]*3;exp[i]=1;ans[tuple(exp)]=2*G[0][i+1]%p
  for j in range(i,3):
   exp=[0]*3;exp[i]+=1;exp[j]+=1;ans[tuple(exp)]=G[i+1][j+1]*(1 if i==j else 2)%p
 return ans
planes=json.loads(Path('/tmp/oec/pequalnp-pilot-78/geometry_search/rowzero/hollow_planes.json').read_text())
def modrat(x):
 from fractions import Fraction
 q=Fraction(x);return q.numerator*pow(q.denominator,-1,p)%p
planes=[[[modrat(v) for v in row] for row in entry['rref']] for entry in planes]
counts={};exceptions=[];total=0;start=time.monotonic()
for b,c,d,e in itertools.product(range(1,p),repeat=4):
 a=1;f=(-1-b-c-d-e)%p
 if not f or (a*f+b*e+c*d)%p or (a*b*d+a*c*e+b*c*f+d*e*f)%p:continue
 H=[a,b,c,d,e,f];total+=1;hr=[0]*4
 for (i,j),h in zip(edges,H):hr[i]+=h;hr[j]+=h
 tau=[d*e*f,b*c*f,a*c*e,a*b*d];tg=[b*d+c*e,a*d+c*f,a*e+b*f,a*b+e*f,a*c+d*f,b*c+d*e]
 lin=[]
 lin.append([1 if i==j else 2 for i,j in coords]);row=[0]*10
 for ix,vv in zip(diagids,hr):row[ix]=-vv
 for ix,vv in zip(edgeids,[f,e,d,c,b,a]):row[ix]=vv
 lin.append(row);row=[0]*10
 for ix,vv in zip(diagids,hr):row[ix]=vv*vv
 for ix,vv in zip(edgeids,tg):row[ix]=2*vv
 lin.append(row);row=[0]*10
 for ix,vv in zip(diagids,tau):row[ix]=vv
 lin.append(row);row=[0]*10;row[1]=1;lin.append(row);N=kernel(lin)
 if len(N)!=5:key=('dim',len(N));counts[str(key)]=counts.get(str(key),0)+1;exceptions.append((H,key));continue
 diff=[[n[diagids[i]]-n[9] for n in N] for i in range(3)];K=kernel(diff)
 if len(K)!=3:key=('P0dim',len(K));counts[str(key)]=counts.get(str(key),0)+1;exceptions.append((H,key));continue
 full=K.copy();W=[]
 for i in range(5):
  unit=[int(i==j) for j in range(5)]
  if rank(full+[unit])>len(full):full.append(unit);W.append(unit)
  if len(full)==5:break
 G3=gram(lambda V:pform(H,V),N);r3=rank(G3)
 assert all(bil(G3,v,w)==0 for v in K for w in K)
 if r3!=4:key=('q3rank',r3);counts[str(key)]=counts.get(str(key),0)+1;exceptions.append((H,key));continue
 # Graph columns W0+sum_iK_i X_i0 and W1+sum_iK_i X_i1.
 linX=[];rhs=[]
 for j,k in [(0,0),(0,1),(1,1)]:
  row=[0]*6
  for i in range(3):
   row[2*i+j]+=bil(G3,K[i],W[k]);row[2*i+k]+=bil(G3,W[j],K[i])
  linX.append(row);rhs.append(-bil(G3,W[j],W[k])%p)
 x0=solve(linX,rhs);nk=kernel(linX)
 if x0 is None or len(nk)!=3:raise ValueError(('graph',H))
 cols=[]
 for j in range(2):
  C0=add(W[j],lincomb(K,[x0[2*i+j] for i in range(3)]));basis=[C0]+[lincomb(K,[n[2*i+j] for i in range(3)]) for n in nk];cols.append([lincomb(N,x) for x in basis])
 for cc in [cols[0],cols[1],[add(x,y) for x,y in zip(cols[0],cols[1])]]:assert all(v%p==0 for v in polyquad(lambda V:pform(H,V),cc).values())
 polys=[]
 for form in [qform,lambda V:cform(H,V)]:
  for cc in [cols[0],cols[1],[add(x,y) for x,y in zip(cols[0],cols[1])]]:polys.append(polyquad(form,cc))
 mac=[]
 for poly in polys:
  for mult in units:
   col=[0]*20
   for mon,coef in poly.items():col[mi[tuple(x+y for x,y in zip(mon,mult))]]=coef%p
   mac.append(col)
 rr=rank(mac);aug=rank(mac+[[int(mon==(0,0,0)) for mon in mons]]);onplane=any(rank(pl+[H])==2 for pl in planes);key=('rank',rr,'aug',aug,'knownline',onplane);counts[str(key)]=counts.get(str(key),0)+1
 if rr<20:exceptions.append((H,key))
print('PRIME',p,'TOTAL',total,'COUNTS',counts,'SECONDS',time.monotonic()-start)
print('EXCEPTIONS',exceptions)
(job/f'net-locus-f{p}.json').write_text(json.dumps({'prime':p,'total':total,'counts':counts,'exceptions':exceptions},indent=2))
