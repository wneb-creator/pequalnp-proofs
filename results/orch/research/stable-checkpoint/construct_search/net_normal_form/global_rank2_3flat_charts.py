from pathlib import Path
from fractions import Fraction as Q
from functools import reduce
import hashlib,itertools,json,math,random,resource,time
OUT=Path('/tmp/oec/pequalnp-pilot-78/construct_search/net_normal_form');START=time.monotonic()
resource.setrlimit(resource.RLIMIT_AS,(512*2**20,512*2**20));resource.setrlimit(resource.RLIMIT_CPU,(120,123));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
SLOTS=[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)];EDGES=list(itertools.combinations(range(4),2));SLOT_INDEX={xy:i for i,xy in enumerate(SLOTS)};ZERO=(0,)*19
GROUP=[(0,1,2,3),(1,0,2,3),(0,1,3,2),(1,0,3,2)]
ORBIT_LIST=[sorted({tuple(sorted((g[i],g[j]))) for g in GROUP}) for i,j in [(0,1),(2,3),(0,2)]]
assert [len(x) for x in ORBIT_LIST]==[1,1,4] and set(sum(ORBIT_LIST,[]))==set(EDGES)

def add(poly,mon,value):
 if value:poly[mon]=poly.get(mon,0)+value

def multiply(left,right):
 out={}
 for m,c in left.items():
  for n,d in right.items():add(out,tuple(x+y for x,y in zip(m,n)),c*d)
 return {m:c for m,c in out.items() if c}

def linear_text(terms):
 parts=[]
 for index,value in sorted(terms.items()):
  if not value:continue
  coeff=Q(value,2)
  if index<0:parts.append(str(coeff));continue
  var='x'+str(index)
  if coeff==1:parts.append(var)
  elif coeff==-1:parts.append('-'+var)
  else:parts.append(str(coeff)+'*'+var)
 return '+'.join(parts).replace('+-','-') or '0'

def poly_text(poly):
 terms=[]
 for mon,coef in sorted(poly.items(),reverse=True):
  variables=['x'+str(i)+(('^'+str(e)) if e!=1 else '') for i,e in enumerate(mon) if e]
  product='*'.join(variables)
  if not product:terms.append(str(coef))
  elif coef==1:terms.append(product)
  elif coef==-1:terms.append('-'+product)
  else:terms.append(str(coef)+'*'+product)
 return '+'.join(terms).replace('+-','-') or '0'

def eval_poly(poly,assignment):
 powers=[[Q(1)]+[x**n for n in range(1,5)] for x in assignment];total=Q(0)
 for mon,coef in poly.items():
  term=Q(coef)
  for i,e in enumerate(mon):
   if e:term*=powers[i][e]
  total+=term
 return total

def ryser(matrix):
 total=Q(0)
 for mask in range(1,16):
  product=Q(1)
  for row in matrix:product*=sum((row[j] for j in range(4) if mask>>j&1),Q(0))
  total+=(-1)**mask.bit_count()*product
 return total

charts=[]
for name,pivot in [('within01',(0,1)),('within23',(2,3)),('cross02',(0,2))]:
 pivot_index=EDGES.index(pivot);eliminated=max(i for i in range(6) if i!=pivot_index);free=[i for i in range(6) if i not in [pivot_index,eliminated]]
 # Each sparse linear form stores twice the actual matrix entry. Index -1 is its constant.
 basis=[[{} for _ in range(10)] for _ in range(3)]
 basis[0][0]={-1:2};basis[0][4]={};basis[0][7]={0:2};basis[0][9]={1:2}
 basis[1][0]={};basis[1][4]={-1:2};basis[1][7]={2:2};basis[1][9]={3:2}
 for k in range(3):
  for j,edge_index in enumerate(free):basis[k][SLOT_INDEX[EDGES[edge_index]]]={4+4*k+j:2}
  basis[k][SLOT_INDEX[pivot]]={-1:2} if k==2 else {}
  term={-1:-2 if k==2 else -1}
  if k<2:term[2*k]=-1;term[2*k+1]=-1
  for j in range(4):term[4+4*k+j]=-2
  basis[k][SLOT_INDEX[EDGES[eliminated]]]=term
 entries=[]
 for i,j in SLOTS:
  index=SLOT_INDEX[i,j];poly={ZERO:2}
  for k in range(3):
   for variable,value in basis[k][index].items():
    mon=[0]*19;mon[16+k]=1
    if variable>=0:mon[variable]=1
    add(poly,tuple(mon),value)
  entries.append({m:c for m,c in poly.items() if c})
 permanent={}
 for perm in itertools.permutations(range(4)):
  term={ZERO:1}
  for i,j in enumerate(perm):term=multiply(term,entries[SLOT_INDEX[tuple(sorted((i,j)))]] )
  for mon,coef in term.items():add(permanent,mon,coef)
 permanent={m:c for m,c in permanent.items() if c};by_spectral={}
 for mon,coef in permanent.items():add(by_spectral.setdefault(mon[16:],{}),mon[:16],coef)
 assert by_spectral.pop((0,0,0))=={(0,)*16:384}
 assert all(sum(mon)>=2 for mon in by_spectral)
 expected=[mon for degree in [2,3,4] for mon in itertools.product(range(degree+1),repeat=3) if sum(mon)==degree]
 assert set(by_spectral)==set(expected) and len(expected)==31
 equations=[];primitive=[];scales=[]
 for mon in expected:
  poly=by_spectral[mon];content=reduce(math.gcd,(abs(c) for c in poly.values()));sign=1 if poly[max(poly)]>0 else -1
  clean={m:sign*c//content for m,c in poly.items()};scale=Q(16*sign,content)
  assert all(Q(clean[m])==scale*Q(poly[m],16) for m in poly)
  equations.append({'parameter_exponents':mon,'scale_from_permanent_coefficient':str(scale),'polynomial':poly_text(clean),'terms':[[coef,list(m)] for m,coef in sorted(clean.items(),reverse=True)],'degree':max(sum(m) for m in clean),'term_count':len(clean)})
  primitive.append(clean);scales.append(scale)
 rng=random.Random(231000+pivot_index);assignments=[]
 for k in range(8):assignments.append([Q(rng.randrange(-3,4),1 if k<4 else rng.choice([1,2,3])) for _ in range(16)])
 spectral=[(Q(0),Q(0),Q(0)),(Q(1),Q(0),Q(0)),(Q(0),Q(1),Q(0)),(Q(0),Q(0),Q(1)),(Q(-1),Q(0),Q(0)),(Q(0),Q(-1),Q(0)),(Q(0),Q(0),Q(-1)),(Q(1),Q(1),Q(1)),(Q(2),Q(-1),Q(3)),(Q(-2),Q(3),Q(1)),(Q(1,2),Q(-2,3),Q(3,2)),(Q(-3,2),Q(1,3),Q(2,3))]
 checks=0
 for assignment in assignments:
  mats=[]
  for k in range(3):
   mat=[[Q(0) for _ in range(4)] for _ in range(4)]
   for slot,(i,j) in enumerate(SLOTS):
    value=sum((Q(coef,2)*(Q(1) if index==-1 else assignment[index]) for index,coef in basis[k][slot].items()),Q(0));mat[i][j]=mat[j][i]=value
   assert sum(sum(row) for row in mat)==0;mats.append(mat)
  assert [mats[k][0][0] for k in range(3)]==[1,0,0] and [mats[k][1][1] for k in range(3)]==[0,1,0]
  assert all(mats[2][i][i]==0 for i in range(4))
  assert [mats[k][pivot[0]][pivot[1]] for k in range(3)]==[0,0,1]
  coefficients=[eval_poly(poly,assignment)/scale for poly,scale in zip(primitive,scales)]
  for point in spectral:
   matrix=[[Q(1)+sum((point[k]*mats[k][i][j] for k in range(3)),Q(0)) for j in range(4)] for i in range(4)]
   predicted=Q(24)+sum((coefficient*point[0]**mon[0]*point[1]**mon[1]*point[2]**mon[2] for coefficient,mon in zip(coefficients,expected)),Q(0))
   assert predicted==ryser(matrix),(name,assignment,point,predicted,ryser(matrix));checks+=1
 chart={'name':name,'pivot_edge':pivot,'eliminated_edge':EDGES[eliminated],'free_edges':[EDGES[i] for i in free],'variables':['x'+str(i) for i in range(16)],'variable_roles':{'V_diagonal22_33':['x0','x1'],'W_diagonal22_33':['x2','x3'],'V_free_edges':['x'+str(i) for i in range(4,8)],'W_free_edges':['x'+str(i) for i in range(8,12)],'H_free_edges':['x'+str(i) for i in range(12,16)]},'basis_coefficients':[[linear_text(basis[k][i]) for k in range(3)] for i in range(10)],'basis_twice_sparse':[[[[index,coef] for index,coef in sorted(basis[k][i].items())] for k in range(3)] for i in range(10)],'equations':equations,'direct_ryser_audit_checks':checks,'audit_assignments':[[str(x) for x in point] for point in assignments],'audit_spectral_points':[[str(x) for x in point] for point in spectral]}
 charts.append(chart)
 (OUT/f'global-rank2-{name}.ms').write_text(','.join(chart['variables'])+'\n0\n'+',\n'.join(e['polynomial'] for e in equations)+'\n')
 print(json.dumps({'chart':name,'variables':16,'equations':31,'terms':sum(e['term_count'] for e in equations),'max_terms':max(e['term_count'] for e in equations),'checks':checks,'elapsed_seconds':time.monotonic()-START}),flush=True)
coverage='Every 3-dimensional flat of diagonal projection rank 2 has a 1-dimensional hollow kernel. Choose an independent pair of diagonal coordinate restrictions and use S4 to take the unordered pair to {0,1}; choose V,W with those diagonal restrictions equal to I2. Choose a nonzero edge of a hollow kernel vector H. The stabilizer S2 x S2 of {0,1} has the three edge orbits 01, 23, and the four cross edges; normalize its representative to 1, compensating a 0/1 swap by swapping V,W. Subtract the pivot-edge multiples of H from V,W, making their pivot entries 0. The tangent equation sum_all_entries=0 eliminates one other off-diagonal entry of each basis vector. All remaining entries are exactly the 16 free parameters. Conversely the displayed three matrices are always independent by their two diagonal pivots and the hollow edge pivot, and their diagonal image has rank 2. Their first permanent coefficients vanish identically; the 31 degree 2/3/4 equations are therefore equivalent to constant permanent 24 on their span.'
payload={'status':'PASS','scope':'Complete three-chart cover of global symmetric 3-flats with diagonal projection rank 2 and permanent(J+T)=24. No claim of existence or inconsistency.','coordinate_order':SLOTS,'spectral_variables':['s','t','u'],'generation_formula':'24 permutation terms applied to2J+s(2V)+t(2W)+u(2H), then divide permanent coefficients by16 and primitive-integer normalize.','independent_numeric_audit_formula':'16-subset Ryser formula on exact rational matrices.','stabilizer_permutations':GROUP,'edge_orbits':ORBIT_LIST,'coverage_argument':coverage,'charts':charts,'total_ryser_audit_checks':sum(c['direct_ryser_audit_checks'] for c in charts),'seconds':time.monotonic()-START,'max_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
(OUT/'global-rank2-charts.json').write_text(json.dumps(payload,separators=(',',':'))+'\n')
summary={'status':'PASS','charts':3,'variables_each':16,'equations_each':31,'total_ryser_audit_checks':payload['total_ryser_audit_checks'],'seconds':payload['seconds'],'max_rss_kib':payload['max_rss_kib'],'chart_json_bytes':(OUT/'global-rank2-charts.json').stat().st_size}
(OUT/'global-rank2-generation-summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary),flush=True)
