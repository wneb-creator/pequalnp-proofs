from pathlib import Path
import sympy as S, json, collections, resource, hashlib, time
resource.setrlimit(resource.RLIMIT_AS,(384*2**20,384*2**20))
resource.setrlimit(resource.RLIMIT_CPU,(60,65))
base=Path('/tmp/oec/pequalnp-pilot-78');src=base/'geometry_search/rowzero';out=base/'construct_search';start=time.monotonic()
data=json.loads((src/'trace-Bone-systems.json').read_text())['cases']['same-index']
v=S.symbols(' '.join(data['variables']));loc=dict(zip(data['variables'],v));g=[S.sympify(f,locals=loc) for f in data['generators']]
Q=S.Matrix([[1,1,1,1],[1,1,-1,-1],[1,-1,1,-1],[1,-1,-1,1]])/2
matrices=[]
for col in range(2):
 R=[S.sympify(a[col],locals=loc) for a in data['R_forms']];B=[S.sympify(a[col],locals=loc) for a in data['B_forms']];D=[S.sympify(a[col],locals=loc) for a in data['D_forms']]
 M=S.zeros(4)
 for i in range(3):M[i+1,i+1]=B[i];M[0,i+1]=M[i+1,0]=(R[i]+2*D[i])/2
 for i,(a,b) in enumerate([(2,3),(1,3),(1,2)]):M[a,b]=M[b,a]=-R[i]/2
 matrices.append(Q*M*Q.T)
coeff=collections.defaultdict(lambda:S.Integer(0))
for mask in range(1,16):
 cols=[i for i in range(4) if mask>>i&1];term={(0,0):S.Integer((-1)**(4-len(cols)))}
 for i in range(4):
  row=[S.Integer(len(cols))]+[S.expand(sum(M[i,j] for j in cols)) for M in matrices];nxt=collections.defaultdict(lambda:S.Integer(0))
  for e,c in term.items():
   nxt[e]+=c*row[0]
   nxt[e[0]+1,e[1]]+=c*row[1]
   nxt[e[0],e[1]+1]+=c*row[2]
  term=nxt
 for e,c in term.items():coeff[e]+=c
exponents=[(n-j,j) for n in (2,3,4) for j in range(n+1)]
for e,f,scale in zip(exponents,g,data['scales_to_actual_permanent_coefficients']):assert S.expand(coeff[e]-S.sympify(scale)*f)==0,e
assert S.expand(coeff[0,0]-24)==0 and S.expand(coeff[1,0])==0 and S.expand(coeff[0,1])==0
p1,p3,p5,d0,d1,d2,d3,tau=[loc[k] for k in ['p1','p3','p5','d0','d1','d2','d3','tau']]
k=[S.expand(g[i].subs({d1:0,d3:0})) for i in [2,6,11]]
F=5*p1**2+14*p1+10
assert S.rem(k[2],k[0],p3)==4*F
assert S.expand(k[1]+p1*p3*p5)==0
assert S.expand(k[0]+p3**2+p5**2-4*(p1+1)**2+F)==0
alpha=(-7+S.I)/5;assert S.expand(F.subs(p1,alpha))==0 and S.expand(F.subs(p1,S.conjugate(alpha)))==0
first=json.loads((src/'trace-Bone-single-D.json').read_text());sub={loc[k]:S.sympify(z,locals=loc) for k,z in first['substitution'].items()}
eq=[S.expand(f.subs(sub,simultaneous=True)) for f in g];sol={loc[k]:S.sympify(z,locals=loc) for k,z in first['solution'].items()}
M,rhs=S.linear_eq_to_matrix([eq[i] for i in [1,5,10]],[loc[k] for k in ['p0','p2','p4']]);assert S.expand(M.det())!=0
res=[S.expand(f.subs(sol,simultaneous=True)) for f in eq];saved={r['index']:S.sympify(r['polynomial'],locals=loc) for r in first['residuals']}
for i,f in enumerate(res):assert S.expand(f-saved.get(i,0))==0
last=json.loads((src/'trace-Bone-single-D-eliminate.json').read_text());v0=-S.Rational(93,116)-11*S.I/29;kappa=(2+24*S.I)/25
assert S.expand(res[4]-kappa*d0*(d2-v0))==0
assert S.expand(res[3].subs(d0,0)+(tau+1)*(d2**2+tau))==0
for name,subcase in [('u-zero-tau-minus-one',{d0:0,tau:-1}),('u-zero-tau-minus-v-squared',{d0:0,tau:-d2**2})]:
 branch=last['branches'][name];ff=[S.sympify(z,locals=loc) for z in branch['generators']];cc=[S.sympify(z,locals=loc) for z in branch['multipliers']]
 for i,f in zip([0,9],ff):assert S.expand(res[i].subs(subcase,simultaneous=True)-f)==0
 assert S.expand(sum(a*b for a,b in zip(ff,cc))-1)==0
branch=last['branches']['v-fixed-u-nonzero'];U,T=S.symbols('U T');local=loc|{'U':U,'T':T};ff=[S.sympify(z,locals=local) for z in branch['generators']]
for actual,f in zip([res[0],res[9],S.cancel(res[8]/d0)],ff):assert S.expand(actual.subs(d2,v0)-f.subs({U:d0**2,T:tau**2},simultaneous=True))==0
M,rhs=S.linear_eq_to_matrix(ff,[U,T,tau]);ss=S.Matrix([S.sympify(z,locals=local) for z in branch['linear_solution'][0]])
assert S.expand(M.det())!=0 and (M*ss-rhs).applyfunc(S.expand)==S.zeros(3,1)
contradiction=S.expand(ss[1]-ss[2]**2);assert contradiction!=0 and not contradiction.free_symbols
assert S.expand(contradiction-S.sympify(branch['T_minus_tau_squared']))==0
files=['trace-Bone-systems.json','generate_trace_Bone.py','trace_Bone_single_D.py','trace-Bone-single-D.json','trace_Bone_single_D_eliminate.py','trace-Bone-single-D-eliminate.json']
report={'verdict':'PASS independent symbolic Ryser and exact identity audit','scope':'Same-index B-rank-one trace-zero two-plane with kernel D supported on one coordinate only. No generic B-rank-one or global contradiction.','checks':{'actual_permanent_coefficients':12,'kernel_quartic_remainder':'4*(5*p1^2+14*p1+10)','kernel_support_normalization':'axis1/2 swap and simultaneous sign flip preserve D=(1,0,0), B=(1,tau,-1-tau); conjugation covers both roots','linear_system_invertible':True,'bezout_branches':2,'incompatible_linear_branch':True},'files':[{'path':str((src/n).relative_to(base)),'sha256':hashlib.sha256((src/n).read_bytes()).hexdigest()} for n in files],'seconds':time.monotonic()-start}
(out/'Bone-single-D-independent-audit.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report),flush=True)
