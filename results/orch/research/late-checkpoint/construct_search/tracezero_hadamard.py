from pathlib import Path
import sympy as S,json,resource,time,itertools,random
resource.setrlimit(resource.RLIMIT_AS,(512*2**20,512*2**20));resource.setrlimit(resource.RLIMIT_CPU,(60,65))
base=Path('/tmp/oec/pequalnp-pilot-78/construct_search');start=time.monotonic()
a,b,c,d,e,f,x,y,z=S.symbols('a b c d e f x y z');ss,tt=S.symbols('s t');v=S.symbols('p0:6 b0:4 k l');p=v[:6];bs=v[6:10];k,l=v[10:]
D=[ss,tt,k*ss+l*tt];P=[p[2*i]*ss+p[2*i+1]*tt for i in range(3)];B=[bs[0]*ss+bs[1]*tt,bs[2]*ss+bs[3]*tt];B+=[-sum(B)]
sub={a:B[0],b:B[1],c:B[2],x:(P[0]-D[0])/2,y:(P[1]-D[1])/2,z:(P[2]-D[2])/2,f:(3*D[0]-P[0])/2,e:(3*D[1]-P[1])/2,d:(3*D[2]-P[2])/2}
raw=[S.sympify(t) for t in (base/'hadamard-polynomials.txt').read_text().splitlines()];coeff=[];metadata=[]
for degree,expr in zip([2,3,4],raw):
 expr=S.Poly(S.expand(expr.subs(sub,simultaneous=True)),ss,tt)
 for i in range(degree+1):
  g=S.Poly(expr.coeff_monomial(ss**(degree-i)*tt**i),*v);den,h=g.clear_denoms();content,h=h.primitive();coeff.append(h.as_expr());metadata.append({'degree':degree,'t_power':i,'denominator':str(den),'content':str(content),'terms':len(h.terms())})
print('EQUATIONS',len(coeff),'TERMS',sum(m['terms'] for m in metadata),'COUNTS',[m['terms'] for m in metadata],flush=True)
q=S.Matrix([[1,1,1,1],[1,1,-1,-1],[1,-1,1,-1],[1,-1,-1,1]])/2
Tprime=S.Matrix([[0,x,y,z],[x,a,d,e],[y,d,b,f],[z,e,f,c]])
rng=random.Random(78231);perms=list(itertools.permutations(range(4)));scales={2:set(),3:set(),4:set()};checked=0
for test in range(4):
 point={w:rng.randrange(-2,3) for w in v};map0={w:S.expand(g.subs(point)) for w,g in sub.items()};T=q*Tprime.subs(map0,simultaneous=True)*q.T
 direct=S.Poly(S.expand(sum(S.prod(1+T[i,j] for i,j in enumerate(perm)) for perm in perms)-24),ss,tt)
 assert direct.coeff_monomial(ss)==direct.coeff_monomial(tt)==0
 for g,m in zip(coeff,metadata):
  deg=m['degree'];it=m['t_power'];actual=direct.coeff_monomial(ss**(deg-it)*tt**it);expected=g.subs(point)*S.Rational(m['content'])/S.Rational(m['denominator'])
  if expected:scales[deg].add(actual/expected)
  else:assert actual==0
  checked+=1
assert all(len(x)==1 for x in scales.values());print('DIRECT_PERMANENT_AUDIT_PASS',checked,'SCALES',{d:str(next(iter(v))) for d,v in scales.items()},flush=True)
data={'variables':[str(t) for t in v],'equations':[str(g).replace('**','^') for g in coeff],'metadata':metadata,'normalization':'D=(s,t,k*s+l*t); P arbitrary3x2; B tracezero3x2; T=Q*Tprime*Q^t','term_count':sum(m['terms'] for m in metadata),'audit_comparisons':checked,'audit_scales':{str(d):str(next(iter(v))) for d,v in scales.items()}}
(base/'tracezero-hadamard.json').write_text(json.dumps(data,separators=(',',':'))+'\n')
for char in [0,101]:
 (base/f'tracezero-hadamard-{char}.sing').write_text('ring r='+str(char)+',('+','.join(map(str,v))+'),dp;\noption(redSB);\nideal I='+','.join(data['equations'])+';\nideal G=std(I);\nprint("BASIS_SIZE");size(G);print("DIMENSION");dim(G);print("BASIS");G;quit;\n')
print('SECONDS',time.monotonic()-start,flush=True)
