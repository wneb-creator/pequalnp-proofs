from pathlib import Path
import sympy as s,json,hashlib,itertools,time,resource
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
root=Path(__file__).parent;start=time.monotonic()
D,E,F,G,H,A,B,C,S,T,w=s.symbols('D E F G H A B C S T w')
X,Y,Z=s.symbols('X Y Z');unknowns=[D,E,F,G,H,A,B,C,S,T]
I=-D-E-F-G-H-2*(1+S+T)
J=E+H+2*(S-A+C);K=G+I+2*(T-B-C)
M=s.Matrix([[D*X+E*Y,X,S*Y,A*(X-Y)],
 [X,F*X+G*Z,T*Z,B*(X-Z)],
 [S*Y,T*Z,H*Y+I*Z,C*(Y-Z)],
 [A*(X-Y),B*(X-Z),C*(Y-Z),J*(X-Y)+K*(X-Z)]])
assert s.expand(sum(M))==0
assert all(s.expand(v)==0 for v in M.subs({X:1,Y:1,Z:1})[3,:])
oldpath=root.parent/'triangle_concept/triangle-twelve-equations.json';old=json.loads(oldpath.read_text())
loc={str(x):x for x in unknowns+[X,Y,Z]};oldsyms=s.symbols('d0 d1 d3 d5 d7 d8 o0 o1 o3 o5 o7 o8 x y z')
oldenv={str(x):x for x in oldsyms};d0,d1,d3,d5,d7,d8,o0,o1,o3,o5,o7,o8,x,y,z=oldsyms
sub={d0:D,d1:E/S,d3:F,d5:G/T,d7:H/S,d8:I/T,o0:A,o1:-A/S,o3:B,o5:-B/T,o7:C/S,o8:-C/T,x:X,y:S*Y,z:T*Z}
for i in range(4):
 for j in range(4):assert s.cancel(s.sympify(old['matrix'][i][j],locals=oldenv).subs(sub)-M[i,j])==0
print('MATRIX PULLBACK AND TANGENT/KERNEL IDENTITIES PASS',flush=True)
poly=0
for perm in itertools.permutations(range(4)):
 term=1
 for i in range(4):term*=1+M[i,perm[i]]
 poly+=term
poly=s.Poly(s.expand(poly-24),X,Y,Z)
assert all(sum(m)>=2 for m,c in poly.terms())
eq=[];dropped=[]
for m,c in poly.terms():
 if sum(m)==4 and m not in [(2,2,0),(2,0,2),(0,2,2)]:
  dropped.append((m,c));continue
 p=s.Poly(c,*unknowns,domain=s.QQ);content,p=p.clear_denoms()[1].primitive()
 eq.append({'monomial':list(m),'coefficient':str(p.as_expr()),'content':str(content),'terms':len(p.terms())})
# Every retained row is the exact pullback of a reviewed source row;
# omitted quartics only weaken a necessary system, so no sufficiency is used.
oldrows={tuple(r['monomial']):s.sympify(r['coefficient'],locals=oldenv) for r in old['equations'] if r['monomial'] is not None}
for row in eq:
 m=tuple(row['monomial']);c=poly.coeff_monomial(m)
 assert s.cancel(oldrows[m].subs(sub)*S**m[1]*T**m[2]-c)==0
eq.append({'monomial':None,'coefficient':str(w*S*T-1),'content':'1','terms':2,'kind':'nonzero_kernel_coordinates'})
out={'unknowns':[str(x) for x in unknowns+[w]],'equations':eq,'matrix':[[str(M[i,j]) for j in range(4)] for i in range(4)],
 'source':str(oldpath),'source_sha256':hashlib.sha256(oldpath.read_bytes()).hexdigest(),
 'parameter_substitution':{str(k):str(v) for k,v in sub.items()},
 'kernel_in_original_coordinates':['1','S','T'],'scope':'Necessary generic-kernel triangle system only: all three kernel coordinates nonzero, four star kernels forced; keeps six Q, ten C and three quartic coefficients, plus S*T inverse. All edge weights preserved. No ideal or inconsistency verdict.'}
(root/'triangle-generic-eleven-equations.json').write_text(json.dumps(out,indent=2)+'\n')
print('EXPORT',len(eq),'equations',len(unknowns)+1,'variables',sum(r['terms'] for r in eq),'terms','seconds',time.monotonic()-start,flush=True)
print('SHA256',hashlib.sha256((root/'triangle-generic-eleven-equations.json').read_bytes()).hexdigest(),flush=True)
