from pathlib import Path
import sympy as s,itertools,json
job=Path('/tmp/oec/pequalnp-pilot-79');a=s.symbols('a');w=s.symbols('w0:6');ii=s.symbols('ii')
A=s.Matrix([[1,-1,s.I,-s.I],[-1,s.I,-s.I,1],[s.I,-s.I,1,-1],[-s.I,1,-1,s.I]])
B=s.Matrix([[0,-s.I*(w[2]+w[3])-w[5],w[1],w[2]],[-s.I*(w[2]+w[3])-w[5],w[0],w[3],w[4]],[w[1],w[3],2*s.I*(w[2]+w[3])-2*w[4],w[5]],[w[2],w[4],w[5],-w[0]-2*w[1]-2*w[2]-2*w[3]]])
M=s.ones(4)+a*A+B
F=s.Poly(s.expand(sum(s.prod(M[i,p[i]] for i in range(4)) for p in itertools.permutations(range(4))))-24,a,*w)
ps=[]
for j,k in [(0,2),(1,2),(2,2),(0,3),(1,3),(0,4)]:
 f=s.expand(sum(co*s.prod(v**p for v,p in zip(w,mon[1:])) for mon,co in F.terms() if mon[0]==j and sum(mon[1:])==k))
 assert f!=0
 f=s.Poly(s.expand(f).subs(s.I,ii),*w,ii).primitive()[1].as_expr();ps.append(f)
print('equations',[(s.Poly(p,*w,ii).total_degree(),len(s.Poly(p,*w,ii).terms())) for p in ps],flush=True)
for k in range(6):
 variables=[v for v in w if v!=w[k]]+[ii];polys=[s.expand(p.subs(w[k],1)) for p in ps]+[ii**2+1]
 name=job/f'dense-boundary-chart-{k}.msolve'
 name.write_text(','.join(map(str,variables))+'\n0\n'+',\n'.join(str(p).replace('**','^') for p in polys)+'\n')
(job/'dense-boundary-equations.json').write_text(json.dumps({'variables':[str(v) for v in w]+['ii'],'equations':[str(p) for p in ps],'basis':str(B)},indent=2))
print('inputs ready',flush=True)
