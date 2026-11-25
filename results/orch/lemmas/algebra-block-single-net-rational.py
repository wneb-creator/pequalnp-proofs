from pathlib import Path
import sympy as s,json,itertools,time,subprocess,resource
job=Path('/tmp/oec/pequalnp-pilot-79');data=json.loads((job/'rank2-block-single-extension.json').read_text());w=s.symbols('w:7');X,Y,rr=s.symbols('X Y rr');fs=[s.Poly(s.sympify(f),*w,extension=s.sqrt(2)) for f in data['polynomials']]
terms=[[(mon,s.expand(c).subs(s.sqrt(2),rr)) for mon,c in f.terms()] for f in fs]
def limits():
 resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3));resource.setrlimit(resource.RLIMIT_CPU,(60,60))
summary=[]
for i,j in reversed(list(itertools.combinations(range(7),2))):
 slots=[(row,k) for row,piv in enumerate([i,j]) for k in range(piv+1,7) if k not in [i,j]];vs=s.symbols('z:'+str(len(slots)));U=s.zeros(2,7);U[0,i]=1;U[1,j]=1
 for slot,v in zip(slots,vs):U[slot]=v
 coeffs=[]
 for ts in terms:
  poly=s.Poly(s.expand(sum(c*s.prod((X*U[0,k]+Y*U[1,k])**e for k,e in enumerate(mon) if e) for mon,c in ts)),X,Y)
  for _,c in poly.terms():
   q=s.Poly(c,*vs,rr).clear_denoms()[1].primitive()[1].as_expr()
   if q!=0:coeffs.append(q)
 coeffs.append(rr**2-2)
 print('CHART',i,j,'variables',len(vs)+1,'equations',len(coeffs),flush=True)
 name=f'block-single-net-{i}-{j}-rational';(job/f'{name}.msolve').write_text(','.join(map(str,(*vs,rr)))+'\n0\n'+',\n'.join(str(c).replace('**','^') for c in coeffs)+'\n')
 with (job/f'{name}.log').open('w') as out:
  try:ret=subprocess.run(['python',str(job/'neogb-run-rational.py'),'-f',str(job/f'{name}.msolve'),'-o',str(job/f'{name}.json'),'-t','1','--info','2','--max-pairs','128','--hash-size','15'],stdout=out,stderr=subprocess.STDOUT,preexec_fn=limits,timeout=65)
  except subprocess.TimeoutExpired:summary.append({'chart':[i,j],'timeout':True});print(summary[-1],flush=True);break
 rec={'chart':[i,j],'returncode':ret.returncode}
 if ret.returncode==0:
  result=json.loads((job/f'{name}.json').read_text());rec.update({'unit':any(len(f)==1 and not any(f[0]['exponents']) and f[0]['coefficient']!=0 for f in result['basis']),'basis_size':len(result['basis']),'seconds':result['seconds']})
 summary.append(rec);print(rec,flush=True)
 (job/'block-single-net-rational-summary.json').write_text(json.dumps(summary,indent=2))
 if ret.returncode!=0:break
