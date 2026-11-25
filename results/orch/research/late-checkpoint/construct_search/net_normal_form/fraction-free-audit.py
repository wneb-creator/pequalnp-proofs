from pathlib import Path
import runpy,sys,sympy as s,resource,json,time
resource.setrlimit(resource.RLIMIT_AS,(512*2**20,512*2**20));resource.setrlimit(resource.RLIMIT_CPU,(120,123))
p=Path('/tmp/oec/pequalnp-pilot-78/construct_search/net_normal_form');sys.argv=[str(p/'fraction-free-fixed-check.py'),'normalized'];ns=runpy.run_path(str(p/'fraction-free-fixed-check.py'))
H,W,x,y,k,l,m=[ns[v] for v in ['H','W','x','y','k','l','m']];u,z=s.symbols('U Z');perms=list(ns['itertools'].permutations(range(4)))
exports={}
for tag in ['10','01','11']:
 lines=(p/f'fraction-free-{tag}.stdout').read_text().splitlines();res=json.loads((p/f'fraction-free-{tag}.result.json').read_text());assert res['exit']==0 and 'DONE' in lines and not any(line.startswith('   ?') for line in lines)
 exports[tag]={name:compile(lines[lines.index(name)+1].replace('^','**'),'<generated polynomial>','eval') for name in ['EQUATION_Q','EQUATION_C']}
points=[(0,0,0),(1,0,0),(0,1,0),(0,0,1),(-1,2,-1),(2,-1,3),(3,2,1),(-2,-3,1),(1,4,-2),(4,0,-1),(-3,1,2),(2,3,-4)]
ratios={};checks=0;expansions=0;start=time.monotonic()
for point in points:
 VV=W.subs(dict(zip((k,l,m),point)))
 for tag,ss,tt,ll in [('10',1,0,point[1]),('01',0,1,point[2]),('11',1,1,point[1]+point[2])]:
  V=VV.subs({x:ss,y:tt});poly=s.Poly(s.expand(sum(s.prod(1+u*H[i,j]+z*V[i,j] for i,j in enumerate(pm)) for pm in perms)-24),u,z)
  assert all(poly.coeff_monomial(u**i*z)==0 for i in range(4))
  assert poly.coeff_monomial(u*u*z*z)==0
  values={'EQUATION_Q':poly.coeff_monomial(z*z),'EQUATION_C':poly.coeff_monomial(u*z*z)}
  for name in values:
   got=eval(exports[tag][name],{'__builtins__':{}},{'b':5,'c':-12,'d':2,'e':5,'k':point[0],'l':ll});expected=values[name];key=tag+'_'+name
   if expected==0:assert got==0,(point,key,got)
   else:
    ratio=s.Rational(got)/expected
    if key not in ratios:ratios[key]=ratio
    assert ratio==ratios[key] and ratio!=0,(point,key,ratio,ratios[key])
   checks+=1
  expansions+=1
 print('AUDITED_POINT',point,flush=True)
result={'verdict':'PASS','condition_checks':checks,'direct_permanent_expansions':expansions,'seconds':time.monotonic()-start,'scalars':{k:str(v) for k,v in ratios.items()}};(p/'fraction-free-audit.result.json').write_text(json.dumps(result,indent=2));print(json.dumps(result),flush=True)
