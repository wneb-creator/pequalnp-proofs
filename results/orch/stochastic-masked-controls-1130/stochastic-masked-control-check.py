from pathlib import Path
import ast,json,hashlib
b=Path('/tmp/oec/pequalnp-pilot-81');tree=ast.parse((b/'stochastic-compress.py').read_text());functions=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in ['setup','prune']];ns={'cache':{}};exec(compile(ast.Module(body=functions,type_ignores=[]),'shared_cse_helpers','exec'),ns)
iv,calc,fulliv,want,nt,rows=ns['setup'](14,0,7);source=json.loads((b/'algebraic-both-blocking-best.json').read_text());summary=[]
def profile(g,o):
 fan=[0]*(14+len(g));sup=[1<<i for i in range(14)];v=list(fulliv)
 for j,(op,a,c) in enumerate(g):
  assert a!=c and a<14+j and c<14+j
  fan[a]+=1;fan[c]+=1;sup.append(sup[a]&sup[c] if op=='and' else sup[a]|sup[c]);v.append(v[a]&v[c] if op=='and' else v[a]|v[c])
 assert v[o]==want
 elig=bp=bz=0
 for i,n in enumerate(fan):
  if n>1:
   if sup[i]:elig|=sup[i];bp+=n-1
   else:bz+=n-1
 return {'size':len(g),'eligible_inputs':[i for i in range(14) if elig>>i&1],'Bplus':bp,'Bzero':bz}
for repair in [False,True,2]:
 g=[x[:] for x in source['gates']];o=source['output'];vv=iv[:];fixed=[]
 for j,(op,a,c) in enumerate(g):
  z=calc(vv[a],vv[c],op)
  if repair and not(z&((1<<21)-1)):a2=2 if repair==2 and fixed else 1;g[j]=['and',a2,8];z=calc(vv[a2],vv[8],'and');fixed.append(j)
  vv.append(z)
 assert vv[o]==(1<<21)-1
 before=profile(g,o);v=iv[:];mapping={i:i for i in range(14)};new=[];reps={}
 for i,z in enumerate(iv):
  if calc(z,z,'and')==z:reps.setdefault(z,i)
 for j,(op,a,c) in enumerate(g):
  a,c=mapping[a],mapping[c];z=calc(v[a],v[c],op)
  if a==c:assert z==v[a];mapping[14+j]=a;continue
  idem=calc(z,z,'and')==z
  if idem and z in reps:mapping[14+j]=reps[z];continue
  index=14+len(new);new.append([op,a,c]);v.append(z);mapping[14+j]=index
  if idem:reps[z]=index
 assert v[mapping[o]]==vv[o];new,no=ns['prune'](14,new,mapping[o]);after=profile(new,no)
 name='stochastic-masked41-'+('distinct-supported' if repair==2 else ('supported' if repair else 'original'))+'-cse.json';result={'inputs':14,'marked_inputs':[0,7],'gates':new,'output':no,'size':len(new),'failed_bits':[],'full_truth_rows_verified':16384,'derivatives':[False,False]};(b/name).write_text(json.dumps(result,indent=2)+'\n');summary.append({'repair':repair,'replaced_gates':fixed,'before':before,'after_cse':after,'result':name})
(b/'stochastic-masked-control-check.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
