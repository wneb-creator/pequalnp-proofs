import z3,json,time,itertools,sys
from pathlib import Path
from counterexample_sparse_sat import extrema

def synth(n,edges,s,mode='general',timeout=120000):
 t0=time.monotonic();tests,k,mis=extrema(n,edges);w=len(tests);target=(1<<k)-1;mask=(1<<w)-1
 vs=[z3.BitVecVal(sum(1<<j for j,a in enumerate(tests) if a>>i&1),w) for i in range(n)]
 so=z3.SolverFor('QF_BV');so.set(timeout=timeout)
 sels=[];ops=[];bad=[]
 for j in range(s):
  op=z3.Bool('op'+str(j));v=z3.BitVec('v'+str(j),w)
  selects=[]
  for a,b in itertools.combinations(range(n+j),2):
   q=z3.Bool('p%d_%d_%d'%(j,a,b));selects.append((q,a,b));so.add(z3.Implies(q,v==z3.If(op,vs[a]&vs[b],vs[a]|vs[b])))
  so.add(z3.PbEq([(q,1) for q,_,_ in selects],1))
  for prev in vs:so.add(v!=prev)
  bad.append(z3.And(op,(v&z3.BitVecVal(mask^target,w))!=0))
  if mode=='sound':so.add(z3.Not(bad[-1]))
  sels.append(selects);ops.append(op);vs.append(v)
 for j in range(s-1):so.add(z3.Or(*[q for qs in sels[j+1:] for q,a,b in qs if n+j in (a,b)]))
 if mode=='unsound':so.add(z3.Or(*bad))
 so.add(vs[-1]==target)
 print(json.dumps({'starting':True,'n':n,'size':s,'mode':mode,'tests':w,'encoding':'onehot'}),flush=True)
 rr=so.check();r={'n':n,'edges':edges,'size':s,'mode':mode,'tests':w,'result':str(rr),'seconds':time.monotonic()-t0,'encoding':'onehot'}
 if rr==z3.sat:
  m=so.model();r['gates']=[('and' if z3.is_true(m.eval(ops[j])) else 'or',a,b) for j,qs in enumerate(sels) for q,a,b in qs if z3.is_true(m.eval(q))]
 if rr==z3.unknown:r['reason']=so.reason_unknown()
 return r
if __name__=='__main__':
 z3.set_param('memory_max_size',256)
 e=[];n=2
 for size in (2,3,3):
  chain=[0]+list(range(n,n+size-1))+[1];n+=size-1;e+=list(zip(chain,chain[1:]))
 for s,mode in [(10,'general'),(11,'unsound')]:
  r=synth(n,e,s,mode)
  with Path('/tmp/oec/pequalnp-pilot-55/counterexample-onehot-results.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
  print(json.dumps(r),flush=True)
