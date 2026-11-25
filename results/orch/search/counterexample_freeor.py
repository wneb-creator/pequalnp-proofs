import z3,json,time,itertools
from pathlib import Path
from counterexample_sparse_sat import extrema,PETER,FANO

def synth(n,edges,k,timeout=180000):
 begin=time.monotonic();tests,ne,mis=extrema(n,edges);w=len(tests);allones=z3.BitVecVal(0,w);mw=n+k
 vals=[z3.BitVecVal(sum(1<<j for j,a in enumerate(tests) if a>>i&1),w) for i in range(n)]
 so=z3.SolverFor('QF_BV');so.set(timeout=timeout)
 masks=[]
 def monomial(mask,vs):
  value=allones
  for i,v in enumerate(vs):value=value | z3.If(z3.Extract(i,i,mask)==1,v,allones)
  return value
 for j in range(k):
  a=z3.BitVec('a'+str(j),mw);b=z3.BitVec('b'+str(j),mw);v=z3.BitVec('v'+str(j),w)
  so.add(z3.ULT(a,1<<(n+j)),z3.ULT(b,1<<(n+j)),z3.ULE(a,b))
  so.add(v==monomial(a,vals)&monomial(b,vals));vals.append(v);masks.append((a,b))
 output=z3.BitVec('output',mw);so.add(monomial(output,vals)==(1<<ne)-1)
 print(json.dumps({'starting':True,'n':n,'max_and':k,'tests':w,'unlimited_or':True}),flush=True)
 rr=so.check();r={'n':n,'edges':edges,'max_and':k,'tests':w,'unlimited_or':True,'result':str(rr),'seconds':time.monotonic()-begin}
 if rr==z3.sat:
  m=so.model();r['and_masks']=[(m.eval(a).as_long(),m.eval(b).as_long()) for a,b in masks];r['output_mask']=m.eval(output).as_long()
  gates=[];atoms=list(range(n))
  def conjunction(mask):
   bits=[atoms[i] for i in range(len(atoms)) if mask>>i&1]
   if not bits:gates.append(('or',));return n+len(gates)-1
   p=bits[0]
   for q in bits[1:]:gates.append(('or',p,q));p=n+len(gates)-1
   return p
  for a,b in r['and_masks']:
   p=conjunction(a);q=conjunction(b);gates.append(('and',p,q));atoms.append(n+len(gates)-1)
  out=conjunction(r['output_mask']);r['gates']=gates;r['output']=out;r['size']=len(gates)
  errors=[]
  for bits in range(1<<n):
   vs=[bool(bits>>i&1) for i in range(n)]
   for g in gates:
    op,*args=g;vs.append(all(vs[a] for a in args) if op=='and' else any(vs[a] for a in args))
   f=any(bits>>u&1 and bits>>v&1 for u,v in edges)
   if vs[out]!=f:errors.append(bits)
  r['full_truth_table_errors']=errors
 if rr==z3.unknown:r['reason']=so.reason_unknown()
 return r

if __name__=='__main__':
 z3.set_param('memory_max_size',256)
 cases=[('C5',5,[(0,1),(1,2),(2,3),(3,4),(4,0)]),('theta233',7,[(0,2),(2,1),(0,3),(3,4),(4,1),(0,5),(5,6),(6,1)]),('Petersen',10,PETER),('Fano',14,FANO)]
 for name,n,e in cases:
  tau=next(k for k in range(n+1) if any(all(u in c or v in c for u,v in e) for c in itertools.combinations(range(n),k)))
  r=synth(n,e,tau-1);r['name']=name;r['vertex_cover_number']=tau
  with Path('/tmp/oec/pequalnp-pilot-55/counterexample-freeor-results.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
  print(json.dumps(r),flush=True)
