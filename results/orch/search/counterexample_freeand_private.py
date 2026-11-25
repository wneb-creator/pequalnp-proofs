"""Compact free-AND synthesis with private negative witnesses.

An OR node joins two conjunctions of earlier atoms. Each selected conjunction
atom must be necessary on some maximal-independent-set input. Removing an atom
without such a witness preserves every negative signature and raises positive
signatures; downstream monotonicity preserves the required graph function.
Minimize total mask cardinality after minimizing OR count and disjoint-mask
normalization to justify this cut. Padding with unused ORs of incomparable
nonisolated input variables covers smaller OR counts on the graphs below.
These normalization arguments are mathematical assumptions of this external
search, not an imported Lean certificate. Every SAT witness is checked again
on all inputs; UNSAT alone is not a machine-checked theorem.
"""
import z3,json,time
from pathlib import Path
from counterexample_sparse_sat import extrema,PETER,FANO

def synth(n,edges,k,timeout=180000,disjoint=True,positive_cuts=True,private_cuts=True):
 begin=time.monotonic();tests,ne,mis=extrema(n,edges);w=len(tests);allones=z3.BitVecVal((1<<w)-1,w);mw=n+k
 vals=[z3.BitVecVal(sum(1<<j for j,a in enumerate(tests) if a>>i&1),w) for i in range(n)]
 so=z3.SolverFor('QF_BV');so.set(timeout=timeout)
 masks=[]
 def monomial(mask,vs):
  selected=[z3.Extract(i,i,mask)==1 for i in range(len(vs))]
  terms=[z3.If(bit,value,allones) for bit,value in zip(selected,vs)]
  prefix=[allones]
  for term in terms:prefix.append(prefix[-1] & term)
  if private_cuts:
   negative_mask=z3.BitVecVal(((1<<w)-1)^((1<<ne)-1),w)
   suffix=allones
   for i in range(len(vs)-1,-1,-1):
    without_i=prefix[i] & suffix
    witness=without_i & ~vs[i] & negative_mask
    so.add(z3.Implies(selected[i],witness!=0))
    suffix=suffix & terms[i]
  return prefix[-1]
 for j in range(k):
  a=z3.BitVec('a'+str(j),mw);b=z3.BitVec('b'+str(j),mw);v=z3.BitVec('v'+str(j),w)
  so.add(z3.ULT(a,1<<(n+j)),z3.ULT(b,1<<(n+j)),z3.ULE(a,b))
  x=monomial(a,vals);y=monomial(b,vals)
  so.add(v==x|y)
  if disjoint:so.add(a & b == 0)
  if positive_cuts:
   pm=z3.BitVecVal((1<<ne)-1,w)
   so.add((x & ~y & pm)!=0,(y & ~x & pm)!=0)
  vals.append(v);masks.append((a,b))
 output=z3.BitVec('output',mw);so.add(monomial(output,vals)==(1<<ne)-1)
 print(json.dumps({'starting':True,'n':n,'max_or':k,'tests':w,'unlimited_and':True,'private_negative_cuts':private_cuts,'disjoint_masks':disjoint,'positive_incomparability':positive_cuts}),flush=True)
 rr=so.check();r={'n':n,'edges':edges,'max_or':k,'tests':w,'unlimited_and':True,'result':str(rr),'seconds':time.monotonic()-begin,'private_negative_cuts':private_cuts,'disjoint_masks':disjoint,'positive_incomparability':positive_cuts}
 if rr==z3.sat:
  m=so.model();r['or_masks']=[(m.eval(a).as_long(),m.eval(b).as_long()) for a,b in masks];r['output_mask']=m.eval(output).as_long()
  gates=[];atoms=list(range(n))
  def conjunction(mask):
   bits=[atoms[i] for i in range(len(atoms)) if mask>>i&1]
   if not bits:gates.append(('and',));return n+len(gates)-1
   p=bits[0]
   for q in bits[1:]:gates.append(('and',p,q));p=n+len(gates)-1
   return p
  for a,b in r['or_masks']:
   p=conjunction(a);q=conjunction(b);gates.append(('or',p,q));atoms.append(n+len(gates)-1)
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
 import argparse
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--case',choices=['C5','C6','C7','twoC5','theta233','Petersen','Fano'],default='C5')
 parser.add_argument('--or-bound',type=int)
 parser.add_argument('--timeout-ms',type=int,default=180000)
 parser.add_argument('--memory-mb',type=int,default=256)
 parser.add_argument('--output',type=Path)
 args=parser.parse_args()
 cycles={f'C{n}':(n,[(i,(i+1)%n) for i in range(n)]) for n in (5,6,7)}
 cases={**cycles,
  'twoC5':(10,[(i,(i+1)%5) for i in range(5)]+[(i+5,(i+1)%5+5) for i in range(5)]),
  'theta233':(7,[(0,2),(2,1),(0,3),(3,4),(4,1),(0,5),(5,6),(6,1)]),
  'Petersen':(10,PETER),'Fano':(14,FANO)}
 n,edges=cases[args.case]
 k=len(edges)-2 if args.or_bound is None else args.or_bound
 assert k>=0 and args.timeout_ms>0 and args.memory_mb>0
 z3.set_param('memory_max_size',args.memory_mb)
 result=synth(n,edges,k,timeout=args.timeout_ms)
 result['name']=args.case
 text=json.dumps(result)
 if args.output is not None:args.output.write_text(text+'\n')
 print(text,flush=True)
