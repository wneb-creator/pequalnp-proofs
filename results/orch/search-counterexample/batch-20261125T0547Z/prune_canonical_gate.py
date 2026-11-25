import argparse,json
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument('witness');ap.add_argument('mapping');ap.add_argument('output');args=ap.parse_args()
w=json.loads(Path(args.witness).read_text());m=json.loads(Path(args.mapping).read_text())
n=w['input_count'];ops=w['operand_wire_lists'];out=w['output_wire_list'];samples=m['positive_samples']+m['negative_samples'];np=len(m['positive_samples']);pm=(1<<np)-1;full=(1<<len(samples))-1
inputs=[sum(bool(q>>i&1)<<j for j,q in enumerate(samples)) for i in range(n)]
def meet(refs,v):
 x=full
 for i in refs:x &= v[i]
 return x
def evaluate(change_gate=None,replacement=None):
 v=inputs.copy()
 for g,(a,b) in enumerate(ops):v.append(replacement(v) if g==change_gate else meet(a,v)|meet(b,v))
 return meet(out,v),v
expected,values=evaluate();assert expected==pm
results=[]
for g in range(len(ops)):
 without,_=evaluate(g,lambda v:0)
 required=pm&~without
 refs=[i for i,v in enumerate(values[:n+g]) if v&required==required]
 if not refs:
  results.append({'gate':g,'critical_positive_count':required.bit_count(),'replacement_available':False});continue
 actual,_=evaluate(g,lambda v:meet(refs,v))
 results.append({'gate':g,'critical_positive_count':required.bit_count(),'replacement_available':True,'negative_errors':(actual&~pm).bit_count(),'positive_errors':(pm&~actual).bit_count()})
 if actual!=pm:continue
 def remap_list(xs):
  ans=[]
  for x in xs:
   if x==n+g:ans.extend(refs)
   else:ans.append(x if x<n+g else x-1)
  return sorted(set(ans))
 newops=[[remap_list(a),remap_list(b)] for j,(a,b) in enumerate(ops) if j!=g]
 candidate={'input_count':n,'or_count':len(newops),'operand_wire_lists':newops,'output_wire_list':remap_list(out),'deleted_gate':g,'source_witness':args.witness,'checked_positive_samples':np,'checked_negative_samples':len(samples)-np}
 Path(args.output+'.witness.json').write_text(json.dumps(candidate,indent=2)+'\n')
 print('CANDIDATE',len(newops),'ORs',g,flush=True)
 break
Path(args.output+'.json').write_text(json.dumps({'or_count':len(ops),'tested':len(results),'results':results},indent=2)+'\n')
print(json.dumps({'tested':len(results),'candidate':len(results)<len(ops) or any(x.get('negative_errors')==0 and x.get('positive_errors')==0 for x in results)}))
