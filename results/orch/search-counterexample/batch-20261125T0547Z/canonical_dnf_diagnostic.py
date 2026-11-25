import argparse,json
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument('witness');ap.add_argument('output');ap.add_argument('--limit',type=int,default=20000);args=ap.parse_args()
w=json.loads(Path(args.witness).read_text());n=w['input_count'];values=[{1<<i} for i in range(n)]
def minimal(xs):
 out=[]
 for x in sorted(set(xs),key=lambda t:(t.bit_count(),t)):
  if not any(x&y==y for y in out):out.append(x)
  assert len(out)<=args.limit
 return set(out)
def conjunction(refs):
 out={0}
 for i in refs:
  assert len(out)*len(values[i])<=args.limit**2
  out=minimal(a|b for a in out for b in values[i])
 return out
for a,b in w['operand_wire_lists']:values.append(minimal(conjunction(a)|conjunction(b)))
minterms=conjunction(w['output_wire_list'])
D={0,1,3,9};edges={(1<<p)|(1<<(13+l)) for p in range(13) for l in range(13) if (p-l)%13 in D} if n==26 else set()
result={'source_witness':args.witness,'or_count':len(w['operand_wire_lists']),'minimal_true_supports':sorted(minterms),'is_exact_incidence_function':n==26 and minterms==edges,'count':len(minterms)}
Path(args.output).write_text(json.dumps(result,indent=2)+'\n');print({k:v for k,v in result.items() if k!='minimal_true_supports'})
