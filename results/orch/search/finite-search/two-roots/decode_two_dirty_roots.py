import json,sys,itertools
from pathlib import Path
meta=json.loads(Path(sys.argv[1]).read_text());log=Path(sys.argv[2]).read_text();out=Path(sys.argv[3]);truth={int(x) for line in log.splitlines() if line.startswith('v ') for x in line.split()[1:] if int(x)>0}
if 's SATISFIABLE' not in log:raise SystemExit('No SAT model to decode')
def chosen(xs):return [i for i,x in enumerate(xs) if x in truth]
edges=[(i,4+j) for i,row in enumerate(meta['edge']) for j,x in enumerate(row) if x in truth]
dclauses=[[chosen(s) for s in pair] for pair in meta['dclauses']]
raw=[[chosen(s) for s in pair] for pair in meta['raw']]
select=[chosen(s) for s in meta['select']]
assert all((i,i+4) in edges for i in range(meta.get('matching',4)))
assert all(not all((i,j) in edges for i,j in itertools.product(ps,qs)) for ps in itertools.combinations(range(4),2) for qs in itertools.combinations(range(4,8),2))
# Construct actual distinct-fanin gates; OR supports are copied if necessary.
gates=[]
def new(op,a,b):
 assert a!=b and 0<=a<8+len(gates) and 0<=b<8+len(gates)
 gates.append([op,a,b]);return 7+len(gates)
def disj(vs):
 assert vs
 w=vs[0]
 for x in vs[1:]:w=new('or',w,x)
 return w
dw=[new('and',disj(s),disj(t)) for s,t in dclauses]
rw=[]
for root in range(2):
 args=[disj(raw[root][side]+([dw[side]] if root==0 else [dw[d] for d in select[side]])) for side in range(2)]
 rw.append(new('and',*args))
output=new('or',*rw)
def evaluate(mask,base=None,direction=None):
 values=[bool(mask>>i&1) for i in range(8)];deriv=[i==direction for i in range(8)]
 for op,a,b in gates:
  if op=='or':values.append(values[a] or values[b]);deriv.append(deriv[a] or deriv[b])
  else:values.append(values[a] and values[b]);deriv.append((values[a] and deriv[b]) or (deriv[a] and values[b]))
 return values,deriv
witness=[];bad=[]
for d in range(2):
 neg=[]
 for mask in range(256):
  v,_=evaluate(mask);g=any(mask>>a&1 and mask>>b&1 for a,b in edges)
  if d==0 and v[output]!=g:bad.append(mask)
  if mask in meta['rows']:assert v[output]==g if meta.get('exact',True) else not v[output] or g
  if v[dw[d]] and not g:neg.append(mask)
 assert neg and evaluate(17)[0][dw[d]];witness.append(neg[0])
traces=[]
for base,direction in [(0,4),(4,0)]:
 v,dx=evaluate(1<<base,direction=direction);assert not dx[output];traces.append(dx[output])
report={'graph_edges':edges,'dclauses':dclauses,'root_raw':raw,'root1_dirty_select':select,'dirty_witnesses':witness,'gates':gates,'output':output,'and_count':sum(g[0]=='and' for g in gates),'or_count':sum(g[0]=='or' for g in gates),'full_truth_rows_checked':256,'full_truth_valid':not bad,'full_truth_mismatches':bad,'traces':traces,'scope':('positive control with matching3 and exact graph function' if meta.get('matching',4)<4 else ('pair-only diagnostic allowing higher false positives' if meta.get('mode')=='pairs' else 'counterexample only to two-root clean-fragment shadow-cover-at-most-three route, not to full-function AND-surplus or plane gate bound'))}
out.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k!='gates'},indent=2))
