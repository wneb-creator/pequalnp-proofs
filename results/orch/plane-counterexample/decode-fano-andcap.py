from pathlib import Path
import sys,json
D=json.loads(Path('fano-data.json').read_text());M=json.loads(Path('fano6-andcap-layout.json').read_text());n,k=M['inputs'],M['and_cap']
pos=set()
for line in Path(sys.argv[1]).read_text().splitlines():
 if line.startswith('v '):pos.update(int(v) for v in line.split()[1:] if int(v)>0)
chosen=[[[a for a,v in enumerate(side) if v in pos] for side in gate] for gate in M['selectors']]
chosenout=[j for j,v in enumerate(M['output_selectors']) if v in pos]
gates=[];ands=[]
def add(op,a,b):
 gates.append({'op':op,'inputs':[a,b]});return n+len(gates)-1
def orchain(wires):
 wires=list(dict.fromkeys(w for w in wires if w is not None))
 if not wires:return None
 acc=wires[0]
 for w in wires[1:]:acc=add('or',acc,w)
 return acc
for sides in chosen:
 ws=[]
 for side in sides:ws.append(orchain([a if a<n else ands[a-n] for a in side]))
 if any(w is None for w in ws):ands.append(None)
 else:ands.append(add('and',*ws))
output=orchain([ands[j] for j in chosenout])
if output is None:raise ValueError('SAT output is constant false')
# Remove every dead gate after constant propagation; retain all real gates exactly.
live=set()
def visit(w):
 if w<n or w in live:return
 live.add(w)
 for a in gates[w-n]['inputs']:visit(a)
visit(output);ren={i:i for i in range(n)};actual=[]
for j,g in enumerate(gates):
 if n+j in live:
  ren[n+j]=n+len(actual);actual.append({'op':g['op'],'inputs':[ren[a] for a in g['inputs']]})
output=ren[output];errors=[];truth=[];expected=[]
for r in range(1<<n):
 w=[bool(r>>i&1) for i in range(n)]
 for g in actual:
  a,b=g['inputs'];assert a<len(w) and b<len(w)
  w.append(w[a] and w[b] if g['op']=='and' else w[a] or w[b])
 got=w[output];want=any((r>>a)&1 and (r>>b)&1 for a,b in D['edges'])
 truth.append('1' if got else '0');expected.append('1' if want else '0')
 if got!=want:errors.append(r)
nonread=[]
for u,v in D['edges']:
 R=[{(1,0)} if i==u else {(0,1)} if i==v else set() for i in range(n)]
 for g in actual:
  a,b=g['inputs']
  R.append(R[a]|R[b] if g['op']=='or' else {(min(x+z,2),min(y+t,2)) for x,y in R[a] for z,t in R[b]})
 if (1,1) not in R[output]:nonread.append([u,v])
ac=sum(g['op']=='and' for g in actual)
report={'source':'six AND gates with free ORs','selected_operands':chosen,'selected_outputs':chosenout,'gates':actual,'output':output,'actual_size':len(actual),'actual_and_count':ac,'actual_or_count':len(actual)-ac,'is_ao2':all(len(g['inputs'])==2 and all(a<n+j for a in g['inputs']) for j,g in enumerate(actual)),'verified_rows':1<<n,'errors':errors,'actual_truth_table':''.join(truth),'expected_truth_table':''.join(expected),'not_read1_edges':nonread,'and_lower_bound_counterexample':ac<=6 and not errors,'plane_normalization_candidate_refutation':len(actual)<=26 and not errors}
Path(sys.argv[2]).write_text(json.dumps(report,indent=2));print(json.dumps({key:value for key,value in report.items() if key not in ['gates','actual_truth_table','expected_truth_table','selected_operands']}))
