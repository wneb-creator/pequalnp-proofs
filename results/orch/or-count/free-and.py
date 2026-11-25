from pathlib import Path
import sys,json,itertools
mode,stem=sys.argv[1:3];base=Path(__file__).resolve().parent
if mode=='gen':
 data=json.loads(Path(sys.argv[3]).read_text());n=data['inputs'];k=int(sys.argv[4]);edges=data['edges']
 f=lambda r:any(r>>u&1 and r>>v&1 for u,v in edges)
 rows=list(range(1<<n)) if n<=6 else sorted([sum(1<<x for x in e) for e in edges]+[r for r in range(1<<n) if not f(r) and all(f(r|(1<<i)) for i in range(n) if not r>>i&1)])
 clauses=[];nv=0
 def fresh():
  global nv
  nv+=1;return nv
 def oreq(z,terms):
  clauses.append([-z]+terms)
  for t in terms:clauses.append([z,-t])
 def andeq(z,terms):
  clauses.append([z]+[-t for t in terms])
  for t in terms:clauses.append([-z,t])
 selectors=[[[fresh() for _ in range(n+j)] for side in range(2)] for j in range(k)]
 values=[[fresh() for r in rows] for j in range(k)]
 sides=[[[fresh() for r in rows] for side in range(2)] for j in range(k)]
 outsel=[fresh() for _ in range(n+k)];outval=[fresh() for r in rows]
 def conjunction(sels,vs):
  clauses.append(sels)
  for ri,r in enumerate(rows):
   terms=[]
   for source,s in enumerate(sels):
    if source<n:
     if not r>>source&1:terms.append(-s)
    else:
     t=fresh();oreq(t,[-s,values[source-n][ri]]);terms.append(t)
   andeq(vs[ri],terms)
 for j in range(k):
  for side in range(2):conjunction(selectors[j][side],sides[j][side])
  for ri,r in enumerate(rows):oreq(values[j][ri],[sides[j][0][ri],sides[j][1][ri]])
 conjunction(outsel,outval)
 for ri,r in enumerate(rows):clauses.append([outval[ri] if f(r) else -outval[ri]])
 meta={'inputs':n,'or_cap':k,'edges':edges,'rows':rows,'selectors':selectors,'output_selectors':outsel,'variables':nv,'clauses':len(clauses),'normalization':'Each OR operand and final output is a nonempty conjunction of primary inputs and earlier OR nodes; all AND gates free.'}
 (base/(stem+'.cnf')).write_text(f'p cnf {nv} {len(clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in clauses))
 (base/(stem+'-layout.json')).write_text(json.dumps(meta,indent=2));print({key:meta[key] for key in ['inputs','or_cap','variables','clauses']})
else:
 m=json.loads((base/(stem+'-layout.json')).read_text());n,k=m['inputs'],m['or_cap'];pos={int(v) for line in Path(sys.argv[3]).read_text().splitlines() if line.startswith('v ') for v in line.split()[1:] if int(v)>0}
 selected=[[[i for i,v in enumerate(side) if v in pos] for side in gate] for gate in m['selectors']];outselected=[i for i,v in enumerate(m['output_selectors']) if v in pos]
 gates=[];ornodes=[];cache={}
 def add(op,a,b):gates.append({'op':op,'inputs':[a,b]});return n+len(gates)-1
 def conjunction(indices):
  assert indices
  wires=tuple(sorted({i if i<n else ornodes[i-n] for i in indices}))
  if wires in cache:return cache[wires]
  w=wires[0]
  for u in wires[1:]:w=add('and',w,u)
  cache[wires]=w;return w
 for a,b in selected:ornodes.append(add('or',conjunction(a),conjunction(b)))
 output=conjunction(outselected);live=set()
 def visit(w):
  if w<n or w in live:return
  assert w<n+len(gates);live.add(w)
  for a in gates[w-n]['inputs']:assert a<w;visit(a)
 visit(output);ren={i:i for i in range(n)};actual=[]
 for j,g in enumerate(gates):
  if n+j in live:ren[n+j]=n+len(actual);actual.append({'op':g['op'],'inputs':[ren[a] for a in g['inputs']]})
 output=ren[output];errors=[]
 for r in range(1<<n):
  w=[bool(r>>i&1) for i in range(n)]
  for g in actual:
   a,b=g['inputs'];assert a<len(w) and b<len(w);w.append((w[a] and w[b]) if g['op']=='and' else (w[a] or w[b]))
  if w[output]!=any(r>>u&1 and r>>v&1 for u,v in m['edges']):errors.append(r)
 orcount=sum(g['op']=='or' for g in actual)
 report={'source':stem,'inputs':n,'edges':m['edges'],'selected_operands':selected,'selected_output':outselected,'gates':actual,'output':output,'or_count':orcount,'actual_size':len(actual),'verified_rows':1<<n,'errors':errors,'or_bound_counterexample':not errors and orcount<len(m['edges'])-1,'plane_normalization_candidate_refutation':n==14 and not errors and len(actual)<=26}
 (base/(stem+'-decoded.json')).write_text(json.dumps(report,indent=2));print({key:value for key,value in report.items() if key not in ['gates','selected_operands','selected_output','edges']})
 assert not errors and orcount<=k
