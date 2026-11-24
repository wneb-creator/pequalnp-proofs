import itertools,json,pathlib
r=pathlib.Path('/tmp/oec/pequalnp-pilot-21/search/diagnostic157')
lines=[set((w+i)%13 for i in (0,1,3,9)) for w in range(13)]
base=lines[0];p=0
parallel=[w for w,L in enumerate(lines) if p in L and w!=0]
groups=[sorted(lines[w]-{p}) for w in parallel]
A,B,C=groups
net=[]
def gate(op,a,b):net.append((a,b,op=='AND'));return 12+len(net)
def fold(op,points):
 acc=points[0]
 for q in points[1:]:acc=gate(op,acc,q)
 return acc
b=fold('OR',B);c=fold('OR',C);h=gate('AND',b,c)
filters={q:gate('AND',q,h) for q in sorted(base-{p})}
out={}
for w,L in enumerate(lines):
 if p in L:out[w]=fold('AND',sorted(L))
 else:
  q=next(iter(L&base));a=next(iter(L&set(A)))
  out[w]=gate('AND',filters[q],a)
rows=sorted({sum(1<<q for q in sub) for L in lines for n in range(5) for sub in itertools.combinations(L,n)})
def eval_at(x):
 ws=[bool(x>>q&1) for q in range(13)]
 for a,b,op in net:ws.append((ws[a] and ws[b]) if op else (ws[a] or ws[b]))
 return [ws[out[w]] for w in range(13)]
assert len(net)==29 and len(rows)==157
assert all(eval_at(x)==[all(x>>q&1 for q in L) for L in lines] for x in rows)
errors=[0]*13
for x in range(8192):
 if x.bit_count() not in (5,6):continue
 got=eval_at(x)
 for w,L in enumerate(lines):errors[w]+=got[w]!=all(x>>q&1 for q in L)
result={'scope':'157-row dual diagnostic ONLY; not originalband counterexample','gates':net,'out':[out[w] for w in range(13)],'groups':groups,'base_line':sorted(base),'diagnostic_rows':len(rows),'band_errors_per_output':errors}
(r/'explicit29-diagnostic.json').write_text(json.dumps(result,indent=2)+'\n')
print('VALIDATED29 gates onall157diagnosticrows; failsfull5/6band witherrors',errors)
print('groups',groups,'outputs',result['out'])
