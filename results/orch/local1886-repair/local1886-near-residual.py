import itertools,json,time
from pathlib import Path
p=Path('/tmp/oec/pequalnp-pilot-92')
# Original Petersen vertices represented by these six coordinates.
vertices=[0,2,3,5,6,9]
raw=[sum(1<<x for x in range(64) if x>>i&1) for i in range(6)]
allbits=(1<<64)-1
pairs=[(1,3),(5,2),(4,0),(2,4)]
stars=[(0,2,5),(0,1,4),(2,3,4),(1,3,5)]
matching=[(0,3),(1,2),(4,5)]
sv=[raw[a]|raw[b]|raw[c] for a,b,c in stars]
goal=0
for a,b in matching:goal|=raw[a]&raw[b]
def opfn(op,a,b):return a&b if op=='and' else a|b if op=='or' else allbits^a
base=raw+[raw[a]|raw[b] for a,b in pairs]+sv
start=time.time();tested=0;results=[]
for bankop in ['and','or']:
 for a,b in matching:
  bank=base+[opfn(bankop,raw[a],raw[b])]
  gate0=[]
  for u in range(len(bank)):
   gate0.append(('not',u,0,allbits^bank[u]))
   for v in range(u,len(bank)):
    for op in ['and','or']:gate0.append((op,u,v,opfn(op,bank[u],bank[v])))
  for factored,mask in enumerate(sv):
   found=[];best=65;bestg=None
   for op0,u0,v0,t0 in gate0:
    extended=bank+[t0]
    for u in range(len(extended)):
     for op,v in [('not',0)]+[(op,v) for v in range(u,len(extended)) for op in ['and','or']]:
      value=opfn(op,extended[u],extended[v]);errors=((mask&value)^goal).bit_count();tested+=1
      if errors<best:best=errors;bestg=[(op0,u0,v0),(op,u,v)]
      if errors==0:found.append([(op0,u0,v0),(op,u,v)])
   results.append({'supplied_edge':[vertices[a],vertices[b]],'bank_op':bankop,'factored_star':factored,'factored_vertices':[vertices[i] for i in stars[factored]],'best_residual_errors':best,'best_two_gates':bestg,'solutions':found})
report={'scope':'Fixed18-gate near architecture: keep four3-input OR stars and their current four pair-OR prefixes; factor one star D with its center term. Seek two new gates K from all raw six inputs, star/pair ORs, supplied edge bank, with D AND K equal the residual three-edge matching. A success gives18 counted gates after lifting; no success only excludes this finite restricted family.','tested_circuits':tested,'seconds':time.time()-start,'solutions':sum(len(r['solutions']) for r in results),'cases':results}
p.joinpath('local1886-near-residual.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='cases'}))
print(json.dumps([{k:v for k,v in r.items() if k not in ['solutions','best_two_gates']} for r in results]))
