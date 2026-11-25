from pathlib import Path
import json
D=json.loads(Path('fano-data.json').read_text());n,k=14,6;rows=sorted(D['minimal_true']+D['maximal_false'])
clauses=[];nv=0
def fresh():
 global nv
 nv+=1;return nv
def andeq(z,a,b):clauses.extend([[-z,a],[-z,b],[z,-a,-b]])
def oreq(z,terms):
 clauses.append([-z]+terms)
 for t in terms:clauses.append([z,-t])
sel=[[[fresh() for source in range(n+j)] for side in range(2)] for j in range(k)]
val=[[fresh() for r in rows] for j in range(k)]
sideval=[[[fresh() for r in rows] for side in range(2)] for j in range(k)]
outsel=[fresh() for j in range(k)]
for j in range(k):
 for side in range(2):
  for ri,r in enumerate(rows):
   terms=[]
   for source,s in enumerate(sel[j][side]):
    if source<n:
     if r>>source&1:terms.append(s)
    else:
     t=fresh();andeq(t,s,val[source-n][ri]);terms.append(t)
   oreq(sideval[j][side][ri],terms)
 for ri,r in enumerate(rows):andeq(val[j][ri],sideval[j][0][ri],sideval[j][1][ri])
for ri,r in enumerate(rows):
 terms=[]
 for j in range(k):
  t=fresh();andeq(t,outsel[j],val[j][ri]);terms.append(t)
 if r in D['minimal_true']:clauses.append(terms)
 else:clauses.extend([[-t] for t in terms])
Path('fano6-andcap.cnf').write_text(f'p cnf {nv} {len(clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in clauses))
meta={'inputs':n,'and_cap':k,'rows':rows,'selectors':sel,'output_selectors':outsel,'variables':nv,'clauses':len(clauses),'empty_or_operands':'allowed as false; decoder propagates false and removes dead gates','output':'arbitrary subset of AND outputs; no forced inclusion','normalization':'each AND operand is OR closure of primary inputs and earlier AND outputs'}
Path('fano6-andcap-layout.json').write_text(json.dumps(meta,indent=2));print({key:meta[key] for key in ['inputs','and_cap','variables','clauses']})
