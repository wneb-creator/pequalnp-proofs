from pathlib import Path
import itertools,json,subprocess,time

base=Path(__file__).parent
n=7
representatives={}
def code(adj,root,parent=-1):
    return '('+''.join(sorted(code(adj,v,root) for v in adj[root] if v!=parent))+')'
for prufer in itertools.product(range(n),repeat=n-2):
    degree=[1]*n
    for v in prufer: degree[v]+=1
    edges=[]
    for v in prufer:
        leaf=next(i for i,d in enumerate(degree) if d==1)
        edges.append((leaf,v));degree[leaf]-=1;degree[v]-=1
    a,b=[i for i,d in enumerate(degree) if d==1]
    edges.append((a,b))
    adj=[[] for _ in range(n)]
    for a,b in edges: adj[a].append(b);adj[b].append(a)
    key=min(code(adj,v) for v in range(n))
    if key not in representatives: representatives[key]=sorted(tuple(sorted(e)) for e in edges)
assert len(representatives)==11
records=[]
for number,(key,edges) in enumerate(sorted(representatives.items()),1):
    covers=[s for s in range(1<<n) if all((s>>a&1) or (s>>b&1) for a,b in edges)]
    cover=min(covers,key=int.bit_count)
    tau=cover.bit_count();K=len(edges)+tau-1
    graph=base/('tree7-'+str(number).zfill(2)+'.graph')
    graph.write_text(str(n)+' '+str(len(edges))+'\n'+''.join(str(a)+' '+str(b)+'\n' for a,b in edges))
    records.append({'id':number,'canonical_code':key,'n':n,'edges':edges,'cover_mask':cover,'tau':tau,'K':K,'graph':graph.name})
(base/'source-tree7-specifications.json').write_text(json.dumps({'method':'all 7^5 Prüfer sequences, rooted-tree canonical isomorphism code','prufer_sequences':n**(n-2),'tree_count':len(records),'graphs':records},indent=2)+'\n')
solver='/tmp/oec/pequalnp-pilot-75/lean-tools/lean-4.36.0-linux/bin/cadical'
for record in records:
    prefix=base/('tree7-'+str(record['id']).zfill(2)+'-k'+str(record['K'])+'-sources-dirty')
    with prefix.with_suffix('.log').open('w') as f:
        result=subprocess.run(['python3',str(base/'synth_sat_sources_dirty.py'),str(base/record['graph']),str(record['K']),'60',str(prefix),solver,'ordered'],stdout=f,stderr=subprocess.STDOUT,timeout=105)
    print(record['id'],'K',record['K'],'wrapper_exit',result.returncode,flush=True)
