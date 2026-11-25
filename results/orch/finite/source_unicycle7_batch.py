from pathlib import Path
import json,subprocess
p=Path(__file__).parent
cycle5=[(i,(i+1)%5) for i in range(5)]
cycle6=[(i,(i+1)%6) for i in range(6)]
graphs={
 'c6leaf':cycle6+[(0,6)],
 'c5path2':cycle5+[(0,5),(5,6)],
 'c5leaves_same':cycle5+[(0,5),(0,6)],
 'c5leaves_adjacent':cycle5+[(0,5),(1,6)],
 'c5leaves_apart':cycle5+[(0,5),(2,6)]}
records=[]
for name,edges in graphs.items():
 cover=min((s for s in range(128) if all((s>>a&1) or (s>>b&1) for a,b in edges)),key=int.bit_count)
 tau=cover.bit_count();K=len(edges)+tau-1
 graph=p/(name+'.graph')
 graph.write_text('7 '+str(len(edges))+'\n'+''.join(str(a)+' '+str(b)+'\n' for a,b in edges))
 records.append({'name':name,'n':7,'edges':edges,'cover_mask':cover,'tau':tau,'K':K})
(p/'source-unicycle7-specifications.json').write_text(json.dumps(records,indent=2)+'\n')
solver='/tmp/oec/pequalnp-pilot-75/lean-tools/lean-4.36.0-linux/bin/cadical'
for r in records:
 prefix=p/(r['name']+'-k'+str(r['K'])+'-sources-dirty')
 with prefix.with_suffix('.log').open('w') as f:
  result=subprocess.run(['python3',str(p/'synth_sat_sources_dirty.py'),str(p/(r['name']+'.graph')),str(r['K']),'120',str(prefix),solver,'ordered'],stdout=f,stderr=subprocess.STDOUT,timeout=165)
 print(r['name'],'K',r['K'],'wrapper_exit',result.returncode,flush=True)
