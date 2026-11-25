import hashlib
import json
import re
import sys
from datetime import datetime,timezone
from pathlib import Path

P=Path(__file__).resolve().parent
name=sys.argv[1]
finished=json.loads((P/'portfolio1-results.json').read_text())
assert any(r['graph']==name and r['exit_code']==0 for r in finished)
meta=json.loads((P/(name+'.json')).read_text());ng=meta['target_gates'];prefix=P/(name+'-portfolio1');lines=prefix.with_suffix('.stdout').read_text().splitlines();outdir=P/(name+'-portfolio1-candidates');outdir.mkdir(exist_ok=True);seen=set();candidates=[]
for k,line in enumerate(lines):
    if not line.startswith(('BEST ','BEST_WITH_HYPOTHESES ','FINAL_BEST ','FINAL_BEST_WITH_HYPOTHESES ')):continue
    m=re.search(r'fn=(\d+) fp=(\d+) missing=(\d+) mixed=(\d+).*output=(\d+)',line)
    if not m or int(m[3]) or int(m[4]):continue
    gs=[]
    for entry in lines[k+1:k+1+ng]:
        g=re.fullmatch(r'(\d+) ([&|]) (\d+) (\d+)',entry)
        if not g:break
        gs.append([int(g[2]=='|'),int(g[3]),int(g[4])])
    if len(gs)!=ng:continue
    key=json.dumps([gs,int(m[5])])
    if key in seen:continue
    seen.add(key)
    data={'gates':gs,'output':int(m[5]),'boundary_false_negatives':int(m[1]),'boundary_false_positives':int(m[2]),'missing_star_edges':0,'tCount':0,'source_header':line}
    f=outdir/('candidate-'+str(len(candidates)).zfill(2)+'.json'); encoded=json.dumps(data,indent=2)+'\n'; assert not f.exists() or f.read_text()==encoded; f.write_text(encoded) if not f.exists() else None; candidates.append(f)
files=[prefix.with_suffix('.stdout'),prefix.with_suffix('.stderr'),Path(str(prefix)+'.best.json'),Path(str(prefix)+'.best-hyp.json')]+[Path(str(prefix)+'.control'+str(d)+'.json') for d in range(3)]+candidates
files=[f for f in files if f.exists()]
manifest={'frozen_utc':datetime.now(timezone.utc).isoformat(),'graph':name,'notes':'Completed stochastic phase, no counterexample. All hypothesis-satisfying improvement snapshots extracted from immutable full log.','files':[{'path':str(f),'size':f.stat().st_size,'sha256':hashlib.sha256(f.read_bytes()).hexdigest()} for f in files]}
destination=P/(name+'-portfolio1-manifest.json');assert not destination.exists();destination.write_text(json.dumps(manifest,indent=2)+'\n');print(name,'frozen candidates',len(candidates))
