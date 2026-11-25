import argparse,json
from pathlib import Path
from sat_tap_incremental import eval_wires
ap=argparse.ArgumentParser();ap.add_argument('meta');ap.add_argument('circuit');ap.add_argument('output');a=ap.parse_args();meta=json.loads(Path(a.meta).read_text());block=json.loads(Path(a.circuit).read_text());n=meta['n'];mapping=meta['global_inputs'];gs=[]
for i,(op,u,v) in enumerate(block):gs.append([op,mapping[u] if u<n else 26+u-n,mapping[v] if v<n else 26+v-n])
def add(op,u,v):gs.append([op,u,v]);return 26+len(gs)-1
terms=[26+len(gs)-1];data=json.loads(Path('/tmp/oec/pequalnp-pilot-132/circuit-search/cases.json').read_text())
for p in range(13):
 if p in meta['points']:continue
 ns=[13+j for j in range(13) if data['neighbors'][p]>>j&1];w=ns[0]
 for v in ns[1:]:w=add(1,w,v)
 terms.append(add(0,p,w))
w=terms[0]
for v in terms[1:]:w=add(1,w,v)
bad=[x for x in data['positive'] if not eval_wires(26,gs,x)[w]]+[x for x in data['negative'] if eval_wires(26,gs,x)[w]]
print('gates',len(gs),'wrong',len(bad))
if not bad:Path(a.output).write_text(json.dumps(gs))
