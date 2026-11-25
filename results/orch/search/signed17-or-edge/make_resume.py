"""Export only completed nontrivial state exclusions from a search trace."""
import argparse,hashlib,json
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('trace');p.add_argument('output');a=p.parse_args()
source=Path(a.trace);done={};signals={};sha=hashlib.sha256()
with source.open('rb')as f:
 for raw in f:
  sha.update(raw);x=json.loads(raw)
  if x['event']=='done'and x['kind']in('expand','formula0','formula1'):done[x['id']]=x['kind']
  elif x['event']=='signal':signals[x['id']]=x['hex']
nodes=[]
with source.open()as f:
 for raw in f:
  x=json.loads(raw)
  if x['event']=='node'and x['id']in done:nodes.append(x)
with Path(a.output).open('w')as f:
 f.write(sha.hexdigest()+'\n'+str(len(nodes))+'\n')
 for x in nodes:f.write(' '.join(map(str,[x['id'],x['remaining'],len(x['state'])]))+' '+' '.join(signals[i]for i in x['state'])+'\n')
print(json.dumps(dict(source_sha256=sha.hexdigest(),completed_states=len(nodes),output_bytes=Path(a.output).stat().st_size)))
