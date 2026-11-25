import argparse,json
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('input');p.add_argument('output');p.add_argument('--bank',type=int,required=True);p.add_argument('--gates',type=int,required=True);a=p.parse_args()
d=json.loads(Path(a.input).read_text());original=d['gates'][-a.gates:];done={i:i for i in range(a.bank)};remaining=set(range(a.gates));result=[]
while remaining:
 choices=[]
 for i in remaining:
  op,u,v=original[i]
  if u in done and v in done:
   x,y=sorted((done[u],done[v]));choices.append(((y,x,op),i,(op,x,y)))
 assert choices
 _,i,gate=min(choices);remaining.remove(i);done[a.bank+i]=a.bank+len(result);result.append(gate)
assert done[a.bank+a.gates-1]==a.bank+a.gates-1
Path(a.output).write_text(json.dumps({'gates':result}))
