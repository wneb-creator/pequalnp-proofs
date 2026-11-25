import argparse,json,random,time
from pathlib import Path
from synth import CNF
from incremental import Incremental

def eval_wires(n,gs,x):
 ws=[bool(x>>i&1) for i in range(n)]
 for op,u,v in gs:ws.append((ws[u] or ws[v]) if op else(ws[u] and ws[v]))
 return ws

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--stars',type=int,default=3);ap.add_argument('--seconds',type=int,default=120);ap.add_argument('--rounds',type=int,default=30);ap.add_argument('--seed',type=int,default=132);ap.add_argument('--output',required=True);ap.add_argument('--control',action='store_true');ap.add_argument('--free-tap',action='store_true');a=ap.parse_args();rng=random.Random(a.seed);d=Path(a.output);d.mkdir(parents=True,exist_ok=True)
 data=json.loads(Path('/tmp/oec/pequalnp-pilot-132/circuit-search/tap61-tests.json').read_text());n=data['inputs'];gs=data['gates'];fo=data['f_output'];to=data['tap_output'];tests=[tuple(t) for t in data['tests']]
 if a.control:gs=gs[:60]+[[1,84,21]]+gs[60:];fo=86;to=85
 order=[3]+rng.sample([i for i in range(12) if i!=3],11);stars=sorted(order[:a.stars]);free=sorted({4*p+j for p in stars for j in range(4)}|{58,59,60}|set(rng.sample(list(range(48,58)),max(1,a.stars//2))))
 (d/'meta.json').write_text(json.dumps({'stars':stars,'free':free,'f_output':fo,'tap_output':to,'seed':a.seed,'free_tap':a.free_tap},indent=2));(d/'seed.json').write_text(json.dumps(gs));c=CNF();params={};flips=set()
 for i in free:
  m=n+i;sa=[c.var() for _ in range(m)];sb=[c.var() for _ in range(m)];t=c.var();c.atleast_one(sa);c.atleast_one(sb)
  for j,sel in enumerate(sa):c.clause(-sel,*sb[j:])
  params[i]=sa,sb,t;op,u,v=gs[i];u,v=sorted((u,v));flips.update(x for j,x in enumerate(sa) if j!=u);flips.update(x for j,x in enumerate(sb) if j!=v)
  if not op:flips.add(t)
 tap_sel=[c.var() for _ in range(n+len(gs))] if a.free_tap else []
 if tap_sel:c.atleast_one(tap_sel);flips.update(v for i,v in enumerate(tap_sel) if i!=to)
 for wire in range(n+len(gs)):
  if wire==fo or (not a.free_tap and wire==to) or any(j not in params and wire in g[1:] for j,g in enumerate(gs)):continue
  uses=[sel[wire] for j,(sa,sb,t) in params.items() if wire<n+j for sel in [sa,sb]]
  if tap_sel:uses.append(tap_sel[wire])
  c.clause(*uses)
 solver=Incremental();rowvalues={};added=set();chosen=rng.sample([t for t in tests if t[1]],6)+[t for t in tests if t[2] is True]+rng.sample([t for t in tests if not t[1] and t[2] is None],8)+rng.sample([t for t in tests if t[2] is False],8);clauses=0;start=time.monotonic();print('free',free,flush=True)
 if a.free_tap:chosen.extend((1<<v,False,v in data['special_inputs']) for v in range(n))
 for k in range(a.rounds):
  for x,y,z in chosen:
   if (x,y,z) in added:continue
   if x not in rowvalues:
    ws=[1 if x>>i&1 else -1 for i in range(n)]
    for i,g in enumerate(gs):
     if i in params:
      sa,sb,t=params[i];aa=c.select(sa,ws);bb=c.select(sb,ws);out=c.typed(aa,bb,t)
     else:
      op,u,v=g;out=c.gate(ws[u],ws[v],op)
     ws.append(out)
    rowvalues[x]=ws
   ws=rowvalues[x];c.clause(ws[fo] if y else -ws[fo])
   if z is not None:
    if tap_sel:
     for wire,sel in enumerate(tap_sel):c.clause(-sel,ws[wire] if z else -ws[wire])
    else:c.clause(ws[to] if z else -ws[to])
   added.add((x,y,z))
  solver.add(c.cs,flips);clauses+=len(c.cs);c.cs=[];print('round',k,'cases',len(added),'inputrows',len(rowvalues),'vars',c.n,'clauses',clauses,flush=True);result=solver.solve(a.seconds);print('result',result,'elapsed',round(time.monotonic()-start,2),flush=True);(d/f'tests-{k}.json').write_text(json.dumps(list(added)))
  if result!=10:break
  model=solver.model(c.n,flips);out=[g.copy() for g in gs]
  for i,(sa,sb,t) in params.items():out[i]=[int(t in model),next(j for j,v in enumerate(sa) if v in model),next(j for j,v in enumerate(sb) if v in model)]
  decoded_tap=next(i for i,v in enumerate(tap_sel) if v in model) if tap_sel else to
  (d/f'candidate-{k}-tap.json').write_text(json.dumps(decoded_tap))
  wrong=[];fw=tw=0
  for x,y,z in tests:
   ws=eval_wires(n,out,x);fwrong=ws[fo]!=y;twrong=z is not None and ws[decoded_tap]!=z;fw+=fwrong;tw+=twrong
   if fwrong or twrong:wrong.append((x,y,z))
  (d/f'candidate-{k}.json').write_text(json.dumps(out));print('wrong',len(wrong),'f',fw,'tap',tw,'tap_wire',decoded_tap,flush=True)
  if not wrong:
   if a.control:(d/'control62.json').write_text(json.dumps(out));print('CONTROL PASSED',flush=True);break
   (d/'solution61.json').write_text(json.dumps({'gates':out,'output':fo,'tap':decoded_tap}));full=[[op,u+1,v+1] for op,u,v in out];full.append([0,0,decoded_tap+1]);full.append([1,fo+1,26+61]);fulltests=json.loads(Path('/tmp/oec/pequalnp-pilot-132/circuit-search/cases.json').read_text());wrongfull=[x for x in fulltests['positive'] if not eval_wires(26,full,x)[-1]]+[x for x in fulltests['negative'] if eval_wires(26,full,x)[-1]];print('full63 wrong',len(wrongfull),flush=True)
   if not wrongfull:(d/'solution63.json').write_text(json.dumps(full));print('SOLVED FULL63',flush=True)
   break
  rng.shuffle(wrong);wrong.sort(key=lambda t:not(t[1] or t[2] is True));chosen=wrong[:min(32,len(wrong))]
 solver.close()

if __name__=='__main__':main()
