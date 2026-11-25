import argparse,ctypes,json,time,random
from pathlib import Path
import numpy as np
BASE=Path('/tmp/oec/pequalnp-pilot-87/finite_invariants')
CERTS=json.loads((BASE/'rectangle-all-certificates.json').read_text())
LIB=ctypes.CDLL(str(BASE/'rectangle_all_cost.so'))
LIB.rectangle_cost.argtypes=[ctypes.c_int,ctypes.c_uint,ctypes.c_uint]
LIB.rectangle_cost.restype=ctypes.c_longlong
CACHE=[{} for _ in CERTS]
def cost(ci,g):
 c=CERTS[ci]
 p=sum((((g>>r)&1)<<i) for i,r in enumerate(c['positive_rows']))
 n=sum((1-((g>>r)&1))<<i for i,r in enumerate(c['negative_rows']))
 key=(p,n)
 if key not in CACHE[ci]:CACHE[ci][key]=int(LIB.rectangle_cost(ci,p,n))
 return CACHE[ci][key]
def selftest():
 rng=random.Random(2373)
 for ci,c in enumerate(CERTS):
  W=np.array(c['weights'],dtype=np.int64)
  for _ in range(30):
   ps=sorted(rng.sample(range(W.shape[0]),rng.randrange(min(8,W.shape[0]))))
   ns=sorted(rng.sample(range(W.shape[1]),rng.randrange(min(8,W.shape[1]))))
   masks=((np.arange(1<<len(ps))[:,None]>>np.arange(len(ps)))&1)
   expected=int(np.maximum(masks@W[np.ix_(ps,ns)],0).sum(axis=1).max())
   actual=LIB.rectangle_cost(ci,sum(1<<i for i in ps),sum(1<<i for i in ns))
   assert expected==actual,(ci,ps,ns,expected,actual)
def run(banks):
 start=time.monotonic();results=[]
 for bank in banks:
  roots=[int(g,16) for g in bank['state']]
  assert bank['remaining']==len(roots)-1
  tests=[]
  for ci,c in enumerate(CERTS):
   costs=[cost(ci,g) for g in roots];total=sum(costs)
   tests.append(dict(certificate=c['name'],target_total=c['total'],root_costs=costs,cost_sum=total,margin=c['total']-total,excludes=total<c['total']))
  results.append(dict(node=bank['node'],root_count=len(roots),remaining=bank['remaining'],entries=bank['entries'],tests=tests,excludes=any(t['excludes'] for t in tests)))
  print(json.dumps({'node':bank['node'],'root_count':len(roots),'excludes':results[-1]['excludes'],'margins':[t['margin'] for t in tests]}),flush=True)
 return dict(results=results,seconds=time.monotonic()-start,unique_profiles=[len(c) for c in CACHE],excluded=sum(r['excludes'] for r in results),banks=len(results),selftest='390 exact random small-profile comparisons PASS')
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('input');ap.add_argument('output');args=ap.parse_args();selftest()
 src=Path(args.input).read_text()
 banks=json.loads(src) if src.lstrip().startswith('[') else [json.loads(line) for line in src.splitlines()]
 result=run(banks);Path(args.output).write_text(json.dumps(result,indent=2));print(json.dumps({k:v for k,v in result.items() if k!='results'}),flush=True)
