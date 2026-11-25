import argparse,json,hashlib,datetime
from pathlib import Path

def reconstruct(compact):
 atoms=compact['atoms'];n=len(atoms);groups={x:[] for x in range(14)}
 for j,a in enumerate(atoms):
  uses=[(k,s) for k,b in enumerate(atoms) if k>j for s,z in enumerate(b['slots']) if j in z['prior']]
  count=len(uses)+(j in compact['final'])
  assert count in (1,2)
  if count==2:
   assert j not in compact['final'] and a['mode'] and a['mode']>0
   owner=a['mode']-1
   assert all(owner in atoms[k]['slots'][side]['primary'] for k,side in uses)
   groups[owner].append(j)
 gates=[];signals=[];proxy={}
 def join(args):
  assert args and len(args)==len(set(args))
  out=args[0]
  for w in args[1:]:
   assert out!=w;gates.append(['or',out,w]);out=14+len(gates)-1
  return out
 for j,a in enumerate(atoms):
  operands=[]
  for s in a['slots']:
   removed=set();args=[]
   for x in s['primary']:
    if groups[x]:
     assert set(groups[x])<=set(s['prior'])
     assert all(k<j for k in groups[x])
     if x not in proxy:proxy[x]=join([x]+[signals[k] for k in groups[x]])
     args.append(proxy[x]);removed.update(groups[x])
    else:args.append(x)
   args.extend(signals[k] for k in s['prior'] if k not in removed)
   operands.append(join(args))
  assert operands[0]!=operands[1]
  gates.append(['and',*operands]);signals.append(14+len(gates)-1)
 output=join([signals[k] for k in compact['final']])
 assert len(gates)==27 and output==40,(len(gates),output)
 return dict(inputs=14,gates=gates,output=output,size=27)

def evaluate(circuit,mask):
 vals=[bool(mask>>i&1) for i in range(14)]
 for op,a,b in circuit['gates']:vals.append(vals[a] and vals[b] if op=='and' else vals[a] or vals[b])
 return vals

def validate(circuit,compact=None,fano=True):
 gates=circuit['gates'];assert len(gates)==27
 for j,(op,a,b) in enumerate(gates):assert op in ('and','or') and a!=b and 0<=a<14+j and 0<=b<14+j
 fanout=[sum(a==w for _,a,b in gates)+sum(b==w for _,a,b in gates) for w in range(41)]
 assert all(fanout[w]>=1 for w in range(40))
 singles=[evaluate(circuit,1<<x) for x in range(14)]
 assert all(any(fanout[w]>=2 and singles[x][w] for w in range(41)) for x in range(14))
 edges=[(p,7+l) for p in range(7) for l in range(7) if (p-l)%7 in (0,1,3)]
 for mask in range(1<<14):
  out=evaluate(circuit,mask)[-1]
  if fano:assert out==any(mask>>a&1 and mask>>b&1 for a,b in edges)
  if compact is not None:
   vals=[]
   for atom in compact['atoms']:
    slot=[any(mask>>x&1 for x in s['primary']) or any(vals[k] for k in s['prior']) for s in atom['slots']];vals.append(slot[0] and slot[1])
   assert out==any(vals[k] for k in compact['final'])
 def derivative(base,seed):
  vals=evaluate(circuit,1<<base);d=[i==seed for i in range(14)]
  for op,a,b in gates:d.append((vals[a] and d[b]) or (d[a] and vals[b]) if op=='and' else d[a] or d[b])
  return d[-1]
 flags=[dict(point=p,line=l-7,forward=derivative(p,l),reverse=derivative(l,p)) for p,l in edges]
 return dict(verdict='PASS',truth_rows=16384,all_flags=flags,double_quiet_flags=[f for f in flags if not f['forward'] and not f['reverse']],scope='Exact Fano circuit' if fano else 'Structural control, not asserted Fano')

def main():
 p=argparse.ArgumentParser();p.add_argument('source');p.add_argument('--structural-control',action='store_true');args=p.parse_args();source=Path(args.source);compact=json.loads(source.read_text());circuit=reconstruct(compact);report=validate(circuit,compact,not args.structural_control);out=source.with_name(source.stem+'.circuit.json');out.write_text(json.dumps(circuit,indent=2)+'\n');report['source_sha256']=hashlib.sha256(source.read_bytes()).hexdigest();report['circuit']=str(out);report['verified_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();out.with_name(out.stem+'.validation.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
if __name__=='__main__':main()
