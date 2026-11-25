"""Independent semantic replay for a recorded finite Live search trace."""
import argparse,importlib.util,json
from pathlib import Path
BASE=Path('/tmp/oec/pequalnp-pilot-87')
def mod(name,path):
 s=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
live=mod('live',BASE/'library_route/live_search.py');cof=mod('cof',BASE/'status_review/cofactor_prune.py')
def main():
 ap=argparse.ArgumentParser();ap.add_argument('trace');ap.add_argument('--limit',type=int,default=0);a=ap.parse_args()
 nodes={};done={};signals={};header=None
 for line in Path(a.trace).read_text().splitlines():
  x=json.loads(line)
  if x['event']=='node':nodes[x['id']]=x
  elif x['event']=='done':done[x['id']]=x
  elif x['event']=='signal':signals[x['id']]=int(x['hex'],16)
  elif x['event']=='header':header=x
 assert header and len(nodes)==len(done)
 mode=bool(header['mode']);profiles=[(live.FULL^x,15 if mode else 16)for x in live.INPUTS]
 profiles += [(m,l)for m,l,_ in cof._extra_cofactors(mode)]
 profiles += [(m,l)for m,l,_ in cof.supplemental_cofactors(mode)]
 for p in json.loads((BASE/'status_review/extra-profile-cuts.json').read_text())['profiles']:
  mask=live.FULL
  for v in p['zeroes']:mask &=live.FULL^live.INPUTS[v]
  for v in p['ones']:mask &=live.INPUTS[v]
  profiles.append((mask,p['lower']))
 assert signals[header['target']]==live.TARGET
 histories={};counts={};checked=0
 for index,node in sorted(nodes.items()):
  op,ai,bi,zi,keep=node['step'];av,bv,zv=signals[ai],signals[bi],signals[zi]
  assert live.opval(op,av,bv)==zv
  parent=node['parent'];history=histories[parent]+[(op,av,bv)]if parent else[(op,av,bv)]
  histories[index]=history
  state=[signals[x]for x in node['state']]
  if parent:
   ps=nodes[parent]['state'];expected=[x for x in ps if(x!=ai or keep&1)and(x!=bi or keep&2)]+[zi]
   assert sorted(expected)==node['state'],('transition',index)
   assert node['remaining']==nodes[parent]['remaining']-1
  else:assert set(state)==set(live.INPUTS)|{zv}
  d=done[index];kind=d['kind'];counts[kind]=counts.get(kind,0)+1
  if kind=='row':
   p,n=d['a'],d['b'];assert live.TARGET>>p&1 and not live.TARGET>>n&1
   assert all((v>>p&1)==(v>>n&1)for v in state)
  elif kind=='cofactor':
   mask,lower=profiles[d['a']];mass=sum((v&mask)in(0,mask)for v in state);assert mass==d['c']
   paid=cof.paid_pool(state,mask,mode,history);assert paid is not None
   assert lower+mass>node['remaining']+paid[0],('cofactor',index)
  elif kind=='memo':assert d['a'] in nodes and d['a']<index
  elif kind in('formula0','formula1','expand','open','empty','found'):pass
  else:raise AssertionError(kind)
  checked+=1
  if a.limit and checked>=a.limit:break
 print(json.dumps(dict(checked=checked,total_nodes=len(nodes),signals=len(signals),kinds=counts,root_status=done[1]['kind'],note='Row/cofactor/transition checks only; closure and complete branch coverage remain separate')))
if __name__=='__main__':main()
