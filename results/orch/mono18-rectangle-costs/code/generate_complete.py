from pathlib import Path
from collections import defaultdict
import json
base=Path(__file__).resolve().parent
census=base.parent/'mono18-oredge-weak-census'
weights=json.loads((census/'weights.json').read_text());profiles=json.loads((census/'profiles.json').read_text())
groups=defaultdict(list)
for i,p in enumerate(profiles):groups[p['weight']].append((i,p))
blocks=[];byweight=defaultdict(list)
for m,rs in sorted(groups.items()):
 work=0;cur=[]
 for i,r in rs:
  k=1<<min(r['positive_mask'].bit_count(),r['negative_false_mask'].bit_count())
  if cur and (work+k>2560 or len(cur)>=64):
   n=len(blocks);blocks.append(dict(id=n,weight=m,profiles=cur,subsets=work));byweight[m].append(n);cur=[];work=0
  cur.append(i);work+=k
 if cur:
  n=len(blocks);blocks.append(dict(id=n,weight=m,profiles=cur,subsets=work));byweight[m].append(n)
locator={}
for m,ids in byweight.items():
 s='import Mono18RectangleBase\n\nnamespace PEqualNP.Outside.L_meta_2373.Mono18Rectangle\n\n'
 for bid in ids:
  block=blocks[bid];encoded=[];rnum=weights[m]['rows'];cnum=weights[m]['cols']
  for offset,i in enumerate(block['profiles']):
   p=profiles[i];assert p['cost']>=0
   code=p['positive_mask']+(p['negative_false_mask']<<rnum)+(p['cost']<<(rnum+cnum));encoded.append(code);locator[str(i)]=dict(block=bid,offset=offset,weight=m,record=hex(code))
  s+='set_option maxRecDepth 16384 in\nset_option maxHeartbeats 0 in\ndef block'+str(bid)+' : {xs : List Nat // xs.all (checkRecord '+str(m)+') = true} :=\n  ⟨['+','.join(hex(x) for x in encoded)+'], by decide +kernel⟩\n\n'
 s+='end PEqualNP.Outside.L_meta_2373.Mono18Rectangle\n'
 (base/('Mono18RectangleCost'+str(m)+'.lean')).write_text(s)
s=''.join('import Mono18RectangleCost'+str(m)+'\n' for m in byweight)+'\nnamespace PEqualNP.Outside.L_meta_2373.Mono18Rectangle\n\ndef blocks : List Block := [\n'
s+=',\n'.join('  ⟨'+str(b['weight'])+', block'+str(b['id'])+'⟩' for b in blocks)+']\n\nend PEqualNP.Outside.L_meta_2373.Mono18Rectangle\n'
(base/'Mono18RectangleCosts.lean').write_text(s)
(base/'blocks.json').write_text(json.dumps(blocks,indent=2));(base/'profile-locator.json').write_text(json.dumps(locator,indent=2))
summary=dict(profiles=len(profiles),blocks=len(blocks),subsets=sum(b['subsets'] for b in blocks),weights=len(byweight),sources={p.name:p.stat().st_size for p in base.glob('Mono18Rectangle*.lean')})
(base/'generation-summary.json').write_text(json.dumps(summary,indent=2));print(json.dumps(summary,indent=2))

plan=[]
for m in range(19):
 f=base/('Mono18RectangleCost'+str(m)+'.lean');s=f.read_text();parts=s.split('set_option maxRecDepth 16384 in\n')
 prefix=parts[0];defs=[('set_option maxRecDepth 16384 in\n'+x).split('end PEqualNP.Outside.L_meta_2373.Mono18Rectangle')[0] for x in parts[1:]]
 if len(defs)<=8:plan.append(f.name)
 else:
  names=[]
  for k in range(0,len(defs),8):
   name='Mono18RectangleCost'+str(m)+'Part'+str(k//8);names.append(name);(base/(name+'.lean')).write_text(prefix+''.join(defs[k:k+8])+'end PEqualNP.Outside.L_meta_2373.Mono18Rectangle\n');plan.append(name+'.lean')
  f.write_text(''.join('import '+n+'\n' for n in names));plan.append(f.name)
plan.append('Mono18RectangleCosts.lean');(base/'compile-plan.json').write_text(json.dumps(plan,indent=2))
