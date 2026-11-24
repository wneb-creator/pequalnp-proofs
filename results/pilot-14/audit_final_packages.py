from pathlib import Path
import json,hashlib,gzip,itertools
r=Path('/tmp/oec/pequalnp-pilot-14/status-review'); packages=['purecore-package','positive-domain-package','slack-split-package-v2','finite-plans-uncompiled-package']
for package in packages:
 p=r/package;m=json.loads((p/'SHA256.json').read_text());assert isinstance(m,dict)
 for n,want in m.items():assert hashlib.sha256((p/n).read_bytes()).hexdigest()==want,(package,n)
 print(package,'manifest PASS',len(m),'files',hashlib.sha256((p/'SHA256.json').read_bytes()).hexdigest())
p=r/'positive-domain-package';d=json.loads((p/'Data414.json').read_text());old=json.loads((p/'Domains12.json').read_text());new=json.loads((p/'Domains15.json').read_text());assert new[:12]==old and len(new)==15
raw=[tuple(int(x,0)for x in z)for z in d['raw']];mask=(1<<252)-1
for marker,dom in zip([4,6,7],new[12:]):
 ix=[j for j,(a,b)in enumerate(d['pairs'])if(a>>marker)&1 and(b>>marker)&1];assert len(ix)==94
 sel=[ix[j%94]for j in range(252)];assert dom['pos']==dom['neg']==sel
 assert dom['embedding']==[j for j in range(9)if j!=marker]and dom['bound']==10
 for i,vals in zip(dom['embedding'],dom['raw']):assert vals==[sum(((raw[i][side]>>a)&1)<<j for j,a in enumerate(sel))for side in range(2)]
 assert all(sum(((raw[marker][side]>>a)&1)<<j for j,a in enumerate(sel))==mask for side in range(2))
 print('positive domain',marker,'94 selectors and all8 raw signatures PASS')
def cpp(x):return'{'+','.join(cpp(v)for v in x)+'}'if isinstance(x,list)else str(x)
selectors=[[x['pos'],x['neg']]for x in new];words=[[[((s[side]>>(64*w))&((1<<64)-1))for side in range(2)for w in range(4)]for s in x['raw']]for x in new];out=[]
for line in(p/'live_theta12.cpp').read_text().splitlines():
 if line.startswith('static constexpr int projectIndex'):line='static constexpr int projectIndex[D][2][252] = '+cpp(selectors)+';'
 if line.startswith('static constexpr U oldRaw'):line='static constexpr U oldRaw[D][8][8] = '+cpp(words)+';'
 out.append(line.replace('int D=12','int D=15').replace('(q<3?13:11)','(q<3?13:q<12?11:10)'))
assert(p/'live_positive15.cpp').read_text()=='\n'.join(out)+'\n'
print('positive C++ exact source delta PASS; claimed gain',round(100*(1159421-998821)/1159421,2),'percent')
p=r/'purecore-package';tokens=iter(map(int,(p/'ablation_seeds.txt').read_text().split()));n=next(tokens);assert n==2;seeds=[]
for _ in range(n):
 k,t,nw=[next(tokens)for _ in range(3)];codes=[]
 for _ in range(nw):codes.append([next(tokens)for _ in range(next(tokens))])
 for q in range(12):
  ng=next(tokens)
  for gi in range(ng):
   op,a,b=[next(tokens)for _ in range(3)];assert op in[0,1,2]and 0<=a<10+gi and(op==2 or 0<=b<10+gi)
  no=next(tokens);assert no==nw
  assert all(0<=next(tokens)<10+ng for _ in range(no))
 seeds.append((k,t,codes))
assert next(tokens,None)is None
assert seeds[0]==(13,2,[[i]for i in range(1,10)]+[[1,3,11],[2,4,11]])
assert seeds[1][0:2]==(12,4)
print('purecore exact case159 and cut12 seed shape/program-index validation PASS')
p=r/'slack-split-package-v2';d=json.loads((p/'Data414.json').read_text());full=(1<<828)-1;mask=(1<<414)-1
phase=lambda z:z^full if z>>477&1 else z
original=[(int(a,0)<<414)|int(b,0)for a,b in d['raw']];raw=[phase(z)for z in original]
rows=json.loads((p/'slack-one-counts-nomemo.json').read_text())['rows'];sigs=[int(x['signal'],0)for x in rows];lookup={z:i for i,z in enumerate(sigs)};od=json.loads((p/'SlackOneOrbitData.json').read_text());assert len(sigs)==154
for z,recipe,actions in zip(sigs,od['recipes'],od['actions']):
 i,j,sa,sb=recipe;assert phase((raw[i]^(full if sa else 0))&(raw[j]^(full if sb else 0)))==z
 fa=sa^int(original[i]!=raw[i]);fb=sb^int(original[j]!=raw[j])
 assert actions==[lookup[phase((original[g[i]]^(full if fa else 0))&(original[g[j]]^(full if fb else 0)))]for g in d['autos']]
groups={}
for i,aa in enumerate(od['actions']):groups.setdefault(str(min(aa)),[]).append(i)
assert groups==od['all_orbits']and len(groups)==23 and len(od['proper_orbits'])==20
for g in od['proper_orbits']:
 assert g['members']==groups[str(g['representative'])]
 assert all(rows[i]['valid_calls']==g['calls']and rows[i]['moves']==g['moves']for i in g['members'])
print('all154x12 actual phase-correct automorphism actions and23/20 orbit census PASS')
def covered(v):
 c=0
 for z in v:c|=((z>>414)^z)&mask
 return c==mask
for name,dup in [('SlackOneFirst01Children.json',False),('SlackOneFirst01DupGChildren.json',True)]:
 doc=json.loads((p/name).read_text());root=[int(z,0)for z in doc['root']];nodes=doc['nodes'];moves=doc['moves'];expect={};actual={}
 def put(kind,m,slack,depth,w):
  if covered(w):expect[(kind,tuple(m))]=(slack,depth,tuple(sorted(w)))
 if not dup:
  for i,a in enumerate(root):put('duplicate',[i],0,4,[a]+root)
 for i,a in enumerate(root):
  for j,b in enumerate(root):
   if i==j:continue
   rest=[z for k,z in enumerate(root)if k not in[i,j]]
   for op,(sa,sb)in enumerate([(0,0),(0,1),(1,0),(1,1)]):
    z=phase((a^(full if sa else 0))&(b^(full if sb else 0)))
    put('merge',[i,j,op],0 if dup else 1,3,[z]+rest)
    if not dup:put('retain_a',[i,j,op],0,3,[z,a]+rest);put('retain_b',[i,j,op],0,3,[z,b]+rest)
 for m in moves:
  nd=nodes[m['node']];actual[(m['kind'],tuple(m['move']))]=(nd['slack'],nd['depth'],tuple(int(z,0)for z in nd['v']))
 assert actual==expect and len(actual)==len(moves)
 assert len(nodes)==doc['summary']['unique_children']and len(moves)==doc['summary']['ordered_valid_moves']
 assert len(set(actual.values()))==len(nodes)
 assert sum(nd['calls']for nd in nodes)==doc['summary']['sum_unique_calls']
 print(name,'complete one-step states/coverage/multiset transport PASS',len(nodes),len(moves))
costs=json.loads((p/'SlackOneAllCaseCosts.json').read_text())['rows'];pairs=[[0,1],[0,2],[0,3],[0,4],[0,6],[4,6]]
assert[(x['pair'],x['sign'])for x in costs]==[(pair,sign)for pair in pairs for sign in range(4)]
assert sum(x['summary']['root_cost'][1]for x in costs)==29233
assert max(y[1]for x in costs for y in x['covered_retain'])==28
assert sum(len(x['hard_consume'])for x in costs)==21
assert max(y[1]for x in costs for y in x['hard_consume'])==181
for row in costs:
 assert row['summary']['root_cost'][0]is False
 assert row['hard_consume']==[z for z in row['covered_consume']if z[1]>60]
 assert row['hard_retain']==[z for z in row['covered_retain']if z[1]>60]
 assert all(0<=ix<180 for ix,c in row['covered_consume'])and all(0<=ix<360 for ix,c in row['covered_retain'])
print('24-case costs/sign-order/summaries PASS; no recursive cost rerun')
p=r/'finite-plans-uncompiled-package';m=json.loads((p/'signed-cases-manifest.json').read_text());files=list((p/'plans').glob('*.lean'));assert len(files)==40 and len(m)==8
assert not list(p.glob('**/*.olean'))
for c in m:
 assert c['pair_index']in[2,5]and c['pair']==pairs[c['pair_index']]
 assert c['actual_sign']==c['canonical_sign']^2
 assert c['hard_duplicates']==[] and len(c['modules'])==5
 assert c['closed']==c['modules'][-1]
 for mod in c['modules']:
  s=(p/'plans'/f'{mod}.lean').read_text();assert c['namespace']in s
  assert not any(bad in s for bad in ['sorry','native_decide','bv_decide','axiom','_root_','"'])
 common=(p/'plans'/(c['modules'][0]+'.lean')).read_text();i,j=c['pair'];assert f'raw.getD {i} zero'in common and f'raw.getD {j} zero'in common and f'getD {c["canonical_sign"]} zero'in common
print('40 UNCOMPILED plans /8 cases exact manifests and pair/sign references PASS; no proof claim')
