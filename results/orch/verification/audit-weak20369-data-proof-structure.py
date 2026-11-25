from pathlib import Path
import re,json,hashlib,collections
BASE=Path('/tmp/oec/pequalnp-pilot-87')
fpath=BASE/'library_route/mono18-weak-dag/complete-fixture-20369.json'
f=json.loads(fpath.read_text())
dpath=BASE/'status_review/Weak20369Data.lean'; spath=BASE/'status_review/Weak20369Supports.lean'
d=dpath.read_text(); s=spath.read_text(); mask=(1<<1024)-1
vals={int(k):int(v,16) for k,v in f['signals'].items()}
actual={int(k):int(v,16) for k,v in re.findall(r'^def s(\d+) : Sig := (0x[0-9a-f]+)$',d,re.M)}
assert actual==vals
edges=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
truth=lambda r:any((r>>a)&(r>>b)&1 for a,b in edges)
graph=sum(int(truth(r))<<r for r in range(1024))
def decl(text,name):
 m=re.search(r'^def '+name+r'\b.*?:=',text,re.M); assert m,name
 e=re.search(r'^(?:def |lemma |end )',text[m.end():],re.M)
 return text[m.end():m.end()+e.start() if e else len(text)].strip()
def vector(text,name,sig=False):
 z=decl(text,name); assert z.startswith('![') and z.endswith(']'),(name,z)
 return [int(x.strip()[1:] if sig else x.strip()) for x in z[2:-1].split(',')]
def entries(name):
 return [(tuple(map(int,a.split(','))),int(b)) for a,b in re.findall(r'\(!\[([\d, ]+)\], s(\d+)\)',decl(d,name))]
def supports(name):
 return [set(map(int,re.findall(r'\d+',a))) for a in re.findall(r'\{([^}]*)\}',decl(s,name))]
def nested(name,labels=False):
 z=decl(s,name); assert z.startswith('![') and z.endswith(']')
 ans=[]
 for a in re.findall(r'\[([^\[\]]*)\]',z[2:-1]):
  if labels:ans.append([(kind, int(v) if kind=='inl' else int(v=='true')) for kind,v in re.findall(r'Sum\.(inl|inr) (\d+|true|false)',a)])
  else:ans.append(list(map(int,re.findall(r's(\d+)',a))))
 return ans
report={'fixture_sha256':hashlib.sha256(fpath.read_bytes()).hexdigest(),'data_sha256':hashlib.sha256(dpath.read_bytes()).hexdigest(),'supports_sha256':hashlib.sha256(spath.read_bytes()).hexdigest(),'truth_words':len(vals),'nodes':[]}
for nid in [9611,20369]:
 n=f['nodes'][str(nid)]; state=n['node']['state']; k=n['node']['remaining']; ids=vector(d,'signal'+str(nid),True); total=vector(d,'total'+str(nid)); tags=vector(d,'tag'+str(nid)); es=entries('entries'+str(nid)); cuts=entries('cuts'+str(nid))
 assert ids==n['basis']['roots'] and total==n['basis']['total'] and [ids[t] for t in tags]==state
 assert [tags.count(i) for i in range(11)]==total
 assert es==[(tuple(e['counts']),e['signal']) for e in n['entries']]
 expected=[]
 for c in n['cuts']:
  a,b=n['entries'][c['left']],n['entries'][c['right']]
  cs=tuple(x+y for x,y in zip(a['counts'],b['counts']))
  assert vals[c['signal']]==(vals[a['signal']]&vals[b['signal']] if c['op']==0 else vals[a['signal']]|vals[b['signal']])
  assert c['remaining']==k-sum(cs)+1
  expected.append((cs,c['signal']))
 assert cuts==expected
 srcs=re.findall(r'Sum\.inl (\d+)|Sum\.inr \((\d+), (\d+), (\d+)\)',decl(d,'sources'+str(nid)))
 assert len(srcs)==len(es)
 for ei,(cs,v) in enumerate(es):
  assert all(c<=t for c,t in zip(cs,total))
  src=srcs[ei]
  if src[0]:
   j=int(src[0]);assert cs==tuple(int(q==j) for q in range(11)) and v==ids[j]
  else:
   a,b,op=map(int,src[1:]);assert a<ei and b<ei and op in [0,1]
   assert cs==tuple(x+y for x,y in zip(es[a][0],es[b][0]))
   assert vals[v]==(vals[es[a][1]]&vals[es[b][1]] if op==0 else vals[es[a][1]]|vals[es[b][1]])
   assert vals[v] not in [0,mask,vals[es[a][1]],vals[es[b][1]]]
 rows=[tuple(map(int,p)) for p in re.findall(r'\(⟨(\d+), by decide⟩, ⟨(\d+), by decide⟩\)',decl(d,'rows'+str(nid)))]
 assert all(truth(p) and not truth(q) for p,q in rows)
 kept={(c,vals[v]) for c,v in es}; blocked={(c,vals[v]) for c,v in cuts}; census=collections.Counter()
 for ac,av in es:
  for bc,bv in es:
   cs=tuple(x+y for x,y in zip(ac,bc)); a,b=vals[av],vals[bv]
   if a==b or any(c>t for c,t in zip(cs,total)):continue
   for op in [0,1]:
    z=a&b if op==0 else a|b
    if z in [0,mask,a,b]:continue
    census['fresh_candidates']+=1
    if (cs,z) in kept:census['entry']+=1
    elif (cs,z) in blocked:census['cut']+=1
    else:
     assert any(not ((z>>p&1) and not(z>>q&1)) and all(cs[j]>=total[j] or not ((vals[v]>>p&1) and not(vals[v]>>q&1)) for j,v in enumerate(ids)) for p,q in rows)
     census['row']+=1
 assert (tuple(total),graph) not in kept
 ss=supports('support'+str(nid)); labs=nested('childLabels'+str(nid),True); ws=nested('childWs'+str(nid)); caps=vector(s,'childCap'+str(nid))
 assert len(ss)==len(es)==len(labs)==len(ws)==len(caps)==len(n['children'])
 for i,(support,labels,words,cap,edge) in enumerate(zip(ss,labs,ws,caps,n['children'])):
  assert edge['entry']==i
  assert tuple(sum(tags[r]==j for r in support) for j in range(11))==es[i][0]
  basis={('inl',r) for r in range(len(state)) if r not in support}|{('inr',0),('inr',1)}
  assert len(labels)==len(set(labels)) and set(labels)==basis
  assert [state[r] if kind=='inl' else es[i][1] for kind,r in labels]==words
  child=f['nodes'][str(edge['child'])]['node']
  assert words==child['state'] and cap==child['remaining']
  assert len(basis)+(k-len(state))<=cap+1
 if cuts:
  gs=supports('gateSupport'); gl=nested('gateLabels',True); gc=vector(s,'gateCap')
  for i,((cs,v),support,labels,cap) in enumerate(zip(cuts,gs,gl,gc)):
   assert tuple(sum(tags[r]==j for r in support) for j in range(11))==cs
   basis={('inl',r) for r in range(len(state)) if r not in support}|{('inr',0)}
   assert len(labels)==len(set(labels)) and set(labels)==basis
   assert cap==n['cuts'][i]['remaining'] and len(basis)+(k-len(state)+1)<=cap+1
 report['nodes'].append({'node':nid,'entries':len(es),'gate_cuts':len(cuts),'rows':len(rows),'child_labels':len(labs),'census':dict(census)})
report['verdict']='PASS finite data and current uncompiled support source; not a completed-node proof'
print(json.dumps(report,indent=2))
