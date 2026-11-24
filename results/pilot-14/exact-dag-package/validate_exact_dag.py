from pathlib import Path
import json,collections,time,sys
P=Path(__file__).parent
D=json.loads((P/'Data414.json').read_text());DOM=json.loads((P/'Domains12.json').read_text());MASK=(1<<414)-1;OLDMASK=(1<<252)-1
raw=[tuple(int(x,0)for x in a)for a in D['raw']]
def eval_recipe(recipe,perm):
 st=[]
 for tok in recipe:
  if tok<=9:st.append(raw[perm[tok-1]])
  elif tok==10:
   a=st.pop();st.append((a[0]^MASK,a[1]^MASK))
  else:
   b=st.pop();a=st.pop();st.append(tuple(x&y if tok==11 else x|y for x,y in zip(a,b)))
 assert len(st)==1
 return st[0]
def projection(s,q):
 dom=DOM[q]
 return tuple(sum(((s[z]>>i)&1)<<j for j,i in enumerate(dom['pos'if z==0 else'neg']))for z in range(2))
for t in map(int,sys.argv[1:] or ['5','4']):
 started=time.monotonic();d=json.loads((P/f'PrunedDagT{t}.json').read_text());ws=d['wires'];rs=d['records'];sigs=[tuple(int(w[z],0)for z in('p','n'))for w in ws]
 actions={}
 for w,s in zip(ws,sigs):
  a=tuple(eval_recipe(w['recipe'],p)for p in D['autos']);assert a[0]==s;actions[s]=a
 def action(s):
  if s not in actions:
   actions[s]=tuple(tuple(sum(((s[z]>>a)&1)<<b for b,a in enumerate(ix))for z in range(2))for ix in D['auto_indices'])
  return actions[s]
 def key(v):
  vv=[action(s)for s in v]
  return min(tuple(sorted(a[g]for a in vv))for g in range(12))
 rowkeys={}
 for j,r in enumerate(rs):
  k=(r['k'],r['t'],key([sigs[a]for a in r['v']]))
  assert k not in rowkeys
  rowkeys[k]=j
 projections={(a,q):projection(s,q)for a,s in enumerate(sigs)for q in range(12)}
 programcount=0;branchcount=0;edgecount=0
 for j,r in enumerate(rs):
  assert len(r['programs'])==12
  for q,pg in enumerate(r['programs']):
   vals=[tuple(a)for a in DOM[q]['raw']]+[(0,0),(OLDMASK,OLDMASK)]
   for op,*args in pg['gates']:
    assert op in(0,1,2) and len(args)==(1 if op==2 else 2) and all(0<=a<len(vals)for a in args)
    a=vals[args[0]]
    if op==2:z=(a[0]^OLDMASK,a[1]^OLDMASK)
    else:
     b=vals[args[1]];z=tuple(x&y if op==0 else x|y for x,y in zip(a,b))
    vals.append(z)
   assert len(pg['outputs'])==len(r['v'])
   assert [vals[a]for a in pg['outputs']]==[projections[(a,q)]for a in r['v']]
   programcount+=1
  if r['kind']==1:
   q=r['prefix_domain'];c=sum(projections[(a,q)]in((0,0),(OLDMASK,OLDMASK))for a in r['v'])
   assert len(r['programs'][q]['gates'])+r['k']<DOM[q]['bound']+c
   assert not r['children'];continue
  assert r['kind']==2;branchcount+=1;v=[sigs[a]for a in r['v']];vs=set(v);expected=set()
  def next_states(a,b,op):
   if op==2:z=(a[0]^MASK,a[1]^MASK);nt=r['t']-1;rest=vs-{a};nkeep=2
   else:
    z=tuple(x&y if op==0 else x|y for x,y in zip(a,b));nt=r['t'];rest=vs-{a,b};nkeep=4
   if z in vs or z in((0,0),(MASK,MASK)):return
   for keep in range(nkeep):
    w=rest|{z}
    if keep&1:w.add(a)
    if keep&2:w.add(b)
    nk=r['k']-1
    if len(w)>nk-nt+1:continue
    covered=0
    for s in w:covered|=s[0]^s[1]if nt else s[0]&~s[1]
    if covered!=MASK:continue
    expected.add(rowkeys[(nk,nt,key(w))])
  for ia,a in enumerate(v):
   for b in v[ia+1:]:
    next_states(a,b,0);next_states(a,b,1)
   if r['t']:next_states(a,None,2)
  assert expected==set(r['children']),(t,j,len(expected),len(r['children']),expected-set(r['children']),set(r['children'])-expected)
  edgecount+=len(expected)
 print(json.dumps({'t':t,'rows':len(rs),'wires':len(ws),'branches':branchcount,'programs_verified':programcount,'distinct_edges_verified':edgecount,'seconds':round(time.monotonic()-started,3),'status':'Independent Python replay of all rows, programs, and complete legal child sets; not a Lean proof.'}),flush=True)
