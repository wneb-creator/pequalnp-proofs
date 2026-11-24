import itertools,json
hood=[1536,272,1056,192,1282,772,1160,584,562,417,85]
V=range(11)
E={(a,b) for a in V for b in V if a<b and (hood[a]>>b)&1}
LV=[{7,10},{2},{0},{8},{4,8},{3}]
LG=[set(),set(),set(),{0},set(),set()]
RV=[{6,9},{5,10},{9,10},{4,5},{1},{6,7}]
RG=[set(),{0},set(),set(),{0},set()]

def evals(I):
 g=[]
 for av,ag,bv,bg in zip(LV,LG,RV,RG):
  a=bool(av&I) or any(g[j] for j in ag)
  b=bool(bv&I) or any(g[j] for j in bg)
  g.append(a and b)
 return g,any(g[j] for j in range(1,6))
H={e for e in E if evals(set(e))[1]}
false_positives=[]
for s in range(1<<11):
 I={i for i in V if (s>>i)&1}
 if evals(I)[1] and not any(a in I and b in I for a,b in E):false_positives.append(s)

def match_bip(n,m,edges):
 adj={i:[] for i in range(n)}
 for a,b in edges:adj[a].append(b)
 M={}
 def aug(a,seen):
  for b in adj[a]:
   if b in seen:continue
   seen.add(b)
   if b not in M or aug(M[b],seen):M[b]=a;return True
  return False
 return sum(aug(a,set()) for a in range(n))

def bipartition(S,edges):
 color={}
 for u in S:
  if u in color:continue
  color[u]=0;q=[u]
  while q:
   a=q.pop()
   for b in S:
    if (min(a,b),max(a,b)) not in edges:continue
    if b not in color:color[b]=1-color[a];q.append(b)
    elif color[b]==color[a]:return None
 return color

restricted=[];bad=[]
for mask in range(1<<11):
 S={i for i in V if (mask>>i)&1};colors=bipartition(S,E)
 if colors is None:continue
 edges=[(a,b) if colors[a]==0 else (b,a) for a,b in H if a in S and b in S]
 nu=match_bip(11,11,edges)
 # Check all source subcircuits retaining any selection of the five top terms.
 # If g0 is needed it must remain dirty, or simplify to an OR of its direct inputs.
 subs=[{i for i in S if (z>>i)&1} for z in range(1<<11)]
 values=[evals(I)[0] for I in subs]
 has0=any(v[0] for v in values)
 dirty0=any(v[0] and not any(a in I and b in I for a,b in E) for I,v in zip(subs,values))
 # A gate0 that is an existing OR of input variables is free.
 free0=not has0 or any(all(v[0]==(i in I) for I,v in zip(subs,values)) for i in S)
 # two multi-input OR operands can coincide under restriction; then their intersection is OR-free
 av=LV[0]&S;bv=RV[0]&S
 free0=free0 or av<=bv or bv<=av
 for ts in range(1<<5):
  tops={j+1 for j in range(5) if (ts>>j)&1}
  ht={e for e in H if set(e)<=S and any(evals(set(e))[0][j] for j in tops)}
  hh=[(a,b) if colors[a]==0 else (b,a) for a,b in ht]
  mm=match_bip(11,11,hh)
  need0=bool(tops&{1,3,4}) and has0
  if need0 and not free0 and not dirty0:continue
  terms=sum(any(v[j] for v in values) for j in tops)
  cost=terms+int(need0 and not free0)
  if mm>cost:bad.append({'S':sorted(S),'tops':sorted(tops),'matching':mm,'and_budget':cost})
 restricted.append({'S':sorted(S),'matching':nu})
print(json.dumps({'original_edges':sorted(E),'accepted_pair_edges':sorted(H),'omitted_edges':sorted(E-H),'original_false_positive_count':len(false_positives),'double_cover_full_matching':match_bip(11,11,list(E)+[(b,a) for a,b in E]),'double_cover_accepted_matching':match_bip(11,11,list(H)+[(b,a) for a,b in H]),'bipartite_induced_restrictions':len(restricted),'max_restricted_matching':max(x['matching'] for x in restricted),'candidate_failures':bad},indent=2))
