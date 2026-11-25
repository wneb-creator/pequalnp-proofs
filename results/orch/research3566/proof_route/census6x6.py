import itertools,json,time
from pathlib import Path

BASE=Path('/tmp/oec/pequalnp-pilot-178/gap3566/proof_route')
t0=time.monotonic();LIMIT=55
profiles=[(4,3,3,2,2,2),(3,3,3,3,2,2)]
maps=[]
for p in itertools.permutations(range(6)):
    maps.append([sum(1<<p[i] for i in range(6) if m>>i&1) for m in range(64)])
def transpose(rows):
    return [sum(1<<i for i in range(6) if rows[i]>>j&1) for j in range(6)]
canon_cache={}
def canonical(rows):
    key=tuple(sorted(rows))
    if key not in canon_cache:
        rs2=transpose(rows)
        canon_cache[key]=min(tuple(sorted(mapping[x] for x in rs))
            for rs in [rows,rs2] for mapping in maps)
    return canon_cache[key]
def cycle_basis(n,edges):
    adj=[set() for _ in range(n)]
    for a,b in edges:adj[a].add(b);adj[b].add(a)
    parent={};depth={};cycles=[]
    for root in range(n):
        if root in parent:continue
        parent[root]=root;depth[root]=0;stack=[root]
        while stack:
            a=stack.pop()
            for b in sorted(adj[a]):
                if b not in parent:parent[b]=a;depth[b]=depth[a]+1;stack.append(b)
    for a,b in edges:
        if parent.get(a)==b or parent.get(b)==a:continue
        x,y=a,b;left=[x];right=[y]
        while depth[x]>depth[y]:x=parent[x];left.append(x)
        while depth[y]>depth[x]:y=parent[y];right.append(y)
        while x!=y:x=parent[x];y=parent[y];left.append(x);right.append(y)
        cycles.append(left+right[-2::-1])
    return cycles
classes={};visited=0;accepted=0;profile_counts={};complete=True
def visit(rows,cols,opts,profile):
    global visited,accepted
    visited+=1
    if visited%1024==0 and time.monotonic()-t0>LIMIT:raise TimeoutError
    i=len(rows)
    if i==6:
        if min(cols)<2 or sum(c*(c-1)//2 for c in cols)>15:return
        accepted+=1;profile_counts[str(profile)]=profile_counts.get(str(profile),0)+1
        key=canonical(rows)
        if key not in classes:classes[key]={'rows':rows[:],'count':0}
        classes[key]['count']+=1
        return
    for mask in opts[i]:
        if any((r&mask).bit_count()>1 for r in rows):continue
        newcols=[c+(mask>>j&1) for j,c in enumerate(cols)]
        if max(newcols)>4 or any(c+(5-i)<2 for c in newcols):continue
        if sum(c*(c-1)//2 for c in newcols)>15:continue
        visit(rows+[mask],newcols,opts,profile)
try:
    for profile in profiles:
        opts=[]
        for i,d in enumerate(profile):
            opts.append([(1<<i)|sum(1<<j for j in chosen)
                for chosen in itertools.combinations([j for j in range(6) if j!=i],d-1)])
        visit([], [0]*6,opts,profile)
except TimeoutError:complete=False
out=[]
for i,(key,info) in enumerate(sorted(classes.items())):
    rows=info['rows'];edges=[[a,6+b] for a in range(6) for b in range(6) if rows[a]>>b&1]
    item={'name':f'bip6x6_16_class{i}','n':12,'edges':edges,
          'matching':[[i,6+i] for i in range(6)],'tau':6,'expected_size':21,
          'left_degrees':[x.bit_count() for x in rows],
          'right_degrees':[x.bit_count() for x in transpose(rows)],
          'canonical_rows':list(key),'cycle_basis':cycle_basis(12,edges),
          'profile_ordered_labelings':info['count']}
    (BASE/(item['name']+'.json')).write_text(json.dumps(item,indent=2)+'\n');out.append(item)
report={'complete':complete,'profiles':profiles,'visited_prefixes':visited,
        'accepted_profile_ordered':accepted,'profile_counts':profile_counts,
        'isomorphism_classes':len(out),'elapsed_seconds':time.monotonic()-t0,'classes':out}
(BASE/'census6x6.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
