import itertools,json,time
from pathlib import Path

BASE=Path('/tmp/oec/pequalnp-pilot-178/gap3566/proof_route')
t0=time.monotonic()
free=[(i,j) for i in range(5) for j in range(5) if i!=j]
perms=list(itertools.permutations(range(5)))
maps=[]
for p in perms:
    maps.append([sum(1<<p[i] for i in range(5) if m>>i&1) for m in range(32)])
def transpose(rows):
    return [sum(1<<i for i in range(5) if rows[i]>>j&1) for j in range(5)]
def canonical(rows):
    return min(tuple(sorted(mapping[x] for x in rs)) for rs in [rows,transpose(rows)] for mapping in maps)
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
classes={};labelled=0
for chosen in itertools.combinations(free,7):
    rows=[1<<i for i in range(5)]
    for i,j in chosen:rows[i]|=1<<j
    if any((rows[i]&rows[j]).bit_count()>1 for i in range(5) for j in range(i)):continue
    labelled+=1
    key=canonical(rows)
    if key not in classes:classes[key]={'rows':rows,'labelled_with_fixed_matching':0}
    classes[key]['labelled_with_fixed_matching']+=1
out=[]
for i,(key,info) in enumerate(sorted(classes.items())):
    rows=info['rows'];edges=[[a,5+b] for a in range(5) for b in range(5) if rows[a]>>b&1]
    item={'name':f'bip5x5_12_class{i}','n':10,'edges':edges,
          'matching':[[i,5+i] for i in range(5)],'tau':5,'expected_size':16,
          'left_degrees':[x.bit_count() for x in rows],
          'right_degrees':[x.bit_count() for x in transpose(rows)],
          'canonical_rows':list(key),'cycle_basis':cycle_basis(10,edges),
          'labelled_with_fixed_matching':info['labelled_with_fixed_matching']}
    (BASE/(item['name']+'.json')).write_text(json.dumps(item,indent=2)+'\n');out.append(item)
report={'free_edge_choices':77520,'accepted_labelled':labelled,'isomorphism_classes':len(out),
        'elapsed_seconds':time.monotonic()-t0,'classes':out}
(BASE/'census5x5.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
