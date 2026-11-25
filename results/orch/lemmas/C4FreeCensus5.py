import itertools, json, time

start=time.monotonic()
n=5
target_edges=12
options=[[mask for mask in range(1<<n) if mask>>a&1] for a in range(n)]
graphs=[]
nodes=0

def visit(rows,count):
    global nodes
    nodes+=1
    a=len(rows)
    if a==n:
        if count==target_edges: graphs.append(tuple(rows))
        return
    remaining=n-a-1
    for mask in options[a]:
        total=count+mask.bit_count()
        if total+remaining>target_edges or total+n*remaining<target_edges:
            continue
        if any((mask&row).bit_count()>1 for row in rows):
            continue
        visit(rows+[mask],total)

visit([],0)
perms=list(itertools.permutations(range(n)))
def canonical(rows):
    return min(tuple(sorted(sum(((rows[order[a]]>>b)&1)<<a for a in range(n))
                            for b in range(n))) for order in perms)
classes={}
for rows in graphs:
    key=canonical(rows)
    if key not in classes: classes[key]={'count':0,'representative':[[b for b in range(n) if row>>b&1] for row in rows]}
    classes[key]['count']+=1
print(json.dumps({'n':n,'edges':target_edges,'fixed_diagonal':True,'recursion_nodes':nodes,
                  'labelled_graphs':len(graphs),'isomorphism_classes':len(classes),
                  'classes':[dict(canonical_columns=list(key),**value) for key,value in sorted(classes.items())],
                  'elapsed_seconds':time.monotonic()-start},indent=2))
