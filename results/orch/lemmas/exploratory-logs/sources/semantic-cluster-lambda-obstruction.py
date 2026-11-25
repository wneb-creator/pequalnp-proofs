import json

k = 4
n = 5*k + 3
a = 0
U = list(range(1, 1+k))
V = list(range(1+k, 1+2*k))
ZU = list(range(1+2*k, 1+3*k))
ZV = list(range(1+3*k, 1+4*k))
s1, s2 = 1+4*k, 2+4*k
owners = list(range(3+4*k, 3+5*k))
edges = [(a,z) for z in ZU+ZV] + list(zip(U,ZU)) + list(zip(V,ZV)) + [(s1,v) for v in V] + [(s2,u) for u in U] + [(z,u) for z,u in zip(owners,U)] + [(z,v) for z,v in zip(owners,V)]
adj = [set() for _ in range(n)]
for u,v in edges:
    adj[u].add(v)
    adj[v].add(u)
assert all(len(adj[u]&adj[v]) <= 1 for u in range(n) for v in range(u))
assert all(adj[u]&adj[v] == {z} for u,v,z in zip(U,V,owners))
length = (1 << n)//8
inputs=[]
for i in range(n):
    if i < 3:
        pattern = bytes([0xaa, 0xcc, 0xf0][i:i+1])
    else:
        block = 1 << (i-3)
        pattern = bytes(block) + bytes([255])*block
    inputs.append(int.from_bytes(pattern*(length//len(pattern)), 'little'))
target=0
for u,v in edges:
    target |= inputs[u]&inputs[v]
banks=[inputs[u]|inputs[v] for u,v in zip(U,V)]
g=banks[0]
for bank in banks[1:]:
    g &= bank
h1=g&inputs[s1]
h2=g&inputs[s2]
assert all(h1&inputs[z]&~target == 0 for z in ZU)
assert all(h2&inputs[z]&~target == 0 for z in ZV)
x1=sum(1<<u for u in U+[s1])
x2=sum(1<<v for v in V+[s2])
assert (h1>>x1)&1 and not (target>>x1)&1
assert (h2>>x2)&1 and not (target>>x2)&1
assert (target>>(x1|x2))&1
assert not any((h1>>((1<<u)|(1<<v)))&1 for u,v in edges)
assert not any((h2>>((1<<u)|(1<<v)))&1 for u,v in edges)
report={'inputs':n,'edges':edges,'four_cycle_free':True,'common_raw':a,'centres':[ZU,ZV],
        'witness_supports':[U+[s1],V+[s2]],'each_witness_independent':True,
        'witness_union_independent':False,'shared_AND_ancestors':k+1,'payload_roots':2,
        'centre_union':2*k,'OR_disagreements':k,'claimed_no_disagreement_bound_fails':2*k > k+3,
        'payloads_edge_active':False,'raw_banks':list(zip(U,V)),'unique_bank_centres':owners,
        'scope':'Unique bank centres and C4 do not force compatible raw OR choices; abstract aggregate centre charge fails without common independent witness; excluded by minimal-circuit edge activity. Not a gap refutation.'}
print(json.dumps(report,indent=2))
