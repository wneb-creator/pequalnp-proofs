from itertools import product
import json
m = n = 4
qualifying = 0
minimum_surplus = None
extremal = []
for rows in product(range(1 << n), repeat=m):
    if any((rows[a] & rows[b]).bit_count() > 1 for a in range(m) for b in range(a)):
        continue
    qualifying += 1
    adjacent = list(rows)
    for j in range(n):
        adjacent.append(sum(1 << i for i in range(m) if (rows[i] >> j) & 1))
    covers = []
    for mask in range(1 << (m+n)):
        left = mask & ((1 << m)-1)
        right = mask >> m
        if any(not (left >> i)&1 and rows[i] & ~right for i in range(m)):
            continue
        if any((left >> i)&1 and not (rows[i] & ~right) for i in range(m)):
            continue
        if any((right >> j)&1 and not (adjacent[m+j] & ~left) for j in range(n)):
            continue
        covers.append(mask)
    assert covers
    edge_count = sum(row.bit_count() for row in rows)
    tau = min(mask.bit_count() for mask in covers)
    total = sum(mask.bit_count() for mask in covers)
    surplus = total-edge_count-tau
    assert surplus >= 0, (rows, covers, total, edge_count, tau)
    if minimum_surplus is None or surplus < minimum_surplus:
        minimum_surplus=surplus
        extremal=[]
    if surplus == minimum_surplus and len(extremal)<12:
        extremal.append({'rows':rows,'edges':edge_count,'minimum_cover':tau,'cover_weight':total})
print(json.dumps({'scope':'all 65536 bipartite 4 by 4 graphs filtered for no four-cycle','qualifying_graphs':qualifying,'min_surplus':minimum_surplus,'extremal_examples':extremal,'claim':'sum of sizes of inclusion-minimal vertex covers >= edges + minimum vertex-cover size'},indent=2))
