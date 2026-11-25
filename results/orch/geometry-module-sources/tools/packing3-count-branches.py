import json
from pathlib import Path

p = Path('/tmp/oec/pequalnp-pilot-62')
d = json.loads((p / 'packing3-blocks.json').read_text())
blocks = d['blocks']

def ok(s, b):
    return not (s[0] & b[0]) and not (s[4] & b[1])

def step(s, b):
    return (s[0] | b[0], s[1] | b[2], s[2] | b[1],
            s[3] | (s[2] & b[1]), s[4] | (s[3] & b[1]), s[5] + 1)

def prune(s, bs):
    upper = s[1]
    for i in bs:
        upper |= blocks[i][2]
    return upper.bit_count() <= 29 + s[5]

def children(s, bs):
    for k, i in enumerate(bs):
        b = blocks[i]
        assert ok(s, b)
        t = step(s, b)
        later = [j for j in bs[k+1:] if ok(t, blocks[j])]
        yield t, later

def count(s, bs):
    assert s[1].bit_count() <= 29 + s[5]
    if prune(s, bs):
        return 1
    return 1 + sum(count(t, later) for t, later in children(s, bs))

report = []
max_child = 0
total = 0
for r, ids in enumerate(d['root_indices']):
    s = (0, 0, 0, 0, 0, 0)
    for i in ids:
        s = step(s, blocks[i])
    bs = [i for i, b in enumerate(blocks) if ok(s, b) and (r < 27 or i < 26)]
    counts = [count(t, later) for t, later in children(s, bs)]
    max_child = max(max_child, max(counts, default=0))
    total += 1 + sum(counts)
    groups = []
    start = 0
    weight = 0
    for i, value in enumerate(counts):
        if weight and weight + value > 400:
            groups.append([start, i-start, weight])
            start = i
            weight = 0
        weight += value
    if start < len(counts):
        groups.append([start, len(counts)-start, weight])
    report.append({'root': r, 'initial_candidates': bs, 'branch_nodes': counts, 'groups': groups})
    print('ROOT', r, 'NODES', 1+sum(counts), 'CANDIDATES', len(bs),
          'MAX_CHILD', max(counts, default=0), 'GROUPS', len(groups),
          'MAX_GROUP', max((g[2] for g in groups), default=0))
print('TOTAL', total, 'MAX_CHILD', max_child, 'GROUPS', sum(len(r['groups']) for r in report))
assert total == 78682
(p / 'packing3-branch-counts.json').write_text(json.dumps(report))
