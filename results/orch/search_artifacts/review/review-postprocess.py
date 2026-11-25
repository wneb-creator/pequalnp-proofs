import hashlib
import itertools
import json
from functools import lru_cache
from pathlib import Path

BASE = Path('/tmp/oec/pequalnp-pilot-99/gap4970/lower_bound/postprocess')

@lru_cache(None)
def columns(n):
    out = []
    for i in range(n):
        block = 1 << i
        value = ((1 << block) - 1) << block
        size = 2 * block
        while size < (1 << n):
            value |= value << size
            size *= 2
        out.append(value)
    return out

def table(n, p, gates):
    values = columns(n)[:]
    reach = [1 << i for i in range(n)]
    cones = [0] * n
    mixed = 0
    for j, (op, a, b) in enumerate(gates):
        assert op in (0, 1) and 0 <= a < n+j and 0 <= b < n+j
        values.append(values[a] | values[b] if op else values[a] & values[b])
        reach.append(reach[a] | reach[b] if op else 0)
        cones.append(cones[a] | cones[b] | (1 << j))
        if op and reach[-1] & ((1 << p)-1) and reach[-1] >> p:
            mixed |= 1 << j
    return values, cones, mixed

def derive(n, p, gates, output):
    values, cones, mixed = table(n, p, gates)
    val = values[output] if 0 <= output < len(values) else 0
    edges = tuple((a, b) for a in range(n) for b in range(a+1, n)
                  if val >> ((1 << a) | (1 << b)) & 1)
    target = 0
    adj = [set() for _ in range(n)]
    for a, b in edges:
        target |= values[a] & values[b]
        adj[a].add(b)
        adj[b].add(a)
    return values, cones, mixed, val, edges, target, adj

@lru_cache(None)
def tau(n, edges):
    for k in range(n+1):
        for vertices in itertools.combinations(range(n), k):
            mask = sum(1 << v for v in vertices)
            if all(mask & ((1 << a) | (1 << b)) for a, b in edges):
                return k
    raise AssertionError('no cover')

def validate_graph(n, p, edges, adj):
    assert edges and all(a < p <= b for a, b in edges)
    assert all(len(adj[a] & adj[b]) <= 1 for a in range(n) for b in range(a+1, n))

def witnesses(n, gates, values, edges, adj):
    result = []
    for j, (op, _, _) in enumerate(gates):
        if not op:
            continue
        q = {i for i in range(n) if values[n+j] >> (1 << i) & 1}
        ideal = 0
        for i in q:
            ideal |= values[i]
        if len(q) < 2 or ideal != values[n+j]:
            continue
        for center in range(n):
            if q <= adj[center]:
                coverage = sum(1 << k for k, (a, b) in enumerate(edges)
                               if (a == center and b in q) or (b == center and a in q))
                result.append({'gate': j, 'center': center,
                               'support_mask': sum(1 << i for i in q), 'coverage': coverage})
    return result

def kept_options(n, gates, output, cones, ws, edge_count):
    states = {cones[output]}
    for w in ws:
        cone = cones[n+w['gate']]
        states |= {s | cone for s in states}
    target = (1 << edge_count)-1
    choices = []
    for state in states:
        cov = 0
        for w in ws:
            if state >> w['gate'] & 1:
                cov |= w['coverage']
        if cov == target:
            choices.append(state)
    if not choices:
        return []
    size = min(s.bit_count() for s in choices)
    return [s for s in choices if s.bit_count() == size]

def verify_record(n, p, gates, output, record, is_output=False):
    values, cones, mixed, val, edges, target, adj = derive(n, p, gates, output)
    assert tuple(map(tuple, record['edges'])) == edges and val == target
    validate_graph(n, p, edges, adj)
    cover = record['cover_mask']
    assert cover.bit_count() == record['tau'] == tau(n, edges)
    assert all(cover & ((1 << a) | (1 << b)) for a, b in edges)
    assert record['bound'] == len(edges)+record['tau']-1
    ws = witnesses(n, gates, values, edges, adj)
    keeps = kept_options(n, gates, output, cones, ws, len(edges))
    if is_output:
        assert bool(keeps) == record['has_star_cover']
        if not keeps:
            return
        size = record['pruned_gates']
        assert any((mixed & k).bit_count() == record['tCount'] for k in keeps)
    else:
        assert keeps and any(mixed & k == 0 for k in keeps)
        size = record['gates']
    assert size == keeps[0].bit_count()
    assert record['margin'] == size-record['bound'] >= 0

manifest = json.loads((BASE/'postprocess-manifest-01.json').read_text())
for entry in manifest['files']:
    data = (BASE/entry['file']).read_bytes()
    assert len(data) == entry['bytes'] and hashlib.sha256(data).hexdigest() == entry['sha256']

counts = {'files': len(manifest['files']), 'inputs': 0, 'saved_pruned': 0,
          'recorded_outputs': 0, 'recorded_rewires': 0}
for entry in manifest['files']:
    if not entry['file'].endswith('/result.json'):
        continue
    folder = (BASE/entry['file']).parent
    rec = json.loads((folder/'result.json').read_text())
    raw = (folder/'input.circuit.json').read_bytes()
    c = json.loads(raw)
    assert hashlib.sha256(raw).hexdigest() == rec['sha256']
    n, p, gates, output = rec['n'], rec['p'], c['gates'], c['output']
    vals, cones, mixed, val, edges, target, adj = derive(n, p, gates, output)
    assert tuple(map(tuple, rec['derived_edges'])) == edges
    assert (val ^ target).bit_count() == rec['quadratic_wrong_rows']
    assert mixed.bit_count() == rec['tCount']
    assert rec['full_rows_checked'] == 1 << n
    assert rec['bipartite'] == all(a < p <= b for a, b in edges)
    assert rec['c4free'] == all(len(adj[a]&adj[b]) <= 1 for a in range(n) for b in range(a+1,n))
    assert rec['singleton_true_inputs'] == [i for i in range(n) if val >> (1 << i) & 1]
    counts['inputs'] += 1
    if 'pruned_gates' in rec:
        validate_graph(n, p, edges, adj)
        assert val == target and rec['tau'] == tau(n, edges)
        assert rec['minimum_cover_mask'].bit_count() == rec['tau']
        assert all(rec['minimum_cover_mask'] & ((1 << a) | (1 << b)) for a, b in edges)
        ws = witnesses(n, gates, vals, edges, adj)
        assert ws == rec['valid_witnesses']
        keeps = kept_options(n, gates, output, cones, ws, len(edges))
        assert rec['kept_gate_mask'] in keeps
        new = json.loads((folder/'pruned.circuit.json').read_text())
        vv, _, mm, value, ee, tt, aa = derive(n, p, new['gates'], new['output'])
        assert value == target and ee == edges and mm == 0
        ww = witnesses(n, new['gates'], vv, ee, aa)
        cov = 0
        for w in ww:
            cov |= w['coverage']
        assert cov == (1 << len(edges))-1
        assert len(new['gates']) == rec['pruned_gates'] == keeps[0].bit_count()
        assert len(new['gates']) >= len(edges)+rec['tau']-1
        counts['saved_pruned'] += 1
    for row in json.loads((folder/'all-output-results.json').read_text()):
        verify_record(n, p, gates, row['output'], row, True)
        counts['recorded_outputs'] += 1
    for row in json.loads((folder/'mutation-results.json').read_text()):
        gs = [g[:] for g in gates]
        out = output
        bits = row['mutation'].split('-')
        if bits[0] == 'flip':
            gs[int(bits[1])][0] ^= 1
        elif bits[0] == 'read':
            gs[int(bits[1])][int(bits[2])] = int(bits[3])
        elif bits[0] == 'redirect':
            j, src = map(int, bits[1:])
            for k in range(j+1, len(gs)):
                gs[k] = [gs[k][0]] + [src if w == n+j else w for w in gs[k][1:]]
            out = src if out == n+j else out
        else:
            assert bits == ['original']
        verify_record(n, p, gs, out, row)
        counts['recorded_rewires'] += 1
    print(folder.relative_to(BASE), 'PASS')

Path('/tmp/oec/pequalnp-pilot-99/review-postprocess-result.json').write_text(json.dumps(counts, indent=2)+'\n')
print(json.dumps(counts, sort_keys=True))
print('All saved positive claims verified; rejected heuristic variants not rerun. No counterexample or general proof.')
