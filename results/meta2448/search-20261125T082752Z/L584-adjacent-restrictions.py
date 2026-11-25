import hashlib
import json
from pathlib import Path
import time

base = Path('/workspace/pequalnp-proofs/results/meta2448')
source = base / 'petersen-L584-exact20-independent-replay.json'
data = json.loads(source.read_text())
started = time.monotonic()


def prune(n, gates, output):
    if type(output) is bool or output < n:
        return [], output
    used = set()
    def visit(w):
        if w < n or w - n in used:
            return
        used.add(w - n)
        for a in gates[w - n][1:]:
            visit(a)
    visit(output)
    mapping = list(range(n))
    result = []
    for j, (op, a, b) in enumerate(gates):
        if j in used:
            mapping.append(n + len(result))
            result.append([op, mapping[a], mapping[b]])
        else:
            mapping.append(False)
    return result, mapping[output]


def simplify(n, gates, output, bindings, alias=None):
    mapping = list(bindings)
    result = []
    for j, (op, a, b) in enumerate(gates):
        if alias is not None and j == alias[0]:
            value = mapping[alias[1]]
        else:
            a, b = mapping[a], mapping[b]
            if op == 'and' and (a is False or b is False):
                value = False
            elif op == 'or' and (a is True or b is True):
                value = True
            elif type(a) is bool:
                value = b
            elif type(b) is bool:
                value = a
            elif a == b:
                value = a
            else:
                result.append([op, *sorted((a, b))])
                value = n + len(result) - 1
        mapping.append(value)
    return prune(n, result, mapping[output])


def values(n, gates):
    row = [sum(1 << q for q in range(1 << n) if q >> i & 1)
           for i in range(n)]
    for op, a, b in gates:
        row.append(row[a] & row[b] if op == 'and' else row[a] | row[b])
    return row


def output_value(n, gates, output):
    if type(output) is bool:
        return (1 << (1 << n)) - 1 if output else 0
    return values(n, gates)[output]


def profile(n, gates, edges):
    cones = []
    for j, (_, a, b) in enumerate(gates):
        cone = set()
        for w in [a, b]:
            if w >= n:
                assert w - n < j
                cone.add(w - n)
                cone.update(cones[w - n])
        cones.append(cone)
    rows = values(n, gates)
    owners = []
    bad = []
    for j, (op, _, _) in enumerate(gates):
        owned = []
        if op == 'and':
            for e, (u, v) in enumerate(edges):
                q = (1 << u) | (1 << v)
                if rows[n + j] >> q & 1 and all(
                    gates[k][0] != 'and' or not (rows[n + k] >> q & 1)
                    for k in cones[j]
                ):
                    owned.append(e)
        common = set(range(n))
        for e in owned:
            common.intersection_update(edges[e])
        if owned and not common:
            bad.append(j)
        owners.append(owned)
    return {'has_star_profile': not bad, 'nonstar_gates': bad,
            'owned_edge_indices': owners}


records = []
checks = 0
for deleted in sorted({tuple(sorted(e)) for e in data['edges']}):
    kept = [i for i in range(10) if i not in deleted]
    position = {v: i for i, v in enumerate(kept)}
    edges = sorted({tuple(sorted((position[u], position[v])))
                    for u, v in data['edges']
                    if u in position and v in position})
    n = len(kept)
    target = sum(1 << q for q in range(1 << n)
                 if any(q >> u & 1 and q >> v & 1 for u, v in edges))
    bindings = [position[v] if v in position else False for v in range(10)]
    gates, output = simplify(n, data['gates'], data['output_wire'], bindings)
    assert output_value(n, gates, output) == target
    initial = {'gates': gates, 'output_wire': output, 'gate_count': len(gates),
               'profile': profile(n, gates, edges)}
    steps = []
    while True:
        candidates = []
        for j in range(len(gates)):
            for w in range(n + j):
                other, out = simplify(n, gates, output, range(n), (j, w))
                checks += 1
                if output_value(n, other, out) == target:
                    prof = profile(n, other, edges)
                    candidates.append((len(other), prof['has_star_profile'],
                                       j, w, other, out, prof))
        if not candidates:
            break
        best = min(candidates, key=lambda c: c[:4])
        assert best[0] < len(gates)
        steps.append({'removed_gate': best[2], 'alias_wire': best[3],
                      'before': len(gates), 'after': best[0],
                      'preserving_aliases': len(candidates)})
        gates, output = best[4], best[5]
    assert output_value(n, gates, output) == target
    records.append({'deleted_vertices': deleted, 'input_original_vertices': kept,
                    'edges': edges, 'initial': initial, 'greedy_steps': steps,
                    'final': {'gates': gates, 'output_wire': output,
                              'gate_count': len(gates),
                              'profile': profile(n, gates, edges)},
                    'checked_assignments': 1 << n})

report = {'source': str(source),
          'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
          'records': records, 'alias_checks': checks,
          'elapsed_seconds': time.monotonic() - started,
          'scope': 'All fifteen adjacent-vertex restrictions of accepted L584, '
                   'then greedy output-preserving aliases to earlier wires. '
                   'Each candidate checked on all256inputs. Greedy ties prefer '
                   'fewer gates, then nonstar profile, then original gate/wire '
                   'indices. This is neither exhaustive alias-sequence search '
                   'nor a refutation of existential minimum-star gap2448.'}
out = base / 'L584-adjacent-restrictions.json'
out.write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({'alias_checks': checks, 'elapsed_seconds': report['elapsed_seconds'],
                  'summary': [{'deleted': r['deleted_vertices'],
                               'initial': r['initial']['gate_count'],
                               'final': r['final']['gate_count'],
                               'star': r['final']['profile']['has_star_profile']}
                              for r in records]}, indent=2))
