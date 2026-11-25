"""Export a small indexed-label first-copy certificate experiment.

The JSON is finite data, not a Lean proof. Every omitted admissible entry
is accompanied by an explicit constructive cofactor cut, and every copy
bridge is retained, row-blocked, or accompanied by the same kind of cut.
"""
import argparse
import importlib.util
import json
from pathlib import Path

BASE = Path('/tmp/oec/pequalnp-pilot-87')
spec = importlib.util.spec_from_file_location('copy_source', BASE / 'library_route/copy_search_pruned.py')
source = importlib.util.module_from_spec(spec)
spec.loader.exec_module(source)


def export(index, profile_limit):
    old = json.loads((BASE / f'library_route/delta1-tables/state-{index}.json').read_text())
    search = source.CopySearch(False, old['remaining'], 60, 100000, 10000)
    live, sr = source.live, search.sr
    signals, ids = [], {}
    nodes = []
    def intern(value, origin=None):
        if value in ids:
            return ids[value]
        result = len(signals)
        ids[value] = result
        signals.append(dict(id=result, hex=hex(value), origin=origin, col=hex(sr.col(value))))
        return result
    inputs = [intern(value, dict(input=i)) for i, value in enumerate(live.INPUTS)]
    initial_history = [(op, int(a), int(b)) for op, a, b in old['history']]
    def history_json(history):
        result = []
        for op, a, b in history:
            c = live.opval(op, a, b)
            result.append([op, intern(a), intern(b), intern(c, dict(op=op, a=intern(a), b=intern(b)))])
        return result
    history_json(initial_history)
    target = intern(live.TARGET, dict(target=True))
    old_sig = [int(s['hex'], 16) for s in old['signals']]
    raw = [old_sig[i] for i in old['raw']]
    profiles = [(m, 15 if i < 10 else low) for i, (m, low) in enumerate(search.profiles[:profile_limit])]
    def cut(values, budget, history):
        for pi, (mask, lower) in enumerate(profiles):
            mass = sum((v & mask) in (0, mask) for v in values)
            if lower + mass <= budget:
                continue
            paid = source.cof.paid_pool(values, mask, False, history)
            if paid is not None and lower + mass > budget + paid[0]:
                return dict(profile=pi, lower=lower, mass=mass, paid=paid[0],
                            selected=list(paid[1]), budget=budget, history=history_json(history))
        return None
    def replay(es, i, history):
        e = es[i]
        if e['left'] < 0:
            return
        replay(es, e['left'], history)
        replay(es, e['right'], history)
        history.append((e['op'], int(signals[es[e['left']]['sig']]['hex'], 16),
                        int(signals[es[e['right']]['sig']]['hex'], 16)))
    def outside(values, basis, mask, value):
        return [v for i, v in enumerate(values) if basis >> i & 1 and not mask >> i & 1] + [value]
    def row_block(values, basis, mask, value):
        pool = outside(values, basis, mask, value)
        for p in sr.positive:
            for n in sr.negative:
                if all(not ((v >> p & 1) and not (v >> n & 1)) for v in pool):
                    return [p, n]
        return None
    def visit(values, basis, depth, history):
        budget = basis.bit_count() + depth - 1
        node = dict(id=len(nodes), raw=[intern(v) for v in values], basis=basis,
                    depth=depth, budget=budget, history=history_json(history))
        nodes.append(node)
        whole = cut([v for i, v in enumerate(values) if basis >> i & 1], budget, history)
        if whole is not None:
            node.update(kind='cofactor', cut=whole)
            return node['id']
        es = [dict(mask=1 << i, sig=intern(v), left=-1, right=-1, op=-1)
              for i, v in enumerate(values) if basis >> i & 1]
        kept = {(e['mask'], int(signals[e['sig']]['hex'], 16)) for e in es}
        omitted = {}
        j = 0
        while j < len(es):
            eb = es[j]
            b = int(signals[eb['sig']]['hex'], 16)
            for i in range(j):
                ea = es[i]
                a = int(signals[ea['sig']]['hex'], 16)
                if ea['mask'] & eb['mask'] or a == b:
                    continue
                mask = ea['mask'] | eb['mask']
                for op in range(2):
                    z = live.opval(op, a, b)
                    if z in (0, live.FULL, a, b) or (mask, z) in kept or (mask, z) in omitted:
                        continue
                    if row_block(values, basis, mask, z) is not None:
                        continue
                    h = list(history)
                    replay(es, i, h)
                    replay(es, j, h)
                    h.append((op, a, b))
                    witness = cut(outside(values, basis, mask, z), budget - mask.bit_count() + 1, h)
                    sid = intern(z, dict(op=op, a=intern(a), b=intern(b)))
                    if witness is not None:
                        omitted[(mask, z)] = dict(mask=mask, sig=sid, left=i, right=j, op=op, cut=witness)
                    else:
                        kept.add((mask, z))
                        es.append(dict(mask=mask, sig=sid, left=i, right=j, op=op))
            j += 1
            if len(es) > 3000:
                raise RuntimeError('fixture closure exceeded its bound')
        assert (basis, live.TARGET) not in kept
        node.update(kind='closure', entries=es, omitted=list(omitted.values()), copies=[])
        if depth:
            for i, e in enumerate(es):
                A, w = e['mask'], int(signals[e['sig']]['hex'], 16)
                h = list(history)
                replay(es, i, h)
                child_values = values + [w, w]
                child_basis = (basis ^ A) | (3 << len(values))
                child_id = visit(child_values, child_basis, depth - 1, h)
                child = nodes[child_id]
                bridges = []
                if child['kind'] == 'closure':
                    child_kept = {(x['mask'], x['sig']) for x in child['entries']}
                    for bi, b in enumerate(es):
                        if A & b['mask']:
                            continue
                        v = int(signals[b['sig']]['hex'], 16)
                        if (b['mask'], b['sig']) in child_kept:
                            bridges.append(dict(entry=bi, kind='entry'))
                            continue
                        row = row_block(child_values, child_basis, b['mask'], v)
                        if row is not None:
                            bridges.append(dict(entry=bi, kind='row', row=row))
                            continue
                        bh = list(h)
                        replay(es, bi, bh)
                        witness = cut(outside(child_values, child_basis, b['mask'], v),
                                      child['budget'] - b['mask'].bit_count() + 1, bh)
                        assert witness is not None, (node['id'], child_id, bi)
                        bridges.append(dict(entry=bi, kind='cofactor', cut=witness))
                node['copies'].append(dict(entry=i, child=child_id, bridges=bridges))
        return node['id']
    root = visit(raw, (1 << len(raw)) - 1, old['remaining'] - len(raw) + 1, initial_history)
    return dict(description='Finite experimental certificate; not checked in Lean',
                source_state=index, mode=False, root=root, inputs=inputs, target=target,
                positive_rows=sr.positive, negative_rows=sr.negative,
                profiles=[dict(mask=hex(m), lower=l) for m, l in profiles], signals=signals, nodes=nodes)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--state', type=int, default=0)
    parser.add_argument('--profiles', type=int, default=10)
    args = parser.parse_args()
    data = export(args.state, args.profiles)
    dest = BASE / f'library_route/pruned-copy-state-{args.state}.json'
    dest.write_text(json.dumps(data, separators=(',', ':')) + '\n')
    print(json.dumps(dict(path=str(dest), bytes=dest.stat().st_size,
                         nodes=len(data['nodes']), signals=len(data['signals']),
                         whole_cuts=sum(n['kind'] == 'cofactor' for n in data['nodes']),
                         entries=sum(len(n.get('entries', [])) for n in data['nodes']),
                         subtree_cuts=sum(len(n.get('omitted', [])) for n in data['nodes']),
                         bridge_cuts=sum(b['kind'] == 'cofactor' for n in data['nodes']
                                         for c in n.get('copies', []) for b in c['bridges']))))


if __name__ == '__main__':
    main()
