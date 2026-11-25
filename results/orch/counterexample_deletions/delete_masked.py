"""Finite three-gate deletion search around validated one-NOT seeds."""
from pathlib import Path
import hashlib
import importlib.util
import itertools
import json
import time

BASE = Path('/tmp/oec/pequalnp-pilot-85/counterexample')
spec = importlib.util.spec_from_file_location('search_truth', BASE / 'synthesize.py')
s = importlib.util.module_from_spec(spec)
spec.loader.exec_module(s)


def trim(gs, k, side):
    replacement = gs[k][side]
    def adjust(w):
        if w == s.N + k:
            w = replacement
        return w - 1 if w > s.N + k else w
    return [(op, adjust(a), adjust(b)) for j, (op, a, b) in enumerate(gs) if j != k]


def live_not(gs):
    live = set()
    todo = [s.N + len(gs) - 1]
    while todo:
        w = todo.pop()
        if w < s.N or w in live:
            continue
        live.add(w)
        op, a, b = gs[w - s.N]
        if op == 2:
            return True
        todo.extend([a, b])
    return False


def main():
    records = json.loads(Path('/tmp/oec/pequalnp-pilot-85/abc-search/masked-seeds/index.json').read_text())
    records = [r for r in records if r['not_count'] == 1 and r['gate_count'] == 27]
    samples = json.loads((BASE / 'all-negative.json').read_text()) + [(1 << a) | (1 << b) for a, b in s.E]
    sample_mask = sum(1 << x for x in set(samples))
    started = time.monotonic()
    total = live = 0
    best_full = best_sample = None
    for number, record in enumerate(records):
        path = Path(record['path'])
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
        data = json.loads(path.read_text())
        gates = data['gates']
        assert data.get('output', s.N + len(gates) - 1) == s.N + len(gates) - 1
        assert not s.evaluate(gates)
        eligible = [j for j, (op, a, b) in enumerate(gates[:-1]) if op != 2]
        for deleted in itertools.combinations(eligible, 3):
            for sides in itertools.product([1, 2], repeat=3):
                candidate = gates
                for k, side in reversed(list(zip(deleted, sides))):
                    candidate = trim(candidate, k, side)
                total += 1
                if not live_not(candidate):
                    continue
                live += 1
                delta = s.evaluate(candidate)
                errors, sample_errors = delta.bit_count(), (delta & sample_mask).bit_count()
                result = {'gates': candidate, 'errors': errors, 'sample_errors': sample_errors,
                          'source': str(path), 'source_sha256': digest,
                          'deleted': deleted, 'replacement_sides': sides,
                          'scope': 'Finite deletion heuristic; only zero full errors is a counterexample'}
                if best_full is None or errors < best_full['errors']:
                    best_full = result
                    (BASE / 'delete-masked-best-full.json').write_text(json.dumps(result, indent=2))
                    print('best full', errors, 'sample errors', sample_errors, flush=True)
                if best_sample is None or (sample_errors, errors) < (best_sample['sample_errors'], best_sample['errors']):
                    best_sample = result
                    (BASE / 'delete-masked-best-sample.json').write_text(json.dumps(result, indent=2))
                    print('best samples', sample_errors, 'full errors', errors, flush=True)
                if errors == 0:
                    print('FOUND exact24-gate circuit', flush=True)
                    return
        print('completed seed', number + 1, 'of', len(records), flush=True)
    report = {'seeds': len(records), 'enumerated': total, 'live_not_candidates': live,
              'elapsed_seconds': time.monotonic() - started,
              'best_full_errors': best_full['errors'],
              'best_sample_errors': best_sample['sample_errors'],
              'best_sample_full_errors': best_sample['errors']}
    (BASE / 'delete-masked-status.json').write_text(json.dumps(report, indent=2))
    print(json.dumps(report), flush=True)


if __name__ == '__main__':
    main()
