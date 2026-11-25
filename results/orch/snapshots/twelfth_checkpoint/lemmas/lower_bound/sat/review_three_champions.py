import hashlib
import json
import time
from pathlib import Path


def main():
    start = time.monotonic()
    folder = Path(__file__).resolve().parents[2] / 'circuit_search'
    seeds = json.loads((folder / 'global-three-champion-seeds.json').read_text())
    fixtures = json.loads((folder / 'global-three-critical-fixtures.json').read_text())
    lines = (folder / 'full-singleton-tests.txt').read_text().splitlines()
    tests = [tuple(map(int, line.split())) for line in lines[1:]]
    assert len(tests) == int(lines[0]) == 782
    assert sum(label for _, label in tests) == 52
    columns = [sum(1 << t for t, (mask, _) in enumerate(tests) if mask >> i & 1)
               for i in range(26)]
    positives = sum(1 << t for t, (_, label) in enumerate(tests) if label)
    negatives = ((1 << len(tests)) - 1) ^ positives
    counts = []
    for index, (seed, fixture) in enumerate(zip(seeds, fixtures, strict=True)):
        gates = seed['gates'] if isinstance(seed, dict) else seed
        assert len(gates) <= 63
        gates = [list(gate) for gate in gates]
        while len(gates) < 63:
            output = 26 + len(gates) - 1
            gates.append([1, output, output])
        values = columns.copy()
        for op, a, b in gates:
            assert op in (0, 1) and 0 <= a < len(values) and 0 <= b < len(values)
            values.append(values[a] | values[b] if op else values[a] & values[b])
        active = {88}
        for i in range(62, -1, -1):
            if 26 + i in active:
                active.update(gates[i][1:])
        correctly_rejected = negatives & ~values[-1]

        def changed_output(i, replacement):
            changed = values[:26 + i] + [replacement]
            for op, a, b in gates[i + 1:]:
                changed.append(changed[a] | changed[b] if op else changed[a] & changed[b])
            return changed[-1]

        count = 0
        for i, (op, a, b) in enumerate(gates):
            if op or a == b or 26 + i not in active:
                continue
            if not values[26 + i] & correctly_rejected:
                continue
            deleted = changed_output(i, 0)
            if (positives & values[-1] & ~deleted).bit_count() < 2:
                continue
            if any(changed_output(i, values[child]) == values[-1] for child in (a, b)):
                continue
            count += 1
        assert fixture == dict(index=index, critical_junk_count=count), (index, count, fixture)
        counts.append(count)
    source = folder / 'search_feature_three_champions.cpp'
    report = dict(
        status='APPROVED', source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
        checked_seeds=len(seeds), boundary_cases=len(tests),
        positive_edges=positives.bit_count(), qualifying_two_or_more=sum(c >= 2 for c in counts),
        first_three=counts[:3], seconds=time.monotonic() - start,
        scope='Soft archive/champion criterion only; independently replayed every fixture. No new hard acceptance restriction.')
    Path(__file__).with_name('reviewer_three_champions_cpp.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report), flush=True)


if __name__ == '__main__':
    main()
