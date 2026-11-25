"""Add reviewed 61/63-gate near-phase lifts to the full-plane restart bank."""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
base = json.loads((HERE / 'global-fourteen-seeds.json').read_text())
permutations = json.loads((HERE / 'global-fourteen-automorphisms.json').read_text())
tests = json.loads((HERE / 'full-case.json').read_text())['tests'] + [[1 << i, 0] for i in range(26)]
columns = [sum((mask >> i & 1) << j for j, (mask, _) in enumerate(tests)) for i in range(26)]
target = sum(label << j for j, (_, label) in enumerate(tests))
guard = sum(1 << j for j, (mask, _) in enumerate(tests)
            if mask.bit_count() == 1 or mask in ((1 << 13)-1, ((1 << 13)-1) << 13))
added = []
for name, expected_errors in [('joint-five-simplified21-error17.full.json', 427), ('joint-five-allraw23-error17.full.json', 427), ('joint-five-archive-best-10.full.json', 234)]:
    source = json.loads((HERE / name).read_text())
    for index, permutation in enumerate(permutations):
        gates = [[op, permutation[a] if a < 26 else a, permutation[b] if b < 26 else b]
                 for op, a, b in source]
        assert len(gates) <= 63 and sum(op == 0 and a != b for op, a, b in gates) == 14
        values = columns.copy()
        for i, (op, a, b) in enumerate(gates):
            assert op in (0, 1) and 0 <= a < 26+i and 0 <= b < 26+i
            values.append(values[a] | values[b] if op else values[a] & values[b])
        assert values[-1] & target == target and values[-1] & guard == 0
        wrong = (values[-1] & ~target).bit_count()
        assert wrong == expected_errors
        added.append(dict(gates=gates, source=name, automorphism=index,
                          boundary_errors=wrong, gates_count=len(gates), and_count=14))
combined = base + added
rows = [str(len(combined))]
for seed in combined:
    rows.append(str(len(seed['gates'])))
    rows.extend(' '.join(map(str, gate)) for gate in seed['gates'])
temporary = HERE / 'global-fourteen-seeds.next.txt'
temporary.write_text('\n'.join(rows)+'\n')
temporary.replace(HERE / 'global-fourteen-seeds.txt')
(HERE / 'global-fourteen-added-seeds.json').write_text(json.dumps(added))
report = dict(original=len(base), added=len(added), active_total=len(combined),
              extension_source='Independently reviewed full DNFs and 14-AND nesting/essentiality.',
              text_sha256=hashlib.sha256((HERE / 'global-fourteen-seeds.txt').read_bytes()).hexdigest())
(HERE / 'global-fourteen-active-bank.json').write_text(json.dumps(report, indent=2))
print(report)
