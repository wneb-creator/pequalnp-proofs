from itertools import combinations
from datetime import datetime, timezone
import json

counts = {}
for n in range(1, 5):
    checked = [0, 0]
    all_assignments = tuple(range(1 << n))
    base_families = tuple(frozenset((1 << i,)) for i in range(n))
    base_truths = tuple(sum(((x >> i) & 1) << x for x in all_assignments) for i in range(n))
    mask = (1 << (1 << n)) - 1
    def visit(families, truths, remaining):
        checked[0] += 1
        for family, truth in zip(families, truths):
            dnf_truth = sum(int(any((x & term) == term for term in family)) << x
                            for x in all_assignments)
            assert dnf_truth == truth
            checked[1] += len(all_assignments)
        # Empty family models all out-of-range wires as false.
        assert not any((0 & term) == term for term in frozenset())
        if not remaining:
            return
        for a, b in combinations(range(len(families)), 2):
            for use_or in (False, True):
                new_family = (families[a] | families[b]) if use_or else frozenset(
                    u | v for u in families[a] for v in families[b])
                new_truth = (truths[a] | truths[b]) if use_or else (truths[a] & truths[b])
                visit(families + (new_family,), truths + (new_truth,), remaining - 1)
    visit(base_families, base_truths, 3)
    counts[n] = {'circuits': checked[0], 'wire_assignment_checks': checked[1]}
print(json.dumps({'utc': datetime.now(timezone.utc).isoformat(), 'n': [1, 4],
                  'maximum_gates': 3, 'result': 'PASS', 'counts': counts}, indent=2))
