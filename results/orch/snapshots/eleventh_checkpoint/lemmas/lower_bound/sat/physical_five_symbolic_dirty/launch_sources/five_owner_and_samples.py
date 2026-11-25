import itertools
import json

from feature_gadget_sat import extend, target
from global_synthesis import evaluate_wires
from and_sample_constraints import force_and_values, and_true_events


def restricted_negative_count(case, top):
    owners = sorted({a for a, _ in case['edges']})
    lines = {i for i in range(case['raw_inputs']) if i not in owners and top >> i & 1}
    neighbors = {p: {b for a, b in case['edges'] if a == p} for p in owners}
    family = set()
    for mask in range(1 << len(owners)):
        selected = [p for i, p in enumerate(owners) if mask >> i & 1]
        forbidden = set().union(*(neighbors[p] for p in selected)) if selected else set()
        available = lines - forbidden
        closed = {p for p in owners if not neighbors[p] & available}
        family.add(sum(1 << i for i in closed | available))
    return len(family)


def prepare(case, phase, false_count, true_count, true_census):
    assert case['raw_inputs'] == 16
    assert false_count >= 0 and true_count >= 0
    negatives = [mask for mask, label in case['raw_tests'] if not label]
    assert len(negatives) == 30
    capacity = (1 << 5) - len(negatives)

    def row(mask, value, evidence):
        encoded = extend(case, mask)
        values = evaluate_wires(phase, encoded, case['inputs'])
        score = sum(values[case['inputs'] + i] != value
                    for i, (op, _, _) in enumerate(phase) if not op)
        return dict(raw_mask=mask, encoded_mask=encoded, value=value,
                    phase_violations=score, evidence=evidence)

    false_rows = []
    for size in (1, 2):
        for support in itertools.combinations(range(16), size):
            mask = sum(1 << i for i in support)
            if target(case, mask):
                continue
            extensions = sum(mask & negative == mask for negative in negatives)
            if extensions > capacity:
                false_rows.append(row(mask, False, dict(maximal_negative_extensions=extensions)))
    true_rows = []
    if true_count:
        source = json.loads(true_census.read_text())
        assert source['input_original'] == case['input_original']
        owner_mask = sum(1 << owner for owner in {a for a, _ in case['edges']})
        for entry in source['assignments']:
            mask = entry['raw_mask']
            assert mask & owner_mask == owner_mask
            count = restricted_negative_count(case, mask)
            assert count == entry['negative_count'] and count > 16
            true_rows.append(row(mask, True, dict(restricted_negative_count=count)))
    order = lambda entry: (-entry['phase_violations'], entry['raw_mask'].bit_count(), entry['raw_mask'])
    return sorted(false_rows, key=order)[:false_count] + sorted(true_rows, key=order)[:true_count]


def dirty_pairs(case):
    negatives = [mask for mask, label in case['raw_tests'] if not label]
    assert len(negatives) == 30
    answer = []
    for a, b in itertools.combinations(range(16), 2):
        mask = (1 << a) | (1 << b)
        if not target(case, mask):
            extensions = sum(mask & negative == mask for negative in negatives)
            if extensions <= 2:
                answer.append(dict(raw_mask=mask, encoded_mask=extend(case, mask),
                                   maximal_negative_extensions=extensions))
    assert len(answer) == 15
    return answer


def add(cnf, selected, case, samples, phase, dirty=()):
    if not samples and not dirty:
        return
    levels = cnf.count_row([-op for op, _, _ in selected], 5)
    guard = levels[6]
    hint = phase if len(phase) == len(selected) else None
    for sample in samples:
        force_and_values(cnf, selected, case['inputs'], sample['encoded_mask'],
                         sample['value'], guard, hint)
    if dirty:
        events = []
        for sample in dirty:
            events.extend(and_true_events(cnf, selected, case['inputs'],
                                           sample['encoded_mask'], hint))
        cnf.clause(guard, *events)
