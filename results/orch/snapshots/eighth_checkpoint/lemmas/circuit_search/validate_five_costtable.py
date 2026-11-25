"""Cross-check C++ costs and correlated-feature semantics on the five-owner data."""
import json
import runpy
from pathlib import Path

HERE = Path(__file__).resolve().parent
ALG = HERE.parent / 'algebra_strategy'
case = json.loads((ALG / 'five-owner-joint-packet.json').read_text())[0]
assemble = runpy.run_path(str(ALG / 'assemble_five_owner.py'))['assemble_five']
fixtures = json.loads((HERE / 'joint-five-budget-fixtures.json').read_text())
accepted = 0
for fixture in fixtures:
    _, report = assemble(case, fixture['gates'])
    assert report['within_budget'] == fixture['accepted']
    accepted += fixture['accepted']
raw, inputs = case['raw_inputs'], case['inputs']
columns = [int(('1' * (1 << i) + '0' * (1 << i)) * (1 << (raw - i - 1)), 2)
           for i in range(raw)]
for feature in case['features']:
    column = 0
    for i in feature['raw_indices']:
        column |= columns[i]
    columns.append(column)
target = 0
for a, b in case['edges']:
    target |= columns[a] & columns[b]
def truth(gates):
    values = columns.copy()
    for op, a, b in gates:
        assert op in (0, 1) and 0 <= a < len(values) and 0 <= b < len(values)
        values.append(values[a] | values[b] if op else values[a] & values[b])
    return values[-1]
initial = json.loads((HERE / 'joint-five-initial.json').read_text())
rewritten = json.loads((HERE / 'joint-five-test-correlated-fixture.json').read_text())
assert truth(initial) == truth(rewritten)
feature_start = json.loads((HERE / 'joint-five-feature-start.json').read_text())
feature_rewritten = json.loads((HERE / 'joint-five-feature-test-correlated-fixture.json').read_text())
assert truth(feature_start) == truth(feature_rewritten)
reports = []
for seed in json.loads((HERE / 'joint-five-seeds.json').read_text()):
    value = truth(seed['gates'])
    assert target & ~value == 0
    assert all(not (value >> (1 << i) & 1) for i in range(raw))
    errors = sum(bool(not label and value >> mask & 1) for mask, label in case['raw_tests'])
    assert errors == seed['boundary_errors']
    reports.append(dict(gates=len(seed['gates']), ands=seed['and_count'],
                        boundary_errors=errors, full_false=(value & ~target).bit_count()))
result = dict(budget_fixtures=len(fixtures), accepted=accepted, rejected=len(fixtures)-accepted,
              assignments_per_seed=1 << raw, seeds=len(reports),
              correlated_rewrite_equivalent=True, seed_reports=reports)
(HERE / 'joint-five-validation.json').write_text(json.dumps(result, indent=2))
print({key: value for key, value in result.items() if key != 'seed_reports'})
