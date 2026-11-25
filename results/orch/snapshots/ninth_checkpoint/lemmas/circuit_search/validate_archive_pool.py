"""Verify saved search scores and assembled costs for both archive profiles."""
import json
import runpy
from pathlib import Path

HERE = Path(__file__).resolve().parent
ALG = HERE.parent / 'algebra_strategy'
reports = []
for tag, packet, module, function, weight in [
    ('five', ALG / 'five-owner-joint-packet.json', ALG / 'assemble_five_owner.py', 'assemble_five', 0),
    ('four', HERE / 'joint-four-owner-packet.json', HERE / 'assemble_joint_four.py', 'assemble_joint', 16),
]:
    case = json.loads(packet.read_text())[0]
    assemble = runpy.run_path(str(module))[function]
    pool = json.loads((HERE / (tag + '-archive-smoke-pool.json')).read_text())
    entries = []
    for item in pool:
        misses = wrong = one = 0
        for value, label in case['tests']:
            values = [value >> i & 1 for i in range(case['inputs'])]
            for op, a, b in item['gates']:
                values.append(values[a] | values[b] if op else values[a] & values[b])
            misses += bool(label and not values[-1])
            wrong += bool(not label and values[-1])
            one += bool(not label and values[-1] and
                        (value & ((1 << len(case['group']))-1)).bit_count() <= 1)
        assert misses == 0 and item['miss'] == 0
        score = wrong + weight * one
        assert item['weighted_score' if weight else 'false'] == score
        _, metadata = assemble(case, item['gates'])
        assert metadata['within_budget']
        used = {case['inputs'] + len(item['gates']) - 1}
        for i in range(len(item['gates'])-1, -1, -1):
            if case['inputs'] + i in used:
                used.update(item['gates'][i][1:])
        and_count = sum(case['inputs'] + i in used and op == 0 and a != b
                        for i, (op, a, b) in enumerate(item['gates']))
        assert item['active_and'] == and_count
        entries.append(dict(ordinary_errors=wrong, score=score, gate_total=metadata['gates']))
    reports.append(dict(case=tag, pool_size=len(pool), all_budget_and_scores_pass=True, entries=entries))
(HERE / 'archive-smoke.validation.json').write_text(json.dumps(reports, indent=2))
print([{k: v for k, v in report.items() if k != 'entries'} for report in reports])
