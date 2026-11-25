import hashlib
import importlib.util
import json
from datetime import datetime, timezone
from pathlib import Path

P = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('fixed_validator', P.parent / 'stochastic' / 'validate.py')
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)
results = []
for i in range(10):
    gp = P / ('control.control' + str(i) + '.graph.json')
    cp = P / ('control.control' + str(i) + '.circuit.json')
    g = json.loads(gp.read_text())
    r = mod.validate(gp, cp)
    assert r['wrong_rows'] == r['tCount'] == 0 and not r['missing_star_edges']
    edges = {tuple(e) for e in g['edges']}
    matching = [tuple(e) for e in g['matching']]
    assert all(e in edges for e in matching)
    assert len({a for a, b in matching}) == len(matching)
    assert len({b for a, b in matching}) == len(matching)
    cover = g['cover_mask']
    assert all((cover >> a & 1) or (cover >> b & 1) for a, b in edges)
    assert cover.bit_count() == len(matching) == g['tau']
    r['matching_and_cover_certificates_checked'] = True
    results.append(r)
    print('CONTROL', i, 'all', r['full_rows_checked'], 'rows; gates', r['gates'], 'bound', r['posted_bound'], 'certificates PASS')
(P / 'control-validation.json').write_text(json.dumps(results, indent=2) + '\n')

