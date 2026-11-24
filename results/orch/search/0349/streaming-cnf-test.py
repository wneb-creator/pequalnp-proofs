import hashlib
import importlib.util
import json
import pathlib

HERE = pathlib.Path('/tmp/oec/pequalnp-pilot-21/search')
ROOT = HERE / 'streaming-cnf-tests'
ROOT.mkdir(exist_ok=True)


def module(name, file):
    spec = importlib.util.spec_from_file_location(name, HERE / file)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


f = module('full_encoder', 'cegis-full.py')
s = module('streaming_writer', 'streaming_cnf.py')
base_class = f.CNF
records = []
for label, n, gates, goals, rows in [
    ('dense4', 4, 4, [0], [x for x in range(16) if x.bit_count() in (2, 3)]),
    ('dense6', 6, 6, [0], [x for x in range(64) if x.bit_count() in (3, 5)]),
    ('full_shape', 13, 38, list(range(13)), [127, 255, 511]),
]:
    inputs = [sum(1 << r for r, x in enumerate(rows) if x >> p & 1) for p in range(n)]
    f.TARGETS = [sum(1 << r for r, x in enumerate(rows) if any(x >> p & 1 for p in f.LINES[w] if p < n)) for w in goals]
    outputs = []
    for kind in ('list', 'stream'):
        f.CNF = base_class if kind == 'list' else s.streaming_class(base_class, ROOT / (label+'.clauses.part'))
        c, ops, aa, bb = f.encode(inputs, [None]*n, list(range(len(goals))), gates, set(range(len(rows))), True)
        c.add(aa[0][0])
        c.add(bb[0][1])
        c.add(*ops)
        path = ROOT / (label+'-'+kind+'.cnf')
        c.save(path)
        outputs.append((path, c.n, len(c.cs), ops, aa, bb))
    left, right = outputs
    assert left[1:] == right[1:]
    data = left[0].read_bytes()
    assert data == right[0].read_bytes()
    record = {'fixture': label, 'variables': left[1], 'clauses': left[2], 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest(), 'whole_file_byte_identical': True}
    records.append(record)
    print(json.dumps(record), flush=True)

# Empty clauses and zero-variable headers must also preserve exact DIMACS bytes.
outputs = []
for kind in ('list', 'stream'):
    cls = base_class if kind == 'list' else s.streaming_class(base_class, ROOT / 'empty.clauses.part')
    c = cls()
    c.add()
    path = ROOT / ('empty-'+kind+'.cnf')
    c.save(path)
    outputs.append(path.read_bytes())
assert outputs[0] == outputs[1] == b'p cnf 0 1\n 0\n'
records.append({'fixture': 'empty_clause', 'whole_file_byte_identical': True})
(ROOT / 'results.json').write_text(json.dumps(records, indent=2)+'\n')
print('ALL_BYTE_EQUIVALENCE_TESTS_PASSED', flush=True)
