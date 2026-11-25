from pathlib import Path
import json, re, hashlib
repo = Path('/workspace/pequalnp-proofs')
p = repo / 'results/orch/lemmas/Mono18Rectangle9611.lean'
s = p.read_text()
sha = hashlib.sha256(p.read_bytes()).hexdigest()
assert sha == '37ce07d4023fd4a9af6fe6203265fb28c8673e34dccd991be907df0833f539b2'
assert not p.with_suffix('.compile.txt').read_bytes()
meta = json.loads((repo / 'results/orch/mono18-rectangle-9611/children9611.json').read_text())
fp = repo / 'results/orch/weak20369-generation/complete-fixture-20369.json'
assert len(meta['signal_order']) == len(meta['profiles']) == len(meta['nodes']) == 12
assert hashlib.sha256(fp.read_bytes()).hexdigest() == meta['fixture_sha256']
f = json.loads(fp.read_text())
words = [int(x, 16) for x in re.findall(r'0x[0-9a-f]+', s.split('def record')[0])]
records = [int(x, 16) for x in re.findall(r'0x[0-9a-f]+', s.split('def record')[1].split('def labels9611')[0])]
labels = [list(map(int, x.split(','))) for x in re.findall(r'\[([0-9,]+)\]', s.split('def labels9611')[1].split('def childSignals9611')[0])]
certs = [tuple(map(int, x)) for x in re.findall(r'certifiedAt_valid ([0-9]+) ([0-9]+)', s)]
assert len(words) == len(records) == len(labels) == len(certs) == 12
for j, (sid, pr) in enumerate(zip(meta['signal_order'], meta['profiles'])):
    assert sid == pr['signal']
    assert words[j] == int(pr['hex'], 16) == int(f['signals'][str(sid)], 16)
    assert records[j] == int(pr['record'], 16)
    assert certs[j] == (pr['block'], pr['offset'])
    assert records[j] >> 30 == pr['cost']
costs = [x >> 30 for x in records]
assert costs == [4] * 9 + [8] * 3
for i, (ls, entry) in enumerate(zip(labels, meta['nodes'])):
    n = 9612 + i
    assert entry == f['rectangles'][str(n)]
    assert [meta['signal_order'][j] for j in ls] == entry['state']
    assert [costs[j] for j in ls] == entry['root_costs']
    assert sum(costs[j] for j in ls) == entry['cost_sum'] < entry['total'] == 79
    assert len(ls) == (15 if i < 11 else 14)
assert '_root_' not in s and '"' not in s and '@[' not in s
report = dict(verdict='PASS', source_sha256=sha, fixture_sha256=meta['fixture_sha256'],
              signals=12, children=12, occurrences=sum(map(len, labels)),
              cost_sums=[sum(costs[j] for j in ls) for ls in labels])
(repo / 'results/orch/review-mono18-rectangle9611.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
