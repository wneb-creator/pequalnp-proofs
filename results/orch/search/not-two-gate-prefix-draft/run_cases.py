from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, os, resource, subprocess, sys, time

base = Path(__file__).resolve().parent
cpu, parity = map(int, sys.argv[1:3])
assert (cpu, parity) in ((1, 0), (4, 1))
matrix = Path('/tmp/oec/pequalnp-pilot-87/finite_invariants/dynamic-loader/rectangles-v3.txt')
edges = ((0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5))
records = json.loads((base/'starts-index.json').read_text())
fixtures = json.loads((base/'priority-starts.json').read_text())['starts']

def limits():
    resource.setrlimit(resource.RLIMIT_AS, (1_000_000_000, 1_000_000_000))
    os.sched_setaffinity(0, {cpu})
    os.nice(10)

def verify(path, fixture):
    d = json.loads(path.read_text())
    gates = d['gates']
    assert len(gates) <= 19 and sum(op == 2 for op, a, b in gates) == 1
    prefix = []
    for g in fixture['prefix']:
        prefix.append([2, g['input'], g['input']] if g['kind'] == 'NOT' else [int(g['kind'] == 'OR'), g['left'], g['right']])
    assert gates[:3] == prefix
    assert 10 <= d['output'] < 10 + len(gates)
    left_only = right_only = False
    sound = True
    last = gates[d['output'] - 10]
    final_or = last[0] == 1
    words = [0] * (10 + len(gates))
    for row in range(1024):
        values = [bool(row >> i & 1) for i in range(10)]
        for op, a, b in gates:
            assert 0 <= a < len(values) and 0 <= b < len(values) and op in (0, 1, 2)
            values.append(values[a] and values[b] if op == 0 else values[a] or values[b] if op == 1 else not values[a])
        goal = any(bool(row >> a & 1) and bool(row >> b & 1) for a, b in edges)
        assert values[d['output']] == goal
        for i, value in enumerate(values):
            if value:
                words[i] |= 1 << row
        if final_or:
            a, b = values[last[1]], values[last[2]]
            left_only |= a and not b
            right_only |= b and not a
            sound &= not (a or b) or goal
    assert words == [int(v, 16) for v in d['values']]
    return dict(gate_count=len(gates), not_count=1, full1024=True, all_intermediate_words=True,
                final_or=final_or, sound_operands=sound, incomparable=left_only and right_only)

results = []
for index in range(parity, len(records), 2):
    record = records[index]
    folder = base/record['case']
    folder.mkdir(exist_ok=True)
    prefix = base/record['prefix_file']
    assert hashlib.sha256(prefix.read_bytes()).hexdigest() == record['prefix_sha256']
    cmd = [str(base/'not_prefix_search'), '--prefix', str(prefix), '--cap', '19', '--seconds', '120',
           '--nodes', '2000000', '--extra-rectangles', str(matrix), '--candidate', str(folder/'candidate.json')]
    metadata = dict(command=cmd, source_sha256=hashlib.sha256((base/'not_prefix_search.cpp').read_bytes()).hexdigest(),
                    prefix_sha256=record['prefix_sha256'], fixture_index=index,
                    matrix_sha256=hashlib.sha256(matrix.read_bytes()).hexdigest(),
                    cpu=cpu, address_limit=1_000_000_000, started_utc=datetime.now(timezone.utc).isoformat(),
                    scope='bounded heuristic witness search only; negative outcomes do not establish UNSAT')
    (folder/'command.json').write_text(json.dumps(metadata, indent=2)+'\n')
    started = time.monotonic()
    with (folder/'stdout.txt').open('w') as out, (folder/'stderr.txt').open('w') as err:
        r = subprocess.run(cmd, cwd=folder, stdout=out, stderr=err, preexec_fn=limits)
    metadata.update(exit_code=r.returncode, wall_seconds=time.monotonic()-started,
                    ended_utc=datetime.now(timezone.utc).isoformat())
    if (folder/'candidate.json').exists():
        metadata['independent_replay'] = verify(folder/'candidate.json', fixtures[index])
    (folder/'status.json').write_text(json.dumps(metadata, indent=2)+'\n')
    results.append(metadata)
    (base/f'worker{parity}-status.json').write_text(json.dumps(results, indent=2)+'\n')
    print(json.dumps(dict(case=record['case'], exit=r.returncode, wall_seconds=metadata['wall_seconds'],
                         witness=metadata.get('independent_replay'))), flush=True)
    if metadata.get('independent_replay'):
        break
