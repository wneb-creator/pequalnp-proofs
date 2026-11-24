"""Package a hash-pinned exact dirty22 control; never launch a search."""
from pathlib import Path
import copy
import datetime
import hashlib
import json
import subprocess
import sys
import time

sys.dont_write_bytecode = True
ROOT = Path('/tmp/oec/pequalnp-pilot-18')
OWN = ROOT / 'orch/S05'
SOURCE = OWN / 'shared-factor-compact-complete.json'
SOURCE_SHA = '0cd2e6eaa92e2a5cd95d1bd20728ad9157e80b9e88a728ad7033f8af420c1299'
TOOLS = ROOT / 'lean-setup/stochastic'
PINS = {
    TOOLS / 'stochastic_tools.py': '1e6f24c16faf2948c0aec5e4c300f9114d3e331c5894f191c9e0e7607f8afe8b',
    TOOLS / 'circuit_anneal': '31620eae27eed733fe22f94965a215394e3fc6bd2a313f566335a3eb30dd4f00',
    TOOLS / 'circuit_anneal.cpp': 'a82e670373e5f0048df004efbcb0f417949ce0255545c0767b647cb7207068b3',
    ROOT / 'validate_raw_candidate.py': 'd244bfc58d60560041c5890592f3c2de90905c78fcd058f691b27e7785131401',
    ROOT / 'lean-setup/validate_sat_candidate.py': 'b807c1a580ce1fa49da51d859e6bc5d94bab2f9f0cd359c35cef35686f826529',
}
EDGES = [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
         (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def write(p, obj):
    with p.open('x') as f:
        json.dump(obj, f, indent=2)
        f.write('\n')

def evaluate(obj, mask):
    offset = obj['gate_wire_offset']
    assert offset in (11,13)
    values = [bool(mask & (1 << i)) for i in range(11)]
    if offset == 13:
        values += [False, True]
    for i, (op, a, b) in enumerate(obj['gates']):
        assert op in ('and','or') and 0 <= a < offset+i and 0 <= b < offset+i
        values.append((values[a] and values[b]) if op == 'and' else (values[a] or values[b]))
    assert 0 <= obj['output'] < len(values)
    return values

def live(obj):
    offset = obj['gate_wire_offset']
    todo = [obj['output']]
    found = set()
    while todo:
        w = todo.pop()
        if w >= offset and w-offset not in found:
            found.add(w-offset)
            todo.extend(obj['gates'][w-offset][1:])
    return sorted(found)

def schedule(gates, mode):
    deps = [{w-11 for w in row[1:] if w >= 11} for row in gates]
    ancestors = set()
    todo = [14]
    while todo:
        g = todo.pop()
        if g not in ancestors:
            ancestors.add(g)
            todo.extend(deps[g])
    order, done = [], set()
    while len(order) < len(gates):
        ready = [g for g in range(len(gates)) if g not in done and deps[g] <= done]
        assert ready
        if mode == 'original':
            g = min(ready)
        elif mode == 'reverse-ready':
            g = max(ready)
        elif mode == 'earliest-junk':
            g = min(ready, key=lambda x: (x not in ancestors, x))
        elif mode == 'latest-junk':
            g = min(ready, key=lambda x: (x == 14, x))
        else:
            raise ValueError(mode)
        order.append(g)
        done.add(g)
    return order

def record_command(command, prefix, expected):
    start = time.monotonic()
    with prefix.with_suffix('.stdout').open('x') as out, prefix.with_suffix('.stderr').open('x') as err:
        result = subprocess.run(command, cwd=OWN, stdout=out, stderr=err, timeout=30)
    record = dict(command=command, cwd=str(OWN), exit_code=result.returncode,
                  elapsed_seconds=time.monotonic()-start,
                  stdout_sha256=sha(prefix.with_suffix('.stdout')),
                  stderr_sha256=sha(prefix.with_suffix('.stderr')))
    write(prefix.with_suffix('.result.json'), record)
    assert result.returncode == expected, record
    return record

def main():
    assert sha(SOURCE) == SOURCE_SHA
    for p, h in PINS.items():
        assert sha(p) == h, str(p)
    family = OWN / 'dirty22-family'
    pack = OWN / 'dirty22-seed-pack'
    control = OWN / 'dirty22-controls'
    assert not family.exists() and not pack.exists() and not control.exists()
    family.mkdir()
    control.mkdir()
    source = json.loads(SOURCE.read_text())
    assert source['inputs'] == 11 and source['gate_wire_offset'] == 11
    assert len(source['gates']) == 22 and source['output'] == 32
    (family / 'source-original.json').write_bytes(SOURCE.read_bytes())
    assert live(source) == list(range(22))
    tables = [evaluate(source, mask) for mask in range(2048)]
    target = [any(mask >> a & 1 and mask >> b & 1 for a,b in EDGES) for mask in range(2048)]
    assert all(row[source['output']] == target[m] for m,row in enumerate(tables))
    junk = [g for g,row in enumerate(source['gates']) if row[0] == 'and'
            and any(tables[m][11+g] and not target[m] for m in range(2048))]
    assert junk == [14]
    entries, details, cases = [], [], []
    for n, mode in enumerate(('original','reverse-ready','earliest-junk','latest-junk')):
        order = schedule(source['gates'], mode)
        old_to_new = {old:new for new,old in enumerate(order)}
        lift = lambda w: w if w < 11 else 13+old_to_new[w-11]
        gates = [[source['gates'][g][0], *sorted(lift(w) for w in source['gates'][g][1:])] for g in order]
        case = f'c{n:04d}-k22'
        obj = dict(inputs=11, gate_wire_offset=13, size=22, gates=gates,
                   output=lift(source['output']), source_sha256=SOURCE_SHA,
                   order_name=mode, new_gate_to_original_gate=order,
                   original_gate_to_new_gate=[old_to_new[g] for g in range(22)],
                   junk_gates=[old_to_new[14]], candidate_only=True,
                   meets_posted_gate_limit=False, requires_Lean_proof=True)
        assert obj['output'] == 34 and live(obj) == list(range(22))
        for mask in range(2048):
            vals = evaluate(obj, mask)
            assert vals[obj['output']] == target[mask]
            assert all(vals[13+old_to_new[g]] == tables[mask][11+g] for g in range(22))
        path = family / (case+'.baseline22.json')
        write(path, obj)
        entries.append(dict(case=case, baseline22_sha256=sha(path)))
        details.append(dict(case=case, order_name=mode, junk_gate=old_to_new[14],
                            all_2048_outputs_pass=True, intermediate_comparisons=2048*22,
                            live_gate_count=22, output=34, constants_read=False))
        cases.append((path,obj))
    assert len({tuple(obj['new_gate_to_original_gate']) for _,obj in cases}) == 4
    write(family/'family.json', dict(complete=True, samples=4, cases=entries,
          kind='four_equivalent_topological_orders_of_one_exact_dirty22_control',
          source_sha256=SOURCE_SHA, generator_sha256=sha(Path(__file__)),
          source_wire_offset=11, packed_wire_offset=13, all_gates_live=True,
          candidate_only=True, assigned_shard_exhaustion=False))
    record_command([sys.executable,'-B',str(TOOLS/'stochastic_tools.py'),'prepare',str(family),str(pack)],
                   control/'prepare',0)
    tokens = (pack/'seeds.txt').read_text().split()
    assert tokens[:3] == ['COVER_ANNEAL','1','4']
    cursor = 3
    for _,obj in cases:
        assert list(map(int,tokens[cursor:cursor+2])) == [22,34]
        cursor += 2
        decoded = []
        for g in range(22):
            op,a,b = map(int,tokens[cursor:cursor+3]); cursor += 3
            assert op in (0,1)
            decoded.append(['and' if op else 'or',a,b])
        assert decoded == obj['gates']
        assert all(evaluate(dict(obj,gates=decoded),m)[34] == target[m] for m in range(2048))
    assert cursor == len(tokens)
    normalizations = []
    for n,(path,obj) in enumerate([(SOURCE,source)]+cases):
        report = control/f'normalize-{n}.json'
        record_command([sys.executable,'-B',str(ROOT/'validate_raw_candidate.py'),str(path),str(report)],
                       control/f'normalize-{n}',2)
        result = json.loads(report.read_text())
        assert result['status'] == 'EXACT_BUT_TOO_LARGE' and result['size'] == 22
        assert result['verified_inputs'] == 2048 and not result['meets_posted_gate_limit']
        normalizations.append(dict(source=str(path),report=str(report),status=result['status'],size=22))
    # Negative controls: forgetting the offset conversion and selecting FALSE both fail.
    wrong_offset = dict(source,gate_wire_offset=13,size=22)
    wrong_output = dict(cases[0][1],output=11)
    negatives = []
    for name,obj in [('unshifted-offset',wrong_offset),('false-output',wrong_output)]:
        mismatches = [m for m in range(2048) if evaluate(obj,m)[obj['output']] != target[m]]
        assert mismatches
        path = control/(name+'.json'); write(path,obj)
        report = control/(name+'-unexpected-report.json')
        record_command([sys.executable,'-B',str(ROOT/'validate_raw_candidate.py'),str(path),str(report)],
                       control/(name+'-rejection'),2)
        assert not report.exists()
        negatives.append(dict(name=name, mismatch_count=len(mismatches),first_mismatch=mismatches[0],rejected=True))
    # Preserve an optional finite control command for main; do not launch the engine.
    write(control/'engine-self-test-not-run.json',dict(status='NOT_RUN_USER_NO_ENGINE_LAUNCH',
          command=[str(TOOLS/'circuit_anneal'),'--pack',str(pack/'seeds.txt'),
                   '--output',str(control/'engine-self-test-future.json'),'--self-test','--seed','134222']))
    for p,h in PINS.items():
        assert sha(p) == h
    checks = dict(status='PASS_READY_FOR_MAIN_REVIEW',source_sha256=SOURCE_SHA,
                  original_full_inputs=2048, seed_full_inputs=4*2048,
                  packed_roundtrip_full_inputs=4*2048,intermediate_comparisons=4*22*2048,
                  seed_details=details,normalizations=normalizations,negative_controls=negatives,
                  tools_unchanged=True,search_worker_launched=False,lean_run=False,
                  exact_21_witness=False,engine_launched=False,engine_self_test='NOT_RUN')
    write(control/'checks.json',checks)
    files = [Path(__file__),SOURCE] + sorted(family.iterdir()) + sorted(pack.iterdir()) + sorted(control.iterdir())
    manifest = dict(status='READY_FOR_MAIN_REVIEW',created_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                    source_sha256=SOURCE_SHA,pack=str(pack/'seeds.txt'),pack_sha256=sha(pack/'seeds.txt'),
                    metadata_sha256=sha(pack/'seeds.json'),checks_sha256=sha(control/'checks.json'),
                    gate_count=22,all_gates_live=True,distinct_orders=4,
                    search_worker_launched=False,meets_posted_gate_limit=False,
                    reviewed_tools=[dict(path=str(p),sha256=h) for p,h in PINS.items()],
                    artifacts=[dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size) for p in files])
    path = OWN/'dirty22-seed-handoff.json'
    write(path,manifest)
    print(json.dumps(dict(status=manifest['status'],manifest=str(path),manifest_sha256=sha(path),
                          pack=manifest['pack'],pack_sha256=manifest['pack_sha256'],details=details)))

if __name__ == '__main__':
    main()
