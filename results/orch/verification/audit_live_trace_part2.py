"""Independent bounded trace audit, not a Lean certificate checker.

Checks transitions, row cuts, projected replay masks, memo isomorphisms, and
complete child enumeration at expanded nodes. Formula leaves remain external.
"""
import collections
import hashlib
import gzip
import importlib.util
import json
import re
from pathlib import Path

BASE = Path('/tmp/oec/pequalnp-pilot-87/library_route')
spec = importlib.util.spec_from_file_location('live', BASE / 'live_search.py')
live = importlib.util.module_from_spec(spec)
spec.loader.exec_module(live)
TRACE = BASE / 'signed17-oredge-part2.jsonl'
FULL, INPUTS, TARGET = live.FULL, live.INPUTS, live.TARGET
source = (BASE / 'live_search_trace.cpp').read_text()
profiles_text = re.search(r'static const CP profiles\[CP_COUNT\] = (.*?);', source).group(1)
profiles = [tuple(map(int, x)) for x in re.findall(r'\{(\d+),(\d+),(\d+),(\d+)\}', profiles_text)]
assert len(profiles) == 1145
nodes, done, words, done_at, children = {}, {}, {}, {}, collections.defaultdict(list)
header = None
resume = {}
resume_header = None
for lineno, line in enumerate(TRACE.read_text().splitlines()):
    e = json.loads(line)
    kind = e['event']
    if kind == 'header':
        assert header is None
        header = e
    elif kind == 'resume_header':
        assert resume_header is None and not nodes
        resume_header = e
    elif kind == 'resume':
        assert not nodes and e['id'] < 0 and e['id'] not in resume
        resume[e['id']] = e
    elif kind == 'node':
        assert e['id'] not in nodes
        nodes[e['id']] = e
        children[e['parent']].append(e['id'])
    elif kind == 'done':
        assert e['id'] not in done
        done[e['id']], done_at[e['id']] = e, lineno
    elif kind == 'signal':
        assert e['id'] not in words
        words[e['id']] = int(e['hex'], 16)
    else:
        raise AssertionError(kind)
assert header and set(nodes) == set(done)
assert len(set(words.values())) == len(words)
assert words[header['target']] == TARGET
assert header['mode'] == 1 and header['cap'] == 17 and header['first'] == 'oredge'
assert all(0 <= w <= FULL for w in words.values())
assert resume_header['sha256'] == '95ac0317b254cb8d0532bc6c730fae33e01bf28067d2e694a6ae1bc539b9c3fb'
assert resume_header['count'] == len(resume) == 3265
archive = Path('/workspace/pequalnp-proofs/results/orch/search/signed17-or-edge/signed17-oredge-resume.txt.gz')
with gzip.open(archive, 'rt') as f:
    assert f.readline().strip() == resume_header['sha256']
    assert int(f.readline()) == len(resume)
    for ordinal, line in enumerate(f, 1):
        cells = line.split()
        source_node, remaining, n = map(int, cells[:3])
        prior = resume[-ordinal]
        assert prior['source_node'] == source_node and prior['remaining'] == remaining
        assert n == len(prior['state']) and prior['state'] == sorted(set(prior['state']))
        assert sorted(words[i] for i in prior['state']) == sorted(int(w, 16) for w in cells[3:])
sample = live.Search(mode=True)
histories = {}
counts = collections.Counter()
expanded_cases = memo_checks = 0
cofactor_counts = collections.Counter()

def operation(d, a, b):
    assert d in range(4)
    return (a & b, a | b, a & (FULL ^ b), (FULL ^ a) & b)[d]

def replay_cut(state, history, record, remaining):
    zi, oi, _, lower = profiles[record['a']]
    mask = FULL
    for j in range(10):
        if zi >> j & 1:
            mask &= FULL ^ INPUTS[j]
        if oi >> j & 1:
            mask &= INPUTS[j]
    def key(w):
        v = w & mask
        return min(v, v ^ mask)
    free = {0} | {key(w) for w in INPUTS}
    defs, order = {}, []
    for op, a, b in history:
        z = key(operation(op, a, b))
        if z in free or z in defs:
            continue
        a, b = key(a), key(b)
        if any(x not in free and x not in defs for x in (a, b)):
            continue
        defs[z] = (len(order), a, b)
        order.append(z)
    pending = [key(w) for w in state]
    selected = 0
    while pending:
        v = pending.pop()
        if v in free:
            continue
        assert v in defs
        i, a, b = defs[v]
        if selected >> i & 1:
            continue
        selected |= 1 << i
        pending += [a, b]
    mass = sum((v & mask) in (0, mask) for v in state)
    assert mass == record['c'] and selected == record['b']
    assert lower + mass > remaining + selected.bit_count()
    cofactor_counts[record['a']] += 1

for index, node in sorted(nodes.items()):
    rec = done[index]
    counts[rec['kind']] += 1
    op, ai, bi, zi, keep = node['step']
    assert op in range(4) and keep in range(4) and ai != bi
    a, b, z = words[ai], words[bi], words[zi]
    assert operation(op, a, b) == z
    assert node['state'] == sorted(set(node['state']))
    state = [words[i] for i in node['state']]
    p = node['parent']
    if p:
        assert p < index and ai in nodes[p]['state'] and bi in nodes[p]['state']
        assert zi not in nodes[p]['state'] and z != 0
        expected = sorted([i for i in nodes[p]['state']
                           if (i != ai or keep & 1) and (i != bi or keep & 2)] + [zi])
        assert expected == node['state']
        assert node['remaining'] == nodes[p]['remaining'] - 1
        histories[index] = histories[p] + [(op, a, b)]
    else:
        assert index == 1 and keep == 3 and op == 1
        assert (a, b) == (INPUTS[0], INPUTS[1])
        assert set(state) == set(INPUTS) | {z} and len(state) == 11
        assert node['remaining'] == header['cap'] - 1
        histories[index] = [(op, a, b)]
    kind = rec['kind']
    if kind == 'row':
        pr, nr = rec['a'], rec['b']
        assert 0 <= pr < 1024 and 0 <= nr < 1024
        assert TARGET >> pr & 1 and not TARGET >> nr & 1
        assert all((w >> pr & 1) == (w >> nr & 1) for w in state)
    elif kind == 'cofactor':
        replay_cut(state, histories[index], rec, node['remaining'])
    elif kind == 'memo':
        earlier = rec['a']
        if earlier < 0:
            assert earlier in resume
            prior = resume[earlier]
            assert prior['remaining'] == node['remaining']
            previous = {words[i] for i in prior['state']}
        else:
            assert earlier < index and earlier in nodes
            assert nodes[earlier]['remaining'] == node['remaining']
            assert done_at[earlier] < done_at[index]
            assert done[earlier]['kind'] not in ('open', 'found')
            previous = {words[i] for i in nodes[earlier]['state']}
        assert any({live.moved(w, p) for w in state} == previous for p in live.AUTOS)
        memo_checks += 1
    elif kind == 'expand':
        expected = set()
        for i, ai2 in enumerate(node['state']):
            for bi2 in node['state'][i + 1:]:
                for op2 in range(4):
                    z2 = operation(op2, words[ai2], words[bi2])
                    if z2 == 0 or z2 in state:
                        continue
                    for keep2 in range(4):
                        child = [words[j] for j in node['state']
                                 if (j != ai2 or keep2 & 1) and (j != bi2 or keep2 & 2)] + [z2]
                        if len(child) > node['remaining']:
                            continue
                        covered = 0
                        for w in child:
                            covered |= sample.col(w)
                        if covered == sample.allcov:
                            expected.add((op2, ai2, bi2, z2, keep2))
        actual = set()
        for c in children[index]:
            op2, ai2, bi2, zi2, keep2 = nodes[c]['step']
            actual.add((op2, ai2, bi2, words[zi2], keep2))
        assert expected == actual and len(actual) == len(children[index])
        expanded_cases += len(expected)
    elif kind == 'empty':
        assert node['remaining'] == 0 and TARGET not in state
    else:
        assert kind in ('formula0', 'formula1', 'open', 'found')
print(json.dumps({'nodes': len(nodes), 'signals': len(words), 'statuses': counts,
                  'memo_isomorphisms_checked': memo_checks,
                  'complete_expanded_child_cases': expanded_cases,
                  'cofactor_profiles_used': dict(cofactor_counts),
                  'root_status': done[1]['kind'],
                  'trace_sha256': hashlib.sha256(TRACE.read_bytes()).hexdigest(),
                  'resume_states_checked': len(resume),
                  'limitation': 'Formula0/1 leaves and prior-trace formula dependencies still require kernel certificates'}))
