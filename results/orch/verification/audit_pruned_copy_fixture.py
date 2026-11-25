"""Independent finite-data audit, not a recursive Lean exclusion certificate."""
from pathlib import Path
import collections
import hashlib
import json
import re

BASE = Path('/tmp/oec/pequalnp-pilot-87')
PATH = BASE / 'library_route/pruned-copy-state-0.json'
data = json.loads(PATH.read_text())
FULL = (1 << 1024) - 1
inputs = [sum(1 << r for r in range(1024) if r >> i & 1) for i in range(10)]
edges = [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),
         (5,7),(7,9),(9,6),(6,8),(8,5)]
target = sum(1 << r for r in range(1024)
             if any((r >> a & 1) and (r >> b & 1) for a,b in edges))
signals = data['signals']
words = [int(s['hex'], 16) for s in signals]
nodes = data['nodes']
assert data['mode'] is False and data['source_state'] == 0 and data['root'] == 0
assert len(set(words)) == len(words)
assert [words[i] for i in data['inputs']] == inputs
assert words[data['target']] == target
positive, negative = data['positive_rows'], data['negative_rows']
assert len(positive) == len(negative) == 15
assert all(target >> r & 1 for r in positive)
assert all(not (target >> r & 1) for r in negative)
ALLCOL = (1 << (len(positive) * len(negative))) - 1

def op(d, a, b):
    assert d in (0, 1)
    return a & b if d == 0 else a | b

def col(w):
    return sum(1 << (i * len(negative) + j)
               for i,p in enumerate(positive) for j,n in enumerate(negative)
               if w >> p & 1 and not (w >> n & 1))

for i,s in enumerate(signals):
    assert s['id'] == i and 0 <= words[i] <= FULL
    assert int(s['col'], 16) == col(words[i])
    origin = s['origin']
    if origin and 'input' in origin:
        assert words[i] == inputs[origin['input']]
    elif origin and 'op' in origin:
        assert words[i] == op(origin['op'], words[origin['a']], words[origin['b']])
    elif origin and 'target' in origin:
        assert words[i] == target
profiles = [(int(p['mask'], 16), p['lower']) for p in data['profiles']]
assert profiles == [(FULL ^ x, 15) for x in inputs]
counts = collections.Counter()
cut_sources = {}

def history_ok(history):
    bank = set(inputs)
    for d,a,b,z in history:
        assert words[a] in bank and words[b] in bank
        assert words[z] == op(d, words[a], words[b])
        bank.add(words[z])

def check_cut(ids, budget, cut):
    mask, lower = profiles[cut['profile']]
    assert lower == cut['lower'] == 15 and budget == cut['budget']
    history_ok(cut['history'])
    selected = cut['selected']
    assert selected == sorted(set(selected)) and len(selected) == cut['paid']
    assert all(0 <= j < len(cut['history']) for j in selected)
    bank = {0, mask} | {x & mask for x in inputs}
    for index in selected:
        d,a,b,z = cut['history'][index]
        assert words[a] & mask in bank and words[b] & mask in bank
        bank.add(words[z] & mask)
    assert all(words[i] & mask in bank for i in ids)
    mass = sum(words[i] & mask in (0, mask) for i in ids)
    assert mass == cut['mass']
    assert lower + mass > budget + len(selected)
    counts['cofactor_cuts'] += 1

def outside(raw, basis, mask, sid):
    return [s for i,s in enumerate(raw) if basis >> i & 1 and not (mask >> i & 1)] + [sid]

def admissible(raw, basis, mask, value):
    covered = col(value)
    for i,s in enumerate(raw):
        if basis >> i & 1 and not (mask >> i & 1):
            covered |= col(words[s])
    return covered == ALLCOL

def replay(entries, i):
    e = entries[i]
    if e['left'] < 0:
        return []
    a,b = e['left'], e['right']
    return replay(entries, a) + replay(entries, b) + [[e['op'], entries[a]['sig'], entries[b]['sig'], e['sig']]]

for ni,node in enumerate(nodes):
    assert node['id'] == ni
    raw, basis, depth, budget = (node[k] for k in ['raw','basis','depth','budget'])
    assert 0 <= basis < 1 << len(raw) and depth >= 0
    assert budget == basis.bit_count() + depth - 1
    history_ok(node['history'])
    if node['kind'] == 'cofactor':
        check_cut([s for i,s in enumerate(raw) if basis >> i & 1], budget, node['cut'])
        continue
    assert node['kind'] == 'closure'
    entries, omitted = node['entries'], node['omitted']
    kept = {(e['mask'], words[e['sig']]) for e in entries}
    removed = {(e['mask'], words[e['sig']]) for e in omitted}
    assert len(kept) == len(entries) and len(removed) == len(omitted) and not (kept & removed)
    assert (basis, target) not in kept
    leaves = set()
    for ei,e in enumerate(entries):
        m,z = e['mask'], words[e['sig']]
        assert m and m & basis == m
        if e['left'] < 0:
            assert e['left'] == e['right'] == e['op'] == -1 and m.bit_count() == 1
            i = m.bit_length() - 1
            assert raw[i] == e['sig']
            leaves.add(i)
        else:
            assert 0 <= e['left'] < ei and 0 <= e['right'] < ei
            a,b = entries[e['left']], entries[e['right']]
            assert not (a['mask'] & b['mask']) and m == a['mask'] | b['mask']
            assert words[a['sig']] != words[b['sig']]
            assert z == op(e['op'], words[a['sig']], words[b['sig']])
            assert z not in (0,FULL,words[a['sig']],words[b['sig']])
            assert admissible(raw,basis,m,z)
    assert leaves == {i for i in range(len(raw)) if basis >> i & 1}
    for oi,e in enumerate(omitted):
        a,b = entries[e['left']], entries[e['right']]
        assert not (a['mask'] & b['mask']) and e['mask'] == a['mask'] | b['mask']
        z = op(e['op'],words[a['sig']],words[b['sig']])
        assert words[e['sig']] == z and z not in (0,FULL,words[a['sig']],words[b['sig']])
        assert admissible(raw,basis,e['mask'],z)
        expected_history = node['history'] + replay(entries,e['left']) + replay(entries,e['right']) + [[e['op'],a['sig'],b['sig'],e['sig']]]
        assert e['cut']['history'] == expected_history
        ws = outside(raw,basis,e['mask'],e['sig'])
        check_cut(ws,budget-e['mask'].bit_count()+1,e['cut'])
        cut_sources[('omitted',ni,oi)] = (ws,e['cut'])
    for i,a in enumerate(entries):
        for b in entries[i+1:]:
            if a['mask'] & b['mask'] or a['sig'] == b['sig']:
                continue
            m = a['mask'] | b['mask']
            for d in range(2):
                z = op(d,words[a['sig']],words[b['sig']])
                if z in (0,FULL,words[a['sig']],words[b['sig']]):
                    continue
                counts['closure_candidates'] += 1
                if admissible(raw,basis,m,z):
                    assert (m,z) in kept or (m,z) in removed
                    counts['admissible_candidates'] += 1
    copies = node['copies']
    assert [c['entry'] for c in copies] == (list(range(len(entries))) if depth else [])
    for ci,c in enumerate(copies):
        e = entries[c['entry']]
        child = nodes[c['child']]
        assert c['child'] > ni
        assert child['raw'] == raw + [e['sig'],e['sig']]
        assert child['basis'] == (basis ^ e['mask']) | (3 << len(raw))
        assert child['depth'] == depth - 1
        assert child['history'] == node['history'] + replay(entries,c['entry'])
        assert child['budget'] == budget - e['mask'].bit_count() + 1
        if child['kind'] != 'closure':
            assert not c['bridges']
            continue
        expected = [i for i,b in enumerate(entries) if not (b['mask'] & e['mask'])]
        assert [b['entry'] for b in c['bridges']] == expected
        child_kept = {(b['mask'],b['sig']) for b in child['entries']}
        for bi,bridge in enumerate(c['bridges']):
            b = entries[bridge['entry']]
            ws = outside(child['raw'],child['basis'],b['mask'],b['sig'])
            if bridge['kind'] == 'entry':
                assert (b['mask'],b['sig']) in child_kept
            elif bridge['kind'] == 'row':
                p,n = bridge['row']
                assert target >> p & 1 and not (target >> n & 1)
                assert all(not ((words[s] >> p & 1) and not (words[s] >> n & 1)) for s in ws)
            else:
                assert bridge['kind'] == 'cofactor'
                assert bridge['cut']['history'] == child['history'] + replay(entries,bridge['entry'])
                check_cut(ws,child['budget']-b['mask'].bit_count()+1,bridge['cut'])
                cut_sources[('bridge',ni,ci,bi)] = (ws,bridge['cut'])
            counts['bridge_alternatives'] += 1
    counts['entries'] += len(entries)
    counts['omitted_entries'] += len(omitted)

mapping = json.loads((BASE/'copy_checker/pruned-copy-fixture0-cut-map.json').read_text())
assert len(mapping) == len(cut_sources) == 42
lean = (BASE/'copy_checker/PrunedCopyFixture0Cuts.lean').read_text()
lean_words = {}
for sid,expression in re.findall(r'^def s(\d+) : Sig := (.+)$',lean,re.M):
    sid = int(sid)
    if expression.startswith('inputs.getD '):
        value = inputs[int(expression.split()[1])]
    elif expression == 'graph':
        value = target
    else:
        d,a,b = map(int,re.fullmatch(r'bin (\d+) s(\d+) s(\d+)',expression).groups())
        value = op(d,lean_words[a],lean_words[b])
    assert value == words[sid]
    lean_words[sid] = value
assert len(lean_words) == len(words)
for i,m in enumerate(mapping):
    assert m['index'] == i
    ws,cut = cut_sources[tuple(m['source'])]
    assert m['ws'] == ws and m['cut'] == cut
    choices = [cut['history'][j][:3] for j in cut['selected']]
    assert m['choices'] == choices
    ws_text = re.search(r'^def cutWs'+str(i)+r' : List Sig := \[(.*)\]$',lean,re.M).group(1)
    assert [int(x) for x in re.findall(r's(\d+)',ws_text)] == ws
    choice_text = re.search(r'^def cutChoices'+str(i)+r' : List Choice := \[(.*)\]$',lean,re.M).group(1)
    assert [list(map(int,t)) for t in re.findall(r'\((\d+), s(\d+), s(\d+)\)',choice_text)] == choices
    bound = re.search(r'^theorem cutCheck'+str(i)+r' : runCofactorCheck false inputs \(ZeroProfiles.domain (\d+)\) (\d+) (\d+) ',lean,re.M)
    assert tuple(map(int,bound.groups())) == (cut['profile'],cut['lower'],cut['budget'])

print(json.dumps({'fixture_sha256':hashlib.sha256(PATH.read_bytes()).hexdigest(),
                  'lean_source_sha256':hashlib.sha256(lean.encode()).hexdigest(),
                  'nodes':len(nodes),'signals':len(words),'counts':dict(counts),
                  'all42_lean_cuts_match':True,
                  'limitation':'All finite branches and cuts checked independently; recursive Lean exclusion theorem still required.'}))
