"""Independent source-to-fixture audit of concrete indexed closure tables."""
from pathlib import Path
import collections
import hashlib
import json
import re

BASE = Path('/tmp/oec/pequalnp-pilot-87')
ARCHIVE = Path('/workspace/pequalnp-proofs/results/orch/lemmas')
data = json.loads((BASE/'library_route/pruned-copy-state-0.json').read_text())
mapping = json.loads((BASE/'copy_checker/pruned-copy-fixture0-cut-map.json').read_text())
rowdata = json.loads((BASE/'copy_checker/fixture0-row-selection.json').read_text())
source = (ARCHIVE/'PrunedCopyFixture0Tables.lean').read_text()
assert hashlib.sha256(source.encode()).hexdigest() == 'a1fa742ea398412c1ccee1c76e0d70019323bd58fbf0b97737dd90d75aa75b8a'
words = [int(s['hex'],16) for s in data['signals']]
FULL = (1<<1024)-1
nodes = data['nodes']
rootcopies = {c['child']:c for c in nodes[0]['copies']}
cuts = collections.defaultdict(list)
for item in mapping:
    origin = item['source']
    if origin[0] == 'omitted':
        node = nodes[origin[1]]
        entry = node['omitted'][origin[2]]
    else:
        parent = nodes[origin[1]]
        copy = parent['copies'][origin[2]]
        node = nodes[copy['child']]
        entry = parent['entries'][copy['bridges'][origin[3]]['entry']]
    cuts[node['id']].append((item['index'],entry['mask'],entry['sig']))

def label(text):
    ts = re.findall(r'Sum.inl|Sum.inr|true|false|\d+|[()]',text)
    assert ''.join(ts) == re.sub(r'\s+','',text)
    def parse(i):
        t = ts[i]
        if t == '(':
            value,j = parse(i+1)
            assert ts[j] == ')'
            return value,j+1
        if t in ('Sum.inl','Sum.inr'):
            value,j = parse(i+1)
            return ('l' if t == 'Sum.inl' else 'r',value),j
        if t in ('true','false'):
            return t == 'true',i+1
        return int(t),i+1
    value,n = parse(0)
    assert n == len(ts)
    return value

def ilabel(i,n):
    return i if n == 0 else ('l',i) if i < 12 else ('r',i == 13)

def listbody(name):
    return re.search(r'^def '+name+r' .* := \[(.*)\]$',source,re.M).group(1)

def labels(text):
    return [label(x.strip()) for x in text.split(',')] if text.strip() else []

def entries(name,n):
    body = listbody(name)
    matches = list(re.finditer(r'\(\{([^}]*)\}, s(\d+)\)',body))
    assert not re.sub(r'[\s,]','',re.sub(r'\(\{[^}]*\}, s\d+\)','',body))
    result=[]
    for m in matches:
        ls=labels(m.group(1))
        assert len(set(ls)) == len(ls)
        result.append((set(ls),int(m.group(2))))
    return result

def blocked(pool,pair):
    p,n=pair
    return all(not (w>>p&1) or (w>>n&1) for w in pool)

count=collections.Counter()
for node in nodes:
    n=node['id'];raw=node['raw'];basis=node['basis']
    expected_labels=[ilabel(i,n) for i in range(len(raw)) if basis>>i&1]
    assert labels(listbody('rootLabels'+str(n))) == expected_labels
    assert len(set(expected_labels)) == len(expected_labels)
    if n == 0:
        body=re.search(r'^def nodeRaw0 .* := \[(.*)\].getD i.val zero$',source,re.M).group(1)
        assert [int(x) for x in re.findall(r's(\d+)',body)] == raw
    else:
        e=nodes[0]['entries'][rootcopies[n]['entry']]
        sid=int(re.search(r'^def nodeRaw'+str(n)+r' : ChildLabel → Sig := duplicateRaw nodeRaw0 s(\d+)$',source,re.M).group(1))
        assert sid == e['sig'] and raw == nodes[0]['raw']+[sid,sid]
    actual=entries('entries'+str(n),n)
    expected=[({ilabel(i,n) for i in range(len(raw)) if e['mask']>>i&1},e['sig']) for e in node['entries']]
    assert actual == expected
    expectedcuts=[({ilabel(i,n) for i in range(len(raw)) if mask>>i&1},sid) for _,mask,sid in cuts[n]]
    assert entries('cuts'+str(n),n) == expectedcuts
    rows=[tuple(map(int,t)) for t in re.findall(r'\((\d+), (\d+)\)',listbody('rows'+str(n)))]
    assert rows == [tuple(r) for r in rowdata[str(n)]['rows']]
    assert all(p in data['positive_rows'] and q in data['negative_rows'] for p,q in rows)
    kept={(e['mask'],words[e['sig']]) for e in node['entries']}
    known={(m,words[s]) for _,m,s in cuts[n]}
    rejected=0
    for i,a in enumerate(node['entries']):
        for b in node['entries'][i+1:]:
            if a['mask']&b['mask'] or a['sig']==b['sig']:
                continue
            mask=a['mask']|b['mask'];av,bv=words[a['sig']],words[b['sig']]
            for z in (av&bv,av|bv):
                if z in (0,FULL,av,bv) or (mask,z) in kept or (mask,z) in known:
                    continue
                pool=[words[s] for j,s in enumerate(raw) if basis>>j&1 and not (mask>>j&1)]+[z]
                assert any(blocked(pool,pair) for pair in rows)
                rejected+=1
    assert rejected == rowdata[str(n)]['rejected']
    count['row_rejected_gate_cases']+=rejected
    count['row_witnesses']+=len(rows)
    count['entries']+=len(actual)
    for ci,mask,sid in cuts[n]:
        m=re.search(r'^theorem budgetCut'+str(ci)+r' : BudgetRunCut \(compressRoots roots(\d+) \{([^}]*)\}\)\n    \(duplicateRaw nodeRaw(\d+) s(\d+)\) false graph (\d+) := by\n  apply budgetRunCut_of_list _ _ \[(.*)\] cutWs(\d+) \(by decide\) \(by decide\) \(by rfl\)\n    false graph (\d+) (\d+) \(by decide\)\n  exact fun k bound => cutRun(\d+) bound',source,re.M)
        assert m is not None
        rn,ms,vn,vs,depth,ls,wi,depth2,cap,ri=m.groups()
        assert tuple(map(int,[rn,vn,vs,depth,wi,depth2,ri])) == (n,n,sid,node['depth'],ci,node['depth'],ci)
        assert set(labels(ms)) == {ilabel(i,n) for i in range(len(raw)) if mask>>i&1}
        expected=[('l',ilabel(i,n)) for i in range(len(raw)) if basis>>i&1 and not (mask>>i&1)]+[('r',False)]
        assert labels(ls) == expected and len(set(expected)) == len(expected)
        assert int(cap) == mapping[ci]['cut']['budget'] == len(expected)+node['depth']-1
        count['budget_adapters']+=1
    if n:
        statement=(f'theorem childNode{n} : PrunedNode (pairColumn false) (pairColumn false graph)\n'
                   f'    false graph 0 ChildLabel roots{n} nodeRaw{n} (entryCert entries{n}) :=\n'
                   f'  prunedNode_zero_of_checks rootLabels{n} nodeRaw{n} false graph entries{n} cuts{n} rows{n}\n'
                   f'    cutsSound{n} checkedLeaves{n} checkedGates{n} checkedMissing{n}')
        assert statement in source
        count['zero_depth_nodes']+=1

for line in source.splitlines():
    if line.startswith('set_option '):
        assert re.fullmatch(r'set_option (maxRecDepth|maxHeartbeats) \d+ in',line)
for bad in ['sorry','native_decide','axiom ','_root_','"','@[']:
    assert bad not in source
assert count['budget_adapters']==42 and count['zero_depth_nodes']==13
print(json.dumps({'source_sha256':hashlib.sha256(source.encode()).hexdigest(),
                  'fixture_sha256':hashlib.sha256((BASE/'library_route/pruned-copy-state-0.json').read_bytes()).hexdigest(),
                  'nodes':len(nodes),'counts':dict(count),
                  'scope':'Exact finite tables,42 cut adapters and13 base PrunedNode constructors; root wrapper/generic Live implication are separate.'}))
