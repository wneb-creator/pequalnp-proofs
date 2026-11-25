from pathlib import Path
import json, hashlib

base=Path('/workspace/pequalnp-proofs/results/orch1735/finite-followup')
manifest=json.loads((base/'MANIFEST.json').read_text())
assert len({e['path'] for e in manifest['files']})==len(manifest['files'])
for e in manifest['files']:
    b=(base/e['path']).read_bytes()
    assert len(b)==e['bytes'] and hashlib.sha256(b).hexdigest()==e['sha256']
    b.decode('utf-8')
assert {p.relative_to(base).as_posix() for p in base.rglob('*') if p.is_file()}=={e['path'] for e in manifest['files']}|{'MANIFEST.json'}

def analyze(path):
    d=json.loads(path.read_text());n=d['n'];gates=d['gates'];output=d.get('output',n+len(gates)-1)
    edges={tuple(sorted(e)) for e in d['graph_edges']}
    inputs=[sum(1<<m for m in range(1<<n) if m>>i&1) for i in range(n)]
    target=sum(1<<m for m in range(1<<n) if any((m>>a&1) and (m>>b&1) for a,b in edges))
    def values(replace=None):
        v=list(inputs)
        for j,(op,a,b) in enumerate(gates):
            assert op in ('and','or') and 0<=a<n+j and 0<=b<n+j
            v.append(v[replace[1]] if replace is not None and j==replace[0]
                     else v[a]&v[b] if op=='and' else v[a]|v[b])
        return v
    vals=values();assert vals[output]==target
    tops=[j for j,(op,a,b) in enumerate(gates) if op=='and' and not vals[n+j]&~target]
    junk=[j for j,(op,a,b) in enumerate(gates) if op=='and' and vals[n+j]&~target]
    assert tops==d['tops'] and junk==d['junk']
    raw=[{i} for i in range(n)];anc=[set() for _ in range(n)]
    for j,(op,a,b) in enumerate(gates):
        raw.append(raw[a]|raw[b] if op=='or' else set())
        anc.append(anc[a]|anc[b]|{j})
        if op=='and':assert not set(tops)&(anc[-1]-{j})
    stars={tuple(sorted((u,v))) for j in tops for u in raw[gates[j][1]] for v in raw[gates[j][2]]}
    ustar=edges-stars;assert ustar=={tuple(sorted(e)) for e in d['Ustar']}
    nested={(i,j) for i in junk for j in junk if i!=j and i in anc[n+j]}
    if 'nested_junk_pairs' in d:assert nested=={tuple(p) for p in d['nested_junk_pairs']}
    bypasses=[];changed={}
    for j,(op,a,b) in enumerate(gates):
        for side,child in enumerate((a,b)):
            altered=values((j,child))[output]
            changed[(j,side)]=altered
            assert altered!=target
            if op=='or':
                assert not altered&~target
                assert any(not (altered >> ((1<<u)|(1<<v)) & 1) for u,v in edges)
            else:
                assert not target&~altered and altered&~target
            bypasses.append((j,child))
    context_name=path.name.replace('-bad-certificate.witness.json','-context.json').replace('.witness.json','-context.json')
    context=json.loads((base/context_name).read_text())
    assert len(context['records'])==len(bypasses) and context['all_child_bypasses_essential']
    for record in context['records']:
        j,side=record['gate'],record['side'];mask=record['certificate_mask']
        assert record['op']==gates[j][0] and record['source']==gates[j][side+1] and record['essential']
        altered=changed[(j,side)]
        if record['op']=='or':
            assert mask.bit_count()==2 and (target>>mask&1) and not(altered>>mask&1)
        else:
            assert not(target>>mask&1) and (altered>>mask&1)
    bad=None
    if 'distinguished_dirty_wire' in d:
        bad=[m for m in range(1<<n) if (vals[d['distinguished_dirty_wire']]>>m&1) and not(target>>m&1)]
        assert bad==d['dirty_bad_assignments']
        assert min(map(int.bit_count,bad))==d['min_independent_bad_certificate']
        even=set(range(0,n,2));monomial=sum(1<<m for m in range(1<<n) if all(m>>i&1 for i in even))
        assert vals[d['distinguished_dirty_wire']]==target|monomial
        assert d['standard_star_upper']==2*d['matching_size']-1<len(gates)
    return {'file':path.name,'full_truth_rows':1<<n,'gates':len(gates),'junk':len(junk),
            'nested_pairs':len(nested),'TopForm':True,'Ustar':len(ustar),
            'child_bypasses_verified':len(bypasses),'independent_bad_assignments':bad}

checks=[analyze(p) for p in sorted(base.glob('*.witness.json'))]
c6=json.loads((base/'c6-omission-correction.json').read_text())
clauses=c6['remaining_cover_clauses']
edges=[(i,(i+1)%6) for i in range(6)]
bad=[m for m in range(64) if all(m & clause for clause in clauses)
     and not any((m>>a&1) and (m>>b&1) for a,b in edges)]
assert bad==c6['actual_independent_bad_assignments']==[5,17,20,21]
assert min(map(int.bit_count,bad))==c6['minimum_bad_certificate']==2
print(json.dumps({'manifest_files':len(manifest['files']),
                  'manifest_bytes':sum(e['bytes'] for e in manifest['files']),
                  'manifest_sha256':hashlib.sha256((base/'MANIFEST.json').read_bytes()).hexdigest(),
                  'all_hashes_and_census_match':True,'witnesses':checks,'C6_correction_verified':True},indent=2))
