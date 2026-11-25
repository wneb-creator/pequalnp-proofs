from pathlib import Path
import hashlib,json,re,time
import sympy as S
from sympy.polys.rings import ring
from sympy.polys.domains import QQ

start=time.monotonic();base=Path('/tmp/oec/pequalnp-pilot-78/geometry_search')
source=base/'rowzero/canonical_extra/CanonicalExtraBody.lean'
text=source.read_text();native=json.loads((base/'canonical55/input.json').read_text())
assert hashlib.sha256(source.read_bytes()).hexdigest()=='2fa445227fb6420fe0c2632242a9653c43d9606deb26a71cd4e44e0dc06b8daa'
R,*x=ring(','.join(f'x{i}' for i in range(18)),QQ)
loc={f'x{i}':S.Symbol(f'x{i}') for i in range(18)}
def lean_poly(s):
    s=re.sub(r'\(p (\d+)\)',lambda m:f'x{m[1]}',s)
    s=re.sub(r'\(b (\d+)\)',lambda m:f'x{9+int(m[1])}',s)
    s=re.sub(r'\s*:\s*ℂ','',s).replace('^','**')
    return R.from_expr(S.sympify(s,locals=loc))
def encoded(poly):
    answer=R.zero
    for mon,c in poly:
        term=R.one*QQ(c)
        for i in mon:term*=x[i]
        answer+=term
    return answer
gens=list(map(encoded,native['encoded_generators']))
defs=re.findall(r'def canonicalExtra(\d+) \(p b : Fin 9 → ℂ\) : ℂ :=\n(.*?)\n\nset_option',text,re.S)
blocks=re.findall(r'lemma canonical_extra_(\d+)_zero .*?\n  linear_combination\n(.*?)(?=\n\ndef canonicalExtra|\n\ndef canonicalExtras)',text,re.S)
assert len(defs)==len(blocks)==24
assert [int(i) for i,_ in defs]==list(range(24))
assert [int(i) for i,_ in blocks]==list(range(24))
details=[]
for (i,definition),(j,proof) in zip(defs,blocks):
    assert i==j;idx=int(i)
    target=lean_poly(definition)
    assert target==gens[31+idx]
    terms=re.findall(r'\((.*?)\) \* h(\d+)(?: \+|\s*$)',proof,re.S)
    assert terms
    rebuilt=R.zero
    used=[]
    for coeff,n in terms:
        n=int(n);assert 0<=n<31 and n not in used;used.append(n)
        rebuilt+=lean_poly(coeff)*gens[n]
    assert rebuilt==target,idx
    details.append({'extra':idx,'target_terms':len(target),'grouped_generators':used,'actual_Lean_identity_verified':True})
assert not any(s in text for s in ['_root_','"','sorry','native_decide','axiom'])
assert not re.search(r'@\[',text)
assert set(re.findall(r'set_option (\w+)',text))=={'maxHeartbeats'}
assert '∀ j : Fin 31, canonicalGenerators p b j=0' in text
assert len(re.findall(r'using canonical_extra_\d+_zero p b h',text))==24
report={'status':'PASS independent source/algebra audit; Lean not yet built',
        'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
        'source_lines':len(text.splitlines()),'all24_actual_Lean_targets_match_native55':True,
        'all24_actual_Lean_linear_combination_identities_verified':True,
        'plain_file_restrictions':True,'details':details,'seconds':time.monotonic()-start,
        'scope':'Exactly24 necessary quartic consequences of the31 canonical generators; no infeasibility or global theorem is asserted.'}
(base/'canonical-extra-source-independent-audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:report[k] for k in ['status','source_sha256','source_lines','seconds']}),flush=True)
