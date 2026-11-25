from pathlib import Path
import hashlib
import json
import re

ROOT=Path('/tmp/oec/pequalnp-pilot-78')
BASE=ROOT/'geometry_search/rowzero/canonical_extra'
API=ROOT/'canonical_coefficients/CanonicalGeneratorCollectionBody.lean'
BODY=BASE/'CanonicalExtraBody.lean'
api=API.read_text();body=BODY.read_text()
assert hashlib.sha256(body.encode()).hexdigest()=='2fa445227fb6420fe0c2632242a9653c43d9606deb26a71cd4e44e0dc06b8daa'
imports=['Mathlib.Basic.Complex.Basic','Mathlib.Data.Fin.VecNotation',
         'Mathlib.Tactic.LinearCombination','Mathlib.Tactic.FinCases']
mathlib=Path('/workspace/pequalnp-proofs/lean/.lake/packages/mathlib')
assert all((mathlib/(module.replace('.','/')+'.lean')).is_file() for module in imports)
defs=[]
for name in [f'canonicalGenerator{i}' for i in range(31)]+['canonicalGenerators']:
    match=re.search(r'^def '+name+r'\b.*?(?=\n\n)',api,re.M|re.S)
    assert match,name
    defs.append(match[0])
prefix='\n'.join('import '+module for module in imports)
prefix+='\n\nnamespace PEqualNP.Outside.L_gct_231\n\n'+'\n\n'.join(defs)+'\n\n'
suffix='\nend PEqualNP.Outside.L_gct_231\n'
outputs=[]
for index in [None]+list(range(24)):
    if index is None:
        name='CanonicalExtraStandalone.lean';piece=body
    else:
        start=body.index(f'def canonicalExtra{index} (')
        end=body.index(f'def canonicalExtra{index+1} (') if index<23 else body.index('def canonicalExtras (')
        piece=body[start:end]
        name=f'CanonicalExtra{index}Standalone.lean'
    text=prefix+piece+suffix
    assert not any(token in text for token in ['_root_','"','sorry','axiom','native_decide'])
    assert not re.search(r'@\[',text)
    assert 'import PEqualNP' not in text
    path=BASE/name;path.write_text(text)
    outputs.append({'index':index,'path':str(path),'sha256':hashlib.sha256(text.encode()).hexdigest(),
                    'lines':len(text.splitlines()),'bytes':len(text.encode()),
                    'exact_extra_body_slice_sha256':hashlib.sha256(piece.encode()).hexdigest()})
report={'status':'PREPARED ONLY; no Lean build run',
        'scope':'Standalone algebra-only wrappers: exact31 canonical polynomial definitions and vector, plus all24 or one extra consequence. No main, Defs, homogeneous, or other PEqualNP import.',
        'imports':imports,'api_sha256':hashlib.sha256(api.encode()).hexdigest(),
        'extra_body_sha256':hashlib.sha256(body.encode()).hexdigest(),
        'copied_declarations':[f'canonicalGenerator{i}' for i in range(31)]+['canonicalGenerators'],
        'outputs':outputs}
(BASE/'standalone-provenance.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'status':report['status'],'wrapper_count':len(outputs),
                  'full_wrapper':outputs[0],'first_single_wrapper':outputs[1]}))
