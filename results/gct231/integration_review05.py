"""Read-only exact integration and helper-format checks."""
from datetime import datetime,timezone
import hashlib
from pathlib import Path
import re


base=Path('/tmp/oec/pequalnp-pilot-75/gct231')
named=Path('/workspace/pequalnp-proofs/lean/PEqualNP/Outside/L_gct_231.lean')
text=named.read_text()
sha=hashlib.sha256(named.read_bytes()).hexdigest()
assert sha=='449df515d9a915699114a3680c21d9de5b4cbcf8e823143374ad52724ff48227'
prior=(base/'lean'/'integration_prior_snapshot.lean').read_text()
assert hashlib.sha256(prior.encode()).hexdigest()=='e00208d33be08325120dce94fa9632031bb0cfbe1cb3595f8e90982e1b11b8ea'
assert text.split('def edgeEnds',1)[0]==prior.split('def edgeEnds',1)[0]
namespace='PEqualNP.Outside.L_gct_231_aux'
def body(path):
    txt=path.read_text()
    return txt.split('namespace '+namespace,1)[1].rsplit('end '+namespace,1)[0].strip()
pieces=[('orbit table',body(base/'EdgeOrbitsTable.lean')),
        ('parameterization',(base/'lean'/'ParameterizationAdditions.txt').read_text().strip()),
        ('polynomial bridge',body(base/'PolyLinearBridge.lean'))]
last=0
for label,piece in pieces:
    assert text.count(piece)==1,label
    at=text.index(piece)
    assert at>last
    last=at+len(piece)
    print('Exact reviewed block preserved:',label)
assert text.startswith('import Mathlib\nimport PEqualNP.Defs\n')
assert len(re.findall(r'^import ',text,re.M))==2
assert len(re.findall(r'^namespace ',text,re.M))==1
assert len(re.findall(r'^end ',text,re.M))==1
assert text.rstrip().endswith('end '+namespace)
assert not re.search(r'\b(sorry|axiom|native_decide|initialize|macro|syntax|notation|elab|attribute)\b',text)
assert '#' not in text and '"' not in text
assert not re.search(r'^\s*(instance|unsafe)\b',text,re.M)
assert not re.search(r'^theorem\s+PEqualNP\.Outside\.L_gct_231\s*:',text,re.M)
assert set(re.findall(r'^set_option\s+(\w+)',text,re.M)) <= {'maxHeartbeats','maxRecDepth','synthInstance','synthInstance.maxSize','synthInstance.maxHeartbeats'}
assert named.is_file() and not named.is_symlink() and len(named.read_bytes())<512*1024
print('Preserved prefix matches prior commit snapshot exactly')
print('Allowed imports, namespace containment, limits, and helper-only format checked')
print('Posted main theorem is absent; file remains partial helper work')
print('Frozen source SHA256',sha)
print('Source lines',len(text.splitlines()),'bytes',len(named.read_bytes()))
print('Review UTC',datetime.now(timezone.utc).isoformat())
print('PASS')
