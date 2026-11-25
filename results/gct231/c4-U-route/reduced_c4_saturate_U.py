"""Exact auxiliary systems testing whether U can be nonzero in a reduced branch."""
from pathlib import Path
import hashlib,json
root=Path('/tmp/oec/pequalnp-pilot-75/gct231')
for case in (2,3):
    source=root/'fresh'/f'c4-nonzero-reduced-{case}.json'
    data=json.loads(source.read_text())
    assert 'U' in data['variables'] and 'invU' not in data['variables']
    data['variables']=data['variables']+['invU']
    data['equations']=data['equations']+['invU*U - 1']
    data['reduced_source_sha256']=hashlib.sha256(source.read_bytes()).hexdigest()
    data['scope']='Original six reduced necessary equations plus the auxiliary assumption U is nonzero. A characteristic-zero unit certificate would imply U=0 for the original reduced system; no verdict claimed.'
    target=root/f'c4-nonzero-U-saturated-{case}.json'
    target.write_text(json.dumps(data,indent=2)+'\n')
    print(case,hashlib.sha256(target.read_bytes()).hexdigest(),flush=True)
