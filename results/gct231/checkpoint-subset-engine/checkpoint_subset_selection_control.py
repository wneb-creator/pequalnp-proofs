"""Cross-check actual budget-2 choices against unchanged full control states."""
from pathlib import Path
import json
root=Path(__file__).parent
def read(path):
    lines=path.read_text().splitlines()
    n,m,p,total=map(int,lines[0].split())
    lengths=list(map(int,lines[1].split()))
    assert len(lengths)==m and sum(lengths)==total
    rows=[];offset=2
    for count in lengths:
        rows.append(lines[offset:offset+count]);offset+=count
    assert offset==len(lines)
    return rows
checks=0
for path in (root/'checkpoint-subset-budget2/controls').glob('*-stop1.result.json'):
    small=json.loads(path.read_text())
    full=json.loads((root/'checkpoint-subset/controls'/path.name).read_text())
    small_meta=small['checkpoint']['metadata'];full_meta=full['checkpoint']['metadata']
    assert small_meta['round']==full_meta['round']
    original=small_meta['original_generators']
    rows=read(Path(full['checkpoint']['path']))[original:]
    expected=[];used=0
    for row in rows:
        if used+len(row)<=2:
            expected.append(row);used+=len(row)
    assert expected==read(Path(small['checkpoint']['path']))[original:]
    assert small_meta['available_basis_rows']==len(rows)
    assert small_meta['available_basis_terms']==sum(map(len,rows))
    checks+=1
assert checks==9
print('PASS deterministic greedy budget2 selection against full production snapshots:',checks,'stopped controls')
