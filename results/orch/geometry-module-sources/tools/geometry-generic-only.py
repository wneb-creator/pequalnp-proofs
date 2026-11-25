import json
from pathlib import Path
p=Path('/tmp/oec/pequalnp-pilot-62')
rows=json.loads((p/'geometry-data.json').read_text())['generic']
posted={r['S'] for r in rows}
lines=[sum(1<<((l+d)%13) for d in [0,1,3,9]) for l in range(13)]
point_lines=[sum(1<<l for l in range(13) if lines[l]>>v&1) for v in range(13)]
weak=[]
for mask in range(8192):
 missing=sum(1<<l for l in range(13) if not(mask&lines[l]))
 collinear=any(mask&~line==0 for line in lines)
 concurrent=any(missing&~through==0 for through in point_lines)
 if not collinear and not concurrent:weak.append(mask)
print('Noncollinear_X_and_nonconcurrent_missing_lines',len(weak))
print('Equal_posted_admissible_masks',set(weak)==posted)
print('Extra_masks',sorted(set(weak)-posted))
print('Missing_masks',sorted(posted-set(weak)))
assert set(weak)==posted
