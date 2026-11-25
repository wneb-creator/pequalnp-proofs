import json
import sys
from pathlib import Path
from rup_tools import verify

path, prefix = map(Path,sys.argv[1:3])
reports = []
for line in path.read_text().splitlines():
    if not line.startswith('BEST '):
        continue
    candidate = json.loads(line[5:])
    assert candidate['order'] == 'oldest first'
    valid, length, traces = verify(candidate['run'])
    assert valid and length == candidate['length']
    candidate['traces'] = traces
    candidate['independently_validated'] = True
    reports.append(dict(trial=candidate['trial'],length=length,valid=valid))
    prefix.with_name(prefix.name+'-best.json').write_text(json.dumps(candidate,indent=2)+'\n')
prefix.with_name(prefix.name+'-validation.json').write_text(json.dumps(reports,indent=2)+'\n')
print(json.dumps(reports))
