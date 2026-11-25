from pathlib import Path
from itertools import combinations
from collections import Counter
import json,sys
rows=json.loads(Path(sys.argv[1]).read_text())['examples'];required={11,69,49}
outside=[m for m in range(128) if m.bit_count()==2 and all(m&t!=m for t in required)]
assert len(outside)==12
initial={0}|{1<<i for i in range(7)}
def closure(family):
    allowed=initial|set(outside)|set(family);known=initial.copy()
    while True:
        old=set(known)
        for a in old:
            for b in old:
                for result in [a|b,a&b]:
                    if result in allowed:known.add(result)
        if known==old:return known
reports=[]
for family in sorted({tuple(row['family']) for row in rows}):
    known=closure(family)
    reports.append({'family':list(family),'reachable':sorted(known),'missing_family_masks':sorted(set(family)-known),'missing_required_triples':sorted(required-known)})
lines=Path(sys.argv[2]).read_text().splitlines();families=[list(map(int,line.split())) for line in lines[1:]];assert len(families)==int(lines[0]);passing=[row for row in families if set(row[1:])<=closure(row[1:])]
output={'scope':'Closure includes union AND intersection and ALL12 outside-triple pairs; saturated-count actual-circuit induction is separate from this finite computation.','outside_pairs':outside,'combined_family_count':len(reports),'combined_constructible_count':sum(not r['missing_family_masks'] for r in reports),'combined_reports':reports,'all_parent_family_count':len(families),'all_parent_constructible_count':len(passing),'all_parent_constructible':passing}
Path(sys.argv[3]).write_text(json.dumps(output,indent=2)+'\n');Path(sys.argv[4]).write_text(str(len(passing))+'\n'+'\n'.join(' '.join(map(str,row)) for row in passing)+'\n')
print(json.dumps({k:v for k,v in output.items() if k not in ['combined_reports','all_parent_constructible']}))
