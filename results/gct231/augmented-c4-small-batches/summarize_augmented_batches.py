"""Summarize complete saved finite-field logs without rerunning a solver."""
from pathlib import Path
import json,re
root=Path('/tmp/oec/pequalnp-pilot-75/gct231')
records=[]
for case in (2,3):
    for pairs in (1,4,32):
        name=f'neogb-c4-augmented{case}-p1009-'+('r1' if pairs==32 else f'b{pairs}')
        data=json.loads((root/(name+'.result.json')).read_text())
        rows=[]
        for line in (root/(name+'.log')).read_text().splitlines():
            match=re.match(r'^\s*(\d+)\s+(\d+)\s+(\d+)\s+(\d+) x (\d+)',line)
            if match:rows.append(tuple(map(int,match.groups())))
        records.append({'case':case,'pairs':pairs,'status':data['status'],
            'unit_F1009':data.get('unit_basis'),'seconds':data['seconds'],
            'printed_pair_rounds':len(rows),
            'max_matrix_entries':max((r[3]*r[4] for r in rows),default=0),
            'max_columns':max((r[4] for r in rows),default=0),
            'max_degree':max((r[0] for r in rows),default=0)})
output={'scope':'Finite-field timing/order observations only; no implication about rational elimination cost.',
        'records':records}
(root/'augmented-batch-summary.json').write_text(json.dumps(output,indent=2)+'\n')
print(json.dumps(output,indent=2))
