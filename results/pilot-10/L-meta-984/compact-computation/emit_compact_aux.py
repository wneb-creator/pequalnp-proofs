from pathlib import Path
import json,hashlib
BASE=Path('/tmp/oec/pequalnp-pilot-10/independent-search/984')
summary=[]
for graph in range(31):
 routes=json.loads((BASE/f'compact/routes{graph}.json').read_text());fast=json.loads((BASE/f'compact/fast_pool_{graph}.json').read_text());cache=json.loads((BASE/f'input_action_cache_{graph}.json').read_text())
 masks=[int(x,16) for r in routes['networks'] for x in r['lo_hex']]
 assert all(x<2**32 for x in masks)
 packed=sum(x<<(32*j) for j,x in enumerate(masks))
 assert all((packed>>(32*j))&((1<<32)-1)==x for j,x in enumerate(masks))
 name=f'C{graph}'
 text=f'def {name}_routeCodes : Nat := {hex(packed)}\n'
 text+=f'def {name}_masks (auto : Nat) : List Nat := (List.range 9).map (fun i => fld {name}_routeCodes 32 (9*auto+i))\n'
 text+=f'def {name}_coords : List Nat := '+str(fast['coordinate_array'])+'\n'
 text+=f'def {name}_rankPool : List Nat := '+str(fast['rank_codes'])+'\n'
 text+=f'def {name}_inputActions : Nat := '+cache['packed_auto_codes_hex']+'\n'
 path=BASE/f'direct/{name}.aux.fragment.lean';path.write_text(text)
 summary.append({'graph':graph,'group':len(routes['networks']),'rank_width':fast['rank_width'],'bytes':len(text.encode()),'sha256':hashlib.sha256(text.encode()).hexdigest(),'route_stages':9,'route_distances':[1,2,4,8,16,8,4,2,1]})
(BASE/'direct/aux-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print('PASS31 aux fragments; bytes',sum(x['bytes'] for x in summary))
