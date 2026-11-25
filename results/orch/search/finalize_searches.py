from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import shutil

archive=Path('/workspace/pequalnp-proofs/results/orch/search')
edges=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
jobs=[('two_not','search_cgp_two_not.log',None,1200),('prefix_adjacent','search_prefix_adjacent.log',1,600),('prefix_nonadjacent','search_prefix_nonadjacent.log',2,600)]
completion=datetime.now(timezone.utc).isoformat()
summaries={}
for name,filename,other,limit in jobs:
    lines=(archive/filename).read_text().splitlines()
    endings=[line for line in lines if line.startswith('END ')]
    assert len(endings)==1, f'{filename} has not completed'
    fields=dict(piece.split('=') for piece in endings[0].split()[1:])
    i=max(i for i,line in enumerate(lines) if line.startswith('BEST') and i+19<len(lines))
    gates=[list(map(int,line.split()))[1:] for line in lines[i+1:i+20]]
    assert len(gates)==19
    assert all(op in (0,1,2) and 0<=a<10+j and 0<=b<10+j for j,(op,a,b) in enumerate(gates))
    assert sum(op==2 for op,a,b in gates)==2
    if other is not None:
        assert gates[:2]==[[2,0,0],[2,other,other]]
        assert all(op in (0,1) for op,a,b in gates[2:])
    values=[]
    errors=[]
    for row in range(1024):
        wires=[bool(row>>k&1) for k in range(10)]
        for op,a,b in gates:
            wires.append(wires[a]&wires[b] if op==0 else wires[a]|wires[b] if op==1 else not wires[a])
        expected=any(row>>a&row>>b&1 for a,b in edges)
        values.append(wires[-1])
        if wires[-1]!=expected:
            errors.append({'row':row,'expected':bool(expected),'actual':wires[-1],'true_inputs':[k for k in range(10) if row>>k&1]})
    used={28}
    active=[]
    for j in range(18,-1,-1):
        if j+10 in used:
            op,a,b=gates[j]
            used.add(a)
            if op==2:
                active.append(j)
            else:
                used.add(b)
    assert len(active)==2
    assert len(errors)==int(fields['best'])
    candidate={'source_log':filename,'source_record':lines[i],'gates':gates,'output':28,'rows_checked':1024,'errors':errors,'active_not_gate_indices':active,'essential_inputs':[k for k in range(10) if any(values[row]!=values[row^(1<<k)] for row in range(1024))],'used_gate_count':sum(j+10 in used for j in range(19)),'output_monotone':all(not values[row] or values[row|(1<<k)] for row in range(1024) for k in range(10)),'is_counterexample':not errors}
    candidate_name=f'best_{name}_final.json'
    (archive/candidate_name).write_text(json.dumps(candidate,indent=2)+'\n')
    summaries[name]={'duration_limit_seconds':limit,'iterations':int(fields['iterations']),'best_errors':len(errors),'candidate':candidate_name,'source_log':filename,'log_sha256':hashlib.sha256((archive/filename).read_bytes()).hexdigest(),'scope':'Heuristic search; no exhaustive lower bound and no Lean-checked result.'}
report={'completion_observed_at':completion,'jobs':summaries,'sources':{}}
for name in ['search_cgp_two_not.cpp','search_cgp_prefix_not.cpp','prefix_symmetry.py']:
    report['sources'][name]=hashlib.sha256((archive/name).read_bytes()).hexdigest()
report['verification_source_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
(archive/'search-snapshot-2.json').write_text(json.dumps(report,indent=2)+'\n')
prefix=json.loads((archive/'prefix-search-report.json').read_text())
prefix['status']='completed'
prefix['completion_observed_at']=completion
prefix['results']={name:summaries['prefix_'+name] for name in ['adjacent','nonadjacent']}
(archive/'prefix-search-report.json').write_text(json.dumps(prefix,indent=2)+'\n')
if Path(__file__).resolve() != (archive/'finalize_searches.py').resolve():
    shutil.copyfile(Path(__file__),archive/'finalize_searches.py')
readme=(archive/'README.md').read_text()
readme=readme.replace('The two-NOT log remains live. Its JSON candidate file is an independently evaluated earlier snapshot. The report timestamps this documentation snapshot and includes hashes of the static two-NOT and window-search sources.', 'The first checkpoint was taken while the two-NOT log was live. Its candidate JSON is an independently evaluated earlier snapshot. The completed runs and final candidate files are identified below.')
(archive/'README.md').write_text(readme)
with (archive/'README.md').open('a') as f:
    f.write('\nThe later searches completed without a counterexample. The general two-NOT run ended with '+str(summaries['two_not']['best_errors'])+' incorrect rows; the adjacent and nonadjacent fixed-prefix runs ended with '+str(summaries['prefix_adjacent']['best_errors'])+' and '+str(summaries['prefix_nonadjacent']['best_errors'])+' incorrect rows. Their final candidates were independently reevaluated on all 1,024 inputs by `finalize_searches.py`. Final counts, hashes, and candidate paths are in `search-snapshot-2.json`; the earlier candidate JSON files remain historical snapshots.\n')
with Path('/workspace/pequalnp-proofs/results/orch/TIMELINE.md').open('a') as f:
    f.write(completion+' completion observed for general two-NOT and both fixed-prefix NOT searches; no witness\n')
with Path('/workspace/pequalnp-proofs/results/orch/NOTES.md').open('a') as f:
    f.write('\n'+completion+' counterexample_search: General two-NOT search and both fixed-input-NOT prefix searches completed without a witness. Final results independently checked on all 1,024 rows and preserved in results/orch/search/search-snapshot-2.json. This remains computational search evidence only.\n')
print(json.dumps(report,indent=2))
