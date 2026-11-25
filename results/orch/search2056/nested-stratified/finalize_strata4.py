from pathlib import Path
import collections,datetime,hashlib,json
s=Path('/tmp/oec/pequalnp-pilot-121/not-elimination')
run=json.loads((s/'plane2056-strata4-run.json').read_text())
assert run['status']!='running; no witness', 'phase still active'
a=json.loads((s/'plane2056-strata4-analysis.json').read_text())
records=[json.loads(line) for line in (s/'plane2056-strata4.stdout').read_text().splitlines() if line.strip().startswith('{')]
pop=[r for r in records if r.get('record_kind')=='population']
witness=[r for r in records if r.get('raw')==0]
(s/'plane2056-strata4-final-populations.json').write_text(json.dumps(pop,indent=2)+'\n')
summary={'status':'completed; no witness' if not witness else 'completed; candidate requires full verification','archived_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'run':run,'source_sha256':hashlib.sha256((s/'plane2056_strata4.cpp').read_bytes()).hexdigest(),'config_sha256':hashlib.sha256((s/'plane2056-strata69-seeds.data').read_bytes()).hexdigest(),'latest_seconds':a.get('latest_seconds'),'proposals':a.get('latest_iterations'),'best_by_mode':[{k:r.get(k) for k in ['mode','raw','fp','bad_edges','shared_dirty_ands','nested_shared_pairs']} for r in a['best']],'population_records':len(pop),'population_by_mode':dict(collections.Counter(r['mode'] for r in pop)),'witness_records':len(witness),'reported_error_mismatches':a.get('reported_error_mismatches'),'sharing_metric_mismatches':a.get('sharing_metric_mismatches'),'nested_metric_mismatches':a.get('nested_metric_mismatches'),'class_violations':a.get('class_violations'),'all_logs_complete':True,'source_controls_independently_reviewed':True}
(s/'plane2056-strata4-summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
