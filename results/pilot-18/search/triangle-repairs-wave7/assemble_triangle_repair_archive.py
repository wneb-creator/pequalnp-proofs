"""Assemble immutable SAT-repair evidence and completed logs; no active outputs."""
from pathlib import Path
import hashlib
import json
import re

ROOT=Path('/tmp/oec/pequalnp-pilot-18');HERE=ROOT/'orch/S02'
STAGE=HERE/'triangle-repairs-preservation-stage/S02-triangle-repairs'
STAGE.mkdir(parents=True,exist_ok=False)
sha=lambda raw:hashlib.sha256(raw).hexdigest()
bindings=[];sources=[]


def copy(source,relative):
    assert source.is_file() and not source.is_symlink() and source.suffix!='.cnf'
    raw=source.read_bytes();text=raw.decode()
    assert not re.search(r'github_pat_[A-Za-z0-9_]{30,}|gh[pousr]_[A-Za-z0-9_]{20,}|[?&]lease=[A-Za-z0-9_-]{16,}',text)
    destination=STAGE/relative;destination.parent.mkdir(parents=True,exist_ok=True)
    with destination.open('xb') as f:f.write(raw)
    assert source.read_bytes()==raw
    bindings.append({'source':str(source),'archive':relative,'sha256':sha(raw),'bytes':len(raw)})


needed=['orch/S02/generate_triangle589_repairs.py','orch/S02/generate_triangle589_best3_repairs.py',
        'orch/S02/generate_best3_rescheduled.py','orch/S02/triangle589-repair-analysis/source-augmented.json',
        'orch/S02/triangle589-best3-source.json','orch/S02/prepare_positive_repairs.py',
        'orch/S02/generate_rescheduled_repairs.py','lean-setup/generate_distance_repairs.py',
        'lean-setup/generate_local_repairs.py','search_l1342_shard17_ancestorreverse.py',
        'validate_raw_candidate.py','lean-setup/validate_sat_candidate.py']
for name in needed:
    relative='scratch/'+name;copy(ROOT/name,relative)
    sources.append({'scratch_path':name,'package_path':relative,'sha256':sha((ROOT/name).read_bytes())})
families=[]
for name,program in [('triangle589-repair-family','generate_triangle589_repairs.py'),
                     ('triangle589-best3-repair-family','generate_triangle589_best3_repairs.py'),
                     ('best3-rescheduled-family','generate_best3_rescheduled.py')]:
    directory=HERE/name
    families.append({'name':name,'generator':'orch/S02/'+program,
                     'expected_files':{p.name:sha(p.read_bytes()) for p in sorted(directory.iterdir())}})
    for p in sorted(directory.iterdir()):
        if p.suffix!='.cnf':copy(p,'metadata/'+name+'/'+p.name)

names=['audit_triangle589_repairs.py','audit_best3_rescheduled.py','analyze_triangle589_repairs.py',
       'triangle589-repair-review.json','triangle589-best3-repair-review.json','triangle589-repair-control-totals.json',
       'triangle589-best3-generator.diff','triangle589-best3-generator-delta.json',
       'triangle589-best3-controller.diff','triangle589-best3-controller-review.json','main-best3-controller.diff',
       'main-best3-repair-review.json','triangle589-best3-repair-handoff.json',
       'best3-rescheduled-review.json','best3-rescheduled-controller.diff','best3-rescheduled-controller-review.json',
       'main-best3-rescheduled-review.json','best3-rescheduled-handoff.json',
       'triangle589-repair-analysis/report.json','triangle589-repair-analysis.stdout.txt','triangle589-repair-analysis.stderr.txt']
for name in names:copy(HERE/name,'reviews/'+name)
for stem in ['triangle589-repairs-help','triangle589-repairs-generation','triangle589-best3-repairs-help',
             'triangle589-best3-repairs-generation','triangle589-repairs-audit','best3-rescheduled-help',
             'best3-rescheduled-generation','best3-rescheduled-audit']:
    for suffix in ['.stdout.txt','.stderr.txt']:copy(HERE/(stem+suffix),'logs/'+stem+suffix)
for name in ['run_triangle589_best3_repair_pilot.py','run_best3_rescheduled_pilot.py','run_context_window_pilot.py']:
    copy(ROOT/name,'controllers/'+name)
for name in ['triangle589-positive21.json','main-134226-best3-scalar.json']:
    copy(ROOT/'orch/S05'/name,'source-provenance/'+name)

control_summaries=[]
for stem in ['triangle589','triangle589-best3']:
    directory=HERE/(stem+'-one-gate-control');report=json.loads((directory/'report.json').read_text())
    assert report['complete'] and report['checked_gate_descriptions']==12362 and report['output_wire_checks']==420308
    assert not report['exact_candidates']
    for p in sorted(directory.iterdir()):copy(p,'one-gate-controls/'+stem+'/'+p.name)
    for suffix in ['.stdout.txt','.stderr.txt']:copy(HERE/(stem+'-one-gate-control'+suffix),'one-gate-controls/'+stem+suffix)
    program='enumerate_triangle589_best3_one_gate.py' if stem.endswith('best3') else 'enumerate_triangle589_one_gate.py'
    copy(HERE/program,'one-gate-controls/'+program)
    control_summaries.append({k:report[k] for k in ['source_sha256','checked_gate_descriptions','output_wire_checks','cpu_seconds','best_all_positive_boundary_FP']})

# The old seed's boundary-score improvement is not an improvement in full error count.
improved=json.loads((HERE/'triangle589-one-gate-control/positive-improvement-00.json').read_text())
edges=[(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
fn=[];fp=[]
for mask in range(2048):
    values=[bool(mask>>i&1) for i in range(11)]+[False,True]
    for op,a,b in improved['gates']:values.append(values[a] and values[b] if op=='and' else values[a] or values[b])
    actual=values[improved['output']];target=any(mask>>a&1 and mask>>b&1 for a,b in edges)
    assert actual==(target or values[9])
    if target and not actual:fn.append(mask)
    if actual and not target:fp.append(mask)
assert not fn and len(fp)==22
(STAGE/'one-gate-controls/old-seed-improvement-scalar.json').write_text(json.dumps({
    'source_sha256':sha((HERE/'triangle589-one-gate-control/positive-improvement-00.json').read_bytes()),
    'scalar_checks':2048,'exact_shape':'F OR x9','full_FN':0,'full_FP_masks':fp,
    'scope':'Boundary score improved6to5, but full errors worsened10to22. Not an exact witness or preferred seed.'},indent=2)+'\n')

run=ROOT/'triangle589-best3-repair-pilot';raw_portfolio=(run/'portfolio.json').read_bytes();portfolio=json.loads(raw_portfolio)
assert portfolio.get('finished') and not portfolio.get('candidate') and not portfolio.get('error')
assert len(portfolio['cases'])==3 and all(v['exit_code']==0 and v['status_lines']==['s UNKNOWN'] for v in portfolio['cases'].values())
expected={'portfolio.json','worker-limit.txt'}|{name+suffix for name in portfolio['cases'] for suffix in ['.stdout','.stderr']}
assert expected=={p.name for p in run.iterdir()}
for p in sorted(run.iterdir()):copy(p,'completed-best3-pilot/'+p.name)
assert (run/'portfolio.json').read_bytes()==raw_portfolio
for name in ['triangle589-best3-repair-controller.stdout','triangle589-best3-repair-controller.stderr','triangle589-best3-repair-launch.json']:
    copy(ROOT/name,'completed-best3-pilot/'+name)

copy(HERE/'reconstruct_triangle_repairs.py','reconstruct_triangle_repairs.py')
copy(Path(__file__),'assemble_triangle_repair_archive.py')
(STAGE/'reconstruction.json').write_text(json.dumps({'sources':sources,'families':families,'scope':'Eight CNFs only; no solver, one-gate enumeration, network or Lean execution.'},indent=2)+'\n')
(STAGE/'copy-bindings.json').write_text(json.dumps({'files':bindings},indent=2)+'\n')
(STAGE/'snapshot-status.json').write_text(json.dumps({'original_triangle589':{'prepared':3,'runtime_included':False},
    'best3':{'prepared':3,'completed':3,'outcomes':{'UNKNOWN':3}},
    'rescheduled_best3':{'prepared':2,'main_review':'PASS','runtime_included':False},
    'one_gate_controls':control_summaries,'active_outputs_read':False,'solver_launched':False,
    'scope':'No exact21 witness or global/shard exhaustion. Rescheduled runtime is explicitly absent from this snapshot.'},indent=2)+'\n')
(STAGE/'README.md').write_text('S02 triangle589 repair preservation\n\n'
    'Eight prepared candidate CNFs: original triangle589 connected11/K4/K6 (no runtime included); immutable best3 connected12/K4/K6 (all three completed UNKNOWN at120seconds); and rescheduled best3 dirty-early14/reverse-readyK6 (main review PASS, runtime explicitly absent). No active solver outputs were read or copied. Historical READY labels and future command recipes are provenance, not evidence of a launch or result.\n\n'
    'Both original and improved source circuits remain inexact. Their exact functions are F OR x2(x0 OR x7)(x1 OR x4), and F OR x2x4(x0 OR x7). The latter has exactly five erroneous full inputs21,29,85,148,149. Rescheduling preserves all21gate values and every input, but different legal dependency orders need not produce nested repair domains.\n\n'
    'Both finite single-gate controls completed12362 arbitrary operator/fanin rewrites and420308 free-output checks each in under0.1CPUsecond; neither found an exact circuit. The original control saved a boundary-score improvement to5FP; independent scalar checking here shows F OR x9 and22full errors, so it is not a better full-error seed. Controls are local finite enumerations, not proofs against multi-gate repairs or the global model.\n\n'
    'Sources, full generation/audit logs, main and self reviews, controller deltas, exact seed metadata, both one-gate control outputs, and all three completed solver stdout/stderr pairs plus complete controller logs are preserved. No raw CNFs, solver executables, credential or lease values are included. MANIFEST.json binds every payload.\n\n'
    'Reconstruct with Python3 and its standard library only: python3 reconstruct_triangle_repairs.py /tmp/oec/pequalnp-pilot-18/fresh-triangle-reproduction. The path must be fresh. Missing pinned sources are staged only under the named scratch root; existing different sources are rejected, never overwritten. All8CNFs/26generated files are checked against exact hashes. No solver, enumeration, network or Lean build runs during reconstruction. Completed results do not establish a21gate witness or any global/shard exhaustion. Main independently reviews before preservation push.\n')
print(json.dumps({'stage':str(STAGE),'exact_copies':len(bindings),'families':3,'CNFs':8,'finished_pilots':3,'active_outputs_read':False}))
