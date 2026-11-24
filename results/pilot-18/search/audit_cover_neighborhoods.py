"""No-solver audit of cover neighborhoods and known-22 validator fixtures."""
from pathlib import Path
from collections import deque
import hashlib
import importlib.util
import itertools
import json
import random
import subprocess
import sys
import datetime

sys.dont_write_bytecode=True
ROOT=Path('/tmp/oec/pequalnp-pilot-18');OUT=ROOT/'lean-setup'
SOURCE=OUT/'generate_cover_neighborhoods.py';FAMILY=ROOT/'cover-neighborhoods'
CONTROLS=OUT/'cover-neighborhood-controls';CONTROLS.mkdir(exist_ok=False)
sha=lambda b:hashlib.sha256(b).hexdigest()


def module(path,name):
    spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m);return m


g=module(SOURCE,'neighborhood_audit_source')
validator_path=OUT/'validate_sat_candidate.py'
assert sha(validator_path.read_bytes())=='b807c1a580ce1fa49da51d859e6bc5d94bab2f9f0cd359c35cef35686f826529'
v=module(validator_path,'neighborhood_audit_validator')
base=g.load_base(ROOT/'search_l1342_shard17_ancestorreverse.py')
manifest=json.loads((FAMILY/'family.json').read_text())
assert manifest['complete'] and manifest['samples']==14 and manifest['program_sha256']==sha(SOURCE.read_bytes())
catalog=json.loads((FAMILY/'cover-catalog.json').read_text())
assert manifest['cover_catalog_sha256']==sha((FAMILY/'cover-catalog.json').read_bytes())
independent_covers=[]
for vertices in itertools.combinations(range(11),7):
    if all(u in vertices or w in vertices for u,w in g.EDGES):
        independent_covers.append(sum(1<<x for x in vertices))
assert sorted(independent_covers)==catalog['cover_masks'] and len(independent_covers)==22


def check_baseline(baseline):
    gates=baseline['gates'];output=baseline['output'];tables=v.truth_tables(gates)
    assert len(gates)==22 and output==34
    v.check_target(tables,output,'known-22 control')
    assert all(not (tables[13+i]&v.NEGATIVE_ROWS) for i,(op,_,_) in enumerate(gates) if op=='and')
    assert v.reachable_gates(gates,output,13)==set(range(22))
    normalized=v.normalize_circuit(gates,output)
    assert normalized['size']==22
    v.check_target(v.truth_tables(normalized['gates'],augmented=False),normalized['output'],'normalized known-22 control')
    ownership=baseline['edge_owners']
    assert [(u,w) for u,w,_ in ownership]==g.EDGES
    assert all(owner in (u,w) and owner in baseline['cover_vertices'] for u,w,owner in ownership)


baseline_controls=0
for cover in independent_covers:
    for seed in range(4):
        check_baseline(g.cover_baseline(cover,random.Random(10000*cover+seed)))
        baseline_controls+=1

cases={};baselines={}
for entry in manifest['cases']:
    name=entry['case'];path=FAMILY/(name+'.cnf');raw=path.read_bytes()
    meta=json.loads(path.with_suffix('.json').read_text())
    baseline=json.loads((FAMILY/(name+'.baseline22.json')).read_text())
    baselines[name]=baseline;check_baseline(baseline);baseline_controls+=1
    assert sha(raw)==entry['cnf_sha256']==meta['sha256']
    assert sha(path.with_suffix('.json').read_bytes())==entry['metadata_sha256']
    assert sha((FAMILY/(name+'.baseline22.json')).read_bytes())==entry['baseline22_sha256']==meta['baseline22_sha256']
    prefix=entry['prefix'];assert 8<=prefix<=14 and meta['size']==21
    original,om=base.build(size=21,first_junk=prefix,second_junk=False,prefix_sort=False,
                         last_output=True,live=False,productive_prefix=False)
    assert sha(g.dimacs(original))==meta['base_with_forced_junk_sha256']
    marker=[om['junk'][prefix]];assert original.clauses.count(marker)==1
    position=original.clauses.index(marker)
    assert position==meta['removed_unit_original_index']
    expected=list(original.clauses);expected.pop(position)
    pins=[]
    for i,(op,a,b) in enumerate(baseline['gates'][:prefix]):
        pins += [[om['ops'][i] if op=='and' else -om['ops'][i]],
                 [om['lefts'][i][a]],[om['rights'][i][b]]]
    expected+=pins
    lines=raw.decode().splitlines();assert lines[0]==f"p cnf {meta['variables']} {meta['clauses']}"
    actual=[]
    for line in lines[1:]:
        c=list(map(int,line.split()));assert c[-1]==0
        assert all(1<=abs(x)<=meta['variables'] for x in c[:-1]);actual.append(c[:-1])
    assert actual==expected and len(actual)==om['clauses']-1+3*prefix
    assert meta['variables']==om['variables'] and meta['pin_clauses']==pins
    assert marker not in actual and om['junk'][prefix+1:] not in actual
    assert meta['enforce_junk'] is False and meta['second_junk'] is False
    assert meta['prefix_sort'] is False and meta['live'] is False and meta['productive_prefix'] is False
    assert meta['last_output'] is True and meta['candidate_only'] and not meta['assigned_shard_exhaustion']
    assert meta['pinned_gates']==baseline['gates'][:prefix]
    for key in ('ops','lefts','rights','junk','output_selectors','prefix_support_tables','prefix_edge_tables'):
        assert meta[key]==om[key]
    cases[name]={'sha256':meta['sha256'],'variables':meta['variables'],'clauses':meta['clauses'],
                 'prefix':prefix,'pins':3*prefix,'removed_exactly_one_forced_junk_unit':True,
                 'all_other_base_clauses_unchanged':True,'baseline_all2048_checked':True}


def unit_model(clauses,variables,seed):
    occurrences={i:[] for i in range(-variables,variables+1) if i}
    remaining=[len(c) for c in clauses];satisfied=[False]*len(clauses)
    for ci,c in enumerate(clauses):
        for literal in c:occurrences[literal].append(ci)
    values=[None]*(variables+1)
    queue=deque(seed.items())
    queue.extend((abs(c[0]),c[0]>0) for c in clauses if len(c)==1)
    while queue:
        variable,value=queue.popleft()
        if values[variable] is not None:
            assert values[variable]==value
            continue
        values[variable]=value
        true_lit=variable if value else -variable
        for ci in occurrences[true_lit]:satisfied[ci]=True
        for ci in occurrences[-true_lit]:
            if satisfied[ci]:continue
            remaining[ci]-=1;assert remaining[ci]>=1
            if remaining[ci]==1:
                unknown=[x for x in clauses[ci] if values[abs(x)] is None]
                assert len(unknown)==1
                x=unknown[0];queue.append((abs(x),x>0))
    free=sum(x is None for x in values[1:])
    assignment={i:bool(values[i]) for i in range(1,variables+1)}
    assert all(any(assignment[abs(x)]==(x>0) for x in c) for c in clauses)
    return assignment,free


fixture_results={}
for entry in manifest['cases'][:7]:
    prefix=entry['prefix'];baseline=baselines[entry['case']]
    cnf,meta=g.neighborhood(base,baseline,prefix,size=22,pin_count=22)
    meta['control_model_origin']='Synthetic known-22 circuit assignment plus unit propagation; no SAT solver was run.'
    raw=g.dimacs(cnf);meta['sha256']=sha(raw)
    name=f'known22-k{prefix:02d}';path=CONTROLS/(name+'.cnf')
    path.write_bytes(raw);path.with_suffix('.json').write_text(json.dumps(meta,indent=2)+'\n')
    seed={}
    for i,(op,a,b) in enumerate(baseline['gates']):
        seed[meta['ops'][i]]=op=='and'
        seed.update({x:j==a for j,x in enumerate(meta['lefts'][i])})
        seed.update({x:j==b for j,x in enumerate(meta['rights'][i])})
        seed[meta['junk'][i]]=False
    seed.update({x:i==baseline['output'] for i,x in enumerate(meta['output_selectors'])})
    assignment,free=unit_model(cnf.clauses,cnf.variables,seed)
    model=CONTROLS/(name+'.synthetic-model.stdout')
    model.write_text('c Synthetic known-22 control; no solver run.\ns SATISFIABLE\nv '+
                     ' '.join(str(i if assignment[i] else -i) for i in range(1,cnf.variables+1))+' 0\n')
    with (CONTROLS/(name+'.validator.stdout.txt')).open('xb') as so,(CONTROLS/(name+'.validator.stderr.txt')).open('xb') as se:
        run=subprocess.run([sys.executable,str(validator_path),str(path),str(model)],stdout=so,stderr=se,timeout=30)
    assert run.returncode==0
    report=json.loads(path.with_suffix('.validated.json').read_text())
    assert report['status']=='VALIDATED' and report['original_gate_count']==report['normalized_gate_count']==22
    assert report['meets_posted_gate_limit'] is False and report['verified_inputs_per_circuit']==2048
    assert report['requested_constraints']['enforce_junk'] is False and report['requested_constraints']['prefix_clean_check']=='passed'
    fixture_results[name]={'cnf_sha256':meta['sha256'],'variables':cnf.variables,'clauses':len(cnf.clauses),
                           'free_irrelevant_auxiliaries_set_false':free,'generic_validator_exit':run.returncode,
                           'report_sha256':sha(path.with_suffix('.validated.json').read_bytes()),
                           'meets_posted_gate_limit':False,'no_solver_run':True}
    print(json.dumps({'fixture':name,'validator':'PASS','gates':22,'clauses':len(cnf.clauses)}),flush=True)

# Reproduce the exact CLI family in a second fresh directory, including metadata.
reproduced=CONTROLS/'reproduced'
g.generate(ROOT/'search_l1342_shard17_ancestorreverse.py',reproduced,14,1342)
files=['family.json','cover-catalog.json']
for entry in manifest['cases']:
    files += [entry['case']+suffix for suffix in ('.cnf','.json','.baseline22.json')]
assert all((FAMILY/name).read_bytes()==(reproduced/name).read_bytes() for name in files)

r={'verdict':'PASS_SELF_AUDIT_READY_FOR_MAIN_INDEPENDENT_REVIEW','timestamp_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
   'generator':str(SOURCE),'generator_sha256':sha(SOURCE.read_bytes()),'base_generator_sha256':g.BASE_SHA,
   'audit_script_sha256':sha(Path(__file__).read_bytes()),'validator_sha256':sha(validator_path.read_bytes()),
   'minimum_cover_count':22,'baseline_circuits_validated_all2048_before_and_after_normalization':baseline_controls,
   'candidate_formulas':len(cases),'candidate_formula_audits':cases,'known22_validator_fixtures':fixture_results,
   'byte_identical_reproduction_files':len(files),'all_prefix_lengths_8_through14_covered':True,
   'exactly_one_required_junk_unit_removed':True,'no_two_junk_condition_added':True,
   'all_original_variable_ids_preserved':True,'prefix_only_op_and_fanin_pins':True,
   'no_search_worker_started':True,'scope':'Only candidate neighborhoods; neither global nor assigned-shard exhaustion.',
   'limitations':['No 21-gate witness or UNSAT result obtained.','Known22 SAT models are explicitly synthetic validation controls, not solver discoveries.',
                  'Main independent review is required before launching candidate searches.'],
   'Sub-agents':'none'}
(OUT/'cover-neighborhood-review.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({'verdict':r['verdict'],'generator_sha256':r['generator_sha256'],'baseline_controls':baseline_controls,
                  'candidate_formulas':len(cases),'known22_validator_fixtures':len(fixture_results),'reproduced_files':len(files)}))
