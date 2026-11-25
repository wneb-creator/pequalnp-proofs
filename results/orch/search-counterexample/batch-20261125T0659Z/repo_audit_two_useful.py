import hashlib
import json
from pathlib import Path

B=Path('/tmp/oec/pequalnp-pilot-62')
R=Path('/workspace/pequalnp-proofs')
old=(B/'multi_output_useful_ordered_cnf.py').read_text()
new=(B/'multi_output_two_useful_ordered_cnf.py').read_text()
assert old.split('start = time.monotonic()',1)[1].split('cnf.finish()',1)[0] == new.split('start = time.monotonic()',1)[1].split('second_pencil_rows = {}',1)[0]
assert "assert not args.two_useful_pencils or args.useful_exact_pencil" in new
assert "if point == 0: continue" in new and "assert set(second_pencil_rows) == set(range(1,13))" in new
assert 'other_choices.append(cnf.conj(exact+[useful]))' in new
assert 'useful = cnf.disj(cnf.neg(wire[row]) for row in rows)' in new

D=R/'results/orch/search-counterexample/batch-20261125T0654Z'
m=json.loads((D/'useful-ordered-pencil39-control.mapping.json').read_text())
w=json.loads((D/'useful-ordered-pencil39-control-run.witness.json').read_text())
negative=m['negative_samples'];targets=m['target_masks'];assert len(set(targets))==13
assert m['points']==m['line_inputs']==list(range(13))
pencils=[sum(1<<l for l in range(13) if (p-l)%13 in {0,1,3,9}) for p in range(13)]
assert targets==pencils
all_samples=m['positive_samples']+negative
allbits=(1<<len(all_samples))-1
values=[sum(1<<r for r,q in enumerate(all_samples) if q>>i&1) for i in range(13)]
for a,b in w['operand_wire_lists']:
    def conj(refs):
        v=allbits
        for i in refs:v&=values[i]
        return v
    values.append(conj(a)|conj(b))
rows_by_point={p:[13+i for i,q in enumerate(negative) if q.bit_count()==4 and not(q&t)] for p,t in enumerate(targets)}
assert all(len(rows)==54 for rows in rows_by_point.values())
useful=[]
for p,t in enumerate(targets):
    if any((v&8191)==t and any(not(v>>r&1) for r in rows_by_point[p]) for v in values[13:]):useful.append(p)
assert useful==list(range(13))
def transform(q,mul):return sum(1<<((mul*i)%13) for i in range(13) if q>>i&1)
for mul in [1,3,9]:
    assert transform(targets[0],mul)==targets[0]
    assert {transform(t,mul) for t in targets[1:]}==set(targets[1:])
    for p,t in enumerate(targets):
        p2=targets.index(transform(t,mul))
        assert {transform(negative[r-13],mul) for r in rows_by_point[p]}=={negative[r-13] for r in rows_by_point[p2]}
report={'reviewer':'repo_audit','status':'PASS source-only second useful-pencil encoding and runner replay; new SAT control pending',
'scope':'The second witness is an actual OR output with exactly one of the12 nonzero pencil singleton supports AND false on one of that pencil’s54 encoded disjoint four-caps. Existing usefulP0 remains required. Distinct target supports force distinct gate witnesses. This is a necessary-condition cut for the restricted13-output model, not a held-gap proof.',
'checks':{'all_old_cnf_body_generation_unchanged_before_append':True,'old_variable_ids_preserved':True,'second_targets':list(range(1,13)),'rows_per_target':54,'positive_row_offset':13,'P0_stabilizer_permutes_other_targets_and_false_cap_rows':True,'ordering_preserves_useful_witnesses_by_unchanged_support_and_decreasing_values':True,'previous_forced39_SAT_control_useful_targets':useful,'runner_requires_distinct_useful_targets_and_matches_serialized_string_keys':True},
'estimated_increment_without_unexpected_simplification':{'control39_variables':2*12*39,'control39_clauses':70*12*39+1,'query38_variables':2*12*38,'query38_clauses':70*12*38+1},
'files':{n:hashlib.sha256((B/n).read_bytes()).hexdigest() for n in ['multi_output_two_useful_ordered_cnf.py','solve_multi_cnf_v4.py']},
'limit':'No new CNF generation, solver, or Lean process was run by this audit. The new forced39 control must still pass before launching the changed38 query. Delta packaging, if introduced, needs its own header/hash review.'}
(B/'two-useful-independent-audit.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
