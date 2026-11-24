#!/usr/bin/env python3
"""Finite hypotheses/arithmetic for the separate mathematical DAG argument."""
from pathlib import Path
import hashlib
import itertools
import json

ROOT = Path(__file__).resolve().parent
FAMILY = ROOT.parent / 'S02/triangle-upper-factors/family.json'
FAMILY_SHA = 'be2632ca05664313c19becd3f11e7525d827ddb133400e89a27dd1762beba9ad'
EDGES = [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
         (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
edge_masks = [(1 << a) | (1 << b) for a,b in EDGES]
neighbor = [sum(1 << (b if a == v else a) for a,b in EDGES if v in (a,b))
            for v in range(11)]
independent = [x for x in range(2048) if all(x&e != e for e in edge_masks)]
assert len(independent) == 125
assert hashlib.sha256(FAMILY.read_bytes()).hexdigest() == FAMILY_SHA
family = json.loads(FAMILY.read_text())
outputs = []
truth_checks = 0
support_extension_checks = 0
for triangle in ((1,4,8),(3,6,7)):
    factors = []
    for owner in triangle:
        s = neighbor[owner]
        residual = [e for e in edge_masks if not s&e]
        covers = [c for c in range(2048) if all(c&e for e in residual)]
        tau = min(c.bit_count() for c in covers)
        cover_witness = next(c for c in covers if c.bit_count() == tau)
        cn = [v for v in range(11) if neighbor[v]&s == s]
        assert cn == [owner]
        factors.append(dict(owner=owner,support_mask=s,
                            residual_edges=residual,residual_cover=tau,
                            residual_cover_witness=cover_witness,
                            individual_bound=s.bit_count()+len(residual)+tau-1,
                            common_neighbors=cn))
        # A reached from this factor through ORs has support containing s.
        # If it can enter a productive clean AND, the other support is {owner}.
        for a in range(2048):
            if a&s != s:
                continue
            allowed = [v for v in range(11) if neighbor[v]&a == a]
            assert not allowed or allowed == [owner]
            support_extension_checks += 1
    for x in range(2048):
        target = any(x&e == e for e in edge_masks)
        values = [target or bool(x&r['support_mask']) for r in factors]
        assert all(values) == target
        truth_checks += 1
    for i, owner in enumerate(triangle):
        x = 1 << owner
        assert [bool(x&r['support_mask']) for r in factors] == [j != i for j in range(3)]
    center = factors[0]
    others = factors[1:]
    assert all(center['support_mask'] & (1 << r['owner']) for r in others)
    assert center['residual_edges']
    cases = []
    for bits in itertools.product((False,True),repeat=2):
        inside = sum(bits)
        outside = 2-inside
        cone_bound = center['individual_bound']+inside
        total_bound = cone_bound+outside
        cases.append(dict(other_factors_are_ancestors=list(bits),
                          extra_AND_deletions=inside,outside_output_gates=outside,
                          cone_lower_bound=cone_bound,total_lower_bound=total_bound))
    bound = center['individual_bound']+2
    assert bound == (18 if triangle[0] == 1 else 19)
    outputs.append(dict(triangle=list(triangle),factors=factors,
                        distinguished_owner=triangle[0],joint_prefix_lower_bound=bound,
                        ancestry_cases=cases))

case_bindings = []
for c in family['cases']:
    p = FAMILY.parent / (c['case']+'.json')
    assert hashlib.sha256(p.read_bytes()).hexdigest() == c['metadata_sha256']
    data = json.loads(p.read_text())
    result = next(r for r in outputs if r['triangle'] == c['triangle'])
    expected = {f['owner']:f for f in result['factors']}
    assert data['productive_prefix'] is True
    assert data['first_junk'] == 17
    for f in data['triangle_factor_constraints']:
        e = expected[f['vertex']]
        assert f['support_mask'] == e['support_mask']
        assert f['clean_wire_gate_lower_bound'] == e['individual_bound']
        assert f['residual_cover_size'] == e['residual_cover']
    case_bindings.append(dict(case=c['case'],metadata_sha256=c['metadata_sha256'],
                             cnf_sha256=c['cnf_sha256'],individual_feasible=c['cost_feasible'],
                             joint_bound=result['joint_prefix_lower_bound']))
result = dict(verdict='PASS_FINITE_HYPOTHESES_AND_ARITHMETIC',
              mathematical_DAG_argument='PENDING_INDEPENDENT_REVIEW',
              mathematical_argument_sha256=hashlib.sha256((ROOT/'joint-factor-cost.md').read_bytes()).hexdigest(),
              source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              family_sha256=FAMILY_SHA,families=outputs,pinned_cases=case_bindings,
              truth_checks=truth_checks,support_extension_checks=support_extension_checks,
              ancestry_arithmetic_cases=8,solver_run=False,Lean_proof=False,
              caveat='Not a machine-checked DAG lower bound or UNSAT certificate; finite values support the separately stated mathematical proof.')
(ROOT/'triangle-joint-cost-validation.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ('verdict','source_sha256','truth_checks','support_extension_checks','ancestry_arithmetic_cases')}))
