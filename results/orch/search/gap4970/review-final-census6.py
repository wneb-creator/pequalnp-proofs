from pathlib import Path
import hashlib, importlib, json, re, sys, time

sys.dont_write_bytecode = True
root = Path('/workspace/pequalnp-proofs/results/orch/search/gap4970')
sys.path.insert(0, str(root))
model = importlib.import_module('free_or_and_sat')
started = time.monotonic()
expected_hashes = {
    'free_or_and_sat.py': 'f8b7264c258883137ed6a5e0eb488bf1a1e043c85e7270a6874adc7f29bb3b44',
    'run_free_or_census6.py': 'cdee85f61159b66614932de48fc645d46c64839805ea33d8e06cfd5d5407d411',
    'make_cases_6x6.py': 'b3fa55fccf9595d16f8f05ed16964ec6d2006927c62f8c4a6915545e597e39fd',
    'case_manifest_6x6.json': '11fd09bc5a10c5c7cebd80484c3b3f34f72e3442d1739294b83871829221e8b2',
}
for name, digest in expected_hashes.items():
    assert hashlib.sha256((root / name).read_bytes()).hexdigest() == digest
summary = json.loads((root / 'and_census6_30s/SUMMARY.json').read_text())
manifest = json.loads((root / 'case_manifest_6x6.json').read_text())
classes = {r['mask']: r for r in manifest['classes']}
eligible = {m for m, r in classes.items() if r['AND5_not_excluded_by_MIS']}
assert len(eligible) == 24
results = summary['results']
assert summary['classes_completed'] == len(results) == 24
assert {r['mask'] for r in results} == eligible
assert sum(r['reused'] for r in results) == 1
checks = {r['mask']: r for r in json.loads((root / 'and_census6_30s/artifact_validation.json').read_text())['cases']}
assert len(checks) == 23
audit = []
for row in results:
    mask = row['mask']
    graph = classes[mask]
    assert row['status'] == 'UNSAT'
    assert row['edge_count'] == len(graph['edges'])
    assert row['maximal_independent_count'] == graph['maximal_independent_count']
    if row['reused']:
        assert mask == 52237542732
        base = root / 'free_or_and_fano_minor_and5_120s'
        result = json.loads(base.with_suffix('.result.json').read_text())
        original = json.loads((root / 'fano_minus_incident_pair.json').read_text())
        boundary = json.loads((root / 'fano_minus_incident_pair_boundary.json').read_text())
        iso = json.loads((root / 'fano_minor_canonical_isomorphism.json').read_text())
        rp = iso['point_permutation_original_to_canonical']
        cp = iso['line_permutation_original_to_canonical']
        assert sorted(rp) == sorted(cp) == list(range(6))
        assert iso['side_preserving'] and iso['canonical_mask'] == mask
        assert {tuple(x) for x in result['edges']} == {tuple(x) for x in original['edges']}
        assert {(rp[a], cp[b]) for a, b in result['edges']} == {tuple(x) for x in graph['edges']}
        def permute(mask):
            return sum(1 << rp[a] for a in range(6) if mask & (1 << a)) + sum(1 << (6 + cp[b]) for b in range(6) if mask & (1 << (6 + b)))
        assert {permute(x) for x in boundary['maximal_independent_masks']} == set(graph['maximal_independent_masks'])
        assert row['isomorphism'] == {'swap_sides': False, 'rows': rp, 'columns': cp}
        stdout_name = '.stdout'
        stderr_name = '.stderr'
    else:
        base = root / 'and_census6_30s' / ('case_' + str(mask))
        result = json.loads(base.with_suffix('.result.json').read_text())
        assert result['edges'] == graph['edges']
        assert result['seconds_limit'] == 30 and result['memory_mb'] == 512
        assert row['variables'] == result['variables'] and row['clauses'] == result['clauses']
        stdout_name = '.driver.stdout'
        stderr_name = '.driver.stderr'
    assert result['p'] == result['l'] == result['cover_number'] == 6
    assert result['and_budget'] == 5 and result['pin_control'] is False
    assert result['status'] == 'UNSAT' and result['returncode'] == 20
    assert row['seconds'] == result['seconds']
    solver = base.with_suffix('.solver.stdout').read_text()
    assert re.findall(r'^s (.+)$', solver, flags=re.M) == ['UNSATISFIABLE']
    assert re.findall(r'^c exit (\d+)$', solver, flags=re.M) == ['20']
    assert base.with_suffix('.solver.stderr').read_bytes() == b''
    assert base.with_suffix(stderr_name).read_bytes() == b''
    assert json.loads(base.with_suffix(stdout_name).read_text()) == result
    cnf, selectors, outputs, tests, edges = model.make_problem(6, 6, [tuple(x) for x in result['edges']], 5, False)
    encoded = ('p cnf ' + str(cnf.n) + ' ' + str(len(cnf.rows)) + '\n' + ''.join(' '.join(map(str, clause)) + ' 0\n' for clause in cnf.rows)).encode()
    actual = base.with_suffix('.cnf').read_bytes()
    assert encoded == actual
    assert cnf.n == result['variables'] and len(cnf.rows) == result['clauses'] and len(tests) == result['test_count']
    digest = hashlib.sha256(actual).hexdigest()
    if not row['reused']:
        assert checks[mask]['cnf_sha256'] == digest
        assert checks[mask]['solver_stdout_bytes'] == len(solver.encode())
    audit.append({'mask': mask, 'reused': row['reused'], 'cnf_sha256': digest, 'cnf_bytes': len(actual), 'solver_exit20_and_UNSAT_line_verified': True, 'regenerated_CNF_exact_match': True})

unknown = root / 'free-and/fano_minor_or14_300'
unknown_result = json.loads(unknown.with_suffix('.result.json').read_text())
assert unknown_result['status'] == 'UNKNOWN' and unknown_result['returncode'] == 0
unknown_solver = unknown.with_suffix('.solver.stdout').read_text()
assert re.findall(r'^s (.+)$', unknown_solver, flags=re.M) in ([], ['UNKNOWN'])
assert re.findall(r'^c exit (\d+)$', unknown_solver, flags=re.M) == ['0']
assert unknown.with_suffix('.solver.stderr').read_bytes() == b''
report = {
    'verdict': 'PASS: all24 reported solver-UNSAT outcomes match complete preserved logs and exact frozen-encoder CNFs; no certified UNSAT or Lean target proof is claimed',
    'fresh_runs_verified': 23, 'isomorphic_reuses_verified': 1,
    'source_hashes_verified': expected_hashes,
    'cases': audit,
    'punctured_Fano_OR14_status': 'UNKNOWN',
    'limitations': ['Solver UNSAT results are not Lean or independently checked proof certificates.', 'The finite census is restricted to6x6 C4-free graphs with minimum degree at least2.', 'The named1148-line Lean file is still a partial without the target theorem.'],
    'seconds': time.monotonic() - started,
}
Path('/tmp/oec/pequalnp-pilot-94/review-final-census6.result.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({k:v for k,v in report.items() if k != 'cases'}))
