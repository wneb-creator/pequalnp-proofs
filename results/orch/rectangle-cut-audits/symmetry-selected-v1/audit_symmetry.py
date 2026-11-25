import argparse, hashlib, json
from pathlib import Path
import audit


def main():
    parser = argparse.ArgumentParser(description='Validate exact transformed-sample rectangle records and all coverage claims.')
    parser.add_argument('--selected', required=True)
    parser.add_argument('--original', required=True)
    parser.add_argument('--banks', required=True)
    parser.add_argument('--audit', required=True)
    parser.add_argument('--out', required=True)
    args = parser.parse_args()
    selected = audit.read(args.selected)
    original = audit.read(args.original)
    banks = audit.read(args.banks)
    checked = audit.read(args.audit)
    assert isinstance(selected, list) and isinstance(original, list) and isinstance(banks, list)
    assert checked['status'] == 'PASS'
    assert checked['matrices_sha256'] == audit.sha(args.selected)
    assert checked['banks_sha256'] == audit.sha(args.banks)
    assert checked['source_sha256'] == audit.sha(Path(audit.__file__))
    assert len({x['name'] for x in selected}) == len(selected)
    assert len({x['name'] for x in original}) == len(original)
    assert len({x['node'] for x in banks}) == len(banks)
    results = {(x['matrix'], x['node']): x for x in checked['results']}
    assert len(results) == len(selected) * len(banks)
    edges = {frozenset(x) for x in audit.EDGES}
    matrices = []
    covered = set()
    for rec in selected:
        p = rec['permutation']
        assert isinstance(p, list) and len(p) == 10
        assert all(audit.integer(i) for i in p) and sorted(p) == list(range(10))
        assert {frozenset((p[a], p[b])) for a, b in audit.EDGES} == edges
        permute = lambda row: sum(((row >> i) & 1) << p[i] for i in range(10))
        assert all(audit.target(row) == audit.target(permute(row)) for row in range(1024))
        source = original[rec['source_matrix_index']]
        assert source['name'] == rec['source_matrix']
        assert rec['weights'] == source['weights'] and rec['total'] == source['total']
        assert rec['positive_rows'] == list(map(permute, source['positive_rows']))
        assert rec['negative_rows'] == list(map(permute, source['negative_rows']))
        assert len(rec['covered_nodes']) == len(rec['margins'])
        assert len(set(rec['covered_nodes'])) == len(rec['covered_nodes'])
        claimed = dict(zip(rec['covered_nodes'], rec['margins']))
        exact_covered = {}
        for bank in banks:
            result = results[rec['name'], bank['node']]
            assert result['tight']
            assert result['root_count'] == len(bank['state'])
            assert result['remaining'] == bank['remaining']
            if result['excludes_tight_bank']:
                exact_covered[bank['node']] = result['margin']
        assert claimed == exact_covered, ('coverage mismatch', rec['name'])
        covered.update(exact_covered)
        matrices.append({'name': rec['name'], 'source_matrix': source['name'],
                         'permutation': p, 'exact_positive_cuts': len(exact_covered),
                         'minimum_positive_margin': min(exact_covered.values())})
    assert covered == {b['node'] for b in banks}
    output = {'status': 'PASS', 'matrices': matrices, 'covered_banks': sorted(covered),
              'all_pairs': len(results), 'unique_profiles': len(checked['profiles']),
              'positive_cuts': sum(x['excludes_tight_bank'] for x in results.values()),
              'inputs': {k: {'path': str(v), 'sha256': audit.sha(v)} for k, v in
                         [('selected', args.selected), ('original', args.original),
                          ('banks', args.banks), ('integer_audit', args.audit),
                          ('integer_auditor', audit.__file__), ('this_source', __file__)]},
              'scope': 'Exact computational verification; no claim of Lean certification or whole-case exhaustion.'}
    Path(args.out).write_text(json.dumps(output, indent=2) + '\n')
    print(json.dumps({'status': 'PASS', 'matrices': len(matrices), 'covered_banks': len(covered),
                      'all_pairs': len(results), 'profiles': len(checked['profiles']),
                      'positive_cuts': output['positive_cuts']}))


if __name__ == '__main__':
    main()
