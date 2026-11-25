import argparse
import hashlib
import json
from pathlib import Path

from joint_decode import HEAWOOD,evaluate
from joint_smoke import normalize


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--metadata',type=Path,required=True)
    parser.add_argument('--seed',type=Path,required=True)
    parser.add_argument('--branch',type=int,required=True)
    parser.add_argument('--output',type=Path,required=True)
    args = parser.parse_args()
    metadata_bytes = args.metadata.read_bytes()
    metadata = json.loads(metadata_bytes)
    assert metadata['format'] == 'joint-correlated-v1'
    assert 0 <= args.branch < len(metadata['variants'])
    variant = metadata['variants'][args.branch]
    data = variant['data']
    seed_bytes = args.seed.read_bytes()
    seed = json.loads(seed_bytes)
    gates = normalize(seed,metadata['ninputs'])
    assert len(gates) == metadata['gates']
    missing = tuple(seed['missing_original_edge'])
    missing_local = tuple(seed['missing_local_edge'])
    assert missing == tuple(data['original_variables'][v] for v in missing_local)
    phases = {}
    def prefer(literal,value):
        key = abs(literal)
        preferred = value if literal > 0 else not value
        assert 1 <= key <= metadata['nv']
        assert key not in phases or phases[key] == preferred
        phases[key] = preferred
    prefer(metadata['truth'],True)
    for index,selector in enumerate(metadata['variant_selectors']):
        prefer(selector,index == args.branch)
    boundary_errors = []
    for row_index,row in enumerate(variant['ordered_rows']):
        for wire,value in enumerate(row['cuts']):
            prefer(metadata['input_values'][wire][row_index],bool(value))
        values = evaluate(list(map(bool,row['cuts'])),gates)
        for index,(structure,(_,a,b)) in enumerate(zip(metadata['structure'],gates)):
            prefer(structure['lv'][row_index],values[a])
            prefer(structure['rv'][row_index],values[b])
            prefer(structure['out'][row_index],values[metadata['ninputs']+index])
        if values[-1] != bool(row['value']):
            boundary_errors.append(row['mask'])
    for (op,a,b),structure in zip(gates,metadata['structure']):
        for wire,variable in enumerate(structure['left']):
            prefer(variable,wire == a)
        for wire,variable in enumerate(structure['right']):
            prefer(variable,wire == b)
        prefer(structure['op'],op == 'or')
    assert boundary_errors == [(1 << missing_local[0])|(1 << missing_local[1])]
    residual_errors = 0
    for mask in range(1 << data['real_inputs']):
        initial = [bool(mask >> i & 1) for i in range(data['real_inputs'])]
        initial.extend(any(initial[v] for v in support) for support in data['free_or_supports'])
        value = evaluate(initial,gates)[-1]
        expected = any(initial[a] and initial[b] for a,b in data['edges'] if (a,b) != missing_local)
        assert value == expected
        residual_errors += value != any(initial[a] and initial[b] for a,b in data['edges'])
    full = [['or' if op else 'and',*sorted((a,b))] for op,a,b in data['fixed_gates']]
    mapping = data['original_variables']+data['fixed_cut_wires']
    for op,a,b in gates:
        full.append([op,*sorted((mapping[a],mapping[b]))])
        mapping.append(13+len(full))
    full.append(['or',*sorted((data['fixed_output'],mapping[-1]))])
    full_errors = 0
    for mask in range(1 << 14):
        initial = [bool(mask >> i & 1) for i in range(14)]
        value = evaluate(initial,full)[-1]
        expected = any(initial[a] and initial[b] for a,b in HEAWOOD if (a,b) != missing)
        assert value == expected
        full_errors += value != any(initial[a] and initial[b] for a,b in HEAWOOD)
    cnf_path = Path(metadata['cnf_file'])
    cnf_bytes = cnf_path.read_bytes()
    assert hashlib.sha256(cnf_bytes).hexdigest() == metadata['cnf_sha256']
    false_clauses = 0
    for line in cnf_bytes.decode().splitlines():
        if not line or line.startswith(('p','c')):
            continue
        literals = list(map(int,line.split()))[:-1]
        if all(abs(v) in phases for v in literals):
            false_clauses += not any(phases[abs(v)] == (v > 0) for v in literals)
    assert false_clauses == 1
    assert not args.output.exists() and not args.output.with_suffix('.json').exists()
    args.output.write_text('\n'.join(str(v if phases[v] else -v) for v in sorted(phases))+'\n')
    result = dict(branch=args.branch,variant=data.get('variant'),metadata=str(args.metadata.resolve()),
                  metadata_sha256=hashlib.sha256(metadata_bytes).hexdigest(),
                  cnf_sha256=metadata['cnf_sha256'],seed=str(args.seed.resolve()),
                  seed_sha256=hashlib.sha256(seed_bytes).hexdigest(),missing_edge=missing,
                  phase_count=len(phases),unphased_auxiliaries=metadata['nv']-len(phases),
                  normalized_gates=gates,boundary_mismatches=boundary_errors,
                  residual_target_errors=residual_errors,full_target_errors=full_errors,
                  full_gate_count=len(full),checked_residual_assignments=1 << data['real_inputs'],
                  checked_full_assignments=16384,fully_phased_false_clauses=false_clauses,
                  scope='Soft CaDiCaL phase preferences only; no assumptions or added clauses. Near-seed is not a satisfying witness.')
    args.output.with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k != 'normalized_gates'}),flush=True)


if __name__ == '__main__':
    main()
