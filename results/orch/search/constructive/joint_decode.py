import argparse
import hashlib
import json
from pathlib import Path

HEAWOOD = [(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),
           (3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),
           (6,8),(6,9),(6,11)]


def evaluate(initial,gates):
    values = list(initial)
    for op,a,b in gates:
        assert op in ('and','or') and 0 <= a < len(values) and 0 <= b < len(values)
        values.append((values[a] or values[b]) if op == 'or' else (values[a] and values[b]))
    return values


def decode(metadata_path,log_path,output_path):
    metadata = json.loads(metadata_path.read_text())
    assert metadata['format'] == 'joint-correlated-v1'
    lines = log_path.read_text().splitlines()
    assert 's SATISFIABLE' in lines
    assignment = {}
    for line in lines:
        if not line.startswith('v '):
            continue
        for word in line.split()[1:]:
            literal = int(word)
            if literal:
                key,value = abs(literal),literal > 0
                assert key not in assignment or assignment[key] == value
                assignment[key] = value
    assert set(assignment) == set(range(1,metadata['nv']+1)), 'Incomplete model'
    def truth(literal):
        return assignment[abs(literal)] == (literal > 0)
    cnf_path = Path(metadata['cnf_file'])
    cnf_bytes = cnf_path.read_bytes()
    assert hashlib.sha256(cnf_bytes).hexdigest() == metadata['cnf_sha256']
    clause_count = 0
    for line in cnf_bytes.decode().splitlines():
        if not line or line.startswith('c'):
            continue
        if line.startswith('p '):
            assert line.split() == ['p','cnf',str(metadata['nv']),str(metadata['clauses'])]
            continue
        literals = list(map(int,line.split()))
        assert literals[-1] == 0 and any(truth(v) for v in literals[:-1])
        clause_count += 1
    assert clause_count == metadata['clauses']
    selected = [i for i,var in enumerate(metadata['variant_selectors']) if assignment[var]]
    assert len(selected) == 1
    selected_index = selected[0]
    variant = metadata['variants'][selected_index]
    data = variant['data']
    cone = []
    for gate in metadata['structure']:
        left = [i for i,var in enumerate(gate['left']) if assignment[var]]
        right = [i for i,var in enumerate(gate['right']) if assignment[var]]
        assert len(left) == len(right) == 1
        cone.append(['or' if assignment[gate['op']] else 'and',left[0],right[0]])
    for row_index,row in enumerate(variant['ordered_rows']):
        initial = list(map(bool,row['cuts']))
        for wire,value in enumerate(initial):
            assert truth(metadata['input_values'][wire][row_index]) == value
        values = evaluate(initial,cone)
        assert values[-1] == bool(row['value'])
        for index,(gate,(_,a,b)) in enumerate(zip(metadata['structure'],cone)):
            assert truth(gate['lv'][row_index]) == values[a]
            assert truth(gate['rv'][row_index]) == values[b]
            assert truth(gate['out'][row_index]) == values[data['cut_inputs']+index]
    for mask in range(1 << data['real_inputs']):
        initial = [bool(mask >> i & 1) for i in range(data['real_inputs'])]
        initial.extend(any(initial[v] for v in support) for support in data['free_or_supports'])
        target = any(mask >> a & 1 and mask >> b & 1 for a,b in data['edges'])
        assert evaluate(initial,cone)[-1] == target, ('Residual mismatch',mask)
    full = [['or' if op else 'and',*sorted((a,b))] for op,a,b in data['fixed_gates']]
    prefix_length = len(full)
    mapping = data['original_variables']+data['fixed_cut_wires']
    assert len(mapping) == data['cut_inputs']
    for op,a,b in cone:
        full.append([op,*sorted((mapping[a],mapping[b]))])
        mapping.append(13+len(full))
    full.append(['or',*sorted((data['fixed_output'],mapping[-1]))])
    assert len(full) == prefix_length+metadata['gates']+1
    for mask in range(1 << 14):
        initial = [bool(mask >> i & 1) for i in range(14)]
        prefix_values = evaluate(initial,full[:prefix_length])
        for wire,support in zip(data['fixed_cut_wires'],data['free_or_supports']):
            expected_cut = any(initial[data['original_variables'][v]] for v in support)
            assert prefix_values[wire] == expected_cut, ('Cut embedding mismatch',mask,wire)
        target = any(initial[a] and initial[b] for a,b in HEAWOOD)
        assert evaluate(initial,full)[-1] == target, ('Full mismatch',mask)
    result = dict(selected_branch_index=selected_index,selected_variant=data.get('variant'),
                  selected_source=variant['source'],selected_source_sha256=variant['sha256'],
                  cone_gates=cone,full_gates=full,full_gate_count=len(full),
                  packed=[a+64*b+(4096 if op == 'or' else 0) for op,a,b in full],
                  checked_cnf_clauses=clause_count,
                  checked_residual_assignments=1 << data['real_inputs'],checked_full_assignments=16384)
    assert not output_path.exists()
    output_path.write_text(json.dumps(result,indent=2)+'\n')
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--metadata',type=Path,required=True)
    parser.add_argument('--log',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    args = parser.parse_args()
    result = decode(args.metadata,args.log,args.output)
    print(f'VERIFIED branch {result["selected_branch_index"]}, all {result["checked_residual_assignments"]} residual inputs and all 16384 full inputs')
    print(json.dumps(result['full_gates'],indent=2))
    print('packed:',result['packed'])


if __name__ == '__main__':
    main()
