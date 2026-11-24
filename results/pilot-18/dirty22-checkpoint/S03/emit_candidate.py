from pathlib import Path
import argparse
import hashlib
import json
import re

ROOT = Path('/tmp/oec/pequalnp-pilot-18')
HERE = ROOT / 'orch/S03'
REPO = Path('/workspace/pequalnp-proofs')
EDGES = [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
         (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
NEGATIVES = [15,29,43,57,71,85,99,113,135,149,163,177,269,325,389,
             526,540,582,596,1066,1186,1288,1408,1546]

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def permitted(path):
    path = path.resolve()
    if not (path.is_relative_to(ROOT) or path.is_relative_to(REPO)):
        raise ValueError('Input must be inside the assigned repository or scratch root')
    return path

def main():
    parser = argparse.ArgumentParser(description='Emit a Lean 40-row certificate harness for a normalized original-model circuit.')
    parser.add_argument('input', type=Path)
    parser.add_argument('--name', required=True)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--helpers-existing', action='store_true', help='Use helpers already compiled in the named module')
    modes.add_argument('--helpers-inline', action='store_true', help='Include helper bodies for a module predating their integration')
    args = parser.parse_args()
    if not re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*', args.name) or '_root_' in args.name:
        raise ValueError('Use an alphanumeric Lean identifier beginning with a letter')
    destination = HERE / (args.name + '.lean')
    manifest = HERE / (args.name + '.generation.json')
    if destination.exists() or manifest.exists():
        raise ValueError('Use a fresh artifact name; existing generation records are preserved')
    source = permitted(args.input)
    raw = source.read_bytes()
    data = json.loads(raw)
    if data.get('inputs', 11) != 11 or data.get('gate_wire_offset', 11) != 11:
        raise ValueError('Requires original-model numbering: input wires0..10, first gate wire11; normalize virtual constants upstream')
    gates = []
    for gate in data['gates']:
        if isinstance(gate, dict):
            op, inputs = gate['op'], gate['inputs']
        else:
            op, *inputs = gate
        if op not in ('and', 'or') or not isinstance(inputs, list) or len(inputs) > 2:
            raise ValueError('Only AND/OR with zero, one or two input wires are supported')
        if any(type(i) is not int or i < 0 for i in inputs):
            raise ValueError('Wire indices must be natural numbers')
        gates.append((op, inputs))
    output = data['output']
    if type(output) is not int or output < 0:
        raise ValueError('Output must be a natural-number wire index')
    for count_key in ('size', 'gate_count'):
        if count_key in data and data[count_key] != len(gates):
            raise ValueError('Declared gate count disagrees with circuit data')

    def evaluate(mask):
        wires = [bool(mask & (1 << i)) for i in range(11)]
        for op, inputs in gates:
            values = [wires[i] if i < len(wires) else False for i in inputs]
            wires.append(all(values) if op == 'and' else any(values))
        return wires[output] if output < len(wires) else False

    expected = lambda m: any(m & (1 << u) and m & (1 << v) for u, v in EDGES)
    rows = [((1 << u) | (1 << v), True) for u,v in EDGES] + [(m,False) for m in NEGATIVES]
    failures = [{'mask': m, 'expected': want, 'actual': evaluate(m)} for m,want in rows if evaluate(m) != want]
    full_failures = [m for m in range(2048) if evaluate(m) != bool(expected(m))]
    assert bool(failures) == bool(full_failures)
    result = {'input': str(source), 'input_sha256': sha(raw), 'gate_count': len(gates),
              'output': output, 'rows_checked': 40, 'boundary_failures': failures,
              'inputs_checked': 2048, 'full_failure_masks': full_failures,
              'status': 'REJECTED_FINITE_CHECK' if failures else 'GENERATED_NOT_COMPILED',
              'proves_posted_statement': False}
    if failures:
        manifest.write_text(json.dumps(result, indent=2)+'\n')
        print(json.dumps({'status': result['status'], 'boundary_failures': len(failures), 'full_failures': len(full_failures), 'manifest': str(manifest)}))
        return 2

    scaffold_raw = (HERE / 'BoundaryFix.lean').read_bytes()
    scaffold = scaffold_raw.decode()
    module_path = REPO / 'lean/PEqualNP/Outside/L_meta_1342.lean'
    module_raw = module_path.read_bytes()
    helper_names = ['targetBoundaryCheck', 'targetBoundaryCheck_iff', 'target_edge_iff_posted',
                    'target_spec_of_boundary_check', 'target_witness_of_boundary_check']
    present = [bool(re.search(r'^(?:def|lemma) '+name+r'\b', module_raw.decode(), re.M)) for name in helper_names]
    if args.helpers_existing:
        existing = True
    elif args.helpers_inline:
        existing = False
    elif all(present):
        existing = True
    elif any(present):
        raise ValueError('Partial helper integration detected; choose a verified helper mode explicitly')
    else:
        existing = False
    if existing:
        prefix = scaffold.split('def targetBoundaryCheck', 1)[0]
    else:
        prefix = scaffold.split('set_option maxRecDepth 10000 in\nset_option maxHeartbeats 1000000 in\nlemma baseline_boundary_check',1)[0]
    assert prefix != scaffold
    n = args.name
    circuit = '\n'.join('    ⟨.'+op+', ['+', '.join(map(str, inputs))+']⟩'+(',' if i+1 < len(gates) else '') for i,(op,inputs) in enumerate(gates))
    theorem_type = scaffold.split('lemma baseline_boundary_positive_control :\n',1)[1].split(' := by',1)[0]
    theorem_type = theorem_type.replace('C.size ≤ 22', 'C.size ≤ '+str(len(gates)))
    emitted = prefix + f'''def {n} : Circuit :=
  ⟨[
{circuit}], {output}⟩

lemma {n}_monotone : PEqualNP.MetaComplexity.Monotone2 {n} := by
  simp [PEqualNP.MetaComplexity.Monotone2, {n}]

lemma {n}_size : {n}.size = {len(gates)} := rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma {n}_boundary : targetBoundaryCheck {n} = true := by
  decide

lemma {n}_certificate :
{theorem_type} := by
  exact target_witness_of_boundary_check {n} {n}_monotone {n}_boundary {len(gates)}
    (Nat.le_of_eq {n}_size)

end PEqualNP.Outside.L_meta_1342_aux
'''
    destination.write_text(emitted)
    result.update({'source': str(destination), 'source_sha256': sha(emitted.encode()),
                   'scaffold_sha256': sha(scaffold_raw), 'exact_bound': len(gates),
                   'emitter_sha256': sha(Path(__file__).read_bytes()),
                   'helper_mode': 'existing' if existing else 'inline',
                   'named_dependency_sha256': sha(module_raw),
                   'import_scope': 'Scratch harness; inline helper/candidate declarations for any final source.'})
    manifest.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({'status': result['status'], 'gate_count': len(gates), 'source_sha256': result['source_sha256'], 'source': str(destination), 'manifest': str(manifest)}))
    return 0

if __name__ == '__main__':
    raise SystemExit(main())
