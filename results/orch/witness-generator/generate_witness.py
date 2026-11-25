import argparse
import ast
import hashlib
import json
import os
from pathlib import Path
import re
import tempfile


MODULE = 'PEqualNP.Outside.L_meta_2732'
BASE = MODULE + '_aux'
REPO = Path('/workspace/pequalnp-proofs')
SCRATCH = Path('/tmp/oec/pequalnp-pilot-70')
EDGES = [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13),
         (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12),
         (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12),
         (6, 8), (6, 9), (6, 11)]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def load_gates(path):
    gates = json.loads(path.read_text())
    require(isinstance(gates, list) and 2 <= len(gates) <= 128,
            'Expected a list containing 2 to 128 gate triples')
    for i, gate in enumerate(gates):
        require(isinstance(gate, list) and len(gate) == 3,
                'Every gate must be a three-element list')
        op, a, b = gate
        require(op in ('and', 'or'), 'Only binary AND and OR gates are supported')
        require(type(a) is int and type(b) is int and 0 <= a < 14 + i and 0 <= b < 14 + i,
                'A fanin is not an earlier nonnegative wire')
    return gates


def check_all_inputs(gates):
    for mask in range(1 << 14):
        values = [bool(mask >> i & 1) for i in range(14)]
        for op, a, b in gates:
            values.append(values[a] or values[b] if op == 'or' else values[a] and values[b])
        target = any(mask >> a & 1 and mask >> b & 1 for a, b in EDGES)
        require(values[-1] == target, 'Circuit fails the full Heawood truth table')


def normalize(gates):
    mapping = {i: i for i in range(14)}
    reduced, seen = [], {}
    for i, (op, a, b) in enumerate(gates):
        a, b = sorted((mapping[a], mapping[b]))
        if a == b:
            wire = a
        elif (op, a, b) in seen:
            wire = seen[op, a, b]
        else:
            wire = 14 + len(reduced)
            reduced.append([op, a, b])
            seen[op, a, b] = wire
        mapping[14 + i] = wire
    output = mapping[14 + len(gates) - 1]
    needed, pending = set(), [output]
    while pending:
        wire = pending.pop()
        if wire < 14 or wire in needed:
            continue
        needed.add(wire)
        pending.extend(reduced[wire - 14][1:])
    compact, remap = [], {i: i for i in range(14)}
    for i, (op, a, b) in enumerate(reduced):
        if 14 + i in needed:
            remap[14 + i] = 14 + len(compact)
            compact.append([op, *sorted((remap[a], remap[b]))])
    require(len(compact) >= 2 and remap[output] == 13 + len(compact),
            'The normalized circuit does not have two prefix gates and a final-gate output')
    require(all(a < b for _, a, b in compact[:2]), 'The prefix fanins must be distinct')
    return compact


def read_bundle(directory):
    manifest = json.loads((directory / 'manifest.json').read_text())
    require(manifest['gap'] == 'L-meta-2732' and manifest['module'] == MODULE
            and manifest['imports'] == ['PEqualNP.Defs'], 'Wrong job manifest')
    template_bytes = (directory / 'WitnessTemplate.lean.in').read_bytes()
    statement_bytes = (directory / 'posted-statement.txt').read_bytes()
    require(hashlib.sha256(template_bytes).hexdigest() == manifest['template_sha256'],
            'Template differs from the reviewed bundle')
    require(hashlib.sha256(statement_bytes).hexdigest() == manifest['statement_sha256'],
            'Posted statement differs from the recorded assignment')
    template, statement = template_bytes.decode(), statement_bytes.decode().strip()
    require(template.count('TAIL_BOUND_TOKEN') == 4, 'Unexpected helper-bound occurrences')
    require(statement.count('(24 : ℕ)') == 1, 'Unexpected posted-bound occurrences')
    return template, statement, manifest


def render(gates, template, statement, relaxed):
    limit = 25 if relaxed else 24
    require(len(gates) - 2 <= limit, 'Normalized circuit exceeds the permitted tail bound')
    if relaxed:
        require(len(gates) == 27, 'The relaxed test is reserved for the 27-gate fixture')
        statement = statement.replace('(24 : ℕ)', '(25 : ℕ)')
    nums = ast.literal_eval(re.search(r'^def nums : List ℕ := (\[.*\])$', template, re.M).group(1))
    codes = [a + 64 * b + (4096 if op == 'or' else 0) for op, a, b in gates]
    values = nums[:]
    for op, a, b in gates:
        values.append(values[a] | values[b] if op == 'or' else values[a] & values[b])
    require(values[-1] == 2097151, 'Packed boundary evaluation is incorrect')
    op1, a, b = gates[0]
    op2, c, d = gates[1]
    u, v = ('true' if op == 'or' else 'false' for op in (op1, op2))
    tail = '[' + ', '.join(map(str, codes[2:])) + ']'
    candidate = f'''def candidateTail : List ℕ := {tail}

set_option maxRecDepth 100000 in
lemma candidate_raw :
    ∃ a b c d op₁ op₂ D, prefixWitness PackedWitness.target a b c d op₁ op₂ D := by
  refine ⟨({a} : Fin 14), ({b} : Fin 14), ({c} : Fin 15), ({d} : Fin 15),
    PackedWitness.op {u}, PackedWitness.op {v}, PackedWitness.tailCircuit candidateTail, ?_⟩
  apply PackedWitness.raw ({a} : Fin 14) ({b} : Fin 14) ({c} : Fin 15) ({d} : Fin 15)
    {u} {v} candidateTail
  · decide
  · decide
  · decide
  · decide +kernel'''
    theorem = f'''theorem {MODULE} :
  {statement} := by
  exact {BASE}.canonical_prefix {BASE}.PackedWitness.target
    {BASE}.candidate_raw ({BASE}.transport_prefix {BASE}.PackedWitness.target)'''
    source = template.replace('TAIL_BOUND_TOKEN', str(limit))
    source = source.replace('CANDIDATE_TOKEN', candidate).replace('THEOREM_TOKEN', theorem)
    require(source.startswith('import PEqualNP.Defs\n'), 'Missing allowed import')
    require(not re.search(r'\bimport\b', source.split('\n', 1)[1]), 'Non-header import token')
    require(not re.search(r'_root_|"|\b(?:sorry|axiom|native_decide|initialize|macro|syntax|notation|elab|attribute)\b|^\s*(?:instance|structure|inductive)\b|@\[|#', source, re.M),
            'Generated Lean violates a plain-file rule')
    require(len(re.findall(r'^theorem ', source, re.M)) == 1, 'Expected exactly one theorem')
    require(source.count('namespace ' + BASE + '\n') == 1, 'Expected one auxiliary namespace block')
    require(len(source.encode()) <= 512 * 1024, 'Generated Lean is too large')
    return source, statement, codes, limit


def main():
    parser = argparse.ArgumentParser(description='Generate the exact L-meta-2732 proof from a fully checked binary gate JSON.')
    parser.add_argument('gates', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--relaxed-27-test', action='store_true',
                        help='Scratch-only validation: replace only the tail bound 24 by 25 and require 27 normalized gates')
    args = parser.parse_args()
    try:
        require(not args.output.is_symlink(), 'Output may not be a symlink')
        output = args.output.resolve()
        require(output.is_relative_to(REPO) or output.is_relative_to(SCRATCH), 'Output must remain in this job workspace')
        if args.relaxed_27_test:
            require(output.is_relative_to(SCRATCH) and not output.is_relative_to(REPO),
                    'Relaxed validation may only write job scratch')
        require(output.name == 'L_meta_2732.lean', 'Use the exact module filename L_meta_2732.lean')
        template, statement, manifest = read_bundle(Path(__file__).resolve().parent)
        original = load_gates(args.gates)
        check_all_inputs(original)
        gates = normalize(original)
        check_all_inputs(gates)
        source, rendered_statement, codes, limit = render(gates, template, statement, args.relaxed_27_test)
        output.parent.mkdir(parents=True, exist_ok=True)
        with tempfile.NamedTemporaryFile('w', encoding='utf-8', dir=output.parent,
                                         prefix='.witness-', suffix='.tmp', delete=False) as tmp:
            tmp.write(source)
            temporary = Path(tmp.name)
        temporary.chmod(0o644)
        os.replace(temporary, output)
        print(json.dumps({'gap': 'L-meta-2732', 'module': MODULE, 'output': str(output),
                          'scope': 'RELAXED 27-GATE TEST ONLY' if args.relaxed_27_test else 'EXACT POSTED STATEMENT',
                          'tail_bound': limit, 'original_gates': len(original), 'normalized_gates': len(gates),
                          'verified_inputs': 16384, 'packed_output': 2097151,
                          'posted_statement_sha256': manifest['statement_sha256'],
                          'rendered_statement_sha256': hashlib.sha256((rendered_statement + '\n').encode()).hexdigest(),
                          'lean_sha256': hashlib.sha256(source.encode()).hexdigest(),
                          'lean_lines': len(source.splitlines()), 'lean_checked': False}))
    except (ValueError, KeyError, TypeError, OSError) as error:
        parser.error(str(error))


if __name__ == '__main__':
    main()
