import argparse
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
SCRATCH = Path('/tmp/oec/pequalnp-pilot-81').resolve()
RESULTS = Path('/workspace/pequalnp-proofs/results').resolve()
PREFIX_HASH = '9c9f942118318eeadd102d8dca458a9cff955af5b6890581157ef250382b7d7a'
STATEMENT_HASH = '946228bccd22fc545145b539b88eaed82998ed5d5a7285e77fb8b30e324d475e'
POINTS = [3, 4, 5, 6]
LOCAL_EDGES = [(i, 4 + t) for i, p in enumerate(POINTS)
               for t in range(7) if (p + t) % 7 in (0, 1, 3)]
POSTED_EDGES = [(p, 7 + t) for p in range(7) for t in range(7)
                if (p - t) % 7 in (0, 1, 3)]


def checked_gates(gates, inputs):
    assert isinstance(gates, list) and gates
    for j, gate in enumerate(gates):
        assert isinstance(gate, list) and len(gate) == 3
        op, a, b = gate
        assert op in ('and', 'or')
        assert type(a) is int and type(b) is int
        assert a != b and 0 <= a < inputs + j and 0 <= b < inputs + j


def values(gates, inputs, mask):
    v = [bool(mask & (1 << i)) for i in range(inputs)]
    for op, a, b in gates:
        v.append(v[a] and v[b] if op == 'and' else v[a] or v[b])
    return v


def trace(gates, inputs, base, seed):
    v = values(gates, inputs, 1 << base)
    d = [i == seed for i in range(inputs)]
    for op, a, b in gates:
        d.append((v[a] and d[b]) or (d[a] and v[b])
                 if op == 'and' else d[a] or d[b])
    return d


def check_truth(gates, inputs, edges):
    for mask in range(1 << inputs):
        expected = any(mask & (1 << a) and mask & (1 << b) for a, b in edges)
        assert values(gates, inputs, mask)[-1] == expected, ('truth', mask)


def splice(local, edge):
    checked_gates(local, 11)
    assert edge in LOCAL_EDGES
    check_truth(local, 11, LOCAL_EDGES)
    assert not trace(local, 11, edge[0], edge[1])[-1]
    assert not trace(local, 11, edge[1], edge[0])[-1]
    mapping = POINTS + [7 + (-t) % 7 for t in range(7)]
    full = []
    for op, a, b in local:
        full.append([op, mapping[a], mapping[b]])
        mapping.append(13 + len(full))
    outputs = [13 + len(full)]
    for p in range(3):
        neighbors = [7 + (p - delta) % 7 for delta in (0, 1, 3)]
        full.append(['or', neighbors[0], neighbors[1]])
        full.append(['or', 13 + len(full), neighbors[2]])
        full.append(['and', p, 13 + len(full)])
        outputs.append(13 + len(full))
    out = outputs[0]
    for other in outputs[1:]:
        full.append(['or', out, other])
        out = 13 + len(full)
    assert len(full) == len(local) + 12
    return full, (mapping[edge[0]], mapping[edge[1]])


def lean_bools(xs):
    return '[' + ', '.join('true' if x else 'false' for x in xs) + ']'


def generate(gates, edge, control):
    prefix_bytes = (HERE / 'constructive-witness-prefix.txt').read_bytes()
    statement_bytes = (HERE / 'constructive-witness-statement.txt').read_bytes()
    assert hashlib.sha256(prefix_bytes).hexdigest() == PREFIX_HASH
    assert hashlib.sha256(statement_bytes).hexdigest() == STATEMENT_HASH
    prefix = prefix_bytes.decode()
    statement = statement_bytes.decode().strip()
    namespace = 'PEqualNP.Outside.L_meta_1479'
    if control:
        namespace = 'PEqualNP.Outside.Pilot81WitnessControl'
        prefix = prefix.replace('PEqualNP.Outside.L_meta_1479', namespace)
        assert statement.count('C.size ≤ 27') == 1
        statement = statement.replace('C.size ≤ 27', 'C.size ≤ 28')
    p, line_wire = edge
    line = line_wire - 7
    forward = trace(gates, 14, p, line_wire)
    reverse = trace(gates, 14, line_wire, p)
    literal = ',\n    '.join('⟨.' + op + ', [' + str(a) + ', ' + str(b) + ']⟩'
                            for op, a, b in gates)
    body = f'''def witnessCircuit : Circuit :=
  ⟨[{literal}], {13 + len(gates)}⟩

def witnessForward : List Bool := {lean_bools(forward)}
def witnessReverse : List Bool := {lean_bools(reverse)}

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma witness_normal : BinaryAO 14 witnessCircuit := by
  apply binaryAO_of_check
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma witness_correct : ∀ x : Fin 14 → Bool,
    witnessCircuit.eval (List.ofFn x) = true ↔ boundaryFanoHit x := by
  apply boundary_correct_of_checks witness_normal <;> decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma witness_forward : DerivativeTrace 14 witnessCircuit
    (fun i => decide (i = Fin.castAdd 7 ({p} : Fin 7)))
    (fun i => decide (i = Fin.natAdd 7 ({line} : Fin 7)))
    (fun i => witnessForward.getD i false) := by
  apply derivativeTrace_of_check witnessForward <;> decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma witness_reverse : DerivativeTrace 14 witnessCircuit
    (fun i => decide (i = Fin.natAdd 7 ({line} : Fin 7)))
    (fun i => decide (i = Fin.castAdd 7 ({p} : Fin 7)))
    (fun i => witnessReverse.getD i false) := by
  apply derivativeTrace_of_check witnessReverse <;> decide +kernel

end {namespace}

open {namespace}

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem {namespace} : {statement} := by
  refine ⟨witnessCircuit, by decide, witness_normal, witness_correct,
    {p}, {line}, by decide, ?_, ?_⟩
  · refine ⟨(fun i => witnessForward.getD i false), ?_, witness_forward.2, by decide⟩
    intro m
    exact ⟨(witness_forward.1 (Fin.castAdd 7 m)).trans (by fin_cases m <;> decide),
      (witness_forward.1 (Fin.natAdd 7 m)).trans (by fin_cases m <;> decide)⟩
  · refine ⟨(fun i => witnessReverse.getD i false), ?_, witness_reverse.2, by decide⟩
    intro m
    exact ⟨(witness_reverse.1 (Fin.castAdd 7 m)).trans (by fin_cases m <;> decide),
      (witness_reverse.1 (Fin.natAdd 7 m)).trans (by fin_cases m <;> decide)⟩
'''
    source = prefix + body
    for forbidden in ('_root_', '"', 'sorry', 'native_decide', 'axiom '):
        assert forbidden not in source
    assert len(source.encode()) < 512 * 1024
    return source, forward, reverse


def main():
    parser = argparse.ArgumentParser(description='Validate and emit the exact L-meta-1479 witness proof into scratch/results.')
    parser.add_argument('--input', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--control-28', action='store_true')
    parser.add_argument('--control-index', type=int)
    args = parser.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(SCRATCH) or output.is_relative_to(RESULTS)
    assert output.suffix == '.lean' and not output.exists()
    receipt_path = output.with_suffix('.delivery.json')
    assert not receipt_path.exists()
    data = json.loads(args.input.read_text())
    if args.control_index is not None:
        assert args.control_28
        data = data['controls'][args.control_index]
        flag = next(f for f in data['flags'] if f['derivatives'] == [False, False])
        data['edge'] = [flag['point_local'], flag['line_local']]
    local_rows = 0
    if 'target_edge' in data:
        assert data.get('n_inputs', 14) == 14
        gates = data['gates']
        assert data['output'] == 13 + len(gates)
        edge = (data['target_edge'][0], 7 + data['target_edge'][1])
    else:
        if 'original' in data:
            assert data['original'] == POINTS + list(range(7, 14))
        assert len(data['gates']) == (16 if args.control_28 else 15)
        gates, edge = splice(data['gates'], tuple(data['edge']))
        local_rows = 2048
    checked_gates(gates, 14)
    assert len(gates) == (28 if args.control_28 else 27)
    assert edge in POSTED_EDGES
    check_truth(gates, 14, POSTED_EDGES)
    flags = [{'point': a, 'line': b - 7,
              'derivatives': [trace(gates, 14, a, b)[-1], trace(gates, 14, b, a)[-1]]}
             for a, b in POSTED_EDGES]
    assert len(flags) == 21
    assert not trace(gates, 14, *edge)[-1] and not trace(gates, 14, *reversed(edge))[-1]
    source, forward, reverse = generate(gates, edge, args.control_28)
    output.write_text(source)
    receipt = dict(scope='28-gate control only' if args.control_28 else '27-gate exact posted witness; Lean build pending',
                   input=str(args.input.resolve()), output=str(output),
                   source_sha256=hashlib.sha256(source.encode()).hexdigest(),
                   source_lines=len(source.splitlines()), size=len(gates), output_wire=13 + len(gates),
                   marked_edge=[edge[0], edge[1] - 7], local_truth_rows=local_rows,
                   full_truth_rows=16384, all_edge_derivatives=flags,
                   forward_trace=forward, reverse_trace=reverse,
                   helper_sha256=PREFIX_HASH, statement_sha256=STATEMENT_HASH)
    receipt_path.write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({k: receipt[k] for k in ('scope', 'output', 'source_sha256', 'source_lines', 'size', 'marked_edge')}))


if __name__ == '__main__':
    main()
