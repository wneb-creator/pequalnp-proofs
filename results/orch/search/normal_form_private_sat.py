import json
import time
from pathlib import Path

import z3
from counterexample_sparse_sat import extrema, PETER, FANO


def search(n, edges, k, timeout=600000):
    started = time.monotonic()
    tests, positive_count, independent = extrema(n, edges)
    width, mask_width = len(tests), n + k
    all_bits = (1 << width) - 1
    positive_bits = (1 << positive_count) - 1
    negative_bits = all_bits ^ positive_bits
    input_signatures = [
        sum(1 << j for j, x in enumerate(tests) if (x >> i) & 1)
        for i in range(n)
    ]
    padding_pairs = [
        (i, j) for i in range(n) for j in range(i + 1, n)
        if input_signatures[i] & ~input_signatures[j] & positive_bits
        and input_signatures[j] & ~input_signatures[i] & positive_bits
        and ~input_signatures[i] & negative_bits
        and ~input_signatures[j] & negative_bits
    ]
    if not padding_pairs:
        raise ValueError('No validated dummy-OR padding pair for this graph')

    ones = z3.BitVecVal(all_bits, width)
    positives = z3.BitVecVal(positive_bits, width)
    negatives = z3.BitVecVal(negative_bits, width)
    values = [z3.BitVecVal(v, width) for v in input_signatures]
    solver = z3.SolverFor('QF_BV')
    solver.set(timeout=timeout)
    masks = []

    def private_conjunction(mask, atoms):
        selected = [z3.Extract(i, i, mask) == 1 for i in range(len(atoms))]
        factors = [z3.If(bit, value, ones) for bit, value in zip(selected, atoms)]
        prefix = [ones]
        for factor in factors:
            prefix.append(prefix[-1] & factor)
        suffix = [ones] * (len(atoms) + 1)
        for i in range(len(atoms) - 1, -1, -1):
            suffix[i] = factors[i] & suffix[i + 1]
        for i, value in enumerate(atoms):
            without = prefix[i] & suffix[i + 1]
            solver.add(z3.Implies(selected[i], (without & ~value & negatives) != 0))
        return prefix[-1]

    for j in range(k):
        a = z3.BitVec('a' + str(j), mask_width)
        b = z3.BitVec('b' + str(j), mask_width)
        solver.add(z3.ULT(a, 1 << (n + j)), z3.ULT(b, 1 << (n + j)))
        solver.add(a != 0, b != 0, (a & b) == 0, z3.ULE(a, b))
        av = private_conjunction(a, values)
        bv = private_conjunction(b, values)
        solver.add((av & ~bv & positives) != 0, (bv & ~av & positives) != 0)
        value = z3.BitVec('v' + str(j), width)
        solver.add(value == (av | bv))
        values.append(value)
        masks.append((a, b))

    output = z3.BitVec('output', mask_width)
    solver.add(private_conjunction(output, values) == positives)
    print(json.dumps({
        'starting': True, 'n': n, 'edges': len(edges), 'max_or': k,
        'tests': width, 'maximal_independent_sets': len(independent),
        'unlimited_and': True, 'memory_limit_mb': 256, 'timeout_ms': timeout,
        'cuts': ['disjoint_nonempty_operands', 'positive_branch_incomparability',
                 'private_negative_atom_witness'],
        'validated_padding_pair': padding_pairs[0],
    }), flush=True)
    verdict = solver.check()
    result = {
        'n': n, 'edges': edges, 'max_or': k, 'tests': width,
        'unlimited_and': True, 'result': str(verdict),
        'seconds': time.monotonic() - started,
        'cuts': ['disjoint_nonempty_operands', 'positive_branch_incomparability',
                 'private_negative_atom_witness'],
        'validated_padding_pair': padding_pairs[0],
    }
    if verdict == z3.unknown:
        result['reason'] = solver.reason_unknown()
    if verdict == z3.sat:
        model = solver.model()
        result['or_masks'] = [
            [model.eval(a).as_long(), model.eval(b).as_long()] for a, b in masks
        ]
        result['output_mask'] = model.eval(output).as_long()

        def concrete(x):
            atoms = [bool((x >> i) & 1) for i in range(n)]

            def conjunction(mask):
                return all(value for i, value in enumerate(atoms) if (mask >> i) & 1)

            for a, b in result['or_masks']:
                atoms.append(conjunction(a) or conjunction(b))
            return conjunction(result['output_mask'])

        result['full_truth_table_errors'] = [
            x for x in range(1 << n)
            if concrete(x) != any(((x >> u) & 1) and ((x >> v) & 1) for u, v in edges)
        ]
        if result['full_truth_table_errors']:
            raise AssertionError('SAT witness failed independent full truth-table replay')
    return result


if __name__ == '__main__':
    z3.set_param('memory_max_size', 256)
    cases = [
        ('C5_below_bound', 5, [(i, (i + 1) % 5) for i in range(5)], 3, 60000),
        ('C5_positive_control', 5, [(i, (i + 1) % 5) for i in range(5)], 4, 60000),
        ('Petersen_below_bound', 10, PETER, 13, 600000),
        ('Fano_below_bound', 14, FANO, 19, 600000),
    ]
    destination = Path('/tmp/oec/pequalnp-pilot-55/normal-form-private-results.jsonl')
    for name, n, edges, k, timeout in cases:
        result = search(n, edges, k, timeout)
        result['name'] = name
        with destination.open('a') as stream:
            stream.write(json.dumps(result) + '\n')
        print(json.dumps(result), flush=True)
        if name == 'C5_below_bound' and result['result'] != 'unsat':
            raise AssertionError('C5 negative control did not return UNSAT')
        if name == 'C5_positive_control' and result['result'] != 'sat':
            raise AssertionError('C5 positive control did not return SAT')
