from and_sample_constraints import evaluate_sample


def add_paid_and_dominance(cnf, selected, case, max_ands=5, phase_seed=None):
    """Requires a complete monotone basis, pairwise-positive negative unions,
    and join-preserving derived inputs; exclude removable ANDs at the minimum count.
    """
    negatives = sum(not label for _, label in case['tests'])
    assert max_ands >= 1 and negatives > (1 << (max_ands - 1))
    levels = cnf.count_row([-op for op, _, _ in selected], max_ands)
    guard = levels[max_ands + 1]
    n = case['inputs']
    hint = phase_seed if phase_seed is not None and len(phase_seed) == len(selected) else None
    values = [evaluate_sample(cnf, selected, n, mask, hint)[n:]
              for mask, _ in case['tests']]
    for i, (op, _, _) in enumerate(selected):
        for earlier in range(i):
            witnesses = []
            for row, (_, label) in zip(values, case['tests']):
                a, b = (row[i], -row[earlier]) if label else (row[earlier], -row[i])
                witness = cnf.var()
                cnf.clause(-witness, a)
                cnf.clause(-witness, b)
                witnesses.append(witness)
            cnf.clause(guard, op, *witnesses)
