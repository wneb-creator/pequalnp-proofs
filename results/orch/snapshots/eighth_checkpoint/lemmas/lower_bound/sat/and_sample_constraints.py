from global_synthesis import evaluate_wires


def evaluate_sample(cnf, selected, ninputs, mask, phase_seed=None):
    wires = [1 if mask >> i & 1 else -1 for i in range(ninputs)]
    hints = evaluate_wires(phase_seed, mask, ninputs) if phase_seed is not None else None
    for i, (op, left, right) in enumerate(selected):
        a = cnf.var(None if hints is None else hints[phase_seed[i][1]])
        b = cnf.var(None if hints is None else hints[phase_seed[i][2]])
        for selectors, evaluated in ((left, a), (right, b)):
            for j, selector in enumerate(selectors):
                cnf.clause(-selector, -evaluated, wires[j])
                cnf.clause(-selector, evaluated, -wires[j])
        output = cnf.ao_gate(op, a, b, None if hints is None else hints[ninputs + i])
        wires.append(output)
    return wires


def force_and_values(cnf, selected, ninputs, mask, value, guard=-1, phase_seed=None):
    """Evaluate one input and constrain every AND result, unless guard is true."""
    wires = evaluate_sample(cnf, selected, ninputs, mask, phase_seed)
    for i, (op, _, _) in enumerate(selected):
        output = wires[ninputs + i]
        cnf.clause(guard, op, output if value else -output)
    return wires


def and_true_events(cnf, selected, ninputs, mask, phase_seed=None):
    wires = evaluate_sample(cnf, selected, ninputs, mask, phase_seed)
    events = []
    for i, (op, _, _) in enumerate(selected):
        event = cnf.var()
        output = wires[ninputs + i]
        cnf.clause(-event, -op)
        cnf.clause(-event, output)
        cnf.clause(op, -output, event)
        events.append(event)
    return events
