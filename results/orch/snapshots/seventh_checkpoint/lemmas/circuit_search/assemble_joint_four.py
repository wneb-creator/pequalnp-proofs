import json
import pathlib
import sys


def compact_core(inputs, gates, output=None):
    if output is None:
        output = inputs+len(gates)-1
    mapping = {i: i for i in range(inputs)}
    cache, made = {}, []
    for i, (op, a, b) in enumerate(gates):
        assert op in (0, 1) and 0 <= a < inputs+i and 0 <= b < inputs+i
        a, b = sorted((mapping[a], mapping[b]))
        key = (op, a, b)
        if a == b:
            mapping[inputs+i] = a
        elif key in cache:
            mapping[inputs+i] = cache[key]
        else:
            mapping[inputs+i] = inputs+len(made)
            cache[key] = inputs+len(made)
            made.append(list(key))
    output = mapping[output]
    used = {output}
    for i in range(len(made)-1, -1, -1):
        if inputs+i in used:
            used.update(made[i][1:])
    ren, compact = {i: i for i in range(inputs)}, []
    for i, (op, a, b) in enumerate(made):
        if inputs+i in used:
            ren[inputs+i] = inputs+len(compact)
            compact.append([op, ren[a], ren[b]])
    return compact, ren[output], {i for i in used if i < inputs}


def assemble_joint(case, gates, output=None):
    core, core_output, used = compact_core(case['inputs'], gates, output)
    made, cache = [], {}
    def gate(op, a, b):
        if a == b:
            return a
        key = (op, *sorted((a, b)))
        if key not in cache:
            cache[key] = 26+len(made)
            made.append(list(key))
        return cache[key]
    mapping = {i: original for i, original in enumerate(case['input_original'])}
    extra = 0
    for owner in case['outside_owners']:
        lines = owner['core_lines']
        if len(lines) == 2:
            mapping[owner['whole_input']] = gate(1, *lines)
        else:
            chosen = [i for i in owner['optional_inputs'] if i in used]
            extra += max(0, len(chosen)-1)
            if not chosen:
                chosen = owner['optional_inputs'][:1]
            for feature_input in chosen:
                pair = case['features'][feature_input-case['raw_inputs']]['original_lines']
                mapping[feature_input] = gate(1, *pair)
            pair = case['features'][chosen[0]-case['raw_inputs']]['original_lines']
            third = next(l for l in lines if l not in pair)
            mapping[owner['whole_input']] = gate(1, mapping[chosen[0]], third)
    terms = []
    for owner in case['outside_owners']:
        neighborhood = mapping[owner['whole_input']]
        for line in owner['original_neighbors']:
            if line not in owner['core_lines']:
                neighborhood = gate(1, neighborhood, line)
        terms.append(gate(0, owner['outside_point'], neighborhood))
    outside = terms[0]
    for term in terms[1:]:
        outside = gate(1, outside, term)
    outside_cost = len(made)
    assert outside_cost == case['outside_base_cost']+extra
    # Append core gates without reusing outside syntactic gates so the count is exact.
    for i, (op, a, b) in enumerate(core):
        made.append([op, mapping[a], mapping[b]])
        mapping[case['inputs']+i] = 25+len(made)
    made.append([1, outside, mapping[core_output]])
    assert len(made) == outside_cost+len(core)+1
    metadata = dict(core_gates=len(core), outside_gates=outside_cost, prefix_extra_cost=extra,
                    used_optional_inputs=[i for group in case['optional_prefix_groups'] for i in group if i in used],
                    gates=len(made), within_budget=len(made) <= 63)
    return made, metadata


if __name__ == '__main__':
    packet, case_index, candidate, destination = sys.argv[1:]
    case = json.loads(pathlib.Path(packet).read_text())[int(case_index)]
    obj = json.loads(pathlib.Path(candidate).read_text())
    gates = obj['gates'] if isinstance(obj, dict) else obj
    output = obj.get('output') if isinstance(obj, dict) else None
    full, report = assemble_joint(case, gates, output)
    assert report['within_budget'], report
    pathlib.Path(destination).write_text(json.dumps(full)+'\n')
    pathlib.Path(destination).with_suffix('.assembly.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report))
