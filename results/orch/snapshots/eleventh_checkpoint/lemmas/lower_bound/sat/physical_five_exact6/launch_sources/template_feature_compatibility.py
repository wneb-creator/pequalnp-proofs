def template_feature_constraints(cnf, selected, raw_inputs, ninputs, groups):
    """Require the referenced features to fit one allowed OR tree per outside row."""
    owned = [wire for group in groups for wire in group['inputs']]
    assert sorted(owned) == list(range(raw_inputs, ninputs))
    used = {}
    for wire in owned:
        occurrences = [side[wire] for _, left, right in selected
                       for side in (left, right)]
        literal = cnf.var()
        used[wire] = literal
        cnf.clause(-literal, *occurrences)
        for occurrence in occurrences:
            cnf.clause(-occurrence, literal)
    chosen = []
    for group in groups:
        templates = group['templates']
        assert templates
        assert all(set(template) <= set(group['inputs']) for template in templates)
        choices = [cnf.var() for _ in templates]
        if len(choices) == 1:
            cnf.clause(choices[0])
        else:
            cnf.exactly_one(choices)
        chosen.append(choices)
        for wire in group['inputs']:
            permitted = [choice for template, choice in zip(templates, choices)
                         if wire in template]
            cnf.clause(-used[wire], *permitted)
    allowance = len(selected) - raw_inputs + 1
    assert allowance >= 0
    levels = cnf.count_row(list(used.values()), allowance)
    cnf.clause(-levels[allowance + 1])
    return dict(used=used, chosen=chosen)


def choose_compatible_templates(gates, groups):
    referenced = {wire for _, left, right in gates for wire in (left, right)}
    choices = []
    for group in groups:
        required = referenced.intersection(group['inputs'])
        compatible = [i for i, template in enumerate(group['templates'])
                      if required <= set(template)]
        assert compatible
        choices.append(compatible[0])
    return choices
