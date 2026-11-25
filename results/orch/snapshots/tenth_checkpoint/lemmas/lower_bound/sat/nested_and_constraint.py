"""Weak structural nesting cut for an exact budget-realizable monotone gadget.

The caller must make every paid gate live in the output cone, and the free
features must be ORs of raw inputs. If no AND has an AND ancestor, every AND
reaches the output through ORs alone, so exactness makes all ANDs graph-sound.
Together with sound outside stars this contradicts the checked pair-clean
lower bound for the assembled size at most 63.

Copies count as ANDs here. They may satisfy this weak cut without genuine
nonlinear behavior; this weakens pruning but cannot discard an exact witness.
No such constraint belongs on the overbudget calibration circuit.
"""


def require_nested_and(cnf, selected, inputs):
    contains = [-1] * inputs
    witnesses = []
    for op, left_selectors, right_selectors in selected:
        parents = []
        for selectors in (left_selectors, right_selectors):
            assert len(selectors) == len(contains)
            value = cnf.var()
            for selector, ancestor in zip(selectors, contains):
                cnf.clause(-selector, -value, ancestor)
                cnf.clause(-selector, value, -ancestor)
            parents.append(value)
        left, right = parents
        inherited = cnf.var()
        cnf.clause(-left, inherited)
        cnf.clause(-right, inherited)
        cnf.clause(left, right, -inherited)
        nested = cnf.var()
        cnf.clause(-nested, -op)
        cnf.clause(-nested, inherited)
        cnf.clause(op, -inherited, nested)
        witnesses.append(nested)
        current = cnf.var()
        cnf.clause(op, current)
        cnf.clause(-inherited, current)
        cnf.clause(-current, -op, inherited)
        contains.append(current)
    cnf.clause(*witnesses)
    return witnesses


def has_nested_and(gates, inputs):
    contains = [False] * inputs
    found = False
    for op, left, right in gates:
        assert op in (0, 1) and 0 <= left < len(contains) and 0 <= right < len(contains)
        inherited = contains[left] or contains[right]
        found = found or (op == 0 and inherited)
        contains.append(op == 0 or inherited)
    return found
