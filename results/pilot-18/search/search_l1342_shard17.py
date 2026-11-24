"""Reproducible SAT search overapproximation for L-meta-1342, shard 17.

All seventeen prefix AND gates are clean. The four-gate suffix is replaced
by one of seven read-once formula templates. Repeated leaves and constants
are allowed; suffix junk flags are deliberately unconstrained. Every shard
witness normalizes into this larger family, subject to the separately
reviewed clean-bound and liveness arguments. UNSAT for one case alone is
not exhaustion. Solver proof certificates still require checking.

This standard-library-only program generates all seven DIMACS inputs and
metadata, with source and CNF SHA256 hashes. It makes no network requests.
The optional distinct-prefix flag has a separate normalization argument.
"""

import argparse
import hashlib
import json
from pathlib import Path

EDGES = [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
         (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
N = 11



class CNF:
    def __init__(self):
        self.variables = 0
        self.clauses = []
    def var(self):
        self.variables += 1
        return self.variables
    def add(self, *xs):
        self.clauses.append(list(xs))
    def exactly_one(self, xs):
        self.add(*xs)
        prior = None
        for i, x in enumerate(xs):
            if prior is not None:
                self.add(-prior, -x)
            if i < len(xs)-1:
                current = self.var()
                self.add(-x, current)
                if prior is not None:
                    self.add(-prior, current)
                prior = current
    def equiv_or(self, y, xs):
        self.add(-y, *xs)
        for x in xs:
            self.add(-x, y)


def target(mask):
    return any(mask & (1 << u) and mask & (1 << v) for u, v in EDGES)


def conditional_mux(cnf, selectors, tables, width):
    """Under each selector, return exactly that table; exhaustive if one-hot."""
    out = [cnf.var() for _ in range(width)]
    for sel, table in zip(selectors, tables):
        for y, value in zip(out, table):
            cnf.add(-sel, -y, value)
            cnf.add(-sel, y, -value)
    return out


def binary_value(cnf, op, a, b):
    y = cnf.var()
    cnf.add(-op, -y, a)
    cnf.add(-op, -y, b)
    cnf.add(-op, y, -a, -b)
    cnf.add(op, y, -a)
    cnf.add(op, y, -b)
    cnf.add(op, -y, a, b)
    return y


def build(size=21, first_junk=17, second_junk=True, prefix_sort=False,
          last_output=False, last_op=None, live=False, productive_prefix=False):
    if not 0 <= first_junk < size:
        raise ValueError('Require 0 <= first_junk < size')
    if last_op not in (None, 'and', 'or'):
        raise ValueError('last_op must be and, or, or None')
    if live and (size != 21 or first_junk != 17 or not second_junk):
        raise ValueError('--live requires size=21, first_junk=17, and at least two junk ANDs')
    if last_op is not None and not (last_output or live):
        raise ValueError('--last-op requires --last-output or --live')
    last_output = last_output or live
    independent = [m for m in range(1 << N) if not target(m)]
    maximal = [m for m in independent if all(
        m & (1 << v) or target(m | (1 << v)) for v in range(N))]
    edge_rows = [(1 << u) | (1 << v) for u, v in EDGES]
    rows = edge_rows + maximal
    adjacency = {frozenset(e) for e in EDGES}
    forbidden = [(u, v) for u in range(N) for v in range(N)
                 if u == v or frozenset((u, v)) not in adjacency]
    cnf = CNF()
    one = cnf.var()
    cnf.add(one)
    supports = [[one if u == v else -one for v in range(N)] for u in range(N)]
    supports += [[-one] * N, [one] * N]
    edge_values = [[one if mask & (1 << v) else -one for mask in edge_rows]
                   for v in range(N)]
    edge_values += [[-one] * len(edge_rows), [one] * len(edge_rows)]
    suffix_values = []
    prefix_wires = N + 2 + first_junk
    ops, lefts, rights, junk = [], [], [], []
    prefix_operand_supports = []

    def suffix_operand(selectors):
        # Prefix singleton bits are multiplexed once for this operand.
        # They are deliberately unconstrained when a suffix wire is selected.
        prefix = cnf.var()
        cnf.equiv_or(prefix, selectors[:prefix_wires])
        bits = conditional_mux(cnf, selectors[:prefix_wires], supports, N)
        values = [cnf.var() for _ in maximal]
        for y, mask in zip(values, maximal):
            terms = [bits[v] for v in range(N) if mask & (1 << v)]
            cnf.add(-prefix, -y, *terms)
            for x in terms:
                cnf.add(-prefix, y, -x)
        for sel, table in zip(selectors[prefix_wires:], suffix_values):
            for y, value in zip(values, table):
                cnf.add(-sel, -y, value)
                cnf.add(-sel, y, -value)
        return values

    for gate in range(size):
        op = cnf.var()
        left = [cnf.var() for _ in edge_values]
        right = [cnf.var() for _ in edge_values]
        cnf.exactly_one(left)
        cnf.exactly_one(right)
        # Commutativity only: equality of the two operands remains permitted.
        for a in range(len(edge_values)):
            for b in range(a):
                cnf.add(-left[a], -right[b])
        if prefix_sort and 0 < gate < first_junk:
            for a, sel in enumerate(rights[-1]):
                for b in range(a):
                    cnf.add(-sel, -right[b])

        a_edges = conditional_mux(cnf, left, edge_values, len(edge_rows))
        b_edges = conditional_mux(cnf, right, edge_values, len(edge_rows))
        out_edges = [binary_value(cnf, op, a, b)
                     for a, b in zip(a_edges, b_edges)]
        j = cnf.var()

        if gate < first_junk:
            a_bits = conditional_mux(cnf, left, supports, N)
            b_bits = conditional_mux(cnf, right, supports, N)
            prefix_operand_supports.append((a_bits, b_bits))
            out_bits = [cnf.var() for _ in range(N)]
            for a, b, y in zip(a_bits, b_bits, out_bits):
                cnf.add(-op, -y)  # A clean AND has no singleton support.
                cnf.add(op, y, -a)
                cnf.add(op, y, -b)
                cnf.add(op, -y, a, b)
            for u, v in forbidden:
                # No singleton or independent-pair witness for a prefix AND.
                cnf.add(-op, -a_bits[u], -b_bits[v])
            supports.append(out_bits)
            cnf.add(-j)
        else:
            a_neg = suffix_operand(left)
            b_neg = suffix_operand(right)
            out_neg = [binary_value(cnf, op, a, b)
                       for a, b in zip(a_neg, b_neg)]
            has_false_positive = cnf.var()
            cnf.equiv_or(has_false_positive, out_neg)
            cnf.add(-j, op)
            cnf.add(-j, has_false_positive)
            cnf.add(j, -op, -has_false_positive)
            suffix_values.append(out_neg)

        edge_values.append(out_edges)
        ops.append(op)
        lefts.append(left)
        rights.append(right)
        junk.append(j)

    cnf.add(junk[first_junk])
    if second_junk:
        cnf.add(*junk[first_junk + 1:])
    output_selectors = [cnf.var() for _ in edge_values]
    cnf.exactly_one(output_selectors)
    for s, (selector, table) in enumerate(zip(output_selectors, edge_values)):
        for y in table:
            cnf.add(-selector, y)
        if s < prefix_wires:
            # Every vertex lies in a maximal independent set. Thus a prefix
            # output is zero on all such sets iff its singleton support is empty.
            for y in supports[s]:
                cnf.add(-selector, -y)
        else:
            for y in suffix_values[s - prefix_wires]:
                cnf.add(-selector, -y)

    # Append optional restrictions only after the original encoding, preserving
    # every existing variable number and the default DIMACS byte sequence.
    if last_output:
        cnf.add(output_selectors[-1])
    if last_op is not None:
        cnf.add(ops[-1] if last_op == 'and' else -ops[-1])
    if live:
        for gate in range(size - 1):
            wire = N + 2 + gate
            readers = [selectors[wire]
                       for later in range(gate + 1, size)
                       for selectors in (lefts[later], rights[later])]
            cnf.add(*readers)

    if productive_prefix:
        for op, (a_bits, b_bits) in zip(ops, prefix_operand_supports):
            cnf.add(-op, *a_bits)
            cnf.add(-op, *b_bits)

    data = dict(productive_prefix=productive_prefix, size=size, first_junk=first_junk, second_junk=second_junk,
                prefix_sort=prefix_sort, rows=rows, maximal_independent_sets=maximal,
                ops=ops, lefts=lefts, rights=rights, junk=junk,
                output_selectors=output_selectors, last_output=last_output,
                last_op=last_op, live=live,
                encoding='clean-prefix-singletons-and-edges',
                prefix_support_bits=N, edge_rows=len(edge_rows), negative_rows=len(maximal),
                prefix_wires=prefix_wires, program=Path(__file__).name,
                program_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                variables=cnf.variables, clauses=len(cnf.clauses))
    return cnf, data


def write(cnf, data, output):
    with output.open('w') as stream:
        stream.write(f'p cnf {cnf.variables} {len(cnf.clauses)}\n')
        for clause in cnf.clauses:
            stream.write(' '.join(map(str, clause)) + ' 0\n')
    data['sha256'] = hashlib.sha256(output.read_bytes()).hexdigest()
    output.with_suffix('.json').write_text(json.dumps(data, indent=2) + '\n')
    print(json.dumps({k: data[k] for k in ['size', 'first_junk', 'second_junk',
                                         'prefix_sort', 'last_output', 'last_op', 'live',
                                         'variables', 'clauses', 'sha256', 'program_sha256']}))


def add_prefix_lex(source, output):
    data = json.loads(source.with_suffix('.json').read_text())
    raw = source.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == data['sha256']
    assert data['first_junk'] == 17 and data['size'] == 21
    assert data['prefix_sort']
    lines = raw.decode().splitlines()
    assert lines[0] == f"p cnf {data['variables']} {data['clauses']}"
    assert len(lines) == data['clauses'] + 1
    variables = data['variables']
    extra = []
    flags = []
    for gate in range(data['first_junk'] - 1):
        equal_right, equal_left = variables + 1, variables + 2
        variables += 2
        flags.append([equal_right, equal_left])
        left, next_left = data['lefts'][gate], data['lefts'][gate + 1]
        right, next_right = data['rights'][gate], data['rights'][gate + 1]
        # Equality forces the flag. On inequality the flag can be false;
        # requiring the reverse implication is unnecessary for satisfiability.
        for a in range(len(right)):
            extra.append([-right[a], -next_right[a], equal_right])
        for a in range(len(left)):
            extra.append([-left[a], -next_left[a], equal_left])
            for b in range(a):
                extra.append([-equal_right, -left[a], -next_left[b]])
        extra.append([-equal_right, -equal_left,
                      data['ops'][gate], -data['ops'][gate + 1]])
    result = [f"p cnf {variables} {data['clauses'] + len(extra)}"]
    result.extend(lines[1:])
    result.extend(' '.join(map(str, clause)) + ' 0' for clause in extra)
    output.write_text('\n'.join(result) + '\n')
    updated = dict(data)
    updated.update(parent_sha256=data['sha256'], prefix_lex=True,
                   prefix_equality_flags=flags, variables=variables,
                   clauses=data['clauses'] + len(extra),
                   sha256=hashlib.sha256(output.read_bytes()).hexdigest())
    output.with_suffix('.json').write_text(json.dumps(updated, indent=2) + '\n')
    print(json.dumps({k: updated[k] for k in ['variables', 'clauses', 'sha256']}))


def add_distinct_prefix(source, output):
    data = json.loads(source.with_suffix('.json').read_text())
    raw = source.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == data['sha256']
    assert data['prefix_lex'] and data['first_junk'] == 17
    lines = raw.decode().splitlines()
    extra = []
    for gate, (eq_right, eq_left) in enumerate(data['prefix_equality_flags']):
        a, b = data['ops'][gate], data['ops'][gate+1]
        extra.extend([[-eq_right,-eq_left,a,b],[-eq_right,-eq_left,-a,-b]])
    assert len(extra) == 32
    output.write_text('\n'.join([f"p cnf {data['variables']} {data['clauses']+32}"] +
                      lines[1:] + [' '.join(map(str,c))+' 0' for c in extra])+'\n')
    data.update(prefix_distinct=True, parent_sha256=data['sha256'],
                clauses=data['clauses']+32,sha256=hashlib.sha256(output.read_bytes()).hexdigest())
    output.with_suffix('.json').write_text(json.dumps(data,indent=2)+'\n')


TEMPLATES = {
    'meet5': ([('and','A','B'),('and','C',0),('and','D',1),('and','E',2)],
              [('A','B','C','D','E')]),
    'or1meet4': ([('and','B','C'),('and','D',0),('and','E',1),('or','A',2)],
                 [('B','C','D','E')]),
    'or2meet3': ([('and','A','B'),('and','C','D'),('and','E',1),('or',0,2)],
                 [('A','B'),('C','D','E')]),
    'meet1or1meet3': ([('and','C','D'),('and','E',0),('or','B',1),('and','A',2)],
                     [('C','D','E')]),
    'meet1or2meet2': ([('and','B','C'),('and','D','E'),('or',0,1),('and','A',2)],
                     [('B','C'),('D','E'),('B','D')]),
    'meet2or1meet2': ([('and','D','E'),('or','C',0),('and','A','B'),('and',1,2)],
                     [('A','B'),('D','E')]),
    'meet3or2': ([('and','A','B'),('or','D','E'),('and','C',0),('and',1,2)],
                 [('A','B','C'),('D','E')]),
}


def generate(source, output_dir):
    d = json.loads(source.with_suffix('.json').read_text())
    raw = source.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == d['sha256']
    assert d['size'] == 21 and d['first_junk'] == 17 and d['second_junk']
    assert d['last_output'] and d['live'] and d['prefix_sort']
    lines = raw.decode().splitlines()
    assert lines[0] == f"p cnf {d['variables']} {d['clauses']}"
    clauses = [list(map(int,line.split()[:-1])) for line in lines[1:]]
    assert len(clauses) == d['clauses']
    for constraint in ([d['junk'][17]], d['junk'][18:]):
        assert clauses.count(constraint) == 1, constraint
        clauses.remove(constraint)
    output_dir.mkdir(parents=True, exist_ok=True)
    for name, (gates, ordered_groups) in TEMPLATES.items():
        extra, leaves = [], {}
        for k, (op,a,b) in enumerate(gates):
            gate = 17+k
            extra.append([d['ops'][gate] if op == 'and' else -d['ops'][gate]])
            for operand, selectors in zip((a,b), (d['lefts'][gate],d['rights'][gate])):
                if isinstance(operand,int):
                    assert operand < k
                    extra.append([selectors[30+operand]])
                else:
                    assert operand in 'ABCDE' and operand not in leaves
                    leaves[operand] = selectors[:30]
                    extra.extend([-v] for v in selectors[30:])
        assert set(leaves) == set('ABCDE')
        for group in ordered_groups:
            for a,b in zip(group,group[1:]):
                extra.extend([-leaves[a][i],-leaves[b][j]]
                             for i in range(30) for j in range(i))
        combined = clauses+extra
        out = output_dir/(name+'.cnf')
        out.write_text('\n'.join([f"p cnf {d['variables']} {len(combined)}"] +
                      [' '.join(map(str,c))+' 0' for c in combined])+'\n')
        meta = dict(d)
        meta.update(second_junk=False,enforce_junk=False,tail_template=name,
                    tail_gates=gates,tail_leaf_selectors=leaves,
                    tail_ordered_groups=ordered_groups,parent_sha256=d['sha256'],
                    clauses=len(combined),sha256=hashlib.sha256(out.read_bytes()).hexdigest(),
                    tail_generator_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
        out.with_suffix('.json').write_text(json.dumps(meta,indent=2)+'\n')
        print(json.dumps({k:meta[k] for k in ['tail_template','variables','clauses','sha256']}))



if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='Reproduce the L-meta-1342 shard17 fixed-tail search instances.')
    parser.add_argument('output_dir', type=Path)
    parser.add_argument('--distinct-prefix', action='store_true', help='Optional reviewed canonical description strengthening.')
    args = parser.parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    base_path = args.output_dir/'prefix-base.cnf'
    cnf, data = build(prefix_sort=True, live=True, productive_prefix=True)
    write(cnf, data, base_path)
    lex_path = args.output_dir/'prefix-lex.cnf'
    add_prefix_lex(base_path, lex_path)
    if args.distinct_prefix:
        distinct_path = args.output_dir/'prefix-distinct.cnf'
        add_distinct_prefix(lex_path, distinct_path)
        lex_path = distinct_path
    generate(lex_path, args.output_dir)
