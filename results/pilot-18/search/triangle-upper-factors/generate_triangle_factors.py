"""Candidate-only exact upper-factor pins on the reviewed original-DAG parent.

No solver is invoked. The last three clean-prefix wires are restricted to
F_G OR OR(N(v)) for one triangle, in all six orders. This is not a WLOG claim.
"""
from pathlib import Path
import argparse
import copy
import hashlib
import itertools
import json

ROOT = Path('/tmp/oec/pequalnp-pilot-18')
PARENT = ROOT / 'orch/S01/consecutive-junk-v2/normalized.cnf'
PARENT_SHA = '3fefefe3949bc703fc2b9f023be12bc42f1afe7619e8ed5ed63be2f8e7648812'
META_SHA = 'a7425759cf64d1eef6ccd281dedf0c2e67049b88ce335a4ac166fcc0d077e19b'
EDGES = [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
         (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
TRIANGLES = [(1,4,8), (3,6,7)]
SUFFIX = [['and',27,27], ['and',30,30], ['and',28,31], ['and',29,32]]


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def require(ok, message):
    if not ok:
        raise ValueError(message)


def encode(value):
    return (json.dumps(value, indent=2) + '\n').encode()


def target(mask):
    return any(mask >> a & 1 and mask >> b & 1 for a, b in EDGES)


def neighbors(vertex):
    return sorted(b if a == vertex else a for a, b in EDGES if vertex in (a,b))


def factor(mask, vertex):
    return bool(target(mask) or any(mask >> u & 1 for u in neighbors(vertex)))


def factor_cost(vertex):
    support = neighbors(vertex)
    residual = [(a,b) for a,b in EDGES if a not in support and b not in support]
    cover = min(mask.bit_count() for mask in range(2048)
                if all(mask >> a & 1 or mask >> b & 1 for a,b in residual))
    return {'support': support, 'support_mask': sum(1 << v for v in support),
            'residual_edges': residual, 'residual_cover_size': cover,
            'clean_wire_gate_lower_bound': len(support) + len(residual) + cover - 1}


def read_parent(path):
    raw, metadata = path.read_bytes(), path.with_suffix('.json').read_bytes()
    require(sha(raw) == PARENT_SHA, 'Parent CNF SHA256 mismatch')
    require(sha(metadata) == META_SHA, 'Parent metadata SHA256 mismatch')
    meta = json.loads(metadata)
    require(meta['sha256'] == PARENT_SHA, 'Parent metadata binding mismatch')
    header, body = raw.split(b'\n', 1)
    require(header == b'p cnf 11968 114567' and raw.endswith(b'\n'), 'Unexpected parent dimensions')
    require(meta['variables'] == 11968 and meta['clauses'] == 114567, 'Wrong metadata dimensions')
    require(meta['size'] == 21 and meta['first_junk'] == 17 and meta['second_junk'], 'Wrong shard')
    require(meta['original_DAG'] and meta['live'] and meta['last_output'] and meta['consecutive_junk'], 'Wrong parent restrictions')
    require(not meta['fixed_chain'] and 'tail_template' not in meta, 'Unexpected pre-fixed suffix')
    require(meta['prefix_wires'] == 30 and meta['edge_rows'] == 16 and meta['negative_rows'] == 24, 'Wrong prefix/boundary shape')
    require(meta['rows'][:16] == [(1 << a) | (1 << b) for a,b in EDGES], 'Wrong edge-row order')
    clauses = [list(map(int, line.split())) for line in body.splitlines()]
    require(len(clauses) == meta['clauses'] and all(c and c[-1] == 0 and
            all(0 < abs(v) <= meta['variables'] for v in c[:-1]) for c in clauses), 'Malformed parent clauses')
    for wire in (27,28,29):
        require(len(meta['prefix_support_tables'][wire]) == 11 and len(meta['prefix_edge_tables'][wire]) == 16,
                'Wrong factor table width')
        require(all(type(v) is int and 1 < abs(v) <= meta['variables'] for v in
                    meta['prefix_support_tables'][wire] + meta['prefix_edge_tables'][wire]), 'Invalid factor literal')
    return body, meta


def pin_units(meta, order):
    require(tuple(sorted(order)) in TRIANGLES and len(set(order)) == 3, 'Invalid factor order')
    units = []
    for wire, vertex in zip((27,28,29), order):
        support = neighbors(vertex)
        units.extend([literal if bit in support else -literal]
                     for bit, literal in enumerate(meta['prefix_support_tables'][wire]))
        units.extend([literal] for literal in meta['prefix_edge_tables'][wire])
    for g, (op,a,b) in zip(range(17,21), SUFFIX):
        require(op == 'and' and 0 <= a <= b < 13 + g, 'Invalid fixed suffix')
        units += [[meta['ops'][g]], [meta['lefts'][g][a]], [meta['rights'][g][b]]]
    require(len(units) == 93 and all(len(c) == 1 for c in units), 'Wrong unit delta')
    require(len({abs(c[0]) for c in units}) == 93, 'Repeated or conflicting pin variable')
    return units


def generate(parent, output):
    require(not output.exists(), 'Output directory must be fresh')
    body, meta = read_parent(parent)
    costs = {v: factor_cost(v) for triangle in TRIANGLES for v in triangle}
    for vertex, row in costs.items():
        require(meta['support_cost_bounds'][row['support_mask']] == row['clean_wire_gate_lower_bound'],
                'Independent residual-cost calculation differs from parent table')
    for triangle in TRIANGLES:
        require(all(all(factor(mask,v) for v in triangle) == target(mask) for mask in range(2048)),
                'Triangle factor identity fails')
    output.mkdir(parents=True, exist_ok=False)
    program_sha = sha(Path(__file__).read_bytes())
    family = {'kind': 'candidate_only_triangle_exact_upper_factors', 'complete': False,
              'program_sha256': program_sha, 'parent_sha256': PARENT_SHA, 'parent_metadata_sha256': META_SHA,
              'assigned_shard_exhaustion': False, 'claimed_WLOG': False, 'solver_launched': False,
              'factor_definition': 'H_v = F_G OR OR(N(v))', 'factor_costs': costs,
              'fixed_factor_wires': [27,28,29], 'fixed_suffix': SUFFIX,
              'all_2048_factor_product_checks': 4096, 'cases': []}
    for triangle in TRIANGLES:
        for order in itertools.permutations(triangle):
            units = pin_units(meta, order)
            constraints = [{'vertex': v, 'wire': 27+i, 'gate_index': 14+i,
                            'available_prefix_gates': 15+i, **costs[v],
                            'cost_feasible': costs[v]['clean_wire_gate_lower_bound'] <= 15+i}
                           for i,v in enumerate(order)]
            feasible = all(row['cost_feasible'] for row in constraints)
            name = 'tri-' + '-'.join(map(str,triangle)) + '-order-' + '-'.join(map(str,order))
            suffix = ''.join(str(c[0]) + ' 0\n' for c in units).encode('ascii')
            raw = f'p cnf {meta["variables"]} {meta["clauses"]+len(units)}\n'.encode('ascii') + body + suffix
            child = copy.deepcopy(meta)
            child.update(sha256=sha(raw), clauses=meta['clauses'] + len(units), candidate_only=True,
                         assigned_shard_exhaustion=False, triangle_factor_parent_sha256=PARENT_SHA,
                         triangle_factor_parent_metadata_sha256=META_SHA,
                         triangle_factor_generator_sha256=program_sha, triangle_factor_triangle=list(triangle),
                         triangle_factor_order=list(order), triangle_factor_constraints=constraints,
                         triangle_factor_added_units=units, triangle_factor_claimed_WLOG=False,
                         triangle_factor_cost_feasible=feasible, triangle_factor_fixed_suffix=SUFFIX,
                         triangle_factor_boundary_values=[[factor(mask,v) for mask in meta['rows']] for v in order],
                         operation_case='AAAA', research_status='CANDIDATE_GENERATED_NO_SOLVER_VERDICT')
            path = output / (name + '.cnf')
            path.write_bytes(raw)
            path.with_suffix('.json').write_bytes(encode(child))
            family['cases'].append({'case': name, 'triangle': list(triangle), 'order': list(order),
                'cost_feasible': feasible, 'variables': meta['variables'], 'clauses': child['clauses'],
                'added_unit_clauses': len(units), 'cnf_sha256': sha(raw),
                'metadata_sha256': sha(path.with_suffix('.json').read_bytes())})
    family['complete'] = True
    family['cost_feasible_case_count'] = sum(c['cost_feasible'] for c in family['cases'])
    (output / 'family.json').write_bytes(encode(family))
    return family


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    parser.add_argument('--parent', type=Path, default=PARENT)
    args = parser.parse_args()
    result = generate(args.parent, args.output)
    print(json.dumps({'output': str(args.output), 'cases': len(result['cases']),
                      'cost_feasible_cases': result['cost_feasible_case_count'],
                      'generator_sha256': result['program_sha256'], 'solver_launched': False}))
