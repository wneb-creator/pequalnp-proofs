import argparse
import hashlib
import json
from pathlib import Path


def load_variants(paths):
    variants = []
    for path in paths:
        raw = path.read_bytes()
        data = json.loads(raw)
        assert isinstance(data, dict)
        real, count = data['real_inputs'], data['cut_inputs']
        assert count == real + len(data['free_or_supports'])
        assert len(data['original_variables']) == real
        assert len(data['fixed_cut_wires']) == count-real
        assert all(support and all(0 <= v < real for v in support)
                   for support in data['free_or_supports'])
        edges = [tuple(edge) for edge in data['edges']]
        def target(mask):
            return any(mask >> a & 1 and mask >> b & 1 for a,b in edges)
        positive = {(1 << a)|(1 << b) for a,b in edges}
        negative = {mask for mask in range(1 << real) if not target(mask) and
                    all(target(mask|(1 << i)) for i in range(real) if not mask >> i & 1)}
        assert set(data['positive_rows']) == positive
        assert set(data['negative_rows']) == negative
        ordered = sorted(data['rows'],key=lambda row:(not bool(row['value']),row['mask']))
        assert len(ordered) == len(positive)+len(negative)
        assert {row['mask'] for row in ordered} == positive|negative
        for row in ordered:
            values = [bool(row['mask'] >> i & 1) for i in range(real)]
            values.extend(any(values[v] for v in support) for support in data['free_or_supports'])
            assert row['cuts'] == list(map(int,values))
            assert bool(row['value']) == target(row['mask'])
        variants.append(dict(source=str(path.resolve()),sha256=hashlib.sha256(raw).hexdigest(),
                             data=data,ordered_rows=ordered))
    assert variants
    first = variants[0]
    for variant in variants[1:]:
        for key in ('real_inputs','cut_inputs','original_variables','edges'):
            assert variant['data'][key] == first['data'][key], key
        assert [(r['mask'],r['value']) for r in variant['ordered_rows']] == [
            (r['mask'],r['value']) for r in first['ordered_rows']]
        assert len(variant['data']['fixed_gates']) == len(first['data']['fixed_gates'])
    return variants


def generate(variants,gates,path,lex_order=True):
    assert gates > 0
    assert not path.exists() and not path.with_suffix('.map.json').exists()
    ninputs = variants[0]['data']['cut_inputs']
    rows = variants[0]['ordered_rows']
    count = 0
    clauses = []
    def var():
        nonlocal count
        count += 1
        return count
    def clause(*literals):
        literals = set(literals)
        assert 0 not in literals
        if any(-v in literals for v in literals):
            return
        clauses.append(tuple(sorted(literals,key=abs)))
    def exactly_one(xs):
        clause(*xs)
        if len(xs) < 2:
            return
        acc = xs[0]
        for x in xs[1:-1]:
            y = var()
            clause(-acc,y)
            clause(-x,y)
            clause(-acc,-x)
            acc = y
        clause(-acc,-xs[-1])
    truth = var()
    clause(truth)
    selectors = [var() for _ in variants]
    exactly_one(selectors)
    values = []
    varying_cells = []
    conditional_clause_count = 0
    for wire in range(ninputs):
        column = []
        for row_index in range(len(rows)):
            bits = [variant['ordered_rows'][row_index]['cuts'][wire] for variant in variants]
            if all(bit == bits[0] for bit in bits):
                literal = truth if bits[0] else -truth
            else:
                literal = var()
                for selector,bit in zip(selectors,bits):
                    clause(-selector,literal if bit else -literal)
                    conditional_clause_count += 1
                varying_cells.append(dict(wire=wire,row=row_index,variable=literal,bits=bits))
            column.append(literal)
        values.append(column)
    input_values = [list(column) for column in values]
    structure = []
    for index in range(gates):
        available = ninputs+index
        left = [var() for _ in range(available)]
        right = [var() for _ in range(available)]
        op = var()
        exactly_one(left)
        exactly_one(right)
        for a in range(available):
            for b in range(a):
                clause(-left[a],-right[b])
        lv = [var() for _ in rows]
        rv = [var() for _ in rows]
        out = [var() for _ in rows]
        for side,selected in ((left,lv),(right,rv)):
            for wire,selector in enumerate(side):
                for row_index,y in enumerate(selected):
                    source = values[wire][row_index]
                    clause(-selector,-y,source)
                    clause(-selector,y,-source)
        for a,b,y in zip(lv,rv,out):
            clause(op,-y,a)
            clause(op,-y,b)
            clause(op,y,-a,-b)
            clause(-op,y,-a)
            clause(-op,y,-b)
            clause(-op,-y,a,b)
        if lex_order and index:
            previous = structure[-1]
            dependent = right[-1]
            equal_left,equal_right = var(),var()
            for a in range(available-1):
                clause(-previous['left'][a],-left[a],equal_left)
                clause(-previous['right'][a],-right[a],equal_right)
                for b in range(a):
                    clause(dependent,-previous['left'][a],-left[b])
                    clause(dependent,-equal_left,-previous['right'][a],-right[b])
            clause(dependent,-equal_left,-equal_right,-previous['op'],op)
        values.append(out)
        structure.append(dict(left=left,right=right,op=op,out=out,lv=lv,rv=rv))
    for row,literal in zip(rows,values[-1]):
        clause(literal if row['value'] else -literal)
    with path.open('w') as output:
        output.write(f'p cnf {count} {len(clauses)}\n')
        for item in clauses:
            output.write(' '.join(map(str,item))+' 0\n')
    metadata = dict(format='joint-correlated-v1',gates=gates,ninputs=ninputs,nv=count,
                    clauses=len(clauses),truth=truth,variant_selectors=selectors,
                    variants=variants,ordered_base_masks=[r['mask'] for r in rows],
                    targets=[r['value'] for r in rows],input_values=input_values,
                    varying_cells=varying_cells,conditional_clause_count=conditional_clause_count,
                    structure=structure,lex_order=lex_order,allow_initial_repeats=True,
                    allow_trivial=True,liveness=False,canonical_prefix=False,
                    cnf_file=str(path.resolve()),cnf_sha256=hashlib.sha256(path.read_bytes()).hexdigest())
    path.with_suffix('.map.json').write_text(json.dumps(metadata)+'\n')
    return dict(file=str(path),gates=gates,variants=len(variants),rows=len(rows),
                variables=count,clauses=len(clauses),varying_cells=len(varying_cells),
                conditional_clauses=conditional_clause_count)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--variants',type=Path,nargs='+',required=True)
    parser.add_argument('--gates',type=int,required=True)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--no-lex-order',action='store_true')
    args = parser.parse_args()
    variants = load_variants(args.variants)
    print(json.dumps(generate(variants,args.gates,args.output,not args.no_lex_order)),flush=True)


if __name__ == '__main__':
    main()
