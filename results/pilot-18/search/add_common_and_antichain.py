"""Fresh common-outer-AND support antichain variants of reviewed tail CNFs.

Only meet5, meet3or2, and meet2or1meet2 qualify. Full-support factors are
exempt. All parent clauses and variable identifiers are retained unchanged.
"""
from pathlib import Path
import argparse
import hashlib
import itertools
import json

GENERATOR_SHA = 'b10d8832060d1c554fd3daa563b7159d515a3c55adc49718989eaa9bd0c2f24f'
PORTS = {
    'meet5': {'A':(17,'left'),'B':(17,'right'),'C':(18,'left'),
              'D':(19,'left'),'E':(20,'left')},
    'meet3or2': {'A':(17,'left'),'B':(17,'right'),'C':(19,'left')},
    'meet2or1meet2': {'A':(19,'left'),'B':(19,'right')},
}


class ExtraCNF:
    def __init__(self, variables):
        self.variables = variables
        self.clauses = []

    def var(self):
        self.variables += 1
        return self.variables

    def add(self, *literals):
        self.clauses.append(list(literals))


def selected_support(cnf, selectors, tables):
    assert len(selectors) == len(tables) and tables
    width = len(tables[0])
    assert all(len(row) == width for row in tables)
    bits = [cnf.var() for _ in range(width)]
    for selector, row in zip(selectors, tables):
        for bit, value in zip(bits, row):
            cnf.add(-selector, -bit, value)
            cnf.add(-selector, bit, -value)
    return bits


def full_support(cnf, bits):
    full = cnf.var()
    for bit in bits:
        cnf.add(-full, bit)
    cnf.add(full, *[-bit for bit in bits])
    return full


def incomparable_pair(cnf, left, right, left_full, right_full):
    assert len(left) == len(right)
    left_only, right_only = [], []
    for a,b in zip(left,right):
        x,y = cnf.var(),cnf.var()
        cnf.add(-x,a)
        cnf.add(-x,-b)
        cnf.add(-y,b)
        cnf.add(-y,-a)
        left_only.append(x)
        right_only.append(y)
    cnf.add(left_full,right_full,*left_only)
    cnf.add(left_full,right_full,*right_only)
    return left_only,right_only


def restrictions(meta):
    name = meta['tail_template']
    ports = PORTS[name]
    tables = meta['prefix_support_tables']
    assert len(tables) == 30 and all(len(row) == 11 for row in tables)
    cnf = ExtraCNF(meta['variables'])
    leaves = {}
    for leaf,(gate,side) in ports.items():
        selectors = meta['tail_leaf_selectors'][leaf]
        assert selectors == meta[side+'s'][gate][:30] and len(selectors) == 30
        bits = selected_support(cnf,selectors,tables)
        full = full_support(cnf,bits)
        leaves[leaf] = {'gate':gate,'side':side,'support_bits':bits,'full_flag':full}
    pairs = []
    for a,b in itertools.combinations(ports,2):
        x,y = incomparable_pair(cnf,leaves[a]['support_bits'],leaves[b]['support_bits'],
                                leaves[a]['full_flag'],leaves[b]['full_flag'])
        pairs.append({'left_leaf':a,'right_leaf':b,'left_only_witnesses':x,
                      'right_only_witnesses':y})
    return cnf,leaves,pairs


def transform(source_dir, output_dir):
    if output_dir.exists():
        raise ValueError('Output directory must be fresh')
    own_hash = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    prepared = []
    for name,ports in PORTS.items():
        path = source_dir/(name+'.cnf')
        raw = path.read_bytes()
        meta = json.loads(path.with_suffix('.json').read_text())
        assert hashlib.sha256(raw).hexdigest() == meta['sha256']
        assert meta['program_sha256'] == meta['tail_generator_sha256'] == GENERATOR_SHA
        assert meta['size'] == 21 and meta['first_junk'] == 17
        assert meta['prefix_constant_canonical'] and meta['prefix_totalizer_reverse']
        assert meta['suffix_some_junk'] and meta['enforce_junk'] is False
        assert meta['second_junk'] is False and meta['tail_template'] == name
        assert 'common_and_antichain' not in meta
        lines = raw.decode('ascii').splitlines()
        assert lines[0] == f"p cnf {meta['variables']} {meta['clauses']}"
        clauses = []
        for line in lines[1:]:
            row = list(map(int,line.split()))
            assert row and row[-1] == 0
            assert all(1 <= abs(x) <= meta['variables'] for x in row[:-1])
            clauses.append(row[:-1])
        assert len(clauses) == meta['clauses'] and raw.endswith(b'\n')
        for gate,side in ports.values():
            selectors = meta[side+'s'][gate]
            assert selectors in clauses
            assert all([-s] in clauses for s in selectors[30:])
        assert all(1 <= abs(x) <= meta['variables'] for row in meta['prefix_support_tables'] for x in row)
        cnf,leaves,pairs = restrictions(meta)
        parent_hash = meta['sha256']
        old_variables,old_clauses = meta['variables'],meta['clauses']
        meta.update(variables=cnf.variables,clauses=old_clauses+len(cnf.clauses))
        header = f"p cnf {meta['variables']} {meta['clauses']}\n".encode('ascii')
        added = ''.join(' '.join(map(str,c))+' 0\n' for c in cnf.clauses).encode('ascii')
        result = header + raw.split(b'\n',1)[1] + added
        meta.update(sha256=hashlib.sha256(result).hexdigest(),common_and_antichain=True,
                    common_and_antichain_added_variables=cnf.variables-old_variables,
                    common_and_antichain_added_clauses=len(cnf.clauses),
                    common_and_antichain_leaves=leaves,common_and_antichain_pairs=pairs,
                    common_and_antichain_parent_sha256=parent_hash,
                    common_and_antichain_postprocessor_sha256=own_hash)
        prepared.append((name,result,meta))
    output_dir.mkdir(parents=True,exist_ok=False)
    for name,raw,meta in prepared:
        path = output_dir/(name+'.cnf')
        path.write_bytes(raw)
        path.with_suffix('.json').write_text(json.dumps(meta,indent=2)+'\n')
        print(json.dumps({'case':name,'variables':meta['variables'],'clauses':meta['clauses'],
                          'sha256':meta['sha256'],'added_variables':meta['common_and_antichain_added_variables'],
                          'added_clauses':meta['common_and_antichain_added_clauses']}))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source_dir',type=Path)
    parser.add_argument('output_dir',type=Path)
    args = parser.parse_args()
    transform(args.source_dir,args.output_dir)
