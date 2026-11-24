"""Add the separately reviewed one-junk consequence to fresh tail formulas.

This is specific to the fixed 11-input target and its clean lower bound 22.
It never restores the removed gate-17 unit or the two-junk restriction.
"""
from pathlib import Path
import argparse
import hashlib
import json

CASES = ('meet5','or1meet4','or2meet3','meet1or1meet3','meet1or2meet2',
         'meet2or1meet2','meet3or2')


def transform(source_dir, output_dir):
    if output_dir.exists():
        raise ValueError('Output directory must be fresh')
    prepared = []
    own_hash = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    for name in CASES:
        path = source_dir/(name+'.cnf')
        raw = path.read_bytes()
        meta = json.loads(path.with_suffix('.json').read_text())
        assert hashlib.sha256(raw).hexdigest() == meta['sha256']
        assert meta['size'] == 21 and meta['first_junk'] == 17
        assert meta['enforce_junk'] is False and meta['second_junk'] is False
        assert meta['tail_template'] == name and meta['last_output']
        assert meta['prefix_totalizer_reverse'] and meta['prefix_constant_canonical']
        assert 'suffix_some_junk' not in meta
        assert len(meta['junk']) == 21 and len(set(meta['junk'])) == 21
        clause = meta['junk'][17:]
        assert len(clause) == 4 and all(1 <= x <= meta['variables'] for x in clause)
        lines = raw.decode('ascii').splitlines()
        assert lines[0] == f"p cnf {meta['variables']} {meta['clauses']}"
        clauses = []
        for line in lines[1:]:
            row = list(map(int,line.split()))
            assert row and row[-1] == 0
            assert all(1 <= abs(x) <= meta['variables'] for x in row[:-1])
            clauses.append(row[:-1])
        assert len(clauses) == meta['clauses']
        assert [meta['junk'][17]] not in clauses
        assert meta['junk'][18:] not in clauses
        assert clause not in clauses and raw.endswith(b'\n')
        parent_hash = meta['sha256']
        meta['clauses'] += 1
        header = f"p cnf {meta['variables']} {meta['clauses']}\n".encode('ascii')
        result = header + raw.split(b'\n',1)[1] + (' '.join(map(str,clause))+' 0\n').encode('ascii')
        meta.update(sha256=hashlib.sha256(result).hexdigest(),suffix_some_junk=True,
                    suffix_some_junk_added_clauses=1,suffix_some_junk_added_variables=0,
                    suffix_some_junk_parent_sha256=parent_hash,
                    suffix_some_junk_postprocessor_sha256=own_hash)
        prepared.append((name,result,meta))
    output_dir.mkdir(parents=True,exist_ok=False)
    for name,raw,meta in prepared:
        path = output_dir/(name+'.cnf')
        path.write_bytes(raw)
        path.with_suffix('.json').write_text(json.dumps(meta,indent=2)+'\n')
        print(json.dumps({'case':name,'variables':meta['variables'],
                          'clauses':meta['clauses'],'sha256':meta['sha256']}))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source_dir',type=Path)
    parser.add_argument('output_dir',type=Path)
    args = parser.parse_args()
    transform(args.source_dir,args.output_dir)
