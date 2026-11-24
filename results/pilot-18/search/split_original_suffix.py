"""Partition the reviewed original shard CNF by its four suffix operations."""
import argparse
import hashlib
import itertools
import json
from pathlib import Path

PARENT_SHA='38d93ec59a86378a8434b232d19b2b53e8cbc3c715e81432ee94db59ca6ace08'
OPS=[2807,3072,3341,3614]

def main(parent, output):
    raw=parent.read_bytes()
    meta=json.loads(parent.with_suffix('.json').read_text())
    assert hashlib.sha256(raw).hexdigest()==meta['sha256']==PARENT_SHA
    assert meta['ops'][17:]==OPS
    assert meta['original_DAG'] and meta['suffix_at_least_three_ANDs']
    assert meta['first_junk']==17 and meta['second_junk']
    assert not output.exists()
    lines=raw.decode('ascii').splitlines()
    assert lines[0]==f"p cnf {meta['variables']} {meta['clauses']}"
    clauses=[list(map(int,line.split()))[:-1] for line in lines[1:]]
    assert len(clauses)==meta['clauses']
    assert [meta['junk'][17]] in clauses
    assert [-meta['junk'][17],OPS[0]] in clauses
    assert all([a,b] in clauses for a,b in itertools.combinations(OPS,2))
    patterns=[bits for bits in itertools.product([False,True],repeat=4)
              if bits[0] and sum(bits)>=3]
    assert len(patterns)==4
    output.mkdir()
    manifest={'parent_sha256':PARENT_SHA,
      'program_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'scope':'Four cases partition the parent CNF; each UNSAT still needs certificate checking.',
      'complete_partition':True,'cases':[]}
    for bits in patterns:
        name='suffix-'+''.join('A' if bit else 'O' for bit in bits)
        units=[op if bit else -op for op,bit in zip(OPS,bits)]
        result=(f"p cnf {meta['variables']} {meta['clauses']+4}\n".encode('ascii')
                +raw.split(b'\n',1)[1]
                +''.join(f'{u} 0\n' for u in units).encode('ascii'))
        m=dict(meta,clauses=meta['clauses']+4,sha256=hashlib.sha256(result).hexdigest(),
               suffix_partition_parent_sha256=PARENT_SHA,suffix_partition_units=units,
               suffix_partition_program_sha256=manifest['program_sha256'])
        (output/(name+'.cnf')).write_bytes(result)
        mp=output/(name+'.json');mp.write_text(json.dumps(m,indent=2)+'\n')
        manifest['cases'].append({'case':name,'units':units,'cnf_sha256':m['sha256'],
                                 'metadata_sha256':hashlib.sha256(mp.read_bytes()).hexdigest()})
    (output/'family.json').write_text(json.dumps(manifest,indent=2)+'\n')
    print(json.dumps(manifest,indent=2))

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('parent',type=Path);parser.add_argument('output',type=Path)
    args=parser.parse_args();main(args.parent,args.output)
