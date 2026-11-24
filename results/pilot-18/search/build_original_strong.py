"""Reproduce the original shard-17 suffix DAG with reviewed prefix consequences.

Generate the parent using the pinned reverse-counter generator with
--distinct-prefix, then pass its prefix-distinct.cnf here. Original first-junk,
two-junk, liveness and output-last requirements remain. No tail rewrite occurs.
The sibling add_ancestor_support.py is hash-pinned before loading.
"""
import argparse
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path

PARENT_GENERATOR='b10d8832060d1c554fd3daa563b7159d515a3c55adc49718989eaa9bd0c2f24f'
PARENT_CNF='811937a8a658d01fac36418e9fb3087218820a9f9dc571ef09246f936df8168e'
SUPPORT_SOURCE='6bd7f7a2120d7d5446d9609a0551308b224d91d23463354514cefe631803e38b'

def transform(parent,output):
    if output.exists():raise ValueError('Output directory must be fresh')
    helper=Path(__file__).with_name('add_ancestor_support.py')
    assert hashlib.sha256(helper.read_bytes()).hexdigest()==SUPPORT_SOURCE
    spec=importlib.util.spec_from_file_location('support_consequence',helper)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    raw=parent.read_bytes();meta=json.loads(parent.with_suffix('.json').read_text())
    assert hashlib.sha256(raw).hexdigest()==meta['sha256']==PARENT_CNF
    assert meta['program_sha256']==PARENT_GENERATOR
    assert meta['first_junk']==17 and meta['size']==21
    assert meta['second_junk'] and meta['live'] and meta['last_output']
    assert 'tail_template' not in meta
    assert meta['prefix_distinct'] and meta['prefix_totalizer_reverse']
    lines=raw.decode('ascii').splitlines()
    assert lines[0]==f"p cnf {meta['variables']} {meta['clauses']}"
    clauses=[]
    for line in lines[1:]:
        row=list(map(int,line.split()));assert row[-1]==0
        assert all(1<=abs(v)<=meta['variables'] for v in row[:-1])
        clauses.append(row[:-1])
    assert len(clauses)==meta['clauses'] and raw.endswith(b'\n')
    assert [meta['junk'][17]] in clauses and meta['junk'][18:] in clauses
    assert [meta['output_selectors'][-1]] in clauses
    variables,extra,flags,some=module.append_gadget(meta)
    three_and=[[meta['ops'][i],meta['ops'][j]]
               for i,j in itertools.combinations(range(17,21),2)]
    extra+=three_and
    meta.update(variables=variables,clauses=meta['clauses']+len(extra),
      prefix_ancestor_support=True,ancestor_support_parent_sha256=PARENT_CNF,
      ancestor_support_postprocessor_sha256=SUPPORT_SOURCE,
      ancestor_support_added_variables=204,ancestor_support_added_clauses=3536,
      prefix_common_neighbor_flags=flags,prefix_has_common_neighbor=some,
      suffix_at_least_three_ANDs=True,suffix_three_AND_clauses=three_and,
      original_DAG=True,original_DAG_generator_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    result=f"p cnf {variables} {meta['clauses']}\n".encode('ascii')+raw.split(b'\n',1)[1]
    result+=''.join(' '.join(map(str,c))+' 0\n' for c in extra).encode('ascii')
    meta['sha256']=hashlib.sha256(result).hexdigest()
    output.mkdir(parents=True,exist_ok=False)
    (output/'original.cnf').write_bytes(result)
    (output/'original.json').write_text(json.dumps(meta,indent=2)+'\n')
    print(json.dumps({k:meta[k] for k in ['sha256','variables','clauses','original_DAG_generator_sha256']}))

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('parent',type=Path);parser.add_argument('output',type=Path)
    args=parser.parse_args();transform(args.parent,args.output)
