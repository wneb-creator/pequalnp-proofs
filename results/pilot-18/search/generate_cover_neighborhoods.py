"""Candidate-only 21-gate neighborhoods of checked 22-gate cover circuits.

No solver is invoked. The family is not an exhaustion of any assigned shard.
Inputs are eleven real variables plus virtual FALSE/TRUE wires 11 and 12.
"""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import itertools
import json
import random
import sys

sys.dont_write_bytecode = True
BASE_SHA = 'b10d8832060d1c554fd3daa563b7159d515a3c55adc49718989eaa9bd0c2f24f'
EDGES = [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
         (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
ALL = (1<<2048)-1
INPUT_TABLES = [sum(1<<m for m in range(2048) if m&(1<<v)) for v in range(11)]
TARGET = sum(1<<m for m in range(2048) if any(m&(1<<u) and m&(1<<v) for u,v in EDGES))


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def load_base(path):
    if digest(path.read_bytes()) != BASE_SHA:
        raise ValueError('Base generator differs from the reviewed SHA256')
    spec = importlib.util.spec_from_file_location('reviewed_neighborhood_base',path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    assert module.N==11 and module.EDGES==EDGES
    return module


def minimum_covers():
    covers=[]
    for mask in range(1<<11):
        if all(mask&(1<<u) or mask&(1<<v) for u,v in EDGES):
            assert mask.bit_count()>=7
            if mask.bit_count()==7:covers.append(mask)
    assert covers
    return covers


def circuit_tables(gates):
    tables=INPUT_TABLES+[0,ALL]
    for op,a,b in gates:
        assert op in ('and','or') and 0<=a<=b<len(tables)
        tables.append(tables[a]&tables[b] if op=='and' else tables[a]|tables[b])
    return tables


def cover_baseline(cover, rng):
    vertices=[v for v in range(11) if cover&(1<<v)]
    assert len(vertices)==7 and all(u in vertices or v in vertices for u,v in EDGES)
    owned={v:[] for v in vertices};ownership=[]
    for u,v in EDGES:
        owner=rng.choice([w for w in (u,v) if w in owned])
        owned[owner].append(v if owner==u else u)
        ownership.append([u,v,owner])
    # A minimum cover is inclusion-minimal, so every center has a forced edge
    # to its complement and remains nonempty under any ownership choices.
    assert all(owned[v] for v in vertices)
    gates=[]

    def gate(op,a,b):
        a,b=sorted((a,b));wire=13+len(gates)
        assert 0<=a<=b<wire
        gates.append([op,a,b])
        return wire

    def merge_or(wires):
        pool=list(wires);assert pool
        while len(pool)>1:
            i,j=sorted(rng.sample(range(len(pool)),2),reverse=True)
            a,b=pool.pop(i),pool.pop(j)
            pool.append(gate('or',a,b))
        return pool[0]

    rng.shuffle(vertices)
    star_outputs=[]
    for v in vertices:
        neighbors=list(owned[v]);rng.shuffle(neighbors)
        star_outputs.append(gate('and',v,merge_or(neighbors)))
    output=merge_or(star_outputs)
    tables=circuit_tables(gates)
    assert len(gates)==22 and output==34 and tables[output]==TARGET
    assert sum(op=='and' for op,_,_ in gates)==7
    assert all(not tables[13+i]&(ALL^TARGET) for i,(op,_,_) in enumerate(gates) if op=='and')
    return {'kind':'known_22_gate_baseline_not_a_21_gate_witness','cover_mask':cover,
            'cover_vertices':sorted(vertices),'star_order':vertices,'edge_owners':ownership,
            'inputs':11,'virtual_false':11,'virtual_true':12,'gate_wire_offset':13,
            'gates':gates,'output':output,'size':22,'all_2048_inputs_checked':True,
            'all_AND_gates_clean':True,'target_truth_table_sha256':digest(TARGET.to_bytes(256,'little'))}


def dimacs(cnf):
    return (f'p cnf {cnf.variables} {len(cnf.clauses)}\n'+
            ''.join(' '.join(map(str,c))+' 0\n' for c in cnf.clauses)).encode('ascii')


def neighborhood(base, baseline, prefix, size=21, pin_count=None):
    # size 22 and full pinning are reserved for no-solver validation fixtures.
    assert size in (21,22) and 8<=prefix<=14 and prefix<size
    pin_count=prefix if pin_count is None else pin_count
    assert prefix<=pin_count<=min(size,len(baseline['gates']))
    cnf,meta=base.build(size=size,first_junk=prefix,second_junk=False,
        prefix_sort=False,last_output=True,live=False,productive_prefix=False)
    original_hash=digest(dimacs(cnf));original_clauses=len(cnf.clauses)
    marker=[meta['junk'][prefix]]
    assert cnf.clauses.count(marker)==1
    removed_index=cnf.clauses.index(marker)
    cnf.clauses.pop(removed_index)
    pins=[]
    for g,(op,a,b) in enumerate(baseline['gates'][:pin_count]):
        assert 0<=a<=b<13+g
        pins += [[meta['ops'][g] if op=='and' else -meta['ops'][g]],
                 [meta['lefts'][g][a]],[meta['rights'][g][b]]]
    cnf.clauses.extend(pins)
    assert marker not in cnf.clauses
    assert meta['junk'][prefix+1:] not in cnf.clauses
    meta.update(enforce_junk=False,clean_prefix_length=prefix,
        first_junk_field_means_clean_prefix_boundary=True,
        forced_first_junk_unit_removed=marker,removed_unit_original_index=removed_index,
        base_with_forced_junk_sha256=original_hash,base_with_forced_junk_clauses=original_clauses,
        pinned_gate_count=pin_count,pinned_gates=baseline['gates'][:pin_count],pin_clauses=pins,
        variables=cnf.variables,clauses=len(cnf.clauses),inputs=11,virtual_false=11,virtual_true=12,
        candidate_only=size==21,compatibility_control_22=size==22,
        assigned_shard_exhaustion=False,
        scope=('Global at-most-21 witness neighborhood; not assigned-shard exhaustion.' if size==21
               else 'Known 22-gate compatibility control; not a 21-gate witness.'),
        base_generator=Path(base.__file__).name,base_generator_sha256=BASE_SHA,
        program=Path(__file__).name,program_sha256=digest(Path(__file__).read_bytes()))
    return cnf,meta


def generate(base_path,output_dir,samples,seed,prefix_min=8,prefix_max=14):
    if output_dir.exists():raise ValueError('Output directory must be fresh')
    if not 1<=samples<=10000:raise ValueError('samples must be in 1..10000')
    if not 8<=prefix_min<=prefix_max<=14:raise ValueError('prefix interval must lie in 8..14')
    base=load_base(base_path);rng=random.Random(seed)
    covers=minimum_covers();order=list(covers);rng.shuffle(order)
    output_dir.mkdir(parents=True,exist_ok=False)
    catalog={'minimum_cardinality':7,'cover_masks':covers,
             'covers':[[v for v in range(11) if m&(1<<v)] for m in covers]}
    (output_dir/'cover-catalog.json').write_text(json.dumps(catalog,indent=2)+'\n')
    manifest={'kind':'candidate_only_neighborhood_family','complete':False,'seed':seed,
        'samples':samples,'prefix_min':prefix_min,'prefix_max':prefix_max,
        'program_sha256':digest(Path(__file__).read_bytes()),'base_generator_sha256':BASE_SHA,
        'cover_catalog_sha256':digest((output_dir/'cover-catalog.json').read_bytes()),
        'cover_count':len(covers),'assigned_shard_exhaustion':False,'cases':[]}
    for index in range(samples):
        prefix=prefix_min+index%(prefix_max-prefix_min+1)
        baseline=cover_baseline(order[index%len(order)],rng)
        baseline.update(family_seed=seed,family_index=index)
        stem=f'c{index:04d}-k{prefix:02d}'
        bp=output_dir/(stem+'.baseline22.json')
        bp.write_text(json.dumps(baseline,indent=2)+'\n')
        cnf,meta=neighborhood(base,baseline,prefix)
        meta.update(family_seed=seed,family_index=index,baseline22_file=bp.name,
                    baseline22_sha256=digest(bp.read_bytes()),cover_mask=baseline['cover_mask'])
        raw=dimacs(cnf);meta['sha256']=digest(raw)
        path=output_dir/(stem+'.cnf');path.write_bytes(raw)
        path.with_suffix('.json').write_text(json.dumps(meta,indent=2)+'\n')
        entry={'case':stem,'prefix':prefix,'cover_mask':baseline['cover_mask'],
               'cnf_sha256':meta['sha256'],'metadata_sha256':digest(path.with_suffix('.json').read_bytes()),
               'baseline22_sha256':meta['baseline22_sha256'],'variables':cnf.variables,'clauses':len(cnf.clauses)}
        manifest['cases'].append(entry)
        (output_dir/'family.json').write_text(json.dumps(manifest,indent=2)+'\n')
        print(json.dumps(entry),flush=True)
    manifest['complete']=True
    (output_dir/'family.json').write_text(json.dumps(manifest,indent=2)+'\n')


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output_dir',type=Path)
    parser.add_argument('--base-generator',type=Path,required=True)
    parser.add_argument('--samples',type=int,default=14)
    parser.add_argument('--seed',type=int,default=1342)
    parser.add_argument('--prefix-min',type=int,default=8)
    parser.add_argument('--prefix-max',type=int,default=14)
    args=parser.parse_args()
    generate(args.base_generator,args.output_dir,args.samples,args.seed,args.prefix_min,args.prefix_max)
