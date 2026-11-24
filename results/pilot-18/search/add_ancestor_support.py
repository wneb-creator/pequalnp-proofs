"""Expose a consequence of productive clean prefix gates and exact ancestry.

If a gate's singleton support has no common neighbor, any later gate using it
transitively must be an OR and retain that support. A productive clean AND
would need a vertex adjacent to every element of the inherited support.
Only fresh output directories are accepted; no running formula is modified.
"""
import argparse
import hashlib
import json
from pathlib import Path

EDGES = [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
         (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
CASES = ['meet5','or1meet4','or2meet3','meet1or1meet3','meet1or2meet2',
         'meet2or1meet2','meet3or2']

def append_gadget(meta):
    assert meta['productive_prefix'] and meta['prefix_ancestor_cost']
    assert meta['size']==21 and meta['first_junk']==17 and meta['prefix_wires']==30
    assert meta['edge_rows']==16
    assert meta['rows'][:16]==[(1<<u)|(1<<v) for u,v in EDGES]
    assert 'prefix_ancestor_support' not in meta
    supports=meta['prefix_support_tables'][13:30]
    ancestors=meta['prefix_ancestor_flags']
    assert len(supports)==len(ancestors)==17
    assert all(len(s)==11 for s in supports)
    assert all(len(row)==g for g,row in enumerate(ancestors))
    assert all(1<=abs(lit)<=meta['variables'] for row in supports+ancestors for lit in row)
    var=meta['variables']; clauses=[]; neighbors=[]; has_neighbor=[]
    adjacency={frozenset(e) for e in EDGES}
    for support in supports:
        flags=[]
        for v in range(11):
            var+=1; flag=var;flags.append(flag)
            forbidden=[support[u] for u in range(11) if frozenset((u,v)) not in adjacency]
            for lit in forbidden: clauses.append([-flag,-lit])
            clauses.append([flag,*forbidden])
        var+=1;some=var
        clauses.append([-some,*flags])
        for flag in flags:clauses.append([-flag,some])
        neighbors.append(flags);has_neighbor.append(some)
    for g in range(17):
        for h,ancestor in enumerate(ancestors[g]):
            guard=[-ancestor,has_neighbor[h]]
            clauses.append([*guard,-meta['ops'][g]])
            for old,new in zip(supports[h],supports[g]):
                clauses.append([*guard,-old,new])
    return var,clauses,neighbors,has_neighbor

def transform(source,output):
    if output.exists():raise ValueError('Output directory must be fresh')
    prepared=[]
    own_hash=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    for name in CASES:
        path=source/(name+'.cnf');raw=path.read_bytes()
        meta=json.loads(path.with_suffix('.json').read_text())
        assert hashlib.sha256(raw).hexdigest()==meta['sha256']
        assert raw.startswith(f"p cnf {meta['variables']} {meta['clauses']}\n".encode('ascii'))
        assert raw.endswith(b'\n') and len(raw.splitlines())==meta['clauses']+1
        var,clauses,neighbors,some=append_gadget(meta)
        old_variables=meta['variables'];old_hash=meta['sha256']
        meta.update(variables=var,clauses=meta['clauses']+len(clauses),
          prefix_ancestor_support=True,ancestor_support_parent_sha256=old_hash,
          ancestor_support_postprocessor_sha256=own_hash,
          ancestor_support_added_variables=var-old_variables,
          ancestor_support_added_clauses=len(clauses),
          prefix_common_neighbor_flags=neighbors,prefix_has_common_neighbor=some)
        result=f"p cnf {var} {meta['clauses']}\n".encode('ascii')+raw.split(b'\n',1)[1]
        result+=''.join(' '.join(map(str,c))+' 0\n' for c in clauses).encode('ascii')
        meta['sha256']=hashlib.sha256(result).hexdigest()
        prepared.append((name,result,meta))
    output.mkdir(parents=True,exist_ok=False)
    for name,raw,meta in prepared:
        path=output/(name+'.cnf');path.write_bytes(raw)
        path.with_suffix('.json').write_text(json.dumps(meta,indent=2)+'\n')
        print(json.dumps({'case':name,'sha256':meta['sha256'],'variables':meta['variables'],
                          'clauses':meta['clauses']}))

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source',type=Path);parser.add_argument('output',type=Path)
    args=parser.parse_args();transform(args.source,args.output)
