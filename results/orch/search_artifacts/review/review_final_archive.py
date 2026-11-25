"""Read-only audit of stopped2590 small archive and existing controls; runs no solver."""
import hashlib
import itertools
import json
from pathlib import Path

ROOT=Path('/tmp/oec/pequalnp-pilot-99/gap2590/counterexample')
EDGES={(0,1),(1,2),(2,3),(3,4),(0,4),(0,5),(1,6),(2,7),(3,8),(4,9),
       (5,7),(7,9),(6,9),(6,8),(5,8)}


def cnf(name):
    result=[]
    with (ROOT/name).open() as stream:
        for line in stream:
            if line.startswith('p '):
                _,kind,n,m=line.split();assert kind=='cnf';n,m=int(n),int(m)
            elif line.strip() and not line.startswith('c'):
                row=list(map(int,line.split()));assert row[-1]==0 and 0 not in row[:-1]
                assert all(abs(x)<=n for x in row[:-1]);result.append(tuple(row[:-1]))
    assert len(result)==m
    return result


def main():
    manifest=json.loads((ROOT/'final-manifest.json').read_text())
    assert isinstance(manifest,dict) and isinstance(manifest['files'],list)
    paths=set()
    for item in manifest['files']:
        assert set(item)=={'path','size','sha256'}
        path=Path(item['path']);assert path.parent==ROOT and path not in paths
        assert path.suffix!='.lrat';paths.add(path)
        data=path.read_bytes()
        assert len(data)==item['size']
        assert hashlib.sha256(data).hexdigest()==item['sha256'],path.name
    assert len(paths)==33
    print('PASS all33 final-manifest hashes and sizes;',sum(x['size'] for x in manifest['files']),'bytes')
    log=(ROOT/'petersen19-enc2.stdout').read_text().splitlines()
    assert 'c caught signal 2 (SIGINT)' in log
    assert 'c UNKNOWN' in log
    assert 'c raising signal 2 (SIGINT)' in log
    assert not any(line in ('s SATISFIABLE','s UNSATISFIABLE') for line in log)
    print('PASS baseline stopped by SIGINT and reports UNKNOWN; no SAT/UNSAT result')
    inspection=json.loads((ROOT/'prefix-format-inspection.json').read_text())
    assert inspection['events']==10000 and inspection['additions']==7397
    assert inspection['negative_hint_records']==0
    print('NOTE prefix inspection is a format sample only; unfinished LRAT file was not opened')
    model=json.loads((ROOT/'code_model.json').read_text())
    codes={int(v):set(c) for v,c in model['codes'].items()}
    assert set(codes)==set(range(10))
    assert all(1<=len(c)<=2 and all((p^1) not in c for p in c) for c in codes.values())
    assert all(any((p^1) in codes[b] for p in codes[a]) for a,b in EDGES)
    assert all(not codes[x].issubset(codes[a]|codes[b]) for x in range(10)
               for a in range(10) for b in range(a,10)
               if x!=a and x!=b and (a,b) not in EDGES)
    covered={(a,b) for a in range(10) for b in range(a+1,10)
             if any((p^1) in codes[b] for p in codes[a])}
    active=set().union(*codes.values())
    assert len(active)==12 and sum(map(len,codes.values()))==20
    assert len({p//2 for p in active})==8
    assert sorted(covered-EDGES)==list(map(tuple,model['false_positive_pairs']))
    assert len(covered-EDGES)==12
    assert 'gates' not in model and 'output' not in model
    print('PASS static code model constraints:12 slots/20 memberships/8 pairs, but12 false-positive pairs; not a circuit')
    for prefix in ['skeleton6-control','skeleton6-control-disjoint']:
        circuit=json.loads((ROOT/(prefix+'.circuit.json')).read_text())
        gates=circuit['gates'];outputs=circuit['output'];assert len(gates)==6
        for j,sides in enumerate(gates):
            assert len(sides)==2 and all(0<=i<10+j for side in sides for i in side)
        assert all(0<=j<len(gates) for j in outputs)
        for row in range(1024):
            values=[bool(row&(1<<i)) for i in range(10)]
            for left,right in gates:
                values.append(any(values[i] for i in left) and any(values[i] for i in right))
                if row.bit_count()==1:assert not values[-1]
            actual=any(values[10+j] for j in outputs)
            expected=any((row&(1<<a)) and (row&(1<<b)) for a,b in EDGES)
            assert actual==expected,(prefix,row)
        reads=[sum(v in side for pair in gates for side in pair) for v in range(10)]
        cost=len(gates)+sum(max(0,len(side)-1) for pair in gates for side in pair)+max(0,len(outputs)-1)
        assert reads==circuit['raw_reads']==[3,1,3,1,2,1,2,2,3,3]
        assert cost==circuit['naive_binary_gate_cost']==20
        assignment={}
        for line in (ROOT/(prefix+'.stdout')).read_text().splitlines():
            if line.startswith('v '):
                for lit in map(int,line[2:].split()):
                    if lit:assignment[abs(lit)]=lit>0
        clauses=cnf(prefix+'.cnf')
        assert all(any(assignment[abs(x)]==(x>0) for x in cl) for cl in clauses)
        print('PASS',prefix,':1024 rows, saved SAT model satisfies',len(clauses),'clauses, naive binary cost20, not19')
    negative=cnf('skeleton6-read2-negative.cnf')
    units={cl[0] for cl in negative if len(cl)==1}
    meta=json.loads((ROOT/'skeleton6-read2-negative.meta.json').read_text())
    fixed=json.loads((ROOT/'skeleton6-control.json').read_text())
    for j,sides in enumerate(fixed['gates']):
        for side,source in enumerate(sides):
            for i,var in enumerate(meta['selectors'][j][side]):
                assert (var if i in source else -var) in units
    for j,var in enumerate(meta['outputs']):
        assert (var if j in fixed['output'] else -var) in units
    conflict=None
    for v in range(10):
        forced=[meta['selectors'][j][side][v] for j in range(6) for side in range(2)
                if v in fixed['gates'][j][side]]
        if len(forced)>2:
            for triple in itertools.combinations(forced,3):
                clause=tuple(-x for x in triple)
                if clause in negative:
                    assert all(x in units for x in triple);conflict=triple;break
        if conflict:break
    assert conflict is not None
    print('PASS read2 negative control fixes the same3-read star; forced triple',conflict,'contradicts an explicit at-most2 clause')
    print('NOTE this negative control does not prove absence of other6-AND read2 skeletons')
    print('ALL FINAL ARCHIVE CONTROLS PASSED; no solver or unfinished proof was run')


if __name__=='__main__':main()
