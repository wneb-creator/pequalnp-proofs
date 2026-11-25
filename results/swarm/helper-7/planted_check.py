#!/usr/bin/env python3
"""Pin an explicit minimum-cover circuit in the strongest synthesis encoding."""
import argparse
import importlib.util
import itertools
import json
from pathlib import Path
import subprocess
import time

ROOT=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('synthesize',ROOT/'synthesize.py')
s=importlib.util.module_from_spec(spec)
spec.loader.exec_module(s)

def star_cover(info):
    n,edges=info['n'],info['edges']
    cover=next(c for k in range(n+1) for c in itertools.combinations(range(n),k)
               if all(a in c or b in c for a,b in edges))
    owns={c:[] for c in cover}
    for a,b in edges:
        owner=min(v for v in (a,b) if v in cover)
        owns[owner].append(b if owner==a else a)
    gates=[]
    def add(op,a,b):
        idx=n+len(gates)
        gates.append({'op':op,'left':a,'right':b,'pad':False})
        return idx
    def join(xs):
        assert xs
        out=xs[0]
        for v in xs[1:]: out=add('or',out,v)
        return out
    terms=[]
    for c in cover:
        assert owns[c]
        terms.append(add('and',c,join(owns[c])))
    output=join(terms)
    assert output==n+len(gates)-1
    assert len(gates)==info['standard_bound']
    s.verify(info,gates)
    return cover,gates

def normalize(n,gates,perm):
    wiremap={v:perm[v] for v in range(n)}
    remaining=set(range(len(gates)))
    output=[]
    while remaining:
        ready=[]
        for j in remaining:
            g=gates[j]
            if g['left'] in wiremap and g['right'] in wiremap:
                a,b=sorted((wiremap[g['left']],wiremap[g['right']]))
                ready.append((b,a,g['op']=='and',j))
        b,a,_,j=min(ready)
        output.append({'op':gates[j]['op'],'left':a,'right':b,'pad':False})
        wiremap[n+j]=n+len(output)-1
        remaining.remove(j)
    assert wiremap[n+len(gates)-1]==n+len(gates)-1
    return output

def check(name,solver):
    g=json.loads((ROOT/'graphs'/f'{name}.json').read_text())
    info=s.graph_info(g['n'],g['edges'])
    cover,original=star_cover(info)
    symmetry=s.first_pair_symmetry(info)
    candidates=[normalize(info['n'],original,p) for p in symmetry['automorphisms']]
    gates=min(candidates,key=lambda gs:tuple((x['right'],x['left'],x['op']=='and') for x in gs))
    assert (gates[0]['left'],gates[0]['right']) in map(tuple,symmetry['representatives'])
    verification=s.verify(info,gates)
    f,mapping=s.encode(info,len(gates),normalized=True,symmetry=symmetry,undominated=True,oriented=True)
    for j,gate in enumerate(gates):
        f.add(mapping['left'][j][gate['left']])
        f.add(mapping['right'][j][gate['right']])
        f.add(mapping['op'][j] if gate['op']=='and' else -mapping['op'][j])
        f.add(-mapping['pad'][j])
    directory=ROOT/'synthesis'/f'{name}-planted-{time.time_ns()}'
    directory.mkdir(parents=True)
    f.write(directory/'input.cnf')
    (directory/'witness.json').write_text(json.dumps({'graph':name,'info':info,'original_cover':cover,'gates':gates,'verification':verification},indent=2))
    with (directory/'solver.stdout').open('w') as out,(directory/'solver.stderr').open('w') as err:
        process=subprocess.Popen([str(solver),'--time=10',str(directory/'input.cnf')],stdout=out,stderr=err)
        print(json.dumps({'event':'started','pid':process.pid,'graph':name,'directory':str(directory)}),flush=True)
        process.wait()
    assert process.returncode==10,process.returncode
    decoded=s.decode((directory/'solver.stdout').read_text(),mapping)
    assert decoded==gates
    s.verify(info,decoded)
    result={'graph':name,'status':'SAT planted strongest encoding','gate_count':len(gates),'verification':verification,'gates':gates,'directory':str(directory)}
    (directory/'result.json').write_text(json.dumps(result,indent=2))
    print(json.dumps(result),flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('graphs',nargs='*',default=['C8','C6leaf'])
    p.add_argument('--solver',type=Path,default=s.DEFAULT_SOLVER)
    args=p.parse_args()
    if args.solver is None:
        p.error('Kissat was not found; provide --solver PATH')
    for name in args.graphs: check(name,args.solver)
