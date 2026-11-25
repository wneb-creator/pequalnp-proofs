import argparse
import hashlib
import itertools
import json
import os
from pathlib import Path
import subprocess
import time

ROOT=Path('/tmp/oec/pequalnp-pilot-66')
SOLVER=ROOT/'cadical-rel-3.1.0/build/cadical'


def automorphisms(n,edges,name):
    edges={tuple(sorted(e)) for e in edges}
    if name=='petersen':
        labels=[(0,1),(2,3),(0,4),(1,3),(2,4),(3,4),(1,4),(1,2),(0,2),(0,3)]
        inverse={p:i for i,p in enumerate(labels)}
        candidates=[tuple(inverse[tuple(sorted((p[a],p[b])))] for a,b in labels)
                    for p in itertools.permutations(range(5))]
    else:
        degrees=[sum(v in e for e in edges) for v in range(n)]
        classes=[[v for v in range(n) if degrees[v]==d] for d in sorted(set(degrees))]
        candidates=[]
        for blocks in itertools.product(*[list(itertools.permutations(c)) for c in classes]):
            p=list(range(n))
            for old,new in zip(classes,blocks):
                for a,b in zip(old,new):p[a]=b
            candidates.append(tuple(p))
    answer=[]
    for p in candidates:
        assert sorted(p)==list(range(n))
        image={tuple(sorted((p[a],p[b]))) for a,b in edges}
        if image==edges:answer.append(p)
    group=set(answer)
    assert tuple(range(n)) in group
    assert all(tuple(p[q[i]] for i in range(n)) in group for p in group for q in group)
    return sorted(group)


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--graph',required=True)
    parser.add_argument('--name',required=True)
    parser.add_argument('--gates',type=int,required=True)
    parser.add_argument('--seconds',type=int,required=True)
    parser.add_argument('--depth',type=int,default=3)
    parser.add_argument('--minimal-pruning',action='store_true')
    parser.add_argument('--all-owned',action='store_true')
    args=parser.parse_args()
    base_name=args.name+'base'
    command=['python3',str(ROOT/'circuit-sat.py'),'--graph',args.graph,'--name',base_name,
             '--gates',str(args.gates),'--emit-only']
    suffix=''
    if args.all_owned:command.append('--all-owned');suffix+='-allowned'
    if args.minimal_pruning:command.append('--minimal-pruning');suffix+='-minimal'
    base_tag=f'sat-{base_name}-{args.gates}'+suffix
    tag=f'sat-{args.name}-{args.gates}'+suffix+'-sym'
    with (ROOT/(tag+'-emit.log')).open('w') as log:
        subprocess.run(command,check=True,cwd='/workspace/pequalnp-proofs',stdout=log,stderr=subprocess.STDOUT)
    meta=json.loads((ROOT/(base_tag+'-encoding.json')).read_text())
    n=meta['n'];edges=meta['edges'];ports=meta['ports']
    group=automorphisms(n,edges,args.graph)
    extra=[];nodes=[0]*args.depth
    def key(pair):return pair[1],pair[0]
    def image(p,w):return p[w] if w<n else w
    def canonicalize(depth,subgroup,condition):
        nodes[depth]+=1
        for a,b in itertools.combinations(range(n+depth),2):
            orbit={tuple(sorted((image(p,a),image(p,b)))) for p in subgroup}
            representative=min(orbit,key=key)
            selected=[ports[depth][0][a],ports[depth][1][b]]
            if (a,b)!=representative:
                extra.append([-v for v in condition+selected])
            elif depth+1<args.depth:
                stabilizer=[p for p in subgroup if tuple(sorted((image(p,a),image(p,b))))==(a,b)]
                if len(stabilizer)>1:canonicalize(depth+1,stabilizer,condition+selected)
    canonicalize(0,group,[])
    base=(ROOT/(base_tag+'.cnf')).read_text()
    header,body=base.split('\n',1)
    _,_,variables,clauses=header.split()
    cnf=ROOT/(tag+'.cnf')
    cnf.write_text(f'p cnf {variables} {int(clauses)+len(extra)}\n'+body+
                   ''.join(' '.join(map(str,c))+' 0\n' for c in extra))
    symmetry={'n':n,'edges':edges,'automorphisms':group,'group_size':len(group),'prefix_depth':args.depth,
              'prefix_nodes':nodes,'added_clauses':len(extra),'base_sha256':hashlib.sha256(base.encode()).hexdigest(),
              'cnf_sha256':hashlib.sha256(cnf.read_bytes()).hexdigest(),
              'caveat':'Automorphisms and group closure exhaustively checked; circuit canonicalization argument not Lean checked.'}
    (ROOT/(tag+'-symmetry.json')).write_text(json.dumps(symmetry,indent=2))
    print('graph',args.graph,'name',args.name,'gates',args.gates,'group',len(group),'prefix_nodes',nodes,
          'extra_clauses',len(extra),'minimal_pruning',args.minimal_pruning,flush=True)
    start=time.time()
    with (ROOT/(tag+'-solver.log')).open('w') as log:
        answer=subprocess.run([str(SOLVER),'-t',str(args.seconds),str(cnf)],stdout=log,stderr=subprocess.STDOUT)
    log=(ROOT/(tag+'-solver.log')).read_text()
    result={'graph':args.graph,'n':n,'edges':edges,'gate_count':args.gates,'seconds_limit':args.seconds,
            'returncode':answer.returncode,'elapsed':time.time()-start,'group_size':len(group),
            'prefix_depth':args.depth,'minimal_pruning':args.minimal_pruning,'all_owned':args.all_owned}
    if answer.returncode==10:
        model={int(x) for line in log.splitlines() if line.startswith('v ') for x in line[2:].split()}
        gates=[]
        for j in range(args.gates):
            gates.append(('and' if meta['op'][j] in model else 'or',
                          next(i for i,v in enumerate(ports[j][0]) if v in model),
                          next(i for i,v in enumerate(ports[j][1]) if v in model)))
        def evaluate(x):
            values=[bool(x>>i&1) for i in range(n)]
            for op,a,b in gates:values.append(values[a] and values[b] if op=='and' else values[a] or values[b])
            return values
        valid=all(evaluate(x)[-1]==any(x>>a&1 and x>>b&1 for a,b in edges) for x in range(1<<n))
        cones=[];owned=[]
        for j,(op,a,b) in enumerate(gates):
            cone=set()
            for w in (a,b):
                if w>=n:cone.add(w-n);cone.update(cones[w-n])
            cones.append(cone)
            if op=='and':
                own=[]
                for u,v in edges:
                    values=evaluate(1<<u|1<<v)
                    if values[n+j] and not any(gates[i][0]=='and' and values[n+i] for i in cone):own.append([u,v])
                owned.append({'gate':j,'edges':own})
        result.update({'gates':gates,'all_inputs_validated':valid,'ownership':owned})
    (ROOT/(tag+'.json')).write_text(json.dumps(result,indent=2))
    print(json.dumps(result),flush=True)


if __name__=='__main__':main()
