import argparse
import itertools
import json
import os
import subprocess
import time
from pathlib import Path

OUT = Path(os.environ.get('PNP_SEARCH_DIR', str(Path(__file__).resolve().parent)))
SOLVER = Path(os.environ.get('PNP_CADICAL', str(OUT / 'cadical-rel-3.1.0/build/cadical')))


def graph(name):
    if name.startswith('cycle'):
        n = int(name[5:])
        return n, sorted({tuple(sorted((i, (i + 1) % n))) for i in range(n)})
    if name == 'petersen':
        return 10, sorted({*[(i, (i + 1) % 5) for i in range(5)],
                           *[(i, i + 5) for i in range(5)],
                           *[(i + 5, (i + 2) % 5 + 5) for i in range(5)]})
    if name.startswith('file:'):
        data=json.loads(Path(name[5:]).read_text())
        return data['n'],data['edges']
    raise ValueError(name)


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--graph',required=True)
    parser.add_argument('--gates',type=int,required=True)
    parser.add_argument('--seconds',type=int,default=120)
    parser.add_argument('--dirty-and',action='store_true')
    parser.add_argument('--singleton-safe',action='store_true')
    parser.add_argument('--unowned-and',action='store_true')
    parser.add_argument('--all-owned',action='store_true')
    parser.add_argument('--sound-ands',action='store_true')
    parser.add_argument('--unsound-and',action='store_true')
    parser.add_argument('--canonical-first',action='store_true')
    parser.add_argument('--name')
    parser.add_argument('--emit-only',action='store_true')
    args=parser.parse_args()
    label=args.name or args.graph
    tag=f'sat-{label}-{args.gates}'+('-dirty' if args.dirty_and else '')
    tag+=('-singletonsafe' if args.singleton_safe else '')
    tag+=('-unowned' if args.unowned_and else '')+('-allowned' if args.all_owned else '')
    tag+=('-sound' if args.sound_ands else '')
    tag+=('-unsound' if args.unsound_and else '')
    n,raw_edges=graph(args.graph)
    edges=sorted({tuple(sorted(e)) for e in raw_edges})
    independent=[x for x in range(1<<n) if all(not(x>>a&1 and x>>b&1) for a,b in edges)]
    iset=set(independent)
    maximal=[x for x in independent if all(x>>v&1 or x|(1<<v) not in iset for v in range(n))]
    alpha=max(x.bit_count() for x in independent)
    tests=[(1<<a|1<<b,1) for a,b in edges]+[(x,0) for x in maximal]
    if args.dirty_and or args.singleton_safe:tests.extend([(1<<i,0) for i in range(n)])
    k=args.gates
    print('graph',label,'n',n,'edges',edges,'alpha',alpha,'star_bound',len(edges)+n-alpha-1,flush=True)
    print('tests',len(tests),'gates',k,'dirty',args.dirty_and,flush=True)
    count=0
    def fresh():
        nonlocal count
        count+=1
        return count
    op=[fresh() for _ in range(k)]
    ports=[[[fresh() for _ in range(n+j)] for _ in range(2)] for j in range(k)]
    values=[[fresh() for _ in tests] for _ in range(k)]
    operands=[[[fresh() for _ in tests] for _ in range(2)] for _ in range(k)]
    clauses=[]
    def add(*args):clauses.append(list(args))
    for j in range(k):
        for port in ports[j]:
            add(*port)
            for a,b in itertools.combinations(port,2):add(-a,-b)
        for a,p in enumerate(ports[j][0]):
            for b,q in enumerate(ports[j][1]):
                if a>=b:add(-p,-q)
        for ti,(assignment,expected) in enumerate(tests):
            for pi in range(2):
                dest=operands[j][pi][ti]
                for w,selector in enumerate(ports[j][pi]):
                    if w<n:
                        add(-selector,dest if assignment>>w&1 else -dest)
                    else:
                        src=values[w-n][ti]
                        add(-selector,-dest,src)
                        add(-selector,dest,-src)
            z,u,v,a=values[j][ti],operands[j][0][ti],operands[j][1][ti],op[j]
            add(-a,-z,u);add(-a,-z,v)
            add(z,-u,-v)
            add(a,z,-u);add(a,z,-v)
            add(-z,u,v)
    for j in range(k-1):
        add(*[ports[l][p][n+j] for l in range(j+1,k) for p in range(2)])
    # A topological ordering may choose ready gates in nondecreasing last-operand order.
    for j in range(1,k):
        for b,q in enumerate(ports[j][1]):
            for old_b,old_q in enumerate(ports[j-1][1]):
                if b<old_b:add(-q,-old_q)
    # Within a shared larger operand, independent gates may be sorted by smaller operand.
    prefixes=[]
    for j in range(k):
        prefix=[ports[j][0][0]]
        for a in range(1,n+j):
            z=fresh();p=prefix[-1];q=ports[j][0][a]
            add(-p,z);add(-q,z);add(-z,p,q);prefix.append(z)
        prefixes.append(prefix)
    for j in range(1,k):
        for b in range(n+j-1):
            q,old_q=ports[j][1][b],ports[j-1][1][b]
            for a in range(b):
                add(-q,-old_q,-prefixes[j][a],prefixes[j-1][a])
                p,old_p=ports[j][0][a],ports[j-1][0][a]
                add(-q,-old_q,-p,-old_p,op[j-1])
                add(-q,-old_q,-p,-old_p,-op[j])
    if args.canonical_first:
        add(ports[0][0][0])
        if args.graph.startswith('cycle'):
            for b in range(n//2+1,n):add(-ports[0][1][b])
        elif args.graph=='petersen':
            for b in range(n):
                if b not in (1,2):add(-ports[0][1][b])
        else:raise ValueError('canonical first supports only cycles and Petersen')
    for ti,(_,expected) in enumerate(tests):add(values[-1][ti] if expected else -values[-1][ti])
    if args.dirty_and:
        witnesses=[]
        for j in range(k):
            for i in range(n):
                v=values[j][len(tests)-n+i]
                w=fresh();witnesses.append(w)
                add(-w,op[j]);add(-w,v)
        add(*witnesses)
    if args.singleton_safe:
        for j in range(k):
            for i in range(n):add(-op[j],-values[j][len(tests)-n+i])
    if args.sound_ands:
        for j in range(k):
            for ti,(_,expected) in enumerate(tests):
                if not expected:add(-op[j],-values[j][ti])
    if args.unsound_and:
        witnesses=[]
        for j in range(k):
            for ti,(_,expected) in enumerate(tests):
                if not expected:
                    w=fresh();witnesses.append(w)
                    add(-w,op[j]);add(-w,values[j][ti])
        add(*witnesses)
    if args.unowned_and or args.all_owned:
        inclusive=[[fresh() for _ in edges] for _ in range(k)]
        cone_operands=[[[fresh() for _ in edges] for _ in range(2)] for _ in range(k)]
        bads=[]
        for j in range(k):
            good_witnesses=[]
            bad=fresh();bads.append(bad);add(-bad,op[j])
            for ei in range(len(edges)):
                for pi in range(2):
                    dest=cone_operands[j][pi][ei]
                    for w,selector in enumerate(ports[j][pi]):
                        if w<n:add(-selector,-dest)
                        else:
                            src=inclusive[w-n][ei]
                            add(-selector,-dest,src);add(-selector,dest,-src)
                z,p,q,a,v=inclusive[j][ei],cone_operands[j][0][ei],cone_operands[j][1][ei],op[j],values[j][ei]
                add(-z,p,q,a);add(-z,p,q,v)
                add(-a,-v,z);add(-p,z);add(-q,z)
                if args.unowned_and:add(-bad,-v,p,q)
                if args.all_owned:
                    good=fresh();good_witnesses.append(good)
                    add(-good,a);add(-good,v);add(-good,-p);add(-good,-q)
            if args.all_owned:add(-op[j],*good_witnesses)
        if args.unowned_and:add(*bads)
    path=OUT/(tag+'.cnf')
    with path.open('w') as f:
        f.write(f'p cnf {count} {len(clauses)}\n')
        for clause in clauses:f.write(' '.join(map(str,clause))+' 0\n')
    metadata={'n':n,'edges':edges,'gate_count':k,'op':op,'ports':ports,'values':values,
              'tests':tests,'clauses':len(clauses),'variables':count,'star_bound':len(edges)+n-alpha-1,
              'order':'max,min,op','version':2,'canonical_first':args.canonical_first}
    (OUT/(tag+'-encoding.json')).write_text(json.dumps(metadata))
    print('variables',count,'clauses',len(clauses),flush=True)
    if args.emit_only:return
    start=time.time()
    with (OUT/(tag+'-solver.log')).open('w') as log:
        result=subprocess.run([str(SOLVER),'-t',str(args.seconds),str(path)],stdout=log,stderr=subprocess.STDOUT)
    s=(OUT/(tag+'-solver.log')).read_text()
    print('returncode',result.returncode,'elapsed',time.time()-start,flush=True)
    print('\n'.join(line for line in s.splitlines() if line.startswith('s ')),flush=True)
    summary={'graph':label,'n':n,'edges':edges,'gate_count':k,'returncode':result.returncode,
             'elapsed':time.time()-start,'star_bound':len(edges)+n-alpha-1,'forced_dirty':args.dirty_and,
             'forced_unowned':args.unowned_and,'all_owned':args.all_owned,'singleton_safe':args.singleton_safe,
             'sound_ands':args.sound_ands,'unsound_and':args.unsound_and,'encoding_version':2,
             'canonical_first':args.canonical_first}
    if result.returncode==10:
        assignments={int(x) for line in s.splitlines() if line.startswith('v ') for x in line[2:].split()}
        gates=[]
        for j in range(k):
            gates.append(('and' if op[j] in assignments else 'or',
                          next(w for w,v in enumerate(ports[j][0]) if v in assignments),
                          next(w for w,v in enumerate(ports[j][1]) if v in assignments)))
        valid=True
        for x in range(1<<n):
            wires=[bool(x>>i&1) for i in range(n)]
            for operation,a,b in gates:wires.append(wires[a] and wires[b] if operation=='and' else wires[a] or wires[b])
            if wires[-1] != any(x>>a&1 and x>>b&1 for a,b in edges):valid=False;break
        cones=[];owned=[];singletons=[]
        for j,(operation,a,b) in enumerate(gates):
            cone=set()
            for w in (a,b):
                if w>=n:cone.add(w-n);cone.update(cones[w-n])
            cones.append(cone)
            if operation!='and':continue
            es=[];ss=[]
            for u,v in edges+[(i,i) for i in range(n)]:
                wires=[i in (u,v) for i in range(n)]
                for oper,a,b in gates:wires.append(wires[a] and wires[b] if oper=='and' else wires[a] or wires[b])
                if u==v and wires[n+j]:ss.append(u)
                if u!=v and wires[n+j] and not any(gates[h][0]=='and' and wires[n+h] for h in cone):es.append([u,v])
            owned.append({'gate':j,'edges':es});singletons.append({'gate':j,'vertices':ss})
        summary.update({'gates':gates,'all_inputs_validated':valid,'ownership':owned,'singletons':singletons})
        print('WITNESS',json.dumps(summary),flush=True)
    (OUT/(tag+'.json')).write_text(json.dumps(summary,indent=2))


if __name__=='__main__':main()
