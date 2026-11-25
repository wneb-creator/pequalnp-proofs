"""Finite one-NOT check on connected bipartite C4-free graphs with <=7 vertices."""
import argparse, collections, importlib.util, itertools, json, subprocess, time
from pathlib import Path


def graphs():
    representatives = []
    for n in range(2, 8):
        seen = set()
        for a in range(1, n // 2 + 1):
            b = n - a
            pa = list(itertools.permutations(range(a)))
            pb = list(itertools.permutations(range(b)))
            def canon(bits):
                return min(sum(1 << (i*b+j) for i,p in enumerate(ps) for j,q in enumerate(qs)
                               if bits >> (p*b+q) & 1) for ps in pa for qs in pb)
            for bits in range(1, 1 << (a*b)):
                rows = [sum(1 << j for j in range(b) if bits >> (i*b+j) & 1) for i in range(a)]
                if not all(rows) or any(not any(r >> j & 1 for r in rows) for j in range(b)):
                    continue
                if any((r&s).bit_count() > 1 for r,s in itertools.combinations(rows,2)):
                    continue
                edges = [(i,a+j) for i in range(a) for j in range(b) if rows[i] >> j & 1]
                reached = {0}
                for _ in range(n):
                    reached |= {u for u,v in edges if v in reached} | {v for u,v in edges if u in reached}
                if len(reached) < n:
                    continue
                key_bits = canon(bits)
                if a == b:
                    tr = sum(1 << (j*b+i) for i in range(a) for j in range(b) if bits >> (i*b+j) & 1)
                    key_bits = min(key_bits,canon(tr))
                key = (a,b,key_bits)
                if key in seen:
                    continue
                seen.add(key)
                tau = min(mask.bit_count() for mask in range(1 << n)
                          if all((mask >> u & 1) or (mask >> v & 1) for u,v in edges))
                representatives.append({'n':n,'a':a,'b':b,'edges':edges,'star_bound':len(edges)+tau-1,'tau':tau})
    return representatives


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--solver',required=True)
    ap.add_argument('--encoder',required=True)
    ap.add_argument('--out',required=True)
    ap.add_argument('--seconds',type=int,default=25)
    args = ap.parse_args()
    out = Path(args.out)
    out.mkdir(exist_ok=True)
    spec = importlib.util.spec_from_file_location('frozen_encoder',args.encoder)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    (out/'encoder.py').write_text(Path(args.encoder).read_text())
    family = graphs()
    (out/'graphs.json').write_text(json.dumps(family,indent=2)+'\n')
    results = []
    for i,g in enumerate(family):
        case = out/f'case-{i:02d}'
        case.mkdir(exist_ok=True)
        module.N = g['n']
        module.MASK = (1 << (1 << module.N))-1
        module.X = [sum(1 << x for x in range(1 << module.N) if x >> j & 1) for j in range(module.N)]
        module.TARGET = 0
        for a,b in g['edges']:
            module.TARGET |= module.X[a]&module.X[b]
        budget = g['star_bound']-1
        result = {'case':i,'graph':g,'gate_budget':budget,'not_count':1}
        if budget == 0:
            result['status'] = 'EMPTY_ONE_NOT_BUDGET'
        else:
            started = time.monotonic()
            cnf,schema = module.make(list(range(1 << module.N)),budget,not_count=1)
            path = case/'query.cnf'
            cnf.write(path)
            (case/'schema.json').write_text(json.dumps(schema))
            (case/'graph.json').write_text(json.dumps(g))
            command = [args.solver,'--default','-t',str(args.seconds),str(path)]
            (case/'command.json').write_text(json.dumps(command))
            log = case/'solver.log'
            with log.open('w') as f:
                p = subprocess.run(command,stdout=f,stderr=subprocess.STDOUT)
            result.update({'exit':p.returncode,'variables':cnf.n,'clauses':len(cnf.clauses),'elapsed':time.monotonic()-started})
            if p.returncode == 20:
                result['status'] = 'UNSAT_FINITE_MODEL'
            elif p.returncode == 0:
                result['status'] = 'UNKNOWN'
            elif p.returncode == 10:
                model = {int(v) for line in log.read_text().splitlines() if line.startswith('v ')
                         for v in line[2:].split() if int(v)>0}
                gates = module.decode(model,schema)
                assert sum(o==2 for o,_,_ in gates)==1
                delta = module.evaluate(gates)
                assert not delta,'Full-truth-table model evaluation failed'
                result['status'] = 'FOUND'
                (case/'FOUND.json').write_text(json.dumps({'graph':g,'gates':gates,'errors':0},indent=2)+'\n')
            else:
                result['status'] = 'SOLVER_ERROR'
        results.append(result)
        (out/'summary.json').write_text(json.dumps(results,indent=2)+'\n')
        print(result,flush=True)
        if result['status'] in {'FOUND','SOLVER_ERROR'}:
            break
    print('COMPLETE',len(results),dict(collections.Counter(r['status'] for r in results)),flush=True)


if __name__=='__main__':
    main()
