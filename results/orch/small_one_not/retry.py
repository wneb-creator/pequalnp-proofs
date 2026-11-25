"""Resolve the remaining size7 graph, splitting unused-NOT and used-NOT cases."""
import argparse,importlib.util,json,subprocess,sys,time
from pathlib import Path
sys.path.insert(0,str(Path(__file__).parent.parent/'star-cut'))
from normalized import add_normalization

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--solver',required=True)
    ap.add_argument('--out',required=True)
    ap.add_argument('--seconds',type=int,default=60)
    a=ap.parse_args()
    base=Path(__file__).parent
    out=Path(a.out);out.mkdir(exist_ok=True)
    rows=json.loads((base/'runs/summary.json').read_text())
    graph=next(r['graph'] for r in rows if r['status']=='UNKNOWN')
    spec=importlib.util.spec_from_file_location('enc',base/'runs/encoder.py')
    m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
    m.N=graph['n'];m.MASK=(1<<(1<<m.N))-1
    m.X=[sum(1<<x for x in range(1<<m.N) if x>>i&1) for i in range(m.N)]
    m.TARGET=0
    for u,v in graph['edges']:m.TARGET|=m.X[u]&m.X[v]
    summary=[]
    for not_count,budget in [(0,graph['star_bound']-2),(1,graph['star_bound']-1)]:
        case=out/f'not-{not_count}';case.mkdir(exist_ok=True)
        started=time.monotonic()
        c,schema=m.make(list(range(1<<m.N)),budget,not_count=not_count)
        keys=add_normalization(c,schema,0,input_count=m.N)
        p=case/'query.cnf';c.write(p)
        (case/'schema.json').write_text(json.dumps({'gates':schema,'keys':keys}))
        command=[a.solver,'--default','-t',str(a.seconds),str(p)]
        (case/'command.json').write_text(json.dumps(command))
        log=case/'solver.log'
        with log.open('w') as f:proc=subprocess.run(command,stdout=f,stderr=subprocess.STDOUT)
        result={'not_count':not_count,'gate_budget':budget,'exit':proc.returncode,'elapsed':time.monotonic()-started}
        if proc.returncode==20:result['status']='UNSAT_NORMALIZED_MODEL'
        elif proc.returncode==0:result['status']='UNKNOWN'
        elif proc.returncode==10:
            model={int(v) for l in log.read_text().splitlines() if l.startswith('v ') for v in l[2:].split() if int(v)>0}
            gates=m.decode(model,schema)
            assert not m.evaluate(gates)
            result['status']='FOUND'
            (case/'FOUND.json').write_text(json.dumps({'graph':graph,'gates':gates,'errors':0}))
        else:result['status']='SOLVER_ERROR'
        summary.append(result)
        (out/'summary.json').write_text(json.dumps({'graph':graph,'results':summary},indent=2)+'\n')
        print(result,flush=True)
        if result['status'] in {'FOUND','SOLVER_ERROR'}:break

if __name__=='__main__':main()
