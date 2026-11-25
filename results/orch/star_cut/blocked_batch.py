import argparse,json,time
from pathlib import Path
import normalized
from blocked_compact import make

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--solver',required=True);ap.add_argument('--out',required=True)
    ap.add_argument('--seconds',type=int,default=90);ap.add_argument('--total-seconds',type=int,default=540)
    a=ap.parse_args();base=Path(__file__).parent;out=Path(a.out);out.mkdir(exist_ok=True)
    normalized.make=make
    original=json.loads((base/'pairs/summary.json').read_text())
    previous=json.loads((base/'normalized-batch/summary.json').read_text())
    excluded={r['case'] for r in original if r['status']=='UNSAT_LOCAL_MODEL'}|{6}
    excluded|={r['original_case'] for r in previous if r['status']=='UNSAT_NORMALIZED_LOCAL_MODEL'}
    jobs=[r for r in original if r['case'] not in excluded]
    results=[];started=time.monotonic()
    for row in jobs:
        if time.monotonic()-started>a.total_seconds or (out/'STOP').exists():break
        name=f"case-{row['case']:03d}";case=out/name;case.mkdir(exist_ok=True)
        scope=json.loads((base/'pairs'/name/'scope.json').read_text())
        print('START',row['case'],scope['chosen'],flush=True)
        result=normalized.run_case(scope,case,a.solver,a.seconds)
        result['original_case']=row['case'];results.append(result)
        (out/'summary.json').write_text(json.dumps(results,indent=2)+'\n')
        print('FINISH',result,flush=True)
        if result['status'] in {'FOUND','SOLVER_ERROR'}:break
    print('COMPLETE',len(results),'elapsed',time.monotonic()-started,flush=True)

if __name__=='__main__':main()
