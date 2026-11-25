import argparse,json,time
from pathlib import Path
from normalized import run_case

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--solver',required=True);ap.add_argument('--out',required=True)
    ap.add_argument('--seconds',type=int,default=60);ap.add_argument('--total-seconds',type=int,default=840)
    a=ap.parse_args();base=Path(__file__).parent;out=Path(a.out);out.mkdir(exist_ok=True)
    rows=json.loads((base/'pairs/summary.json').read_text())
    jobs=sorted([r for r in rows if r['status']=='UNKNOWN' and r['case']!=6],key=lambda r:(r['variable'],r['case']))
    results=[];started=time.monotonic()
    for row in jobs:
        if time.monotonic()-started>a.total_seconds or (out/'STOP').exists():break
        name=f"case-{row['case']:03d}";case=out/name;case.mkdir(exist_ok=True)
        scope=json.loads((base/'pairs'/name/'scope.json').read_text())
        print('START',row['case'],scope['chosen'],flush=True)
        result=run_case(scope,case,a.solver,a.seconds)
        result['original_case']=row['case'];results.append(result)
        (out/'summary.json').write_text(json.dumps(results,indent=2)+'\n')
        print('FINISH',result,flush=True)
        if result['status'] in {'FOUND','SOLVER_ERROR'}:break
    print('COMPLETE',len(results),'elapsed',time.monotonic()-started,flush=True)

if __name__=='__main__':main()
