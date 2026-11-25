import argparse
import json
from pathlib import Path
from resynthesize import run_window, evaluate
from subset_search import validate_basis


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('case',type=Path)
    parser.add_argument('pool',type=Path)
    parser.add_argument('output',type=Path)
    parser.add_argument('--seconds',type=int,default=90)
    parser.add_argument('--limit',type=int,default=16)
    parser.add_argument('--free-ops',action='store_true')
    parser.add_argument('--free-count',action='store_true')
    parser.add_argument('--min-and',type=int,default=7)
    args=parser.parse_args()
    data=json.loads(args.case.read_text());tests=validate_basis(data)
    pool=json.loads(args.pool.read_text())
    ranked=[]
    for entry in pool:
        gates=entry['gates'];count=sum(g[0]==0 for g in gates)
        if count<args.min_and:continue
        missing=sum(label and not evaluate(gates,mask,data['inputs'])[-1] for mask,label in tests)
        false=sum(not label and evaluate(gates,mask,data['inputs'])[-1] for mask,label in tests)
        ranked.append((missing+false/8-entry.get('priority',0)/100,missing,false,count,gates))
    ranked.sort(key=lambda item:item[:4])
    chosen=[];quota={}
    for score,missing,false,count,gates in ranked:
        key=(count,bool(false))
        if quota.get(key,0)>=3:continue
        quota[key]=quota.get(key,0)+1
        chosen.append((score,missing,false,count,gates))
        if len(chosen)>=args.limit:break
    args.output.mkdir(exist_ok=True,parents=True)
    for index,(score,missing,false,count,gates) in enumerate(chosen):
        name=f'seed-{index:02}-and{count}'
        print(name,'miss',missing,'false',false,'score',score,'freeops',args.free_ops,flush=True)
        answer=run_window(gates,tests,list(range(len(gates))),args.output,name,args.seconds,
                          fixed_ops=not args.free_ops,ninputs=data['inputs'],ordered_inputs=True,
                          require_used=True,positive_live=True,or_incomparable=True,
                          allow_equal_and=True,and_incomparable=True,seed_phases=True,
                          and_count=count if args.free_ops and not args.free_count else None)
        if answer is not None:
            assert all(evaluate(answer,m,data['inputs'])[-1]==any(m>>a&1 and m>>b&1 for a,b in data['edges']) for m in range(1<<data['inputs']))
            result={'gates':answer,'input_original':data['input_original'],'original_rows':data['original_rows'],'case':data['name']}
            (args.output/'FULL-SUBSET-WITNESS.json').write_text(json.dumps(result))
            print('FULL SUBSET WITNESS',name,flush=True)
            return


if __name__=='__main__':main()
