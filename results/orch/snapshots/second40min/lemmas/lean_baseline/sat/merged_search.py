import argparse
import json
from pathlib import Path
from resynthesize import run_window, evaluate
from subset_search import validate_basis


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('case',type=Path)
    parser.add_argument('seeds',type=Path)
    parser.add_argument('output',type=Path)
    parser.add_argument('--seconds',type=int,default=180)
    args=parser.parse_args()
    data=json.loads(args.case.read_text());tests=validate_basis(data)
    seeds=json.loads(args.seeds.read_text())
    representatives={}
    for item in seeds:
        first=len(set(item['group'])&{0,1,3})
        second=len(item['group'])-first
        key=tuple(sorted((first,second)))
        representatives.setdefault(key,item)
    args.output.mkdir(exist_ok=True,parents=True)
    for key,item in sorted(representatives.items(),key=lambda pair:(sum(pair[0]),pair[0])):
        gates=[list(g) for g in item['gates']]
        while len(gates)<28:
            wire=data['inputs']+len(gates)-1;gates.append([0,wire,wire])
        assert len(gates)==28
        assert all(evaluate(gates,1<<i,data['inputs'])[-1] is False for i in range(data['inputs']))
        assert all(evaluate(gates,m,data['inputs'])[-1] for m,y in tests if y)
        name=f'merge-{key[0]}-{key[1]}'
        print(name,'group',item['group'],'original-size',len(item['gates']),'negative-errors',sum(evaluate(gates,m,data['inputs'])[-1] for m,y in tests if not y),flush=True)
        answer=run_window(gates,tests,list(range(28)),args.output,name,args.seconds,
                          fixed_ops=False,ninputs=data['inputs'],ordered_inputs=True,require_used=True,
                          positive_live=True,or_incomparable=True,allow_equal_and=True,
                          and_incomparable=True,seed_phases=True)
        if answer is not None:
            assert all(evaluate(answer,m,data['inputs'])[-1]==any(m>>a&1 and m>>b&1 for a,b in data['edges']) for m in range(1<<data['inputs']))
            result={'gates':answer,'input_original':data['input_original'],'original_rows':data['original_rows'],'case':data['name']}
            (args.output/'FULL-SUBSET-WITNESS.json').write_text(json.dumps(result))
            print('FULL SUBSET WITNESS',name,flush=True)
            return


if __name__=='__main__':main()
