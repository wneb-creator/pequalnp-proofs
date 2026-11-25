import argparse
import importlib.util
import json
import time
from pathlib import Path

p=argparse.ArgumentParser()
p.add_argument('--engine',type=Path,required=True)
p.add_argument('--source',type=Path,required=True)
p.add_argument('--states',type=Path,nargs='+',required=True)
p.add_argument('--out',type=Path,required=True)
a=p.parse_args()
spec=importlib.util.spec_from_file_location('neutral',a.engine)
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
base=m.load_module(a.source)

def bypass(gates,removed,side):
    ren={i:i for i in range(26)}
    result=[]
    for j,(op,left,right) in enumerate(gates):
        if j==removed:
            ren[26+j]=ren[(left,right)[side]]
            continue
        x,y=ren[left],ren[right]
        if x==y:
            if op==1:return None
            ren[26+j]=x
        else:
            result.append((op,min(x,y),max(x,y)))
            ren[26+j]=25+len(result)
    return m.trim(tuple(result),ren[25+len(gates)])

start=time.monotonic();checked=0;first_valid=0
inputs=[]
for path in a.states:
    data=json.loads(path.read_text());gates=tuple(tuple(g) for g in data['gates'])
    assert len(gates) in (65,66) and all(g[0] in (0,1) for g in gates) and m.valid(gates,base)
    inputs.append({'source':str(path),'gates':gates})
    for j in range(len(gates)):
        for side in range(2):
            candidate=bypass(gates,j,side)
            if candidate is None:continue
            checked+=1
            if not m.valid(candidate,base):continue
            first_valid+=1
            if len(candidate)<=64:
                result={'found':True,'gates':candidate,'source':str(path),'removed':[(j,side)]}
                a.out.write_text(json.dumps(result)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='gates'}));raise SystemExit
            for k in range(len(candidate)):
                for side2 in range(2):
                    smaller=bypass(candidate,k,side2)
                    if smaller is None:continue
                    checked+=1
                    if len(smaller)<=64 and m.valid(smaller,base):
                        result={'found':True,'gates':smaller,'source':str(path),'removed':[(j,side),(k,side2)]}
                        a.out.write_text(json.dumps(result)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='gates'}));raise SystemExit
result={'found':False,'seconds':time.monotonic()-start,'complete_candidates_checked':checked,
        'valid_first_reductions':first_valid,'input_states':inputs,
        'scope':'Exact bounded one/two-bypass audit only; not a global lower bound.'}
a.out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='input_states'}))
