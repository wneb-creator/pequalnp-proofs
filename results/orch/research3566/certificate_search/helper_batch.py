import argparse,itertools,json,subprocess,time
from pathlib import Path

p=argparse.ArgumentParser();p.add_argument('--metadata',default='c8-helper-dp-rows.json');p.add_argument('--name',default='c8-one-helper');args=p.parse_args()
base=Path(args.name);base.mkdir(exist_ok=True)
d=json.loads(Path(args.metadata).read_text());values=d['values'];rows=d['rows'];es=d['graph']['edges'];base_inputs=len(values)
free_helpers=d.get('helpers',[d.get('helper',[0,1])])
seen=set(values);candidates=[]
for op in ('and','or'):
    for a,b in itertools.combinations(range(len(values)),2):
        v=values[a]&values[b] if op=='and' else values[a]|values[b]
        if v not in seen and v not in (0,(1<<len(rows))-1):
            seen.add(v);candidates.append((op,a,b,v))
start=time.monotonic();results=[]
for i,(op,a,b,v) in enumerate(candidates):
    inp=base/f'case-{i}.input';out=base/f'case-{i}.json';log=base/f'case-{i}.log'
    inp.write_text(f'{len(rows)} {base_inputs+1} {(1<<len(es))-1} 9\n'+' '.join(map(str,values+[v]))+'\n')
    with log.open('w') as f:r=subprocess.run(['./formula_dp',str(inp),str(out),'10'],stdout=f,stderr=subprocess.STDOUT)
    if r.returncode:raise RuntimeError((i,r.returncode))
    ans=json.loads(out.read_text());total=ans['dag_gates']+1
    results.append({'index':i,'helper':[op,a,b],'size_with_helper':total,'formula':ans['formula_gates']})
    if total<=10:
        gs=[[op,a,b]]+ans['gates'];wrong=[]
        for s in range(256):
            w=[bool(s>>j&1) for j in range(8)]
            for x,y in free_helpers:w.append(w[x] or w[y])
            for o,u,v in gs:w.append((w[u] and w[v]) if o=='and' else (w[u] or w[v]))
            goal=any(s>>u&1 and s>>v&1 for u,v in es)
            if w[ans['output']]!=goal:wrong.append(s)
        assert not wrong
        Path(args.name+'-witness.json').write_text(json.dumps({'graph':d['graph'],'free_helpers':free_helpers,
            'gates':[['or',x,y] for x,y in free_helpers]+gs,'output':ans['output'],
            'size':len(free_helpers)+total,'additional_size':total,'all_rows_checked':256},indent=2))
        print('FOUND',i,total,flush=True);break
    if (i+1)%10==0:print('completed',i+1,'best',min(x['size_with_helper'] for x in results),'seconds',time.monotonic()-start,flush=True)
Path(args.name+'-results.json').write_text(json.dumps({'results':results,'seconds':time.monotonic()-start},indent=2))
print('FINISHED',len(results),'best',min(x['size_with_helper'] for x in results),'seconds',time.monotonic()-start,flush=True)
