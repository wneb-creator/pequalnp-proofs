import argparse,json,subprocess,time
from pathlib import Path

p=argparse.ArgumentParser();p.add_argument('--min-cost',type=int,default=2);p.add_argument('--max-cost',type=int,default=3)
p.add_argument('--seconds',type=int,default=180);p.add_argument('--name',required=True)
p.add_argument('--all-signals',action='store_true');p.add_argument('--extra-budget',type=int,default=0)
p.add_argument('--skip',type=int,default=0)
p.add_argument('--seed-file',default='c8-helper-seeds.json')
args=p.parse_args()
base=Path(args.name);base.mkdir(exist_ok=True)
d=json.loads(Path('c8-helper-dp-rows.json').read_text());values=d['values'];rows=d['rows'];es=d['graph']['edges']
seeds=json.loads(Path(args.seed_file).read_text())
seeds=[(i,z) for i,z in enumerate(seeds) if args.min_cost<=z['formula_cost']<=args.max_cost]
seeds=seeds[args.skip:]
start=time.monotonic();results=[];best=1000

def merge(seed,ans):
    wvals=values[:];byval={v:i for i,v in enumerate(wvals)};gs=[]
    def gate(op,a,b):
        v=wvals[a]&wvals[b] if op=='and' else wvals[a]|wvals[b]
        if v in byval:return byval[v]
        k=len(wvals);wvals.append(v);byval[v]=k;gs.append([op,a,b]);return k
    hmap={i:i for i in range(9)}
    for j,(op,a,b) in enumerate(seed['gates']):hmap[9+j]=gate(op,hmap[a],hmap[b])
    qmap={i:i for i in range(9)}
    if args.all_signals:
        for j in range(len(seed['gates'])):qmap[9+j]=hmap[9+j]
    else:qmap[9]=hmap[seed['output']]
    qinputs=9+(len(seed['gates']) if args.all_signals else 1)
    for j,(op,a,b) in enumerate(ans['gates']):qmap[qinputs+j]=gate(op,qmap[a],qmap[b])
    output=qmap[ans['output']];live=set()
    def visit(k):
        if k<9 or k in live:return
        live.add(k);_,a,b=gs[k-9];visit(a);visit(b)
    visit(output);ren={i:i for i in range(9)};final=[]
    for k in sorted(live):
        op,a,b=gs[k-9];ren[k]=9+len(final);final.append([op,ren[a],ren[b]])
    return final,ren[output]

for index,seed in seeds:
    if time.monotonic()-start>args.seconds:break
    cap=10-len(seed['gates'])+args.extra_budget
    inp=base/f'case-{index}.input';out=base/f'case-{index}.json';log=base/f'case-{index}.log'
    extra=[]
    if args.all_signals:
        vs=values[:]
        for op,a,b in seed['gates']:
            v=vs[a]&vs[b] if op=='and' else vs[a]|vs[b]
            vs.append(v);extra.append(v)
    else:extra=[seed['value']]
    inp.write_text(f'{len(rows)} {9+len(extra)} {(1<<len(es))-1} {cap}\n'+' '.join(map(str,values+extra))+'\n')
    with log.open('w') as f:r=subprocess.run(['./formula_dp',str(inp),str(out),'10'],stdout=f,stderr=subprocess.STDOUT)
    if r.returncode:raise RuntimeError((index,r.returncode))
    if not out.exists():
        diagnostic=log.read_text()
        if 'TIME_LIMIT' in diagnostic:status='solver_timeout'
        elif 'NO_ROOT_DECOMPOSITION' in diagnostic:status='no_root_decomposition'
        else:raise RuntimeError(('unexpected missing result',index))
        results.append({'index':index,'helper_cost':len(seed['gates']),'status':status});continue
    ans=json.loads(out.read_text());gs,output=merge(seed,ans);total=len(gs)
    results.append({'index':index,'helper_cost':len(seed['gates']),'size':total,'formula':ans['formula_gates']})
    if total<best:
        best=total;print('BEST',best,'helper',index,'cost',len(seed['gates']),'seconds',time.monotonic()-start,flush=True)
    if total<=10:
        wrong=[]
        for s in range(256):
            w=[bool(s>>j&1) for j in range(8)];w.append(w[0] or w[1])
            for op,a,b in gs:w.append((w[a] and w[b]) if op=='and' else (w[a] or w[b]))
            want=any(s>>a&1 and s>>b&1 for a,b in es)
            if w[output]!=want:wrong.append(s)
        assert not wrong
        Path(args.name+'-witness.json').write_text(json.dumps({'graph':d['graph'],'free_helper':['or',0,1],
            'gates':gs,'output':output,'size':total,'all_rows_checked':256,'seed':seed},indent=2))
        print('FOUND',index,total,flush=True);break
    if len(results)%50==0:
        print('completed',len(results),'of',len(seeds),'best',best,'seconds',time.monotonic()-start,flush=True)
        Path(args.name+'-results.json').write_text(json.dumps({'parameters':vars(args),'results':results,'total_candidates':len(seeds),'seconds':time.monotonic()-start},indent=2))
Path(args.name+'-results.json').write_text(json.dumps({'parameters':vars(args),'results':results,'total_candidates':len(seeds),'seconds':time.monotonic()-start},indent=2))
print('FINISHED',len(results),'of',len(seeds),'best',best,'seconds',time.monotonic()-start,flush=True)
