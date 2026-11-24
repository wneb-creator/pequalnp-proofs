import itertools,json,sys,time
from pathlib import Path

start=time.monotonic()
for modelpath in sys.argv[1:]:
    model=json.loads(Path(modelpath).read_text());n=model['n'];gates=model['gates'];output=model['output']
    es={tuple(sorted(e)) for e in model['edges']};adj=[set() for _ in range(n)]
    for a,b in es:adj[a].add(b);adj[b].add(a)
    inputs=[sum(1<<row for row in range(1<<n) if row>>i&1) for i in range(n)]
    target=0
    for a,b in es:target|=inputs[a]&inputs[b]
    safe={inputs[a]|inputs[b]:(a,b) for a,b in itertools.combinations(range(n),2) if not(adj[a]&adj[b])}
    def evaluate(cut=-1,change=None):
        vals=inputs.copy()
        for j,g in enumerate(gates):
            op,a,b=change if j==cut else g
            vals.append(vals[a]&vals[b] if op=='and' else vals[a]|vals[b])
        return vals
    vals=evaluate();assert vals[output]==target
    original=[(i,safe[v]) for i,v in enumerate(vals) if v in safe]
    print(json.dumps({'model':modelpath,'gates':len(gates),'safe_pairs':len(safe),'original_safe_or_wires':original}),flush=True)
    if original:continue
    attempts=0;equal_main=0
    for cut in range(len(gates)):
        seen=set()
        for a in range(n+cut):
            for b in range(a,n+cut):
                for op in ['and','or']:
                    v=vals[a]&vals[b] if op=='and' else vals[a]|vals[b]
                    if v==vals[n+cut] or v in seen:continue
                    seen.add(v);attempts+=1
                    new=evaluate(cut,[op,a,b])
                    if new[output]!=target:continue
                    equal_main+=1
                    matches=[(i,safe[v]) for i,v in enumerate(new) if v in safe]
                    if matches:
                        w,pair=matches[0];model['gates'][cut]=[op,a,b]
                        model['aux_wire']=w;model['aux_pair']=pair
                        out=Path(modelpath).with_name(Path(modelpath).stem+'-safe-witness.json')
                        out.write_text(json.dumps(model,indent=2))
                        print('WITNESS',out,'cut',cut,'new',op,a,b,'aux',w,pair,flush=True);sys.exit(0)
    print(json.dumps({'attempts':attempts,'equal_main_rewrites':equal_main,'elapsed':time.monotonic()-start}),flush=True)
