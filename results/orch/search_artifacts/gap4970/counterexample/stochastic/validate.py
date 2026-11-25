import argparse
import json
from pathlib import Path

def validate(graph_path,circuit_path):
    g=json.loads(Path(graph_path).read_text());c=json.loads(Path(circuit_path).read_text());n=g['n'];p=g['p'];edges=[tuple(e) for e in g['edges']];gs=c['gates'];out=c['output'];full=(1<<n)-1
    adj=[set() for _ in range(n)]
    for a,b in edges:adj[a].add(b);adj[b].add(a)
    assert all(len(adj[a]&adj[b])<=1 for a in range(n) for b in range(a+1,n))
    tau=min(r.bit_count() for r in range(1<<n) if all((r>>a&1) or (r>>b&1) for a,b in edges));assert tau==g['tau']
    masks=[sum(1<<v for v in ns) for ns in adj];sup=[1<<i for i in range(n)];reach=sup[:];pure=[];centers=[];mixed=0
    for j,(op,a,b) in enumerate(gs):
        assert op in (0,1) and 0<=a<n+j and 0<=b<n+j
        q=(sup[a]|sup[b]) if op else (sup[a]&sup[b]);sup.append(q);reach.append((reach[a]|reach[b]) if op else 0)
        mixed+=bool(op and (reach[-1]&((1<<p)-1)) and (reach[-1]&(full^((1<<p)-1))))
        choices=[v for v in range(n) if q.bit_count()>=2 and q&~masks[v]==0] if op else []
        assert len(choices)<=1;centers.append(choices[0] if choices else None);pure.append(bool(choices))
    errors=0
    for row in range(1<<n):
        w=[bool(row>>i&1) for i in range(n)]
        for j,(op,a,b) in enumerate(gs):
            w.append((w[a] or w[b]) if op else (w[a] and w[b]))
            if pure[j] and w[-1]!=bool(row&sup[n+j]):pure[j]=False
        target=any((row>>a&1) and (row>>b&1) for a,b in edges)
        errors+=((w[out] if 0<=out<len(w) else False)!=target)
    witnesses=[{'gate':j,'center':centers[j],'support':[i for i in range(n) if sup[n+j]>>i&1]} for j in range(len(gs)) if pure[j]]
    missing=[e for e in edges if not any((s['center']==e[0] and e[1] in s['support']) or (s['center']==e[1] and e[0] in s['support']) for s in witnesses)]
    result={'graph':g['name'],'circuit':str(circuit_path),'gates':len(gs),'full_rows_checked':1<<n,'wrong_rows':errors,'tCount':mixed,'missing_star_edges':missing,'witnesses':witnesses,'tau':tau,'posted_bound':len(edges)+tau-1,'is_counterexample':errors==0 and mixed==0 and not missing and len(gs)<len(edges)+tau-1}
    return result

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('graph');ap.add_argument('circuits',nargs='+');ap.add_argument('--output',required=True);a=ap.parse_args();results=[validate(a.graph,c) for c in a.circuits];Path(a.output).write_text(json.dumps(results,indent=2)+'\n')
    for r in results:print(r['graph'],r['gates'],'gates; wrong',r['wrong_rows'],'T',r['tCount'],'missing',len(r['missing_star_edges']),'COUNTEREXAMPLE',r['is_counterexample'])
