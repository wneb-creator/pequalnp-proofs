import argparse, itertools, json, sys
from pathlib import Path

sys.path.insert(0, '/tmp/oec/pequalnp-pilot-31/search')
from synth import CNF

p=argparse.ArgumentParser()
p.add_argument('graph');p.add_argument('--shared',type=int,required=True)
p.add_argument('--local',default='7,6,6');p.add_argument('--fixed-pairs',action='store_true')
p.add_argument('--out',required=True);a=p.parse_args()
budgets=list(map(int,a.local.split(',')));assert len(budgets)==3
graph=json.loads(Path(a.graph).read_text());n=graph['n'];es={tuple(sorted(e)) for e in graph['edges']}
adj={i:{j for j in range(n) if tuple(sorted((i,j))) in es} for i in range(n)}
A=sorted(i for i in range(n) if len(adj[i])==3)
C=sorted(set().union(*(adj[i] for i in A)))
B=sorted(set(range(n))-set(A)-set(C))
cnf=CNF()
def const(b):
    v=cnf.var();cnf.clause(v if b else -v);return v
def synth(vals,k,rows,fix=None):
    gates=[]
    for z in range(k):
        m=len(vals);ls=[cnf.var() for _ in range(m)];rs=[cnf.var() for _ in range(m)];op=cnf.var()
        cnf.onehot(ls);cnf.onehot(rs)
        for i in range(m):
            for j in range(i+1):cnf.clause(-ls[i],-rs[j])
        if fix is not None:
            l,r=fix[z];cnf.clause(ls[l]);cnf.clause(rs[r]);cnf.clause(op)
        elif gates:
            _,oldrs,_=gates[-1]
            for i,u in enumerate(oldrs):
                for j,v in enumerate(rs):
                    if i>j:cnf.clause(-u,-v)
        out=[]
        for row in range(rows):
            l,r,y=cnf.var(),cnf.var(),cnf.var();out.append(y)
            for i in range(m):cnf.equiv(l,vals[i][row],ls[i]);cnf.equiv(r,vals[i][row],rs[i])
            cnf.clause(op,-y,l);cnf.clause(op,-y,r);cnf.clause(op,y,-l,-r)
            cnf.clause(-op,y,-l);cnf.clause(-op,y,-r);cnf.clause(-op,-y,l,r)
        vals.append(out);gates.append([ls,rs,op])
    return gates
shared_vals=[[const(row>>i&1) for row in range(16)] for i in range(4)]
fix=list(itertools.combinations(range(4),2)) if a.fixed_pairs else None
if fix is not None:assert a.shared==6
shared=synth(shared_vals,a.shared,16,fix)
locals=[];aux_pair=None
for z,b in enumerate(B):
    cp,cq=sorted(adj[b]&set(C));vertices=A+[cp,cq,b]
    edges=[(i,j) for i in range(7) for j in range(i) if tuple(sorted((vertices[i],vertices[j]))) in es]
    independent=lambda row:not any(row>>i&1 and row>>j&1 for i,j in edges)
    positives={(1<<i)|(1<<j) for i,j in edges}
    negatives={row for row in range(128) if independent(row) and all(not independent(row|(1<<i)) for i in range(7) if not(row>>i&1))}
    rowset=positives|negatives
    if z==0:
        ai=min(i for i in range(4) if vertices[i] in adj[cp]);ci=4
        aux_pair=[vertices[ai],cp]
        assert not (adj[vertices[ai]]&adj[cp])
        rowset|={1<<ai,1<<ci,127^((1<<ai)|(1<<ci))}
    rows=sorted(rowset)
    vals=[[const(row>>i&1) for row in rows] for i in range(7)]
    vals.extend([[shared_vals[4+h][row&15] for row in rows] for h in range(a.shared)])
    gates=synth(vals,budgets[z],len(rows))
    if z==0:
        main_sel=[cnf.var() for _ in gates];aux_sel=[cnf.var() for _ in gates]
        cnf.onehot(main_sel);cnf.onehot(aux_sel)
        for k in range(len(gates)):
            for row,v in zip(rows,vals[7+a.shared+k]):
                main=not independent(row);aux=bool(row>>ai&1 or row>>ci&1)
                cnf.clause(-main_sel[k],v if main else -v)
                cnf.clause(-aux_sel[k],v if aux else -v)
    else:
        main_sel=aux_sel=None
        for row,v in zip(rows,vals[-1]):cnf.clause(v if row in positives else -v)
    locals.append({'vertices':vertices,'gates':gates,'rows':rows,'main_sel':main_sel,'aux_sel':aux_sel})
out=Path(a.out);budget=a.shared+sum(budgets)+7
out.write_text(f'p cnf {cnf.n} {len(cnf.cs)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in cnf.cs))
out.with_suffix('.json').write_text(json.dumps({'n':n,'edges':sorted(es),'A':A,'B':B,'C':C,
    'shared':shared,'locals':locals,'budget':budget,'aux_pair':aux_pair,
    'variables':cnf.n,'clauses':len(cnf.cs)}))
print(json.dumps({'budget':budget,'shared':a.shared,'locals':budgets,'aux_pair':aux_pair,
    'variables':cnf.n,'clauses':len(cnf.cs)}),flush=True)
