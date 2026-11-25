"""Finite necessary inequalities for Steiner point/line modules, not a Lean proof."""
from pathlib import Path
import json
from itertools import product

def bits(w):
    while w:
        f=w&-w;yield f.bit_length()-1;w-=f

def subsets(w):
    v=w
    while True:
        yield v
        if not v:return
        v=(v-1)&w

def analyze(r,cap=None):
    k=r['k']; groups=[sum(1<<i for i in s) for s in r['groups']]; b=len(groups)
    rows=[sum(1<<j for j,g in enumerate(groups) if g>>i&1) for i in range(k)]
    assert all(a.bit_count()>=2 for a in rows+groups)
    P=(1<<k)-1;L=(1<<b)-1;E=sum(a.bit_count() for a in groups)
    target=E-b
    cap=target-1 if cap is None else cap
    combos=0; survivors=0; examples=[]
    for ep in range(P+1):
        il_forbidden=0
        for i in bits(P^ep): il_forbidden|=rows[i]
        for el_opt in subsets(L^il_forbidden):
            el=il_forbidden|el_opt
            if ep.bit_count()+el.bit_count()>cap:continue
            poss_p=sum(1<<i for i,a in enumerate(rows) if not a&~el)
            poss_l=sum(1<<j for j,a in enumerate(groups) if not a&~ep)
            pr=[];lr=[]
            for pl in subsets(poss_l):
                ml=L^pl
                cp=sum(max((ep>>i)&1, (w&pl).bit_count()+int(bool(w&ml))-1) for i,w in enumerate(rows))
                eil=(ml&~el).bit_count()
                base=cp+el.bit_count()
                if base+eil<=cap:lr.append((pl,base,eil))
            if not lr:continue
            for pp in subsets(poss_p):
                mp=P^pp
                cl=sum(max((el>>j)&1,(g&pp).bit_count()+int(bool(g&mp))-1) for j,g in enumerate(groups))
                eip=(mp&~ep).bit_count()
                base=cl+ep.bit_count()
                if base+eip<=cap:pr.append((pp,base,eip))
            for p,basep,eip in pr:
                for l,basel,eil in lr:
                    combos+=1;z=max(eip,eil)
                    if max(basep,basel)+z>cap:continue
                    rem=cap-ep.bit_count()-el.bit_count()-z
                    exP=[max(0,(w&l).bit_count()+int(bool(w&(L^l)))-1-((ep>>i)&1)) for i,w in enumerate(rows)]
                    exL=[max(0,(g&p).bit_count()+int(bool(g&(P^p)))-1-((el>>j)&1)) for j,g in enumerate(groups)]
                    fullP=[(w&~el).bit_count()+int(bool(w&el))-1 for w in rows]
                    fullL=[(g&~ep).bit_count()+int(bool(g&ep))-1 for g in groups]
                    if any(req>((ep>>i)&1)+rem-sum(exP)+exP[i] for i,req in enumerate(fullP)):continue
                    if any(req>((el>>j)&1)+rem-sum(exL)+exL[j] for j,req in enumerate(fullL)):continue
                    survivors+=1
                    if len(examples)<10:examples.append(dict(ep=list(bits(ep)),el=list(bits(el)),present_p=list(bits(p)),present_l=list(bits(l)),bound=max(basep,basel)+z))
    return dict(id=r['id'],k=k,lines=b,edges=E,target_surplus=target,under_cap=cap,paired=combos,survivors=survivors,examples=examples)

if __name__=='__main__':
    allresults=[]
    for r in json.loads(Path('fresh-module-catalog.json').read_text()):
        if r['k']<4:continue
        r=r.copy();r['groups']=[g for g in r['groups'] if len(g)>1]
        if not all(sum(i in g for g in r['groups'])>=2 for i in range(r['k'])):continue
        allresults.append(analyze(r))
    for a in allresults:print(a['id'],a['under_cap'],a['survivors'],a['examples'][:1])
    Path('fresh-charge-carrier-catalog.json').write_text(json.dumps(allresults,indent=2))
