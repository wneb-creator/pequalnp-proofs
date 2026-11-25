"""Necessary status counts for the affine plane AG(2,3), under the
dominator, carrier, and terminal-marking inequalities. Not a Lean proof."""
from collections import Counter
from itertools import product
import json
from pathlib import Path
from fresh_case_charge import bits, subsets

def affine():
    points=list(product(range(3),repeat=2))
    groups=[[i for i,(x,y) in enumerate(points) if x==a] for a in range(3)]
    groups += [[i for i,(x,y) in enumerate(points) if (y-m*x)%3==a]
               for m in range(3) for a in range(3)]
    groupm=[sum(1<<i for i in g) for g in groups]
    rows=[sum(1<<j for j,g in enumerate(groups) if i in g) for i in range(9)]
    autos=[]
    for a,b,c,d in product(range(3),repeat=4):
        if (a*d-b*c)%3==0:continue
        for x0,y0 in points:
            p=[points.index(((a*x+b*y+x0)%3,(c*x+d*y+y0)%3)) for x,y in points]
            l=[groupm.index(sum(1<<p[i] for i in g)) for g in groups]
            autos.append((p,l))
    return groupm,rows,autos

def masks(per):
    table=[0]*(1<<len(per))
    for x in range(1,len(table)):
        low=x&-x
        table[x]=table[x^low]|(1<<per[low.bit_length()-1])
    return table

def orbitreps(groups,rows,autos):
    pm={};lm={};perms=[]
    for p,l in autos:
        pk=tuple(p);lk=tuple(l)
        if pk not in pm:pm[pk]=masks(p)
        if lk not in lm:lm[lk]=masks(l)
        perms.append((pm[pk],lm[lk]))
    seen=set();reps=[]
    for ip in range(512):
        no=0
        for i in bits(ip):no|=rows[i]
        for il in subsets(4095^no):
            state=(ip,il)
            if state in seen:continue
            orb={(pp[ip],lp[il]) for pp,lp in perms}
            seen.update(orb);reps.append((ip,il,len(orb)))
    return reps

def side_options(eligible,othereligible,neighbors,otherneighbors):
    full=(1<<len(neighbors))-1
    poss=sum(1<<i for i,w in enumerate(neighbors) if not w&~othereligible)
    requirements=[(w&~eligible).bit_count()+int(bool(w&eligible))-1 for w in otherneighbors]
    for present in subsets(poss):
        missing=full^present
        empty=(missing&~eligible).bit_count()
        extra=[max(0,(w&present).bit_count()+int(bool(w&missing))-1-((othereligible>>j)&1)) for j,w in enumerate(otherneighbors)]
        total=sum(extra)
        minimum=max([total]+[req-((othereligible>>j)&1)+total-extra[j] for j,req in enumerate(requirements)])
        yield present,empty,minimum

def evaluate(groups,rows,reps,cap):
    P,L=511,4095
    by=Counter();minb=100;ex=[];paircount=0;eligiblecount=0
    for ip,il,orb in reps:
        ep=P^ip;el=L^il
        used=ep.bit_count()+el.bit_count()
        # Removing one point and a parallel line class is the largest
        # residue possible when every vertex has at most one ineligible neighbor.
        stay=int(bool(ip))+max((il&(7<<(3*i))).bit_count() for i in range(4))
        mark=(ip.bit_count()+il.bit_count()-stay+1)//2
        if used+mark>cap:continue
        popts=Counter((z,max(r,mark)) for p,z,r in side_options(ep,el,rows,groups) if used+z+max(r,mark)<=cap)
        lopts=Counter((z,max(r,mark)) for l,z,r in side_options(el,ep,groups,rows) if used+z+max(r,mark)<=cap)
        cnt=0;best=100
        for (zp,rp),pc in popts.items():
            for (zl,rl),lc in lopts.items():
                v=used+max(zp,zl)+max(rp,rl)
                if v<=cap:cnt+=pc*lc;best=min(best,v)
        if cnt:
            eligiblecount+=orb
            paircount+=orb*cnt
            t=(ip.bit_count(),il.bit_count(),best)
            by[t]+=orb
            if best<minb:minb=best;ex=[]
            if best==minb and len(ex)<5:
                ex.append(dict(ineligible_points=list(bits(ip)),ineligible_lines=list(bits(il)),orbit=orb,minimum_surplus=best,valid_status_pairs=cnt))
    return dict(cap=cap,minimum_surplus=minb,eligible_pairs=eligiblecount,present_status_pairs=paircount,example_eligibility=ex,grouped_eligibility=[(list(t),n) for t,n in sorted(by.items())])

if __name__=='__main__':
    groups,rows,autos=affine();reps=orbitreps(groups,rows,autos)
    result=evaluate(groups,rows,reps,23)
    result.update(group_order=len(autos),eligibility_orbits=len(reps),eligibility_cover_count=sum(size for p,l,size in reps),
        groups=[list(bits(g)) for g in groups])
    print(json.dumps({k:result[k] for k in ('cap','minimum_surplus','eligible_pairs','present_status_pairs','eligibility_orbits','eligibility_cover_count','example_eligibility')},indent=2))
    Path('fresh-affine-charge.json').write_text(json.dumps(result,indent=2)+'\n')
