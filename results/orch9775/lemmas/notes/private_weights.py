"""Generate exact ValidPrivate/cost_one/cost_two witnesses for the target graph."""
import collections
import itertools
import json
import argparse
from pathlib import Path
from core_analysis import EDGES

N=14;ALL=(1<<N)-1
NB=[sum(1<<(v if u==i else u) for u,v in EDGES if i in (u,v)) for i in range(N)]


def members(s): return [i for i in range(N) if s>>i&1]
def neighborhood(s):
    ans=0
    for i in members(s):ans|=NB[i]
    return ans
def independent(s):return all(not(NB[i]&s) for i in members(s))
def packpoint(i,j=0,x=0,y=0,z=0):return i|(j<<4)|(x<<8)|(y<<12)|(z<<16)


def geometry(T,extended_two=False):
    ts=members(T);out={(0,0):0}
    for i in range(N):
        for x,y in itertools.combinations([x for x in ts if NB[i]>>x&1],2):
            out.setdefault((1,1<<i),packpoint(i,0,x,y))
    if len(ts)==3 or (extended_two and len(ts)>3):
        for x,y,z in itertools.permutations(ts,3):
            for i in range(N):
                if not(NB[i]>>x&1 and NB[i]>>y&1):continue
                for j in range(N):
                    if NB[j]>>x&1 and NB[j]>>z&1:
                        out.setdefault((2,(1<<i)|(1<<j)),packpoint(i,j,x,y,z))
    return [(m,r,p) for (m,r),p in out.items()]


def validate(row,extended_two=False):
    K,T,J,k,m,p,a=row
    assert independent(K) and J&K==J
    assert k+T.bit_count() <= J.bit_count()+m
    assert J & neighborhood(T)==J
    for f in members(T):
        A=(a>>(14*f))&ALL
        assert independent(A) and (T&~(1<<f))&A==T&~(1<<f)
        assert NB[f]&A
        assert all(NB[i]&A for i in members(J))
    i,j,x,y,z=[(p>>(4*b))&15 for b in range(5)]
    if m:
        assert K>>i&1 and NB[i]>>x&1 and NB[i]>>y&1
        assert T>>x&1 and T>>y&1 and x!=y
    if m==2:
        assert K>>j&1 and NB[j]>>x&1 and NB[j]>>z&1
        assert (T.bit_count()==3 or (extended_two and T.bit_count()>3)) and T>>z&1 and len({x,y,z})==3


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--max-t',type=int,default=3)
    parser.add_argument('--extended-two',action='store_true')
    args=parser.parse_args()
    inds=[s for s in range(1<<N) if independent(s)]
    indset=set(inds)
    mis=[s for s in inds if all((s>>i&1) or NB[i]&s for i in range(N))]
    coverage={s:neighborhood(s) for s in mis}
    best={}
    tested=0;valid=0
    for size in range(1,args.max_t+1):
        for ts in itertools.combinations(range(N),size):
            T=sum(1<<i for i in ts);nt=neighborhood(T)
            options={f:[A for A in mis if (T&~(1<<f))&A==T&~(1<<f) and NB[f]&A] for f in ts}
            if any(not options[f] for f in ts):continue
            geoms=geometry(T,args.extended_two)
            for J in inds:
                if J&nt!=J:continue
                tested+=1
                witnesses={}
                for f in ts:
                    A=next((A for A in options[f] if J&coverage[A]==J),None)
                    if A is None:break
                    witnesses[f]=A
                if len(witnesses)!=size:continue
                valid+=1
                packed=sum(A<<(14*f) for f,A in witnesses.items())
                for m,R,p in geoms:
                    K=J|R;k=J.bit_count()+m-size
                    if k<=0 or K not in indset:continue
                    row=(K,T,J,k,m,p,packed)
                    if K not in best or k>best[K][3]:best[K]=row
    rows=sorted(best.values(),key=lambda r:(r[0].bit_count(),r[0],-r[3]))
    for row in rows:validate(row,args.extended_two)
    # Remove a row already implied with at least the same weight by a smaller key.
    irredundant=[]
    for row in rows:
        if not any(old[0]&row[0]==old[0] and old[3]>=row[3] for old in irredundant):irredundant.append(row)
    profiles=[]
    for K in inds:
        w=max([r[3] for r in irredundant if r[0]&K==r[0]]+[0])
        profiles.append({'mask':K,'card':K.bit_count(),'private_weight':w,'Bplus_floor':N-K.bit_count()+w})
    survivors={str(cap):[p['mask'] for p in profiles if p['Bplus_floor']<=cap] for cap in [9,10,11]}
    result={'semantics':'finite ValidPrivate+cost_one/two witnesses; no Lean claim yet',
            'neighbors':NB,'independent_count':len(inds),'maximal_independent_sets':mis,
            'tested_T_J':tested,'valid_T_J':valid,'all_best_rows':rows,
            'irredundant_rows':irredundant,'profiles':profiles,'survivors':survivors}
    suffix=('' if args.max_t==3 else f'_T{args.max_t}')+('_extended2' if args.extended_two else '')
    path=Path(__file__).with_name('private_weights'+suffix+'.json');path.write_text(json.dumps(result,indent=2)+'\n')
    lean=Path(__file__).with_name('private_weights_generated'+suffix+'.txt')
    lean.write_text('def weightSpecs : List WeightSpec := [\n'+',\n'.join(
        f'({K},{T},{J},{k},{m},{hex(p)},{hex(a)})' for K,T,J,k,m,p,a in irredundant)+']\n\n'+
        'def weights : List (Nat × Nat) := ['+','.join(f'({r[0]},{r[3]})' for r in irredundant)+']\n')
    print(json.dumps({'independent':len(inds),'MIS':len(mis),'weights':len(rows),
                      'irredundant':len(irredundant),'survivor_counts':{k:len(v) for k,v in survivors.items()},
                      'survivors':survivors,'path':str(path)}))


if __name__=='__main__':main()
