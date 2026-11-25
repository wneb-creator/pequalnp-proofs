"""Alternate actual-K optimization checks the generated subset-key coverage."""
import itertools
import json
from pathlib import Path
from private_weights import N,ALL,NB,members,independent,neighborhood


def main():
    root=Path(__file__).resolve().parent
    saved=json.loads((root/'private_weights.json').read_text())
    inds=[s for s in range(1<<N) if independent(s)]
    mis=[s for s in inds if all(s>>i&1 or NB[i]&s for i in range(N))]
    Ts=[]
    for size in range(1,4):
        for xs in itertools.combinations(range(N),size):
            t=sum(1<<x for x in xs)
            options=[[A for A in mis if (t&~(1<<f))&A==t&~(1<<f) and NB[f]&A] for f in xs]
            if any(not os for os in options):continue
            valid=[]
            for J in inds:
                if J&neighborhood(t)!=J:continue
                if all(any(all(NB[j]&A for j in members(J)) for A in os) for os in options):valid.append(J)
            Ts.append((t,size,valid))
    actual=[]
    for K in inds:
        strongest=0
        for T,size,Js in Ts:
            pairsets={NB[i]&T for i in members(K) if (NB[i]&T).bit_count()>=2}
            m=int(bool(pairsets))
            if size==3 and any(a|b==T for a in pairsets for b in pairsets):m=2
            jmax=max((J.bit_count() for J in Js if J&K==J),default=-100)
            strongest=max(strongest,jmax+m-size)
        actual.append((K,strongest))
    expected={r['mask']:r['private_weight'] for r in saved['profiles']}
    errors=[(K,w,expected[K]) for K,w in actual if expected[K]!=w]
    report={'actual_K_count':len(actual),'T_count':len(Ts),
            'mismatches':errors,'complete_for_T_sizes':[1,2,3],
            'independent_validation':'For each actualK directlymaximizeJsubsetK;geometryusesallKvertices'}
    (root/'private_weights_coverage.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report))
    assert not errors


if __name__=='__main__':main()
