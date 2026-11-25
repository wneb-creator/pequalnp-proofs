"""Direct graph-isomorphism comparison with the new L_meta_9774 graph."""
import collections
import json
from pathlib import Path
from core_analysis import EDGES

UPSTREAM=(EDGES-{(1,9)})|{(2,12)}


def graph(edges,deleted=()):
    nodes=[i for i in range(14) if i not in deleted]
    return {i:{v if i==u else u for u,v in edges if i in (u,v)
               and u not in deleted and v not in deleted} for i in nodes}


def iso(a,b):
    ca={x:len(a[x]) for x in a};cb={x:len(b[x]) for x in b}
    for _ in a:
        sa={x:(ca[x],tuple(sorted(ca[y] for y in a[x]))) for x in a}
        sb={x:(cb[x],tuple(sorted(cb[y] for y in b[x]))) for x in b}
        if collections.Counter(sa.values()) != collections.Counter(sb.values()):return None
        labels={s:i for i,s in enumerate(sorted(set(sa.values())|set(sb.values())))}
        na={x:labels[s] for x,s in sa.items()};nb={x:labels[s] for x,s in sb.items()}
        if na==ca and nb==cb:break
        ca,cb=na,nb
    mapping={};used=set()
    def go():
        if len(mapping)==len(a):return dict(mapping)
        x=min((v for v in a if v not in mapping),key=lambda v:
              (sum(cb[y]==ca[v] for y in b if y not in used),-len(a[v]&mapping.keys()),-len(a[v])))
        for y in b:
            if y in used or cb[y]!=ca[x]:continue
            if any((u in a[x])!=(v in b[y]) for u,v in mapping.items()):continue
            mapping[x]=y;used.add(y)
            answer=go()
            if answer is not None:return answer
            del mapping[x];used.remove(y)
        return None
    return go()


def distances(a,vertices):
    answer=[]
    for s in vertices:
        d={s:0};q=collections.deque([s])
        while q:
            u=q.popleft()
            for v in a[u]:
                if v not in d:d[v]=d[u]+1;q.append(v)
        answer.extend(d[t] for t in vertices if s<t)
    return sorted(answer)


def main():
    a,b=graph(EDGES),graph(UPSTREAM)
    da=[v for v in a if len(a[v])==2];db=[v for v in b if len(b[v])==2]
    matches=[]
    for u in range(14):
        for v in range(14):
            mapping=iso(graph(EDGES,[u]),graph(UPSTREAM,[v]))
            if mapping is not None:
                matches.append({'delete_target':u,'delete_upstream':v,'mapping':mapping})
    result={'whole_isomorphic':iso(a,b) is not None,
            'target_degree2':da,'upstream_degree2':db,
            'target_degree2_distances':distances(a,da),
            'upstream_degree2_distances':distances(b,db),
            'one_false_cofactor_matches':matches}
    path=Path(__file__).with_suffix('.json')
    path.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result))


if __name__=='__main__':main()
