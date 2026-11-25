"""Exact finite graph diagnostics; no circuit lower bound is claimed."""
import itertools
import json
from pathlib import Path

EDGES = {(0,1),(0,4),(0,5),(1,2),(1,6),(2,3),(2,7),(3,4),(3,8),(4,9),(5,7),(5,8),(6,8),(6,9),(7,9)}
ADJ = {(a,b) for e in EDGES for a,b in (e,e[::-1])}

def automorphisms():
    def extend(p, unused):
        if not unused:
            yield tuple(p)
            return
        u=len(p)
        for v in sorted(unused):
            if all(((u,w) in ADJ)==((v,p[w]) in ADJ) for w in range(u)):
                yield from extend(p+[v],unused-{v})
    return list(extend([],set(range(10))))

def details(removed):
    old=[v for v in range(10) if v not in removed]
    index={v:i for i,v in enumerate(old)}
    edges=sorted((index[a],index[b]) for a,b in EDGES if a in index and b in index)
    n=len(old)
    edge_masks=[(1<<a)|(1<<b) for a,b in edges]
    independent={s for s in range(1<<n) if all(s&e!=e for e in edge_masks)}
    alpha=max(map(int.bit_count,independent))
    maximum=sorted(s for s in independent if s.bit_count()==alpha)
    maximal=sorted(s for s in independent if all(s|(1<<v) not in independent for v in range(n) if not(s>>v&1)))
    seen={0}
    while True:
        new=seen|{b for a,b in edges if a in seen}|{a for a,b in edges if b in seen}
        if new==seen: break
        seen=new
    graph_edges={frozenset(e) for e in edges}
    cycles={}
    for size in range(3,n+1):
        found=set()
        for start in range(n):
            def walk(path):
                if len(path)==size:
                    if frozenset((path[-1],start)) in graph_edges:
                        cycle=tuple(path)
                        rev=(start,)+tuple(reversed(path[1:]))
                        found.add(min(cycle,rev))
                    return
                for nxt in range(start+1,n):
                    if nxt not in path and frozenset((path[-1],nxt)) in graph_edges:
                        walk(path+[nxt])
            walk([start])
        if found: cycles[str(size)]=len(found)
    assert len(seen)==n and '3' not in cycles and '4' not in cycles
    return {'removed':sorted(removed),'old_vertices':old,'n':n,'edges':edges,'edge_count':len(edges),
      'vertex_cover_number':n-alpha,'minimum_cover':[v for v in range(n) if not(maximum[0]>>v&1)],
      'maximum_independent_masks':maximum,'maximal_independent_masks':maximal,
      'degrees':[sum(v in e for e in edges) for v in range(n)],'cycle_counts':cycles,
      'star_DNF_gate_upper_bound':len(edges)+n-alpha-1,
      'scope':'Exact finite combinatorics and constructive star-DNF upper bound only; no minimum-circuit lower bound.'}

autos=automorphisms()
assert len(autos)==120
remaining={tuple(s) for k in (1,2) for s in itertools.combinations(range(10),k)}
orbits=[]
while remaining:
    representative=min(remaining,key=lambda s:(len(s),s))
    orbit={tuple(sorted(p[v] for v in representative)) for p in autos}
    assert orbit<=remaining
    remaining-=orbit
    data=details(representative)
    data['deleted_set_orbit']=sorted(orbit)
    data['orbit_size']=len(orbit)
    orbits.append(data)
assert sorted(o['orbit_size'] for o in orbits)==[10,15,30]
report={'automorphism_count':len(autos),'deleted_set_count':55,'classes':orbits,
  'preferred_new_core':'Deleting adjacent vertices gives an 8-vertex 10-edge K4 subdivision; four subdivided edges and two unsubdivided opposite edges. Try 12 total gates against a 13-gate star control.',
  'nonadjacent_note':'Deleting two nonadjacent vertices leaves one leaf; deleting that leaf gives theta(2,3,3), already searched.'}
Path('results/meta2448/petersen-deletions.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
