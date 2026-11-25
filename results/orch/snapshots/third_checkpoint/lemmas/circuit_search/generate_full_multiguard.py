import itertools
import json
import pathlib
import random
import runpy

HERE = pathlib.Path(__file__).resolve().parent
shared = runpy.run_path(str(HERE/'generate_full_guard_seeds.py'))
Builder = shared['Builder']
edges, signatures, target = shared['edges'], shared['signatures'], shared['target']
guardmask, maxnegmask, pairmask = (shared[k] for k in ('guardmask','maxnegmask','pairmask'))
seeds=[]
rng=random.Random(65063)
for side in range(2):
    owners=list(range(13)) if side==0 else list(range(13,26))
    neighbors={p:{b if a==p else a for a,b in edges if p in (a,b)} for p in owners}
    for group in itertools.chain(itertools.combinations(owners,5),itertools.combinations(owners,6)):
        pairs=list(itertools.combinations(group,2))
        rng.shuffle(pairs)
        for guarded in pairs[:2]:
            builder=Builder()
            common=set(group)-set(guarded)
            builder.union(common)
            guards=[]
            for p in guarded:
                a=builder.union(set(group)-{p})
                b=builder.union(neighbors[p])
                guards.append(builder.gate(1,a,b))
            merged=builder.gate(0,builder.union(group),builder.union(set().union(*(neighbors[p] for p in group))))
            for guard in guards:merged=builder.gate(0,merged,guard)
            terms=[merged]
            for p in owners:
                if p not in group:terms.append(builder.gate(0,p,builder.union(neighbors[p])))
            output=terms[0]
            for term in terms[1:]:output=builder.gate(1,output,term)
            gates=builder.compact(output)
            if len(gates)>63:continue
            values=signatures.copy()
            for op,a,b in gates:values.append(values[a]|values[b] if op else values[a]&values[b])
            result=values[-1]
            assert result&target==target and result&guardmask==0
            a,b=guarded
            cubic_lines=set().union(*(neighbors[p] for p in group))-neighbors[a]-neighbors[b]
            assert cubic_lines
            # The two guarded owners plus each such opposite vertex form an added cubic.
            for l in cubic_lines:
                for selected,expected in [({a,b,l},1),({a,l},0),({b,l},0)]:
                    v=[int(i in selected) for i in range(26)]
                    for op,x,y in gates:v.append(v[x]|v[y] if op else v[x]&v[y])
                    assert v[-1]==expected
            seeds.append(dict(side=side,group=group,guarded=guarded,gates=gates,output=25+len(gates),
                              size=len(gates),genuine_cubics=[[a,b,l] for l in sorted(cubic_lines)],
                              maximal_negative_errors=(result&maxnegmask).bit_count(),
                              nonedge_errors=(result&pairmask).bit_count()))
(HERE/'full-multiguard-seeds.json').write_text(json.dumps(seeds))
with (HERE/'full-multiguard-seeds.txt').open('w') as f:
    f.write(f'{len(seeds)}\n')
    for seed in seeds:
        gates=seed['gates'].copy()
        while len(gates)<63:
            output=25+len(gates);gates.append([0,output,output])
        f.write(f'{len(gates)}\n')
        for gate in gates:f.write(' '.join(map(str,gate))+'\n')
summary=dict(seeds=len(seeds),minimum_size=min((s['size'] for s in seeds),default=None),
             minimum_pairs=min((s['nonedge_errors'] for s in seeds),default=None),
             minimum_maximal_negatives=min((s['maximal_negative_errors'] for s in seeds),default=None))
(HERE/'full-multiguard-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(summary)
