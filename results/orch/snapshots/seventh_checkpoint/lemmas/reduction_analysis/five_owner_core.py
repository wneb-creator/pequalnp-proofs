import json
from pathlib import Path
from itertools import combinations

HERE = Path(__file__).resolve().parent
ROWS = [0, 1, 2, 5, 7]
INPUT_ORIGINAL = [0, 1, 2, 5, 7, 13, 14, 15, 16, 17, 19, 20, 21, 22, 24, 25]
NEIGHBORS = [
    [13,14,16,22], [13,15,21,25], [14,20,24,25],
    [13,19,23,24], [18,22,23,25], [17,21,22,24],
    [16,20,21,23], [15,19,20,22], [14,18,19,21],
    [13,17,18,20], [16,17,19,25], [15,16,18,24], [14,15,17,23],
]


def normalize(terms):
    result = []
    for term in sorted(set(terms), key=lambda term: (len(term), tuple(sorted(term)))):
        if not any(small <= term for small in result):
            result.append(term)
    return frozenset(result)


def forms(n, gates):
    wires = [frozenset([frozenset([i])]) for i in range(n)]
    depth = [0] * n
    for op, a, b in gates:
        assert op in [0,1] and 0 <= a < len(wires) and 0 <= b < len(wires)
        wires.append(normalize(wires[a] | wires[b]) if op == 1 else
                     normalize(u | v for u in wires[a] for v in wires[b]))
        depth.append(max(depth[a], depth[b]) + (op == 0))
    return wires, depth


def assemble(gates, output=None):
    n = len(INPUT_ORIGINAL)
    if output is None:
        output = n + len(gates) - 1
    assert 0 <= output < n + len(gates)
    full = []
    remap = dict(enumerate(INPUT_ORIGINAL))
    for k, (op,a,b) in enumerate(gates):
        assert op in [0,1] and 0 <= a < n+k and 0 <= b < n+k
        full.append([op, remap[a], remap[b]])
        remap[n+k] = 26+k
    out = remap[output]
    for point in range(13):
        if point in ROWS:
            continue
        lines = NEIGHBORS[point]
        s = lines[0]
        for line in lines[1:]:
            full.append([1,s,line])
            s = 26+len(full)-1
        full.append([0,point,s])
        row = 26+len(full)-1
        full.append([1,out,row])
        out = 26+len(full)-1
    assert len(full) == len(gates)+40
    return full, out


def extract(full):
    wf, depth = forms(26, full)
    pointset = set(range(13))
    target = lambda points: frozenset(frozenset([point,line])
                                    for point in points for line in NEIGHBORS[point])
    pairtarget = target([1,2])
    pair = max(w for w in range(26,len(wf)) if pairtarget <= wf[w] and
                all(term & pointset <= {1,2} for term in wf[w]))
    roots = [pair] + [next(w for w in range(26,len(wf)) if wf[w] == target([point]))
                     for point in [0,5,7]]
    used = set()
    pending = list(roots)
    while pending:
        w = pending.pop()
        if w < 26 or w in used:
            continue
        used.add(w)
        pending.extend(full[w-26][1:])
    remap = {v:i for i,v in enumerate(INPUT_ORIGINAL)}
    gates = []
    for w in sorted(used):
        op,a,b = full[w-26]
        gates.append([op,remap[a],remap[b]])
        remap[w] = 16+len(gates)-1
    out = remap[roots[0]]
    for w in roots[1:]:
        gates.append([1,out,remap[w]])
        out = 16+len(gates)-1
    f, d = forms(16,gates)
    localtarget = frozenset(frozenset([INPUT_ORIGINAL.index(point),INPUT_ORIGINAL.index(line)])
                            for point in ROWS for line in NEIGHBORS[point])
    assert localtarget <= f[out]
    extra = sorted(sorted(term) for term in f[out]-localtarget)
    assert all(len(term)==2 for term in extra)
    assembled, assembledout = assemble(gates,out)
    assembledforms,_ = forms(26,assembled)
    assert assembledforms[assembledout] == wf[-1]
    return dict(inputs=16,input_original=INPUT_ORIGINAL,rows=ROWS,gates=gates,output=out,
                and_count=sum(op==0 for op,_,_ in gates),and_depth=d[out],
                source_roots_full=roots,source_internal_gates=len(used),
                extra_edges=extra,extra_edges_original=[[INPUT_ORIGINAL[i] for i in term] for term in extra],
                target_met=not extra,assembled_gate_count=len(assembled),
                verification='Exact antichain DNF; all20 target edges, only listed quadratic extras; completed function equals source full function.')


def main():
    sources = [
      ('filtered23',HERE.parent/'lean_baseline/sat/full63_filtered_5extra_seed.json'),
      ('algebraic5extra22',HERE/'full62_algebraic_5extra_seed.json'),
      ('algebraic4extra23',HERE/'full63_algebraic_4extra_seed.json'),
      ('shared4extra22',HERE/'full62_shared_rows_4extra_seed.json'),
      ('shared2extra23',HERE/'full63_shared_rows_2extra_seed.json'),
    ]
    report=[]
    for name, source in sources:
        full=json.loads(source.read_text())
        assert isinstance(full,list)
        case=extract(full)
        name='five_owner_'+name+'_seed.json'
        (HERE/name).write_text(json.dumps(case,indent=2)+'\n')
        report.append({'file':name,'size':len(case['gates']),'and_count':case['and_count'],
                       'and_depth':case['and_depth'],'extras':case['extra_edges_original']})
    edges={(u,v) for u in ROWS for v in NEIGHBORS[u]}
    lines=set(INPUT_ORIGINAL)-set(ROWS)
    negative_sets=set()
    for mask in range(32):
        points={ROWS[i] for i in range(5) if mask>>i&1}
        neighbors={v for u,v in edges if u in points}
        closure={u for u in ROWS if set(NEIGHBORS[u])<=neighbors}
        negative_sets.add(frozenset(closure | (lines-neighbors)))
    assert len(negative_sets)==30
    negatives=sorted(sum(1<<INPUT_ORIGINAL.index(i) for i in U) for U in negative_sets)
    census=[]
    for u,v in combinations(INPUT_ORIGINAL,2):
        if (u,v) in edges or (v,u) in edges:
            continue
        count=sum({u,v}<=U for U in negative_sets)
        census.append({'original':[u,v],'local':[INPUT_ORIGINAL.index(u),INPUT_ORIGINAL.index(v)],
                       'maximal_negative_extensions':count})
    data={'input_original':INPUT_ORIGINAL,'rows':ROWS,'negative_masks':negatives,
          'negative_count':30,'independent_pair_census':census,
          'five_and_dirty_pair_exceptions':[x for x in census if x['maximal_negative_extensions']<=2],
          'singleton_minimum_extensions':min(sum({u}<=U for U in negative_sets) for u in INPUT_ORIGINAL),
          'scope':'Under an exact5-AND core, weighted packing allows at most2 total equal-child incidences over30 negatives. Every AND is false on singleton inputs and independent pairs outside the exception list. This census is computational data, not a Lean proof.'}
    (HERE/'five_owner_pair_extension_census.json').write_text(json.dumps(data,indent=2)+'\n')
    (HERE/'five_owner_extraction.validation.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__=='__main__':
    main()
