from pathlib import Path
import itertools, json

ROOT = Path(__file__).resolve().parents[4]
PACKET = ROOT / 'results/orch/lemmas/status_review/punctured-four-arc.json'
GEOMETRY = ROOT / 'results/orch/lemmas/circuit_search/geometry.json'

def normalize(terms):
    keep = []
    for t in sorted(set(terms), key=lambda x: (x.bit_count(), x)):
        if not any(s & t == s for s in keep):
            keep.append(t)
    return keep

def dnf(gates, n=26):
    wires = [[1 << i] for i in range(n)]
    for op, a, b in gates:
        assert op in (0,1)
        assert 0 <= a < len(wires) and 0 <= b < len(wires)
        wires.append(normalize((x | y for x in wires[a] for y in wires[b])) if op == 0
                     else normalize(wires[a] + wires[b]))
    return wires

def trim(case, gates, output=None):
    n = case['available_inputs']
    out = n + len(gates) - 1 if output is None else output
    assert 0 <= out < n + len(gates)
    for j,(op,a,b) in enumerate(gates):
        assert op in (0,1) and 0 <= a < n+j and 0 <= b < n+j
    needed = set()
    def visit(w):
        if w < n or w in needed:
            return
        assert n <= w < n + len(gates)
        needed.add(w)
        _, a, b = gates[w-n]
        assert a < w and b < w
        visit(a); visit(b)
    visit(out)
    remap = {i:i for i in range(n)}
    compact = []
    for j, gate in enumerate(gates):
        if n+j in needed:
            op, a, b = gate
            remap[n+j] = n+len(compact)
            compact.append([op, remap[a], remap[b]])
    return compact, remap[out]

def build_outside(case, selected=None):
    raw = case['raw_map']; nr = case['raw_inputs']
    selected = {} if selected is None else selected
    features = {tuple(s): nr+i for i,s in enumerate(case['features'])}
    wires = {i:v for i,v in enumerate(raw)}
    gates = []
    def add(op,a,b):
        gates.append([op,a,b]); return 26+len(gates)-1
    terms = []
    choices = []
    for row in case['outside_rows']:
        core = row['core_lines']
        if len(core) == 3:
            group = row['optional_group']
            choice = selected.get(row['owner'], group[0])
            assert choice in group
            pair = case['features'][choice-nr]
            a,b = (raw[i] for i in pair)
            v = add(1,a,b); wires[choice] = v
            third = next(x for x in core if x not in (a,b))
            v = add(1,v,third)
            all_id = features[tuple(sorted(raw.index(x) for x in core))]
            wires[all_id] = v
            choices.append({'owner':row['owner'],'feature':choice})
        elif len(core) == 2:
            v = add(1,*core)
            wires[features[tuple(sorted(raw.index(x) for x in core))]] = v
        else:
            assert len(core) == 1
            v = core[0]
        for line in row['neighbors']:
            if line not in core:
                v = add(1,v,line)
        terms.append(add(0,row['owner'],v))
    outside = terms[0]
    for term in terms[1:]:
        outside = add(1,outside,term)
    points = case['punctured_owners']
    p_or = points[0]
    for p in points[1:]:
        p_or = add(1,p_or,p)
    point_feature = features[tuple(raw.index(x) for x in points)]
    wires[point_feature] = p_or
    partial = add(0,case['punctured_line'],p_or)
    outside = add(1,outside,partial)
    assert len(gates) == case['outside_cost'] == 47
    return gates, wires, outside, choices

def assemble(case, gates, output=None):
    gates, output = trim(case, gates, output)
    n = case['available_inputs']
    used = {w for _,a,b in gates for w in (a,b) if w < n}
    if output < n:
        used.add(output)
    selected = {}
    for row in case['outside_rows']:
        if 'optional_group' in row:
            active = used.intersection(row['optional_group'])
            assert len(active) <= 1, ('incompatible optional prefixes', row['owner'], sorted(active))
            if active:
                selected[row['owner']] = next(iter(active))
    full, wires, outside, choices = build_outside(case, selected)
    for j,(op,a,b) in enumerate(gates):
        assert a in wires and b in wires
        full.append([op,wires[a],wires[b]])
        wires[n+j] = 26+len(full)-1
    full.append([1,outside,wires[output]])
    return {'inputs':26,'gates':full,'output':26+len(full)-1,
            'core_gates':gates,'core_output':output,'choices':choices,
            'core_size':len(gates),'full_size':len(full),
            'scope':'Exact assembler; a15-gate exact core would give63. Calibrations may be larger.'}

def raw_star_seed(case):
    n = case['available_inputs']; gates=[]; terms=[]
    def add(op,a,b):
        gates.append([op,a,b]); return n+len(gates)-1
    for owner in range(len(case['owners'])):
        ls = [v for u,v in case['edges'] if u == owner]
        v=ls[0]
        for w in ls[1:]: v=add(1,v,w)
        terms.append(add(0,owner,v))
    v=terms[0]
    for w in terms[1:]: v=add(1,v,w)
    return gates,v

def audit():
    c=json.loads(PACKET.read_text()); geom=json.loads(GEOMETRY.read_text())
    E={tuple(e) for e in geom['edges']}; CE={tuple(e) for e in c['full_core_edges']}
    OE={tuple(e) for e in c['outside_edges']}
    assert CE.isdisjoint(OE) and CE|OE == E
    assert CE == {(c['raw_map'][u],c['raw_map'][v]) for u,v in c['edges']}
    supports=[sum(1<<i for i in s) for s in c['features']]
    edge_masks=[(1<<u)|(1<<v) for u,v in c['edges']]
    value=lambda U:any(U&e==e for e in edge_masks)
    encode=lambda U:sum(bool(U&s)<<j for j,s in enumerate(supports))
    for w in c['raw_pivotal_witnesses']:
        assert w['high'] == w['low'] | (1<<w['raw'])
        assert w['low'] ^ w['high'] == 1<<w['raw']
        assert not value(w['low']) and value(w['high'])
        assert encode(w['low']) == encode(w['high']) == w['fixed_feature_values']
    negatives=[]
    for U in range(1<<c['raw_inputs']):
        if not value(U) and all(value(U|1<<v) for v in range(c['raw_inputs']) if not U>>v&1):
            negatives.append(U)
    assert negatives == c['maximal_negatives']
    groups=[r for r in c['outside_rows'] if 'optional_group' in r]
    count=0
    for choices in itertools.product(*(r['optional_group'] for r in groups)):
        selected={r['owner']:v for r,v in zip(groups,choices)}
        gs, fm, out, _=build_outside(c,selected); ds=dnf(gs)
        assert set(ds[out]) == {(1<<u)|(1<<v) for u,v in OE}
        for logical,wire in fm.items():
            supp=[c['raw_map'][logical]] if logical<c['raw_inputs'] else [c['raw_map'][v] for v in c['features'][logical-c['raw_inputs']]]
            assert set(ds[wire]) == {1<<v for v in supp}
        count+=1
    gs,out=raw_star_seed(c); result=assemble(c,gs,out); ds=dnf(result['gates'])
    assert len(gs)==17 and result['full_size']==65
    assert set(ds[result['output']]) == {(1<<u)|(1<<v) for u,v in E}
    direct_outputs=0
    for group in c['optional_groups']:
        for f in group:
            z=assemble(c,[],f); zz=dnf(z['gates'])
            want={(1<<u)|(1<<v) for u,v in OE}|{1<<c['raw_map'][v] for v in c['features'][f-c['raw_inputs']]}
            assert set(zz[z['output']]) == set(normalize(want))
            direct_outputs+=1
    invalid_cases=[([[2,0,1]],None), ([[0,-1,0]],None), ([[0,c['available_inputs'],0]],None), ([], -1), ([],c['available_inputs'])]
    for gg,oo in invalid_cases:
        try: assemble(c,gg,oo)
        except AssertionError: pass
        else: raise AssertionError(('invalid input accepted',gg,oo))
    dest=Path(__file__).parent
    (dest/'punctured-four-arc-calibration65.json').write_text(json.dumps(result,indent=2)+'\n')
    report={'scope':'Independent finite/data/assembler audit; no proof or15-gate witness.',
            'core_edges':len(CE),'outside_edges':len(OE),'raw_inputs':13,'maximal_negatives':len(negatives),
            'pivotal_witnesses_checked':13,'compatible_prefix_choices_audited':count,'direct_optional_outputs_checked':direct_outputs,'invalid_cases_rejected':len(invalid_cases),
            'outside_gates':47,'exact_calibration_core_gates':17,'exact_calibration_full_gates':65,
            'target_core_gates':15,'necessary_distinct_features_at_target':3,
            'three_features_force_paid_cone_tree':True,
            'relation_to_previous_model':'Subclass of full four-owner18 core by moving pointOR+partial-lineAND+combiningOR into thatcore.'}
    (dest/'punctured-four-arc-audit.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__': audit()
