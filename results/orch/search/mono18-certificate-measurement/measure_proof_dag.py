from pathlib import Path
from collections import Counter, defaultdict
import argparse, gzip, hashlib, json, struct

parser = argparse.ArgumentParser()
parser.add_argument('directory', type=Path)
parser.add_argument('output', type=Path)
args = parser.parse_args()
args.output.mkdir(parents=True, exist_ok=True)
nodes = {}
signals = {}
event_counts = Counter()
completion = []
header = None
for line in (args.directory / 'proof.jsonl').open():
    e = json.loads(line)
    event_counts[e['event']] += 1
    if e['event'] == 'header':
        header = e
    elif e['event'] == 'node':
        nodes[e['id']] = dict(node=e, entries=[], cuts=[], children=[])
    elif e['event'] == 'signal':
        signals[e['id']] = e['hex']
    elif e['event'] == 'done':
        nodes[e['id']]['done'] = e
        completion.append(e['id'])
    elif e['event'] in ('basis', 'canonical', 'closure_complete'):
        nodes[e['node']][e['event']] = e
    elif e['event'] == 'entry':
        nodes[e['node']]['entries'].append(e)
    elif e['event'] == 'subtree_cut':
        nodes[e['node']]['cuts'].append(e)
    elif e['event'] == 'copy_child':
        nodes[e['node']]['children'].append(e)
    else:
        raise AssertionError(e)

assert len(completion) == len(nodes)
assert len(set(completion)) == len(nodes)
rank = {n: i for i, n in enumerate(completion)}
assert nodes[1]['done']['kind'] == 'expand'
assert all(n['done']['kind'] not in ('open', 'found') for n in nodes.values())
memo_count = 0
for i, n in nodes.items():
    for c in n['children']:
        assert c['child'] in nodes
        assert nodes[c['child']]['node']['parent'] == i
        assert rank[c['child']] < rank[i]
    if n['done']['kind'] == 'expand':
        assert len(n['children']) == len(n['entries'])
        assert [c['entry'] for c in n['children']] == list(range(len(n['entries'])))
    if n['done']['kind'] == 'memo':
        j = n['done']['ref']
        assert j > 0 and rank[j] < rank[i]
        assert n['node']['remaining'] == nodes[j]['node']['remaining']
        assert n['canonical']['state'] == nodes[j]['canonical']['state']
        memo_count += 1

rectangles = {}
matrix_events = []
for line in (args.directory / 'rectangles.jsonl').open():
    e = json.loads(line)
    if e['event'] == 'rectangle':
        assert e['node'] not in rectangles
        rectangles[e['node']] = e
    elif e['event'] == 'matrix_loaded':
        matrix_events.append(e)

essential = {i for i, n in nodes.items() if n['done']['kind'] in ('expand', 'tight_closure')}
rect_nodes = {i for i, n in nodes.items() if n['done']['kind'] in ('rectangle', 'rectangle_midclosure')}
assert rect_nodes <= rectangles.keys()
cof_nodes = {i for i, n in nodes.items() if n['done']['kind'] == 'cofactor'}
assert all(n['done']['kind'] in ('expand', 'tight_closure', 'rectangle', 'rectangle_midclosure', 'cofactor', 'memo', 'prefix_formula', 'card') for n in nodes.values())

streams = defaultdict(bytearray)
def put(category, *values):
    out = streams[category]
    for v in values:
        assert isinstance(v, int) and v >= 0
        while v >= 128:
            out.append((v & 127) | 128)
            v >>= 7
        out.append(v)

profiles = Counter()
patterns = Counter()
cut_index_patterns = Counter()
entry_nonleaf = 0
hist_lengths = Counter()
for i in completion:
    n = nodes[i]
    kind = n['done']['kind']
    if i in essential:
        put('node_structure', 0 if kind == 'expand' else 1, len(n['basis']['roots']), len(n['entries']))
        # Each nonleaf value and its count vector is derived from two earlier entries.
        for e in n['entries']:
            if e['left'] >= 0:
                put('entry_provenance', e['left'], e['right'], e['op'])
                entry_nonleaf += 1
        for c in n['cuts']:
            bitmask = sum(1 << x for x in c['selected_history'])
            put('cuts_explicit', c['left'], c['right'], c['op'], c['profile'], bitmask)
            put('cuts_witness_only', c['profile'], bitmask)
            profiles[c['profile']] += 1
            patterns[(c['profile'], bitmask)] += 1
            cut_index_patterns[(c['left'], c['right'], c['op'], c['profile'], bitmask)] += 1
        for c in n['children']:
            child = nodes[c['child']]
            ck = child['done']['kind']
            if ck == 'memo':
                ref = child['done']['ref']
                put('children', 0, rank[ref], child['canonical']['automorphism'], nodes[ref]['canonical']['automorphism'])
            elif ck in ('expand', 'tight_closure'):
                put('children', 1, rank[c['child']])
            elif ck in ('rectangle', 'rectangle_midclosure'):
                r = rectangles[c['child']]
                put('children', 2, r['matrix'])
            elif ck == 'cofactor':
                d = child['done']
                mask = sum(1 << x for x in d['selected_history'])
                put('children', 3, d['profile'], mask)
                profiles[d['profile']] += 1
                patterns[(d['profile'], mask)] += 1
            elif ck == 'prefix_formula':
                put('children', 4)
            elif ck == 'card':
                put('children', 5)
            else:
                raise AssertionError(ck)
        hist_lengths[len(n['node']['history'])] += 1

# Reference patterns can be emitted once and selected by a compact index. This
# measures storage only; a Lean decoder and finite soundness checks are separate.
pattern_ids = {p: i for i, (p, _) in enumerate(patterns.most_common())}
for p in pattern_ids:
    put('witness_dictionary', *p)
for i in completion:
    if i not in essential:
        continue
    for c in nodes[i]['cuts']:
        mask = sum(1 << x for x in c['selected_history'])
        put('cut_witness_dictionary_indices', pattern_ids[c['profile'], mask])

template_ids={}
pref_counts=[]
matrix_counts=[]
profile_trial_upper=0
profile_only_counts=0
for i in completion:
    if i not in essential:
        continue
    n=nodes[i]
    template=tuple((e['left'],e['right'],e['op']) for e in n['entries'] if e['left']>=0)
    if template not in template_ids:
        template_ids[template]=len(template_ids)
        put('entry_template_dictionary',len(template))
        for t in template:put('entry_template_dictionary',*t)
    put('entry_template_indices',template_ids[template])
    prefs={}
    profile_freq=Counter()
    for c in n['cuts']:
        mask=sum(1<<x for x in c['selected_history'])
        prefs[c['profile'],mask]=1
        profile_freq[c['profile']]+=1
    childprefs={};matrices=set();links=[]
    for c in n['children']:
        child=nodes[c['child']];kind=child['done']['kind']
        if kind=='cofactor':
            d=child['done'];mask=sum(1<<x for x in d['selected_history'])
            childprefs[d['profile'],mask]=1
        elif kind in ('rectangle','rectangle_midclosure'):
            matrices.add(rectangles[c['child']]['matrix'])
        elif kind=='memo':
            ref=child['done']['ref']
            links.append((c['entry'],0,rank[ref],child['canonical']['automorphism'],nodes[ref]['canonical']['automorphism']))
        elif kind in ('expand','tight_closure'):
            links.append((c['entry'],1,rank[c['child']]))
    put('node_cut_presets',len(prefs))
    for p in sorted(prefs):put('node_cut_presets',pattern_ids[p])
    ordered_profiles=[p for p,_ in profile_freq.most_common()]
    put('node_profile_only_presets',len(ordered_profiles))
    for p in ordered_profiles:put('node_profile_only_presets',p)
    profile_only_counts+=len(ordered_profiles)
    profile_trial_upper+=sum((j+1)*profile_freq[p] for j,p in enumerate(ordered_profiles))
    put('node_child_cofactor_presets',len(childprefs))
    for p in sorted(childprefs):put('node_child_cofactor_presets',pattern_ids[p])
    put('node_rectangle_presets',len(matrices))
    for m in sorted(matrices):put('node_rectangle_presets',m)
    put('node_explicit_child_links',len(links))
    for link in links:put('node_explicit_child_links',*link)
    pref_counts.append(len(prefs));matrix_counts.append(len(matrices))

packing = {}
for name, data in streams.items():
    (args.output / (name + '.varint')).write_bytes(data)
    packed = gzip.compress(data, compresslevel=9, mtime=0)
    (args.output / (name + '.varint.gz')).write_bytes(packed)
    packing[name] = dict(varint_bytes=len(data), gzip_bytes=len(packed), sha256=hashlib.sha256(data).hexdigest())

counts = Counter(n['done']['kind'] for n in nodes.values())
summary = dict(directory=str(args.directory), header={k:v for k,v in header.items() if k != 'automorphisms'},
    event_counts=event_counts, terminal_counts=counts, proof_nodes=len(nodes),
    nonterminal_nodes=len(essential), memo_nodes=memo_count, rectangle_nodes=len(rect_nodes),
    retained_entries=sum(len(nodes[i]['entries']) for i in essential),
    derived_entries=entry_nonleaf, subtree_cut_witnesses=sum(len(nodes[i]['cuts']) for i in essential),
    unique_cofactor_profiles=len(profiles), profile_counts=dict(sorted(profiles.items())),
    unique_profile_history_masks=len(patterns), unique_explicit_cut_records=len(cut_index_patterns),
    provenance_templates=len(template_ids),node_unique_cut_presets=sum(pref_counts),node_unique_rectangle_presets=sum(matrix_counts),
    node_unique_profiles=profile_only_counts,profile_only_trial_upper=profile_trial_upper,
    hist_lengths=dict(sorted(hist_lengths.items())), packing=packing,
    limitations=['Byte counts omit generic Lean decoder/checker, profile lower proofs and rectangle root-cost proofs.',
        'Gzip figures are entropy measurements only; no Lean gzip decoder exists.',
        'Witness-only streams require replaying deterministic candidate enumeration.',
        'Completion-order dependency verification here is structural, not full semantic replay.'])
(args.output / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
(args.output / 'rectangle-nodes.json').write_text(json.dumps(sorted(rect_nodes)) + '\n')
(args.output / 'nonterminal-nodes.json').write_text(json.dumps([i for i in completion if i in essential]) + '\n')
(args.output / 'completion-order.json').write_text(json.dumps(completion) + '\n')
# Smallest concrete linkage fixtures retain original events and exact signal words.
essential_bits = {i:1 << j for j,i in enumerate(sorted(essential))}
dependency_bits = {}
for i in completion:
    bits = essential_bits.get(i,0)
    for c in nodes[i]['children']:
        bits |= dependency_bits[c['child']]
    if nodes[i]['done']['kind'] == 'memo':
        bits |= dependency_bits[nodes[i]['done']['ref']]
    dependency_bits[i] = bits
small = sorted((i for i in essential if nodes[i]['done']['kind'] == 'expand'), key=lambda i:(len(nodes[i]['entries']), len(nodes[i]['cuts']), i))[:10]
complete_small = sorted((i for i in essential if nodes[i]['done']['kind']=='expand' and dependency_bits[i].bit_count()>=2),key=lambda i:(dependency_bits[i].bit_count(),len(nodes[i]['entries']),len(nodes[i]['cuts']),i))[:3]
fixture_specs = [('fixture-',i,False) for i in small]+[('complete-fixture-',i,True) for i in complete_small]
for prefix,i,transitive in fixture_specs:
    chosen = {i} | {c['child'] for c in nodes[i]['children']}
    pending = list(chosen)
    while pending:
        j=pending.pop()
        more=[]
        if nodes[j]['done']['kind']=='memo':
            more.append(nodes[j]['done']['ref'])
        if transitive:
            more += [c['child'] for c in nodes[j]['children']]
        for k in more:
            if k not in chosen:
                chosen.add(k);pending.append(k)
    used = set()
    for j in chosen:
        n = nodes[j]
        used.update(n['node']['state'])
        for gate in n['node']['history']:
            used.update(gate[1:])
        for e in n['entries']:
            used.add(e['signal'])
        for c in n['cuts']:
            used.add(c['signal'])
        if 'canonical' in n:
            used.update(n['canonical']['state'])
    fixture = dict(header=header, parent=i, transitive_complete=transitive,
        nonterminal_dependencies=dependency_bits[i].bit_count(),completion_order=[j for j in completion if j in chosen],
        nodes={j:nodes[j] for j in sorted(chosen)},
        signals={j:signals[j] for j in sorted(used)}, rectangles={j:rectangles[j] for j in chosen if j in rectangles})
    (args.output / (prefix + str(i) + '.json')).write_text(json.dumps(fixture, separators=(',', ':')) + '\n')
summary['smallest_fixtures'] = small
summary['smallest_complete_fixtures'] = [{'node':i,'nonterminal_dependencies':dependency_bits[i].bit_count()} for i in complete_small]
autos = header['automorphisms']
auto_index = {tuple(p): i for i, p in enumerate(autos)}
def moved(word, p):
    result = 0
    for r in range(1024):
        pr = sum(((r >> j) & 1) << p[j] for j in range(10))
        if word >> pr & 1:
            result |= 1 << r
    return result
for prefix,i,transitive in fixture_specs:
    path = args.output / (prefix + str(i) + '.json')
    fixture = json.loads(path.read_text())
    maps = []
    parents=[j for j in map(int,fixture['nodes']) if j in essential] if transitive else [i]
    for parent_id in parents:
      parent = nodes[parent_id]
      roots = parent['basis']['roots']
      total = parent['basis']['total']
      for c in parent['children']:
        e = parent['entries'][c['entry']]
        child = nodes[c['child']]
        cr = sorted(set(child['node']['state']))
        ct = [child['node']['state'].count(v) for v in cr]
        regroup = [cr.index(v) if v in cr else 0 for v in roots]
        wclass = cr.index(e['signal'])
        computed = [0] * len(cr)
        for j, tag in enumerate(regroup):
            computed[tag] += total[j] - e['counts'][j]
        computed[wclass] += 2
        assert computed == ct
        rec = dict(parent=parent_id,child=c['child'], entry=c['entry'], roots=cr, total=ct,
            old_to_child=regroup, inserted_wire_class=wclass)
        if child['done']['kind'] == 'memo':
            ref = nodes[child['done']['ref']]
            rr = sorted(set(ref['node']['state']))
            pc = autos[child['canonical']['automorphism']]
            pr = autos[ref['canonical']['automorphism']]
            invr = [pr.index(j) for j in range(10)]
            perm = [pc[invr[j]] for j in range(10)]
            index = auto_index[tuple(perm)]
            words = {int(signals[v],16): j for j,v in enumerate(rr)}
            classmap = [words[moved(int(signals[v],16),perm)] for v in cr]
            assert all(ct[j] == ref['node']['state'].count(rr[classmap[j]]) for j in range(len(cr)))
            rec['memo'] = dict(ref=child['done']['ref'], automorphism=index,
                vertex_permutation=perm, source_to_reference_classes=classmap,
                reference_roots=rr)
        maps.append(rec)
    fixture['class_maps'] = maps
    path.write_text(json.dumps(fixture,separators=(',',':'))+'\n')
(args.output / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
print(json.dumps(summary, indent=2))
