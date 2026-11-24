"""Heuristic source-set search including shared linear OR helpers."""
import argparse
import json
import math
import random
import time
from pathlib import Path
from SearchReduce import expand_rows, reduce_gates

from SearchPlaneProblem import (ALL_TESTS, EDGES, INPUT_MASKS, N, POINTS, NEIGHBORS,
                                POSITIVES, RAW_NEGATIVES, TARGET, TESTS, bits)

NEGATIVE_SCALE=len(POSITIVES)/(len(TESTS)-len(POSITIVES))
ARCHIVE_ERROR_LIMIT=max(8.0,len(POSITIVES)/2)

def evaluate(rows, out):
    values = list(INPUT_MASKS)
    for row in rows:
        value = ALL_TESTS
        for selected in row:
            operand = 0
            for j in bits(selected):
                operand |= values[j]
            value &= operand
        values.append(value)
    output = 0
    for i in bits(out):
        output |= values[N + i]
    active = out
    for i in range(len(rows) - 1, -1, -1):
        if active >> i & 1:
            for selected in rows[i]:
                active |= selected >> N
    size = out.bit_count() - 1
    for i in bits(active):
        size += sum(s.bit_count() for s in rows[i]) - 1
    wrong_pos = (TARGET & ~output).bit_count()
    wrong_neg = (output & (ALL_TESTS ^ TARGET)).bit_count()
    return size, wrong_pos, wrong_neg, active, output


def decode(rows, out, active):
    gates = []
    node_wires = {}

    def combine(wires):
        assert wires
        current = wires[0]
        for following in wires[1:]:
            gates.append(['or', sorted([current, following])])
            current = N + len(gates) - 1
        return current

    for i in bits(active):
        operands = []
        for selected in rows[i]:
            operands.append(combine([j if j < N else node_wires[j - N]
                                     for j in bits(selected)]))
        if len(operands) == 1:
            node_wires[i] = operands[0]
        else:
            gates.append(['and', sorted(operands)])
            node_wires[i] = N + len(gates) - 1
    output = combine([node_wires[i] for i in bits(out)])
    for x in sorted(POSITIVES | RAW_NEGATIVES):
        vals = [bool(x >> j & 1) for j in range(N)]
        for op, (a, b) in gates:
            assert 0 <= a < len(vals) and 0 <= b < len(vals)
            vals.append(vals[a] and vals[b] if op == 'and' else vals[a] or vals[b])
        assert vals[output] == any((x >> u & 1) and (x >> v & 1) for u, v in EDGES)
    return gates, output


MATCHING_STARTS = 0
SHARED_SUM_STARTS = 0
MIXED_COVER_STARTS = 0
INVALID_BICLIQUE_STARTS = 0


def base_baseline(rng, linear, helpers, mixed):
    centers=list(range(POINTS))
    rng.shuffle(centers)
    rows=[]
    for i in range(linear):
        if rng.random()<.6:
            u=rng.choice(centers)
            choices=rng.sample(NEIGHBORS[u],rng.randrange(2,6))
        else:
            choices=rng.sample(range(N),rng.randrange(2,6))
        rows.append((sum(1<<j for j in choices),))
    dirty_centers=rng.sample(centers,min(helpers,POINTS))
    activate_dirty=rng.random()<.6
    helper_rows = []
    before = mixed // 2
    before_positions = set(rng.sample(range(helpers), min(before, helpers)))
    inserted = 0
    for h in range(helpers):
        if h in before_positions:
            choices = rng.sample(range(N+len(rows)), rng.randrange(2,6))
            rows.append((sum(1<<j for j in choices),))
            inserted += 1
        i=len(rows)
        if activate_dirty and h < len(dirty_centers):
            u=dirty_centers[h]
            other=rng.choice([v for v in centers if v!=u])
            sides=[(1<<u)|(1<<other),sum(1<<v for v in NEIGHBORS[u])]
        else:
            sides=[]
            for _ in range(2):
                choices=rng.sample(range(N+i),rng.randrange(1,6))
                sides.append(sum(1<<j for j in choices))
        helper_rows.append(i)
        rows.append(tuple(sides))
    mixed_after = mixed - inserted
    after_positions = set(rng.sample(range(1, POINTS+1), mixed_after))
    out = 0
    for position,u in enumerate(centers,1):
        right=sum(1<<v for v in NEIGHBORS[u])
        if activate_dirty and u in dirty_centers:
            right=1<<(N+helper_rows[dirty_centers.index(u)])
        out |= 1<<len(rows)
        rows.append((1<<u,right))
        if position in after_positions:
            available = list(bits(out))
            if len(available)>=2 and rng.random()<.65:
                selected = rng.sample(available,rng.randrange(2,min(5,len(available)+1)))
                node = len(rows)
                rows.append((sum(1<<(N+j) for j in selected),))
                out &= ~sum(1<<j for j in selected)
                out |= 1<<node
            else:
                choices = rng.sample(range(N+len(rows)),rng.randrange(2,6))
                rows.append((sum(1<<j for j in choices),))
    for i in range(linear,len(rows)):
        sides=list(rows[i])
        for side in range(len(sides)):
            for h in range(linear):
                if rows[h][0]&sides[side]==rows[h][0]:
                    sides[side]=(sides[side]&~rows[h][0])|(1<<(N+h))
        rows[i]=tuple(sides)
    assert len(rows) == linear + helpers + mixed + POINTS
    return rows,out


def matching_baseline(rng, linear, helpers, mixed):
    global MATCHING_STARTS
    rows, out = base_baseline(rng, linear, helpers, mixed)
    if helpers < 3 or rng.random() >= .6:
        return rows, out
    active = evaluate(rows, out)[3]
    stars = {}
    flat_right = {}
    for i in bits(active):
        row = rows[i]
        if len(row) != 2 or row[0].bit_count() != 1:
            continue
        center = row[0].bit_length()-1
        if center >= N:
            continue
        flat = 0
        for source in bits(row[1]):
            if source < N:
                flat |= 1<<source
            elif source-N < linear:
                flat |= rows[source-N][0]
            else:
                break
        else:
            if flat == sum(1<<j for j in NEIGHBORS[center]):
                stars[center] = i
                flat_right[center] = flat
    if len(stars) != POINTS:
        return rows, out
    latent = [i for i in range(linear, min(stars.values()))
              if len(rows[i]) == 2 and not (active >> i & 1)]
    if len(latent) < 3:
        return rows, out
    a, b = rng.sample(sorted(stars), 2)
    u = rng.choice(sorted(set(NEIGHBORS[b])-set(NEIGHBORS[a])))
    v = rng.choice(sorted(set(NEIGHBORS[a])-set(NEIGHBORS[b])))
    h0, h1, h2 = latent[:3]
    rows[h0] = ((1<<a)|(1<<b), (1<<u)|(1<<v))
    rows[h1] = ((1<<a)|(1<<u), (1<<b)|(1<<v))
    rows[h2] = (1<<(N+h0), 1<<(N+h1))
    rows[stars[a]] = (1<<a, flat_right[a] & ~(1<<v))
    rows[stars[b]] = (1<<b, flat_right[b] & ~(1<<u))
    out |= 1<<h2
    result = evaluate(rows, out)
    assert result[1] == result[2] == 0
    assert result[0] == 131
    MATCHING_STARTS += 1
    return rows, out


def shared_baseline(rng, linear, helpers, mixed):
    global SHARED_SUM_STARTS
    if rng.random()<.5:
        return matching_baseline(rng,linear,helpers,mixed)
    rows,out=base_baseline(rng,linear,helpers,mixed)
    size,wp,wn,active,_=evaluate(rows,out)
    if size!=125 or wp or wn or helpers<2:
        return rows,out
    free_linear=[i for i in range(linear) if not(active>>i&1)]
    if not free_linear:
        return rows,out
    stars={}
    for i in bits(active):
        row=rows[i]
        if len(row)!=2 or row[0].bit_count()!=1:
            continue
        center=row[0].bit_length()-1
        if center>=POINTS:
            continue
        flat=0
        for source in bits(row[1]):
            if source<N:
                flat|=1<<source
            elif source-N<linear:
                flat|=rows[source-N][0]
            else:
                break
        else:
            if flat==sum(1<<j for j in NEIGHBORS[center]):
                stars[center]=i
    if len(stars)<2:
        return rows,out
    first_star=min(stars.values())
    free_ands=[i for i in range(linear,first_star)
               if len(rows[i])==2 and not(active>>i&1)]
    if len(free_ands)<2:
        return rows,out
    a,b=rng.sample(sorted(stars),2)
    shared=rng.choice(free_linear)
    h0,h1=rng.sample(free_ands,2)
    rows=list(rows)
    rows[shared]=((1<<a)|(1<<b),)
    rows[h0]=(1<<(N+shared),sum(1<<j for j in NEIGHBORS[a]))
    rows[h1]=(1<<(N+shared),sum(1<<j for j in NEIGHBORS[b]))
    rows[stars[a]]=(1<<a,1<<(N+h0))
    rows[stars[b]]=(1<<b,1<<(N+h1))
    checked=evaluate(rows,out)
    assert checked[:3]==(128,0,0)
    SHARED_SUM_STARTS+=1
    return rows,out


def structured_baseline(rng,linear,helpers,mixed):
    global MIXED_COVER_STARTS
    if rng.random()>=1/3:
        return shared_baseline(rng,linear,helpers,mixed)
    rows,out=base_baseline(rng,linear,helpers,mixed)
    size,wp,wn,active,_=evaluate(rows,out)
    if size!=125 or wp or wn:
        return rows,out
    stars={}
    for i in bits(active):
        row=rows[i]
        if len(row)!=2 or row[0].bit_count()!=1:
            continue
        center=row[0].bit_length()-1
        if center>=POINTS:
            continue
        flat=0
        for source in bits(row[1]):
            if source<N:
                flat|=1<<source
            elif source-N<linear:
                flat|=rows[source-N][0]
            else:
                break
        else:
            if flat==sum(1<<j for j in NEIGHBORS[center]):
                stars[center]=i
    if not stars:
        return rows,out
    first_star=min(stars.values())
    free_ands=[i for i in range(linear,first_star)
               if len(rows[i])==2 and not(active>>i&1)]
    eligible=[c for c in range(POINTS,N) if all(u in stars for u in NEIGHBORS[c])]
    if not free_ands or not eligible:
        return rows,out
    c=rng.choice(eligible);helper=rng.choice(free_ands)
    rows=list(rows)
    rows[helper]=(1<<c,sum(1<<u for u in NEIGHBORS[c]))
    for u in NEIGHBORS[c]:
        rows[stars[u]]=(1<<u,sum(1<<j for j in NEIGHBORS[u] if j!=c))
    out|=1<<helper
    assert evaluate(rows,out)[:3]==(126,0,0)
    MIXED_COVER_STARTS+=1
    return rows,out


def baseline(rng,linear,helpers,mixed):
    global INVALID_BICLIQUE_STARTS
    if rng.random()>=.4:
        return structured_baseline(rng,linear,helpers,mixed)
    rows,out=base_baseline(rng,linear,helpers,mixed)
    size,wp,wn,active,_=evaluate(rows,out)
    if size!=125 or wp or wn:
        return rows,out
    stars={}
    for i in bits(active):
        row=rows[i]
        if len(row)!=2 or row[0].bit_count()!=1:
            continue
        center=row[0].bit_length()-1
        if center>=POINTS:
            continue
        flat=0
        for source in bits(row[1]):
            if source<N:
                flat|=1<<source
            elif source-N<linear:
                flat|=rows[source-N][0]
            else:
                break
        else:
            if flat==sum(1<<j for j in NEIGHBORS[center]):
                stars[center]=i
    if len(stars)!=POINTS:
        return rows,out
    centers=rng.sample(sorted(stars),rng.choice((2,2,3,4)))
    neighbors=set().union(*(set(NEIGHBORS[u]) for u in centers))
    selected={stars[u] for u in centers};first=min(selected)
    rows=list(rows)
    rows[first]=(sum(1<<u for u in centers),sum(1<<v for v in neighbors))
    out=sum(1<<i for i in stars.values() if i not in selected or i==first)
    checked=evaluate(rows,out)
    assert checked[0]==125-(5*len(centers)-len(neighbors))
    assert checked[1]==0 and checked[2]>0
    INVALID_BICLIQUE_STARTS+=1
    return rows,out


def mutate(rng, rows, out, linear):
    changed = list(rows)
    if rng.random() < .055:
        new_out = out ^ (1 << rng.randrange(linear, len(rows)))
        return changed, new_out or out
    i = rng.randrange(len(rows))
    side = rng.randrange(len(rows[i]))
    operands = list(rows[i])
    old = operands[side]
    limit = N if i < linear else N + i
    choice = rng.random()
    if choice < .38:
        new = old ^ (1 << rng.randrange(limit))
    elif choice < .64:
        remove = rng.choice(list(bits(old)))
        new = (old & ~(1 << remove)) | (1 << rng.randrange(limit))
    elif choice < .80:
        new = old | (1 << rng.randrange(limit))
    elif choice < .90:
        new = 1 << rng.randrange(limit)
    elif choice < .96:
        choices = rng.sample(range(limit), rng.randrange(1, 7))
        new = sum(1 << j for j in choices)
    else:
        # Replace an existing OR subexpression by a compatible shared OR source.
        eligible = [j for j in range(min(i, linear)) if rows[j][0] & old == rows[j][0]]
        if eligible:
            j = rng.choice(eligible)
            new = (old & ~rows[j][0]) | (1 << (N + j))
        else:
            new = old
    operands[side] = new or old
    changed[i] = tuple(operands)
    return changed, out


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--seed', type=int, required=True)
    p.add_argument('--seconds', type=float, required=True)
    p.add_argument('--output-dir', type=Path, required=True)
    p.add_argument('--epoch-steps', type=int, default=18000)
    args = p.parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    rng = random.Random(args.seed)
    started = time.monotonic()
    last_log = started
    steps = epochs = 0
    best_valid = 10 ** 9
    best_by_wrong = {}
    archive = {}
    reduced_seen = set()
    dirty_seen = set()
    near_seen = {1:set(),2:set(),3:set(),4:set()}
    multi_near_seen = set()
    best_overapprox_neg=10**9
    overapprox_saved=0
    print(json.dumps({'event': 'start', 'seed': args.seed, 'seconds': args.seconds,
                      'tests': len(TESTS), 'negative_scale':NEGATIVE_SCALE,
                      'archive_weighted_limit':ARCHIVE_ERROR_LIMIT,
                      'model': 'full42-input plane:balanced negative errors; INVALID compressed-biclique starts; valid mixed126/shared128/matching131; target124; active-AND-diverse archive; full raw verification'}), flush=True)

    def record(rows, out, ev, linear):
        nonlocal best_valid,best_overapprox_neg,overapprox_saved
        size, wp, wn, active, output = ev
        wrong = wp + wn
        previous = best_by_wrong.get(wrong)
        if previous is None or size < previous:
            best_by_wrong[wrong] = size
        if wp==0 and size<=124 and 0<wn<best_overapprox_neg:
            gates,output_wire=expand_rows(N,rows,out,active)
            assert len(gates)==size
            values=list(INPUT_MASKS)
            for operation,(a,b) in gates:
                assert 0<=a<len(values) and 0<=b<len(values)
                values.append(values[a]&values[b] if operation=='and' else values[a]|values[b])
            assert values[output_wire]==output
            mistakes=[]
            for x in sorted(POSITIVES|RAW_NEGATIVES):
                scalar=[bool(x>>j&1) for j in range(N)]
                for operation,(a,b) in gates:
                    scalar.append(scalar[a] and scalar[b] if operation=='and' else scalar[a] or scalar[b])
                expected=any(x>>a&1 and x>>b&1 for a,b in EDGES)
                if scalar[output_wire]!=expected:
                    mistakes.append({'input':x,'actual':scalar[output_wire],'expected':expected})
            assert mistakes and all(m['actual'] and not m['expected'] for m in mistakes)
            best_overapprox_neg=wn
            overapprox_saved+=1
            name=('overapprox-best-'+str(overapprox_saved)+'.json') if overapprox_saved<=32 else 'overapprox-latest.json'
            artifact={'inputs':N,'gates':gates,'output':output_wire,'size':size,'edge_list':EDGES,
                      'wrong_search_tests':wn,'wrong_raw_tests':len(mistakes),'wrong_tests':mistakes,
                      'seed':args.seed,'steps':steps,'rows':rows,'selected_outputs':out,
                      'proof_status':'INVALID positive-complete overapproximation; not a target witness'}
            (args.output_dir/name).write_text(json.dumps(artifact,indent=2)+'\n')
            print(json.dumps({'event':'INVALID_OVERAPPROX','size':size,'wrong_maximal_negatives':wn,
                              'wrong_raw':len(mistakes),'file':name}),flush=True)
        near_key=(size,output)
        save_near=(size<=124 and 1<=wrong<=4 and len(near_seen[wrong])<12
                   and near_key not in near_seen[wrong])
        maybe_multi=(steps%256==0 and size<=124 and 1<=wrong<=6 and len(multi_near_seen)<24
                     and near_key not in multi_near_seen)
        if save_near or maybe_multi:
            gates,output_wire=expand_rows(N,rows,out,active)
            assert len(gates)==size
            values=list(INPUT_MASKS)
            dirty_count=0
            for operation,(a,b) in gates:
                assert 0<=a<len(values) and 0<=b<len(values)
                value=values[a]&values[b] if operation=='and' else values[a]|values[b]
                values.append(value)
                dirty_count+=int(operation=='and' and bool(value&(ALL_TESTS^TARGET)))
            assert values[output_wire]==output
            save_multi=maybe_multi and dirty_count>=2
            if save_near or save_multi:
                mistakes=[]
                for x in sorted(POSITIVES|RAW_NEGATIVES):
                    scalar=[bool(x>>j&1) for j in range(N)]
                    for operation,(a,b) in gates:
                        scalar.append(scalar[a] and scalar[b] if operation=='and' else scalar[a] or scalar[b])
                    expected=any(x>>a&1 and x>>b&1 for a,b in EDGES)
                    if scalar[output_wire]!=expected:
                        mistakes.append({'input':x,'actual':scalar[output_wire],'expected':expected})
                assert mistakes
                artifact={'inputs':N,'gates':gates,'output':output_wire,'size':size,
                          'rows':rows,'selected_outputs':out,'linear_helpers':linear,
                          'edge_list':EDGES,'seed':args.seed,'steps':steps,
                          'wrong_search_tests':wrong,'wrong_raw_tests':len(mistakes),
                          'wrong_tests':mistakes,'active_dirty_ands':dirty_count,
                          'proof_status':'INVALID near miss; not a circuit for the target function'}
                if save_near:
                    near_seen[wrong].add(near_key)
                    path=args.output_dir/('near-'+str(wrong)+'-'+str(len(near_seen[wrong]))+'.json')
                    path.write_text(json.dumps(artifact,indent=2)+'\n')
                    print(json.dumps({'event':'invalid_near','file':str(path),'size':size,
                                      'wrong':wrong,'dirty_ands':dirty_count}),flush=True)
                if save_multi:
                    multi_near_seen.add(near_key)
                    path=args.output_dir/('multi-dirty-near-'+str(len(multi_near_seen))+'.json')
                    path.write_text(json.dumps(artifact,indent=2)+'\n')
                    print(json.dumps({'event':'invalid_multi_dirty_near','file':str(path),
                                      'size':size,'wrong':wrong,'dirty_ands':dirty_count}),flush=True)
        # Keep semantic diversity at the low-error frontier, including ties.
        active_ands=sum(len(rows[i])==2 for i in bits(active))
        key = (linear, len(rows), output, active_ands)
        previous = archive.get(key)
        if wp + NEGATIVE_SCALE*wn <= ARCHIVE_ERROR_LIMIT and (previous is None or size < previous[0] or
                          (size == previous[0] and rng.random() < .002)):
            archive[key] = (size, list(rows), out)
            if len(archive) > 10000:
                del archive[next(iter(archive))]
        if wrong == 0 and size <= 127:
            key = (out, tuple((i, rows[i]) for i in bits(active)))
            if key not in reduced_seen:
                reduced_seen.add(key)
                if len(reduced_seen) > 10000:
                    reduced_seen.pop()
                original_gates, original_output = expand_rows(N, rows, out, active)
                assert len(original_gates) == size
                gates, output_wire = reduce_gates(N, original_gates, original_output, INPUT_MASKS, TARGET)
                values = list(INPUT_MASKS)
                dirty = []
                for operation, (a, b) in gates:
                    value = values[a] & values[b] if operation == 'and' else values[a] | values[b]
                    values.append(value)
                    if operation == 'and' and value & (ALL_TESTS ^ TARGET):
                        dirty.append(value)
                dirty_key = tuple(sorted(dirty))
                save_dirty = (len(gates) <= 125 and dirty_key and dirty_key not in dirty_seen
                              and len(dirty_seen) < 32)
                if len(gates) <= 124 or save_dirty:
                    # Scalar verification is independent of the bit-vector reducer.
                    for x in sorted(POSITIVES | RAW_NEGATIVES):
                        scalar = [bool(x >> j & 1) for j in range(N)]
                        for operation, (a, b) in gates:
                            scalar.append(scalar[a] and scalar[b] if operation == 'and' else scalar[a] or scalar[b])
                        assert scalar[output_wire] == any(x >> a & 1 and x >> b & 1 for a, b in EDGES)
                    result = {'inputs': N, 'output': output_wire, 'gates': gates, 'size': len(gates),
                              'source_size': size, 'edge_list': EDGES, 'seed': args.seed,
                              'steps': steps, 'elapsed_seconds': time.monotonic() - started,
                              'verified_positive': len(POSITIVES), 'verified_negative': len(RAW_NEGATIVES),
                              'proof_status': 'computational witness; requires Lean verification'}
                    if len(gates) <= 124:
                        (args.output_dir / 'witness.json').write_text(json.dumps(result, indent=2) + '\n')
                        (args.output_dir / 'witness-tuples.json').write_text(json.dumps(gates) + '\n')
                        print(json.dumps({'event': 'reduced_witness', 'size': len(gates), 'source_size': size}), flush=True)
                        return True
                    dirty_seen.add(dirty_key)
                    target = args.output_dir / ('dirty-valid-125-' + str(len(dirty_seen)) + '.json')
                    target.write_text(json.dumps(result, indent=2) + '\n')
                    print(json.dumps({'event': 'dirty_valid', 'size': len(gates), 'file': str(target),
                                      'dirty_ands': len(dirty), 'steps': steps}), flush=True)
        if wrong == 0 and size < best_valid:
            gates, output_wire = decode(rows, out, active)
            assert len(gates) == size
            best_valid = size
            result = {'inputs': N, 'output': output_wire, 'gates': gates, 'size': size,
                      'ands': sum(op == 'and' for op, _ in gates),
                      'ors': sum(op == 'or' for op, _ in gates),
                      'edge_list': EDGES, 'rows': rows, 'selected_outputs': out,
                      'linear_helpers': linear, 'seed': args.seed, 'steps': steps,
                      'elapsed_seconds': time.monotonic() - started,
                      'verified_positive': len(POSITIVES),
                      'verified_negative': len(RAW_NEGATIVES),
                      'proof_status': 'computational witness; requires Lean verification'}
            target = args.output_dir / ('best-valid-' + str(size) + '.json')
            target.write_text(json.dumps(result, indent=2) + '\n')
            print(json.dumps({'event': 'valid', 'size': size, 'file': str(target), 'steps': steps}), flush=True)
            if size <= 124:
                (args.output_dir / 'witness.json').write_text(json.dumps(result, indent=2) + '\n')
                (args.output_dir / 'witness-tuples.json').write_text(json.dumps(gates) + '\n')
                return True
        return False

    while time.monotonic() - started < args.seconds:
        linear = (1, 2, 4, 8)[epochs % 4]
        helpers = (1, 2, 3, 4, 8, 12)[(epochs // 4) % 6]
        mixed = (1, 2, 4, 8)[(epochs // 24) % 4]
        rows, out = baseline(rng, linear, helpers, mixed)
        if epochs and rng.random() < .50:
            options = [v for (s, n, _, _), v in archive.items()
                       if s == linear and n == len(rows)]
            if options:
                _, rows, out = rng.choice(options)
                rows = list(rows)
        penalty = rng.choice([.9, 1.2, 1.7, 2.4, 3.5, 5.0, 1.0/NEGATIVE_SCALE, 2.0/NEGATIVE_SCALE])
        neg_weight = NEGATIVE_SCALE*rng.choice([.25, .5, 1.0, 2.0, 4.0])
        ev = evaluate(rows, out)
        if record(rows, out, ev, linear):
            return
        score = ev[0] + penalty * (ev[1] + neg_weight * ev[2])
        for step in range(args.epoch_steps):
            candidate, candidate_out = mutate(rng, rows, out, linear)
            next_ev = evaluate(candidate, candidate_out)
            next_score = next_ev[0] + penalty * (next_ev[1] + neg_weight * next_ev[2])
            temperature = .07 + 1.8 * (1.0 - step / args.epoch_steps) ** 2
            delta = next_score - score
            if delta <= 0 or rng.random() < math.exp(-delta / temperature):
                rows, out, ev, score = candidate, candidate_out, next_ev, next_score
                if record(rows, out, ev, linear):
                    return
            steps += 1
            if steps % 2048 == 0:
                now = time.monotonic()
                if now - last_log >= 15:
                    print(json.dumps({'event': 'progress', 'seconds': round(now - started, 2),
                                      'steps': steps, 'epochs': epochs, 'best_valid': best_valid,
                                      'matching_starts': MATCHING_STARTS,
                                      'shared_sum_starts':SHARED_SUM_STARTS,
                                      'mixed_cover_starts':MIXED_COVER_STARTS,
                                      'invalid_biclique_starts':INVALID_BICLIQUE_STARTS,
                                      'best_overapprox_negative_errors':best_overapprox_neg,
                                      'archive': len(archive),
                                      'frontier': {str(k): v for k, v in sorted(best_by_wrong.items()) if k <= 12}}), flush=True)
                    last_log = now
                if now - started >= args.seconds:
                    break
        epochs += 1
    (args.output_dir / 'frontier.json').write_text(json.dumps(best_by_wrong, indent=2) + '\n')
    print(json.dumps({'event': 'finished', 'seconds': time.monotonic() - started,
                      'steps': steps, 'epochs': epochs, 'best_valid': best_valid,
                      'matching_starts': MATCHING_STARTS,
                      'shared_sum_starts':SHARED_SUM_STARTS,
                      'mixed_cover_starts':MIXED_COVER_STARTS,
                      'invalid_biclique_starts':INVALID_BICLIQUE_STARTS,
                      'best_overapprox_negative_errors':best_overapprox_neg,
                      'conclusion': 'heuristic search only; no lower-bound conclusion'}), flush=True)


if __name__ == '__main__':
    main()
