import counterexample_q3_global_shape as original

inc=original.inc
base=inc.base
force_direct=False

def direct_neighborhood(rng,trial,remove_count=3):
    assert remove_count in (0,3)
    full66,unused,details=original.original_neighborhood(rng,trial,0)
    point,line=details['hidden_edge']
    assert len(full66)==66
    for op,a,b in full66[39:]:assert a not in (62,63) and b not in (62,63)
    shift=lambda wire:wire-1 if wire>=64 else wire
    full65=full66[:36]+[(True,point,line),(False,0,62)]+[(op,shift(a),shift(b)) for op,a,b in full66[39:]]
    assert len(full65)==65
    assert base.evaluate(full65,base.POSITIVE+base.NEGATIVE)==(1<<len(base.POSITIVE))-1
    assert not inc.m.reads_pair(full65,(point,line))
    candidates=[i for i in range(38,53) if not full65[i][0]]
    removed=sorted(rng.sample(candidates,0 if remove_count==0 else 2))
    sides={i:rng.randrange(2) for i in removed}
    mapping={i:i for i in range(base.NINPUT)};seed=[]
    for i,(op,a,b) in enumerate(full65):
        if i in sides:mapping[base.NINPUT+i]=mapping[(a,b)[sides[i]]]
        else:
            mapping[base.NINPUT+i]=base.NINPUT+len(seed)
            seed.append((op,mapping[a],mapping[b]))
    assert len(seed)==(65 if remove_count==0 else 63)
    assert sum(op for op,a,b in seed)==14
    inc.m.forced_pair=(point,line)
    details=dict(details,seed_family='valid65_direct_core_minus_two',removed_gates=removed,
                 replacement_sides=sides,forced_nonread1_edge=[point,line],
                 rewiring='all_gates_fixed_operation_pattern',and_gates=14,or_gates=len(seed)-14)
    return seed,list(range(len(seed))),details

def neighborhood(rng,trial,remove_count=3):
    if force_direct or trial%2:return direct_neighborhood(rng,trial,remove_count)
    return original.neighborhood(rng,trial,remove_count)

inc.geometry.neighborhood=neighborhood
if __name__=='__main__':inc.main()
