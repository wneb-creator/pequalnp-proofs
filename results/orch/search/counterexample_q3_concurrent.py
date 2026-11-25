import json
from pathlib import Path
import counterexample_q3_nonread1 as m

base=m.base

def neighborhood(rng,trial):
    selected=[l for l in range(base.N) if 0 in base.LINES[l]]
    outside=[l for l in range(base.N) if l not in selected]
    rng.shuffle(outside);rng.shuffle(selected)
    line=rng.choice(selected)
    hidden_point=rng.choice(sorted(base.LINES[line]-{0}))
    gates=[];stars=[]
    def add(op,a,b):
        gates.append((op,a,b));return base.NINPUT+len(gates)-1
    def star(l,terms):
        value=terms[0]
        for term in terms[1:]:value=add(False,value,term)
        stars.append(add(True,value,base.N+l))
    for l in outside:star(l,sorted(base.LINES[l]))
    core_start=len(gates)
    g=add(True,add(False,0,hidden_point),add(False,0,base.N+line))
    candidates=[]
    for l in selected:
        begin=len(gates)
        terms=[g if p==0 else p for p in sorted(base.LINES[l]) if not (l==line and p==hidden_point)]
        star(l,terms)
        candidates += list(range(begin,len(gates)-1))
    after_stars=len(gates)
    output=stars[0]
    for star_wire in stars[1:]:output=add(False,output,star_wire)
    assert len(gates)==66
    assert base.evaluate(gates,base.POSITIVE+base.NEGATIVE)==(1<<len(base.POSITIVE))-1
    assert not m.reads_pair(gates,(0,base.N+line))
    old_free=set(range(core_start,after_stars))|set(range(after_stars+len(outside)-2,len(gates)))
    assert len(old_free)==23
    removed=sorted(rng.sample(candidates,3))
    replacement_sides={i:rng.randrange(2) for i in removed}
    mapping={i:i for i in range(base.NINPUT)}
    seed=[];free=[]
    for i,(op,a,b) in enumerate(gates):
        if i in replacement_sides:
            assert not op
            mapping[base.NINPUT+i]=mapping[(a,b)[replacement_sides[i]]]
        else:
            mapping[base.NINPUT+i]=base.NINPUT+len(seed)
            if i in old_free:free.append(len(seed))
            seed.append((op,mapping[a],mapping[b]))
    assert len(seed)==63 and len(free)==20
    m.forced_pair=(0,base.N+line)
    return seed,free,dict(seed_family='valid66_mixed_core_minus_three',selected_lines=selected,
                         line_order=outside+selected,hidden_edge=[hidden_point,base.N+line],
                         removed_gates=removed,replacement_sides=replacement_sides,
                         forced_nonread1_edge=m.forced_pair)

base.neighborhood=neighborhood
if __name__=='__main__':base.main()
