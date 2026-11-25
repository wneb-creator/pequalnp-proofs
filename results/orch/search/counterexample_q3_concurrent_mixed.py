import argparse
import json
import random
import subprocess
import sys
import time
import counterexample_q3_mixedcuts as runner
from pathlib import Path
import counterexample_q3_nonread1 as m

base=m.base
PUNCTURES={}
for point,line_wire in base.EDGES:
    line=line_wire-base.N
    mask=sum(1<<p for p in base.LINES[line] if p!=point)
    mask+=sum(1<<(base.N+l) for l in range(base.N) if l!=line and point in base.LINES[l])
    assert mask in base.NEGATIVE
    PUNCTURES[point,line]=mask
assert len(set(PUNCTURES.values()))==52

def neighborhood(rng,trial,remove_count=3):
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
    removed=sorted(rng.sample(candidates,remove_count))
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
    assert len(seed)==66-remove_count and len(free)==23-remove_count
    m.forced_pair=(0,base.N+line)
    return seed,free,dict(seed_family='valid66_mixed_core_minus_three',selected_lines=selected,
                         line_order=outside+selected,hidden_edge=[hidden_point,base.N+line],
                         removed_gates=removed,replacement_sides=replacement_sides,
                         forced_nonread1_edge=m.forced_pair)

def control():
    ap=argparse.ArgumentParser();ap.add_argument('--solver',required=True);ap.add_argument('--out',required=True)
    ap.add_argument('--concurrent-control',action='store_true');args=ap.parse_args()
    root=Path(args.out);root.mkdir(parents=True,exist_ok=True)
    seed,free,details=neighborhood(random.Random(76),0,0)
    patterns=base.POSITIVE+[base.NEGATIVE[0],base.NEGATIVE[-1]]+[1<<i for i in range(base.NINPUT)]+[mask for (p,l),mask in PUNCTURES.items() if l in details['selected_lines']]
    e=m.Encoding(seed,free,patterns);e.least_or_strict();e.least_singleton()
    cnf=root/'control.cnf';e.write(cnf);phase=root/'control.phases';e.write_phases(phase)
    start=time.monotonic()
    with (root/'control.log').open('w') as out:
        r=subprocess.run([args.solver,str(cnf),str(phase),'60','1000000'],stdout=out,stderr=subprocess.STDOUT)
    report=dict(status=r.returncode,seconds=time.monotonic()-start,variables=e.count,clauses=len(e.clauses),free_gates=free,details=details)
    if r.returncode==10:
        circuit=e.decode((root/'control.log').read_text())
        report['all_boundary_errors']=(base.evaluate(circuit,base.POSITIVE+base.NEGATIVE)^((1<<len(base.POSITIVE))-1)).bit_count()
        report['forced_pair_read1']=m.reads_pair(circuit,m.forced_pair)
        report['circuit']=circuit
    (root/'control.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report),flush=True)

runner.additional_negatives=lambda details:[mask for (p,l),mask in PUNCTURES.items() if l in details['selected_lines']]
runner.priority_negatives=set(PUNCTURES.values())
runner.Encoding=m.Encoding
runner.neighborhood=neighborhood
if __name__=='__main__':
    if '--concurrent-control' in sys.argv:control()
    else:runner.main()
