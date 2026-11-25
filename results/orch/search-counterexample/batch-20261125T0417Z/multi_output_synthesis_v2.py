import argparse
import itertools
import json
from pathlib import Path
import resource
import subprocess
import time
import z3

ap=argparse.ArgumentParser()
ap.add_argument('or_count',type=int)
ap.add_argument('--points',default=','.join(map(str,range(13))))
ap.add_argument('--seconds',type=int,default=900)
ap.add_argument('--tag',default='multi-output')
ap.add_argument('--fixed-baseline',action='store_true')
ap.add_argument('--cnf-only',action='store_true')
args=ap.parse_args()
resource.setrlimit(resource.RLIMIT_AS,(3*1024**3,3*1024**3))
base=Path('/tmp/oec/pequalnp-pilot-62');stem=base/args.tag
data=json.loads((base/'multi-output-line-neighborhoods.json').read_text())
points=sorted(int(p) for p in args.points.split(','))
targets=[data['targets'][p] for p in points]
vertices=sorted({i for t in targets for i in range(13) if t['positive_mask']>>i&1})
index={v:i for i,v in enumerate(vertices)}
project=lambda v:sum((v>>j&1)<<i for i,j in enumerate(vertices))
positive=[1<<i for i in range(len(vertices))]
target_masks=[project(t['positive_mask']) for t in targets]
original_negative=sorted({project(q) for q in data['negative_samples']})
negative_set=set()
for target in target_masks:
    rows=[q for q in original_negative if not q&target]
    negative_set.update(q for q in rows if not any(q!=r and q&~r==0 for r in rows))
negative=sorted(negative_set)
samples=positive+negative
nv=len(vertices);np=nv;nn=len(negative);width=np+nn;k=args.or_count
all_mask=(1<<width)-1;positive_mask=(1<<np)-1
sample_wires=[sum((q>>i&1)<<j for j,q in enumerate(samples)) for i in range(nv)]
baseline_masks=[];baseline_signatures=positive.copy()
for target in target_masks:
    ids=[i for i in range(nv) if target>>i&1]
    assert len(ids)==4
    pairs=[(ids[0],ids[1]),(ids[2],ids[3])]
    children=[]
    for a,b in pairs:
        baseline_masks.append(sorted([baseline_signatures[a],baseline_signatures[b]]))
        children.append(len(baseline_signatures));baseline_signatures.append(baseline_signatures[a]|baseline_signatures[b])
    a,b=children
    baseline_masks.append(sorted([baseline_signatures[a],baseline_signatures[b]]))
    baseline_signatures.append(baseline_signatures[a]|baseline_signatures[b])
if args.fixed_baseline:assert k==len(baseline_masks)
print(json.dumps({'points':points,'line_inputs':vertices,'positive_count':np,'negative_count':nn,'or_count':k,'baseline':args.fixed_baseline}),flush=True)
start=time.monotonic()
s=z3.SolverFor('QF_BV');s.set(timeout=args.seconds*1000)
full=z3.BitVecVal(all_mask,width);pm=z3.BitVecVal(positive_mask,width)
wires=[z3.BitVecVal(w,width) for w in sample_wires]
branch_masks=[];branch_bits=[]
for i in range(k):
    terms=[];masks=[]
    for branch in range(2):
        bits=[z3.Bool(f'signature_{i}_{branch}_{j}') for j in range(np)]
        branch_bits.append(bits)
        sig=z3.Concat(*[z3.If(bit,z3.BitVecVal(1,1),z3.BitVecVal(0,1)) for bit in reversed(bits)])
        mask=z3.ZeroExt(nn,sig)
        s.add(sig!=0)
        term=full
        for wire in wires:term=term&z3.If((wire&mask)==mask,wire,full)
        value=z3.BitVec(f'term_{i}_{branch}',width)
        s.add(value==term,(value&pm)==mask)
        if args.fixed_baseline:s.add(sig==baseline_masks[i][branch])
        masks.append(sig);terms.append(value)
    s.add((masks[0]&~masks[1])!=0,(masks[1]&~masks[0])!=0,z3.ULT(masks[0],masks[1]))
    gate=z3.BitVec(f'gate_{i}',width);s.add(gate==terms[0]|terms[1])
    wires.append(gate);branch_masks.append(masks)
for target in target_masks:
    mask=z3.BitVecVal(target,width);out=full
    for wire in wires:out=out&z3.If((wire&mask)==mask,wire,full)
    wanted=sum(bool(q&target)<<j for j,q in enumerate(samples))
    s.add(out==z3.BitVecVal(wanted,width))
# Join the outputs false at one sample. Their combined sensitivity union gives
# a necessary lower bound on the number of original OR gates false there.
false_bounds=[]
for row,q in enumerate(negative):
    required=[t for t in target_masks if not t&q]
    union=0
    for t in required:union|=t
    bound=max(0,union.bit_count()-len(required));false_bounds.append(bound)
    if bound:s.add(z3.AtLeast(*[z3.Extract(np+row,np+row,w)==0 for w in wires[nv:]],bound))
print('joint_false_OR_bounds',sorted(set(false_bounds)),flush=True)
# Explicit incidence-preserving maps l -> 3^e*l+c, with the same point map.
actions=[]
for multiplier in (1,3,9):
    for shift in range(13):
        if {(multiplier*p+shift)%13 for p in points}!=set(points):continue
        mapped=[(multiplier*l+shift)%13 for l in vertices]
        assert set(mapped)==set(vertices)
        action=[index[l] for l in mapped]
        moved_targets={sum((t>>i&1)<<action[i] for i in range(nv)) for t in target_masks}
        assert moved_targets==set(target_masks)
        moved_neg={sum((q>>i&1)<<action[i] for i in range(nv)) for q in negative}
        assert moved_neg==set(negative)
        actions.append(action)
common=positive_mask
for target in target_masks:common&=target
private=[t&~common for t in target_masks]
if len(target_masks)==3 and common.bit_count()==1 and all(p.bit_count()==3 for p in private) and all(not a&b for a,b in itertools.combinations(private,2)):
    common_index=(common&-common).bit_length()-1
    groups=[[j for j in range(nv) if p>>j&1] for p in private]
    seen={tuple(a) for a in actions}
    for group_order in itertools.permutations(range(3)):
        for internal in itertools.product(list(itertools.permutations(range(3))),repeat=3):
            action=list(range(nv));action[common_index]=common_index
            for group in range(3):
                for position,j in enumerate(groups[group]):action[j]=groups[group_order[group]][internal[group][position]]
            if tuple(action) in seen:continue
            moved_targets={sum((t>>i&1)<<action[i] for i in range(nv)) for t in target_masks}
            moved_negative={sum((q>>i&1)<<action[i] for i in range(nv)) for q in negative}
            if moved_targets==set(target_masks) and moved_negative==set(negative):
                actions.append(action);seen.add(tuple(action))
pairs=list(itertools.combinations(range(nv),2))
representatives=sorted({min(tuple(sorted((a[i],a[j]))) for a in actions) for i,j in pairs})
if not args.fixed_baseline:
    s.add(z3.Or(*[z3.And(branch_masks[0][0]==1<<i,branch_masks[0][1]==1<<j) for i,j in representatives]))
print('verified_symmetries',len(actions),'first_OR_representatives',len(representatives),flush=True)
stem.with_suffix('.smt2').write_text(s.to_smt2())
print('encoded',round(time.monotonic()-start,3),'max_rss_KiB',resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,flush=True)
masks=None
if args.fixed_baseline:
    result=s.check();print('fixed_control',result,'elapsed',round(time.monotonic()-start,3),flush=True)
    assert result==z3.sat
    masks=baseline_masks
else:
    goal=z3.Goal();goal.add(*s.assertions())
    converted=z3.Then('simplify','bit-blast','pb2bv','bit-blast','tseitin-cnf')(goal)
    assert len(converted)==1
    dimacs=converted[0].dimacs()+'\n';stem.with_suffix('.cnf').write_text(dimacs)
    identifiers={}
    for line in dimacs.splitlines():
        fields=line.split()
        if len(fields)==3 and fields[0]=='c' and fields[1].isdigit() and fields[2].startswith('signature_'):
            identifiers[fields[2]]=int(fields[1])
    assert all(str(bit) in identifiers for group in branch_bits for bit in group)
    stem.with_suffix('.mapping.json').write_text(json.dumps({'signature_dimacs_variables':identifiers,'line_inputs':vertices,'points':points,'positive_samples':positive,'negative_samples':negative,'target_masks':target_masks,'signature_bits':[[str(b) for b in group] for group in branch_bits]},indent=2)+'\n')
    print('CNF_ready',round(time.monotonic()-start,3),'bytes',len(dimacs),'max_rss_KiB',resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,flush=True)
    if args.cnf_only:raise SystemExit(0)
    command=['/tmp/oec/pequalnp-pilot-62/elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical','-t',str(args.seconds),'-w',str(stem.with_suffix('.sol')),str(stem.with_suffix('.cnf'))]
    stem.with_suffix('.command.json').write_text(json.dumps(command,indent=2)+'\n')
    with stem.with_suffix('.solver.log').open('w') as log:
        completed=subprocess.run(command,stdout=log,stderr=subprocess.STDOUT)
    result={10:'sat',20:'unsat'}.get(completed.returncode,'unknown')
    print('result',result,'solver_exit',completed.returncode,'elapsed',round(time.monotonic()-start,3),flush=True)
    if completed.returncode==10:
        literals=[]
        for line in stem.with_suffix('.sol').read_text().splitlines():
            if line.startswith('v '):literals.extend(int(v) for v in line.split()[1:] if v!='0')
        true={v for v in literals if v>0}
        values=[sum((identifiers[str(bit)] in true)<<j for j,bit in enumerate(group)) for group in branch_bits]
        masks=[values[2*i:2*i+2] for i in range(k)]
if masks is not None:
    values=sample_wires.copy();ors=[]
    for a,b in masks:
        children=[];terms=[]
        for sig in (a,b):
            selected=[j for j,w in enumerate(values) if w&sig==sig]
            term=all_mask
            for j in selected:term&=values[j]
            assert term&positive_mask==sig
            children.append(selected);terms.append(term)
        ors.append(children);values.append(terms[0]|terms[1])
    outputs=[[j for j,w in enumerate(values) if w&t==t] for t in target_masks]
    evaluated_outputs=[]
    for target,selected in zip(target_masks,outputs):
        out=all_mask
        for j in selected:out&=values[j]
        assert out==sum(bool(q&target)<<j for j,q in enumerate(samples))
    assignments=list(range(1<<nv));all_assignments=(1<<len(assignments))-1
    truth=[sum((q>>i&1)<<j for j,q in enumerate(assignments)) for i in range(nv)]
    for a,b in ors:
        terms=[]
        for branch in (a,b):
            term=all_assignments
            for j in branch:term&=truth[j]
            terms.append(term)
        truth.append(terms[0]|terms[1])
    for target,selected in zip(target_masks,outputs):
        out=all_assignments
        for j in selected:out&=truth[j]
        for q in original_negative:assert bool(out>>q&1)==bool(q&target)
        for i in range(nv):assert bool(out>>(1<<i)&1)==bool(target>>i&1)
        evaluated_outputs.append(out)
    cap_count=0
    for local in assignments:
        global_assignment=sum((local>>i&1)<<v for i,v in enumerate(vertices))
        if not any(global_assignment&t==t for t in data['allowed_concurrent_triples']):
            cap_count+=1
            for target,out in zip(target_masks,evaluated_outputs):assert bool(out>>local&1)==bool(local&target)
    witness={'line_inputs':vertices,'points':points,'ors':ors,'outputs':outputs,'positive_signatures':masks,'verified_original_negative_count':len(original_negative),'verified_all_cap_assignments':cap_count}
    stem.with_suffix('.witness.json').write_text(json.dumps(witness,indent=2)+'\n')
    print('WITNESS_VERIFIED',k,'ORs',len(outputs),'outputs',flush=True)
