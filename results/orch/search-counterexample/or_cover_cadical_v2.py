import argparse
import json
from pathlib import Path
import time
import subprocess
import z3

ap=argparse.ArgumentParser()
ap.add_argument('scenario');ap.add_argument('or_count',type=int)
ap.add_argument('--seconds',type=int,default=120)
ap.add_argument('--delete',type=int)
ap.add_argument('--changes',type=int,default=4)
ap.add_argument('--first-inputs')
ap.add_argument('--first-signatures')
ap.add_argument('--sensitivity',action='store_true')
ap.add_argument('--cover-cuts',action='store_true')
ap.add_argument('--undominated-covers',action='store_true')
ap.add_argument('--orbits',action='store_true')
ap.add_argument('--cadical',action='store_true')
ap.add_argument('--tag',default='cover-query')
ap.add_argument('--fixed-witness')
args=ap.parse_args()
N=13; U=(1<<N)-1
lines=[sum(1<<((l+d)%N) for d in (0,1,3,9)) for l in range(N)]
pencils=[sum(1<<l for l in range(N) if lines[l]>>p&1) for p in range(N)]
negative=[]
for p in range(1<<N):
    q=sum(1<<l for l in range(N) if lines[l]&p==0)
    closure=U
    for l in range(N):
        if q>>l&1: closure&=U^lines[l]
    if closure==p and not any(p&~l==0 for l in lines) and not any(q&~t==0 for t in pencils):negative.append(p|(q<<13))
if args.scenario in ('theta','theta4'):
    ell=0; point=2
    ps=[p for p in range(N) if lines[ell]>>p&1][:3 if args.scenario=='theta' else 4]
    ls=[next(l for l in range(N) if (lines[l]>>point&1) and (lines[l]>>p&1)) for p in ps]
    vertices=[point]+ps+[13+ell]+[13+l for l in ls]
elif args.scenario=='quadrangle':
    ps=[0,1,2,5]
    ls=sorted({l for l in range(N) if sum(lines[l]>>p&1 for p in ps)==2})
    vertices=ps+[13+l for l in ls]
elif args.scenario=='full':vertices=list(range(26))
elif args.scenario.startswith('cycle'):vertices=list(range(int(args.scenario[5:])))
elif args.scenario=='bowtie':vertices=list(range(5))
else:vertices=[int(x) for x in args.scenario.split(',')]
def proj(v):return sum(((v>>x)&1)<<i for i,x in enumerate(vertices))
positives=[proj((1<<p)|(1<<(13+l))) for p in range(N) for l in range(N) if lines[l]>>p&1 and p in vertices and 13+l in vertices]
neg=set(map(proj,negative));neg=sorted(v for v in neg if not any(v!=w and v&~w==0 for w in neg))
if args.scenario.startswith('cycle'):
    size=len(vertices)
    positives=sorted({(1<<i)|(1<<((i+1)%size)) for i in range(size)})
    neg=sorted({(1<<i)|(1<<j) for i in range(size) for j in range(i+1,size)}-set(positives))
elif args.scenario=='bowtie':
    positives=[3,5,6,9,17,24]
    neg=sorted(({(1<<i)|(1<<j) for i in range(5) for j in range(i+1,5)}-set(positives))|{1})
samples=positives+neg
m=len(samples);np=len(positives);nv=len(vertices);k=args.or_count
positive_mask=(1<<np)-1;all_mask=(1<<m)-1
print(json.dumps({'scenario':args.scenario,'vertices':vertices,'positives':np,'negative_maxima':len(neg),'or_count':k}),flush=True)
start=time.monotonic();s=z3.SolverFor('QF_BV');s.set(timeout=args.seconds*1000)
full=z3.BitVecVal(all_mask,m);pm=z3.BitVecVal(positive_mask,m)
wires=[z3.BitVecVal(sum(((v>>i)&1)<<j for j,v in enumerate(samples)),m) for i in range(nv)]
branch_masks=[];branch_bits=[]
for i in range(k):
    terms=[];masks=[]
    for b in range(2):
        bits=[z3.Bool(f'signature_{i}_{b}_{j}') for j in range(np)]
        branch_bits.append(bits)
        small=z3.Concat(*[z3.If(bit,z3.BitVecVal(1,1),z3.BitVecVal(0,1)) for bit in reversed(bits)])
        mask=z3.ZeroExt(m-np,small)
        s.add(small!=0)
        term=full
        for wire in wires:term=term&z3.If((wire&mask)==mask,wire,full)
        var=z3.BitVec(f't_{i}_{b}',m);s.add(var==term);s.add((var&pm)==mask)
        terms.append(var);masks.append(small)
    s.add((masks[0]&~masks[1])!=0,(masks[1]&~masks[0])!=0,z3.ULT(masks[0],masks[1]))
    gate=z3.BitVec(f'g_{i}',m);s.add(gate==terms[0]|terms[1])
    wires.append(gate);branch_masks.append(masks)
out=full
for wire in wires:out=out&z3.If((wire&pm)==pm,wire,full)
s.add(out==pm)
if args.sensitivity:
    bounds=[]
    for row,assignment in enumerate(neg):
        neighbors=0
        for edge in positives:
            if edge&assignment:neighbors|=edge&~assignment
        bound=max(0,neighbors.bit_count()-1);bounds.append(bound)
        if bound:
            s.add(z3.AtLeast(*[(z3.Extract(np+row,np+row,w)==0) for w in wires[nv:]],bound))
    print('false_OR_bounds',bounds,flush=True)
if args.cover_cuts:
    cut_count=0
    for prefix in range(1,k):
        for row,assignment in enumerate(neg):
            eligible=[j for j in range(nv) if not (assignment>>j&1)]+list(range(nv,nv+prefix))
            selected=[z3.Bool(f'cover_{prefix}_{row}_{j}') for j in eligible]
            for sel,j in zip(selected,eligible):
                s.add(z3.Implies(sel,z3.Extract(np+row,np+row,wires[j])==0))
                if args.undominated_covers:
                    pj=wires[j]&pm
                    for other in eligible:
                        if other==j:continue
                        po=wires[other]&pm
                        dominates=z3.And(z3.Extract(np+row,np+row,wires[other])==0,(pj&po)==pj)
                        if other>j:dominates=z3.And(dominates,po!=pj)
                        s.add(z3.Implies(sel,z3.Not(dominates)))
            for edge in range(np):
                s.add(z3.Or(*[z3.And(sel,z3.Extract(edge,edge,wires[j])==1) for sel,j in zip(selected,eligible)]))
            future_true=[z3.Extract(np+row,np+row,w)==1 for w in wires[nv+prefix:]]
            s.add(z3.PbLe([(v,1) for v in selected+future_true],k-prefix+1))
            cut_count+=1
    print('prefix_cover_cuts',cut_count,flush=True)
if args.orbits:
    assert args.scenario=='theta'
    orbit_data=json.loads(Path('/tmp/oec/pequalnp-pilot-62/theta-orbits.json').read_text())
    assert orbit_data['positive_masks']==positives
    s.add(z3.Or(*[z3.And(branch_masks[0][0]==o['representative'][0],branch_masks[0][1]==o['representative'][1]) for o in orbit_data['orbits']]))
    print('first_OR_orbits',len(orbit_data['orbits']),flush=True)
if args.fixed_witness:
    fixed=json.loads(Path(args.fixed_witness).read_text())['positive_signatures']
    assert len(fixed)==k
    for masks,values in zip(branch_masks,fixed):
        for mask,value in zip(masks,values):s.add(mask==value)
if args.first_inputs:
    first=[int(i) for i in args.first_inputs.split(',')]
    vals=sorted(sum(((v>>i)&1)<<j for j,v in enumerate(positives)) for i in first)
    assert len(vals)==2
    for mask,value in zip(branch_masks[0],vals):s.add(mask==value)
if args.first_signatures:
    vals=sorted(int(x) for x in args.first_signatures.split(','))
    assert len(vals)==2
    for mask,value in zip(branch_masks[0],vals):s.add(mask==value)
if args.delete is not None:
    assert args.scenario in ('theta','theta4')
    paths=3 if args.scenario=='theta' else 4
    iv=[sum(((v>>i)&1)<<j for j,v in enumerate(positives)) for i in range(nv)]
    baseline=[]
    def join(bits):
        acc=bits[0]
        for b in bits[1:]:
            baseline.append(sorted([acc,b]));acc|=b
        return acc
    aa=join(iv[1:1+paths]);bb=join(iv[paths+2:])
    matching=join([iv[1+i]&iv[paths+2+i] for i in range(paths)])
    yy=iv[paths+1]&aa;xx=iv[0]&bb
    first=join([yy,xx]);join([first,matching])
    del baseline[args.delete]
    assert len(baseline)==k
    s.add(z3.PbLe([(m!=v,1) for masks,values in zip(branch_masks,baseline) for m,v in zip(masks,values)],args.changes))
    print('repair',args.delete,args.changes,flush=True)
print('encoded',round(time.monotonic()-start,3),flush=True)
masks=None
if args.cadical:
    base=Path('/tmp/oec/pequalnp-pilot-62');stem=base/args.tag
    stem.with_suffix('.smt2').write_text(s.to_smt2())
    goal=z3.Goal();goal.add(*s.assertions())
    converted=z3.Then('simplify','bit-blast','pb2bv','bit-blast','tseitin-cnf')(goal)
    assert len(converted)==1
    dimacs=converted[0].dimacs()+'\n';stem.with_suffix('.cnf').write_text(dimacs)
    identifiers={}
    for line in dimacs.splitlines():
        fields=line.split()
        if len(fields)==3 and fields[0]=='c' and fields[1].isdigit():identifiers[fields[2]]=int(fields[1])
    missing=[str(b) for group in branch_bits for b in group if str(b) not in identifiers]
    assert not missing,missing
    stem.with_suffix('.mapping.json').write_text(json.dumps({'dimacs_variables':identifiers,'vertices':vertices,'positive_samples':positives,'negative_samples':neg,'signature_bits':[[str(b) for b in group] for group in branch_bits]},indent=2)+'\n')
    print('CNF_ready',round(time.monotonic()-start,3),'bytes',len(dimacs),flush=True)
    command=['/tmp/oec/pequalnp-pilot-62/elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical','-t',str(args.seconds),'-w',str(stem.with_suffix('.sol')),str(stem.with_suffix('.cnf'))]
    stem.with_suffix('.command.json').write_text(json.dumps(command,indent=2)+'\n')
    with stem.with_suffix('.solver.log').open('w') as log:
        completed=subprocess.run(command,stdout=log,stderr=subprocess.STDOUT)
    answer={10:'sat',20:'unsat'}.get(completed.returncode,'unknown')
    print('result',answer,'solver_exit',completed.returncode,'elapsed',round(time.monotonic()-start,3),flush=True)
    if completed.returncode==10:
        literals=[]
        for line in stem.with_suffix('.sol').read_text().splitlines():
            if line.startswith('v '):literals.extend(int(v) for v in line.split()[1:] if v!='0')
        true={v for v in literals if v>0}
        values=[sum((identifiers[str(b)] in true)<<j for j,b in enumerate(group)) for group in branch_bits]
        masks=[values[2*i:2*i+2] for i in range(k)]
else:
    ans=s.check();print('result',ans,'elapsed',round(time.monotonic()-start,3),flush=True);print(s.statistics(),flush=True)
    if ans==z3.sat:
        model=s.model();masks=[[model.eval(b).as_long() for b in g] for g in branch_masks]
if masks is not None:
    vals=[sum(((v>>i)&1)<<j for j,v in enumerate(samples)) for i in range(nv)]
    for a,b in masks:
        terms=[]
        for mask in (a,b):
            term=all_mask
            for w in vals:
                if w&mask==mask:term&=w
            assert term&positive_mask==mask
            terms.append(term)
        assert a&~b and b&~a
        vals.append(terms[0]|terms[1])
    final=all_mask
    for w in vals:
        if w&positive_mask==positive_mask:final&=w
    assert final==positive_mask
    ors=[[[j for j,w in enumerate(vals[:nv+i]) if w&b==b] for b in g] for i,g in enumerate(masks)]
    output=[j-nv for j,v in enumerate(vals) if j>=nv and v&positive_mask==positive_mask]
    result={'vertices':vertices,'ors':ors,'output':output,'positive_signatures':masks}
    path=Path('/tmp/oec/pequalnp-pilot-62')/f'or-closure-witness-{args.scenario}-{k}.json';path.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
