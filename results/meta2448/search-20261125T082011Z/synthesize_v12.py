import argparse
import hashlib
import itertools
import json
from pathlib import Path
import resource
import subprocess
import time


class CNF:
    def __init__(self):
        self.variables = 0
        self.clauses = []

    def var(self):
        self.variables += 1
        return self.variables

    @staticmethod
    def neg(x):
        return not x if type(x) is bool else -x

    def add(self, xs):
        s = set()
        for x in xs:
            if x is True: return
            if x is False: continue
            if -x in s: return
            s.add(x)
        self.clauses.append(sorted(s,key=lambda x:(abs(x),x)))

    def conj(self, xs):
        s = set()
        for x in xs:
            if x is False: return False
            if x is True: continue
            if -x in s: return False
            s.add(x)
        if not s: return True
        if len(s) == 1: return next(iter(s))
        y = self.var()
        for x in s: self.add([-y,x])
        self.add([y]+[-x for x in s])
        return y

    def disj(self, xs):
        return self.neg(self.conj(self.neg(x) for x in xs))

    def equal(self,a,b):
        self.add([self.neg(a),b]);self.add([a,self.neg(b)])

    def onehot(self,xs):
        self.add(xs)
        for a,b in itertools.combinations(xs,2): self.add([-a,-b])

    def write(self,path):
        with path.open('w') as out:
            out.write(f'p cnf {self.variables} {len(self.clauses)}\n')
            for c in self.clauses: out.write(' '.join(map(str,c))+' 0\n')


ap=argparse.ArgumentParser()
ap.add_argument('--graph',choices=['path4','cycle5','cycle6','cycle7','petersen','theta233','theta333','cycle5tail','petersen-minus-adjacent'],required=True)
ap.add_argument('--gates',type=int,required=True)
ap.add_argument('--profile',choices=['any','star','nonstar'],default='any')
ap.add_argument('--seconds',type=int,default=60)
ap.add_argument('--tag',required=True)
ap.add_argument('--cnf-only',action='store_true')
ap.add_argument('--fixed-star-baseline',action='store_true')
ap.add_argument('--symmetry-first',action='store_true')
ap.add_argument('--essential-gates',action='store_true')
ap.add_argument('--ordered-independent',action='store_true')
ap.add_argument('--unique-signatures',action='store_true')
ap.add_argument('--undominated-signatures',action='store_true')
ap.add_argument('--at-most',action='store_true')
ap.add_argument('--padding-gates',type=int,default=0)
ap.add_argument('--nonstar-prefix',action='store_true')
ap.add_argument('--bypass-sensitive',action='store_true')
ap.add_argument('--constant-sensitive',action='store_true')
ap.add_argument('--count-bounds',action='store_true')
args=ap.parse_args()
assert not args.nonstar_prefix or (args.at_most and args.profile=='nonstar')
assert args.padding_gates>=0
assert not args.padding_gates or (args.fixed_star_baseline and args.at_most)
resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3))
base=Path('/tmp/oec/pequalnp-pilot-62/meta2448')
stem=base/args.tag
assert not stem.with_suffix('.cnf').exists()
if args.graph=='petersen-minus-adjacent':
    n=8;edges=[(0,1),(0,5),(1,2),(1,6),(2,7),(3,5),(3,6),(4,6),(4,7),(5,7)]
elif args.graph=='theta233':
    n=7;edges=[(0,2),(2,1),(0,3),(3,4),(4,1),(0,5),(5,6),(6,1)]
elif args.graph=='theta333':
    n=8;edges=[(0,2),(2,3),(3,1),(0,4),(4,5),(5,1),(0,6),(6,7),(7,1)]
elif args.graph=='cycle5tail':
    n=6;edges=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5)]
elif args.graph=='path4':
    n=4;edges=[(0,1),(1,2),(2,3)]
elif args.graph.startswith('cycle'):
    n=int(args.graph[5:]);edges=[tuple(sorted((i,(i+1)%n))) for i in range(n)]
else:
    n=10
    edges=[(i,(i+1)%5) for i in range(5)]+[(i,i+5) for i in range(5)]+[(i+5,(i+2)%5+5) for i in range(5)]
edges=sorted(set(tuple(sorted(e)) for e in edges))
neighbors=[{v for e in edges if u in e for v in e if v!=u} for u in range(n)]
assert all(len(neighbors[a]&neighbors[b])<=1 for a,b in itertools.combinations(range(n),2))
assert all(a!=b for a,b in edges)
edge_masks=[(1<<a)|(1<<b) for a,b in edges]
false=[q for q in range(1<<n) if not any(q&e==e for e in edge_masks)]
negative=[q for q in false if all(any((q|(1<<i))&e==e for e in edge_masks) for i in range(n) if not(q>>i&1))]
assert all(any(q&~r==0 for r in negative) for q in false)
samples=edge_masks+negative
vertex_cover_number=n-max(q.bit_count() for q in negative)
and_lower_bound=max((len(negative)-1).bit_length(),min(5,vertex_cover_number))
or_lower_bound=(len(edges)-1).bit_length()
disjoint=[(i,j) for i,j in itertools.combinations(range(len(edges)),2) if not(edge_masks[i]&edge_masks[j])]
assert not any((a,b) in edges and (b,c) in edges and (a,c) in edges for a,b,c in itertools.combinations(range(n),3))
automorphisms=[]
first_pairs=[]
if args.symmetry_first:
    adjacency=[[tuple(sorted((a,b))) in edges for b in range(n)] for a in range(n)]
    order=sorted(range(n),key=lambda v:(-sum(adjacency[v]),v))
    image=[-1]*n;used=set()
    def extend(depth):
        if depth==n:
            automorphisms.append(image.copy());return
        a=order[depth]
        for b in range(n):
            if b in used or sum(adjacency[a])!=sum(adjacency[b]):continue
            if any(adjacency[a][c]!=adjacency[b][image[c]] for c in order[:depth]):continue
            image[a]=b;used.add(b);extend(depth+1);used.remove(b);image[a]=-1
    extend(0)
    assert automorphisms
    first_pairs=sorted({min(tuple(sorted((action[a],action[b]))) for action in automorphisms)
                        for a,b in itertools.combinations(range(n),2)})
k=args.gates
assert k>0
baseline=[]
if args.fixed_star_baseline:
    covers=[q for q in range(1<<n) if all(q&e for e in edge_masks)]
    cover=min(covers,key=lambda q:(q.bit_count(),q))
    assigned={i:[] for i in range(n) if cover>>i&1}
    for a,b in edges: assigned[a if a in assigned else b].append(b if a in assigned else a)
    terms=[]
    def gate(op,a,b):
        baseline.append([op,*sorted((a,b))]);return n+len(baseline)-1
    for c,neighbors in assigned.items():
        if not neighbors:continue
        value=neighbors[0]
        for other in neighbors[1:]:value=gate('or',value,other)
        terms.append(gate('and',c,value))
    result=terms[0]
    for other in terms[1:]:result=gate('or',result,other)
    assert len(baseline)+args.padding_gates==k
    for _ in range(args.padding_gates):
        op,operand,_=baseline[-1]
        result=gate(op,result,operand)
    assert len(baseline)==k and result==n+k-1
baseline_order_swaps=[]
if args.ordered_independent and baseline:
    signatures=[sum(bool(q>>i&1)<<r for r,q in enumerate(samples)) for i in range(n)]
    for op,a,b in baseline:
        signatures.append(signatures[a]&signatures[b] if op=='and' else signatures[a]|signatures[b])
    changed=True
    while changed:
        changed=False
        for g in range(2,k):
            previous=n+g-1;current=n+g
            if previous not in baseline[g][1:] and signatures[previous]>signatures[current]:
                assert g<k-1
                baseline[g-1],baseline[g]=baseline[g],baseline[g-1]
                signatures[previous],signatures[current]=signatures[current],signatures[previous]
                def rename(v):return current if v==previous else previous if v==current else v
                baseline=[[op,*sorted((rename(a),rename(b)))] for op,a,b in baseline]
                baseline_order_swaps.append([g-1,g]);changed=True
                assert len(baseline_order_swaps)<=k*k
    assert all(a<b<n+g for g,(_,a,b) in enumerate(baseline))
cnf=CNF();values=[[bool(q>>i&1) for q in samples] for i in range(n)]
selectors=[];operations=[];cones=[];ownership=[]
earlier_target=False
prefix_bad=[]
operand_values=[];first_target_flags=[];target_before_flags=[];seen_target=False
for g in range(k):
    target_before=earlier_target
    target_before_flags.append(seen_target)
    operation=cnf.var();operations.append(operation)
    sels=[[cnf.var() for _ in range(n+g)] for _ in range(2)];selectors.append(sels)
    for group in sels:cnf.onehot(group)
    for a in range(n+g):
        for b in range(a+1):cnf.add([-sels[0][a],-sels[1][b]])
    branches=[]
    for side in range(2):
        branch=[cnf.var() for _ in samples];branches.append(branch)
        for i,sel in enumerate(sels[side]):
            for j,out in enumerate(branch):
                cnf.add([-sel,-out,values[i][j]])
                cnf.add([-sel,out,cnf.neg(values[i][j])])
    operand_values.append(branches)
    # A minimum circuit cannot have comparable operands on all separating rows:
    # replacing that gate by the selected operand preserves all constraints.
    cnf.add([earlier_target]+[cnf.conj([a,cnf.neg(b)]) for a,b in zip(*branches)])
    cnf.add([earlier_target]+[cnf.conj([b,cnf.neg(a)]) for a,b in zip(*branches)])
    result=[]
    for a,b in zip(*branches):
        out=cnf.var();result.append(out)
        cnf.add([-operation,-out,a]);cnf.add([-operation,-out,b]);cnf.add([-operation,out,-a,-b])
        cnf.add([operation,out,-a]);cnf.add([operation,out,-b]);cnf.add([operation,-out,a,b])
    if args.unique_signatures:
        # In a globally minimum circuit, no gate can alias an earlier signal
        # on the complete separating set: deletion preserves the exact output.
        for earlier in values:
            cnf.add([earlier_target]+[cnf.disj([cnf.conj([a,cnf.neg(b)]),cnf.conj([cnf.neg(a),b])])
                     for a,b in zip(result,earlier)])
    if args.undominated_signatures:
        # Earlier wire w can replace this gate whenever w is at least as true
        # on positive edges and at most as true on maximal false rows.
        for earlier in values:
            witnesses=[cnf.conj([a,cnf.neg(b)]) for a,b in zip(result[:len(edges)],earlier[:len(edges)])]
            witnesses += [cnf.conj([cnf.neg(a),b]) for a,b in zip(result[len(edges):],earlier[len(edges):])]
            cnf.add([earlier_target]+witnesses)
    values.append(result)
    target_here=cnf.conj(result[:len(edges)]+[cnf.neg(v) for v in result[len(edges):]])
    first_target_flags.append(cnf.conj([target_here,cnf.neg(seen_target)]))
    seen_target=cnf.disj([seen_target,target_here])
    if args.at_most:earlier_target=seen_target
    if args.ordered_independent and g>=2:
        equal=True;less=[]
        for a,b in reversed(list(zip(values[n+g-1],result))):
            less.append(cnf.conj([equal,cnf.neg(a),b]))
            equal=cnf.conj([equal,cnf.disj([cnf.neg(a),b]),cnf.disj([a,cnf.neg(b)])])
        cnf.add([sels[0][n+g-1],sels[1][n+g-1]]+less+[equal])
    if args.essential_gates:
        # Otherwise replace this gate by a constant and simplify, preserving
        # every separating row while deleting at least one paid gate.
        cnf.add(result[:len(edges)])
        cnf.add([cnf.neg(v) for v in result[len(edges):]])
    cone=[]
    for i in (range(g) if args.profile!='any' else []):
        cone.append(cnf.disj(cnf.conj([sels[side][n+r],True if i==r else cones[r][i]])
                             for side in range(2) for r in range(i,g)))
    cones.append(cone)
    own=[]
    for e in (range(len(edges)) if args.profile!='any' else []):
        below=[cnf.neg(cnf.conj([cone[i],operations[i],values[n+i][e]])) for i in range(g)]
        own.append(cnf.conj([operation,values[n+g][e]]+below))
    ownership.append(own)
    if args.nonstar_prefix:
        prefix_bad += [cnf.conj([cnf.neg(target_before),own[a],own[b]]) for a,b in disjoint]
    if args.profile=='star':
        for a,b in disjoint:cnf.add([cnf.neg(own[a]),cnf.neg(own[b])])
    if baseline:
        op,a,b=baseline[g];cnf.add([operation if op=='and' else -operation])
        cnf.add([sels[0][a]]);cnf.add([sels[1][b]])
for row in range(len(samples)):cnf.add([values[-1][row] if row<len(edges) else cnf.neg(values[-1][row])])
for g in range(k-1):
    cnf.add([selectors[h][side][n+g] for h in range(g+1,k) for side in range(2)])
if args.symmetry_first and not args.fixed_star_baseline:
    cnf.add([cnf.conj([selectors[0][0][a],selectors[0][1][b]]) for a,b in first_pairs])
if args.profile=='nonstar':
    cnf.add(prefix_bad if args.nonstar_prefix else [cnf.conj([own[a],own[b]]) for own in ownership for a,b in disjoint])
# Accepted maximal-false and small-cover bounds, and the binary dual bound,
# constrain counts in the earliest exact prefix, including padded models.
if args.count_bounds:
    and_counts=[True]+[False]*and_lower_bound
    or_counts=[True]+[False]*or_lower_bound
    for g,operation in enumerate(operations):
        and_counts=[True]+[cnf.disj([and_counts[t],cnf.conj([and_counts[t-1],operation])]) for t in range(1,and_lower_bound+1)]
        or_counts=[True]+[cnf.disj([or_counts[t],cnf.conj([or_counts[t-1],cnf.neg(operation)])]) for t in range(1,or_lower_bound+1)]
        cnf.add([cnf.neg(first_target_flags[g]),and_counts[-1]])
        cnf.add([cnf.neg(first_target_flags[g]),or_counts[-1]])
# Replay every changed wire through all later gates, including reconvergence.
# Test at the earliest exact target prefix, before any optional padding.
if args.bypass_sensitive or args.constant_sensitive:
    for g in range(k):
        replacements=[]
        if args.bypass_sensitive:replacements += [('operand0',operand_values[g][0]),('operand1',operand_values[g][1])]
        if args.constant_sensitive:replacements += [('false',[False]*len(samples)),('true',[True]*len(samples))]
        for kind,replacement in replacements:
            shadow=values[:n+g]+[replacement]
            for h in range(g+1,k):
                branches=[]
                for side in range(2):
                    branch=[cnf.var() for _ in samples];branches.append(branch)
                    for i,sel in enumerate(selectors[h][side]):
                        for r,out in enumerate(branch):
                            cnf.add([-sel,-out,shadow[i][r]])
                            cnf.add([-sel,out,cnf.neg(shadow[i][r])])
                operation=operations[h];result=[]
                for a,b in zip(*branches):
                    out=cnf.var();result.append(out)
                    cnf.add([-operation,-out,a]);cnf.add([-operation,-out,b]);cnf.add([-operation,out,-a,-b])
                    cnf.add([operation,out,-a]);cnf.add([operation,out,-b]);cnf.add([operation,-out,a,b])
                shadow.append(result)
            positive_loss=cnf.disj(cnf.conj([first_target_flags[h],cnf.disj(cnf.neg(v) for v in shadow[n+h][:len(edges)])]) for h in range(g,k))
            negative_gain=cnf.disj(cnf.conj([first_target_flags[h],cnf.disj(shadow[n+h][len(edges):])]) for h in range(g,k))
            guard=target_before_flags[g]
            if kind.startswith('operand'):
                cnf.add([guard,operations[g],positive_loss])
                cnf.add([guard,-operations[g],negative_gain])
            elif kind=='false':cnf.add([guard,positive_loss])
            else:cnf.add([guard,negative_gain])
cnf.write(stem.with_suffix('.cnf'))
mapping={'graph':args.graph,'input_count':n,'edges':edges,'positive_samples':edge_masks,'negative_samples':negative,
         'gate_count':k,'profile':args.profile,'operations':operations,'selectors':selectors,'baseline':baseline,
         'variables':cnf.variables,'clauses':len(cnf.clauses),
         'essential_gates':args.essential_gates,'symmetry_first':args.symmetry_first,
         'automorphisms':automorphisms,'first_pairs':first_pairs,
         'ordered_independent':args.ordered_independent,'baseline_order_swaps':baseline_order_swaps,
         'unique_signatures':args.unique_signatures,'undominated_signatures':args.undominated_signatures,'at_most':args.at_most,'padding_gates':args.padding_gates,'nonstar_prefix':args.nonstar_prefix,'bypass_sensitive':args.bypass_sensitive,'constant_sensitive':args.constant_sensitive,'count_bounds':args.count_bounds,
         'vertex_cover_number':vertex_cover_number,'and_lower_bound':and_lower_bound,'or_lower_bound':or_lower_bound,
         'scope':'Proper binary AND/OR gates, final output and all gates used. Operand incomparability and optional uniqueness/dominance hold before and at the first target gate; in at-most mode later padding gates are exempt. Normalization requires proof for claims about arbitrary Lean circuits. Nonstar whole-circuit status need not hold for its earliest exact prefix.'}
stem.with_suffix('.mapping.json').write_text(json.dumps(mapping,indent=2)+'\n')
print(json.dumps({key:mapping[key] for key in ['graph','input_count','gate_count','profile','variables','clauses']}),flush=True)
if args.cnf_only:raise SystemExit(0)
command=['/tmp/oec/pequalnp-pilot-62/elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical','-t',str(args.seconds),'-w',str(stem.with_suffix('.sol')),str(stem.with_suffix('.cnf'))]
stem.with_suffix('.command.json').write_text(json.dumps(command,indent=2)+'\n')
start=time.monotonic()
with stem.with_suffix('.solver.log').open('w') as out:done=subprocess.run(command,stdout=out,stderr=subprocess.STDOUT)
status={'result':{10:'sat',20:'unsat'}.get(done.returncode,'unknown'),'solver_exit':done.returncode,'elapsed':time.monotonic()-start,'peak_child_KiB':resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss}
stem.with_suffix('.status.json').write_text(json.dumps(status,indent=2)+'\n');print(json.dumps(status),flush=True)
if done.returncode!=10:raise SystemExit(0)
assignment={}
for line in stem.with_suffix('.sol').read_text().splitlines():
    if line.startswith('v '):
        for word in line.split()[1:]:
            lit=int(word)
            if lit:assignment[abs(lit)]=lit>0
gates=[];actual_cones=[]
for g in range(k):
    children=[]
    for sels in selectors[g]:
        chosen=[i for i,s in enumerate(sels) if assignment[s]];assert len(chosen)==1;children+=chosen
    assert children[0]<children[1]
    gates.append(['and' if assignment[operations[g]] else 'or',*children])
    cone=set()
    for child in children:
        if child>=n:cone.add(child-n);cone.update(actual_cones[child-n])
    actual_cones.append(cone)
truth=[]
for q in range(1<<n):
    row=[bool(q>>i&1) for i in range(n)]
    for op,a,b in gates:row.append(row[a] and row[b] if op=='and' else row[a] or row[b])
    assert row[-1]==any(q&e==e for e in edge_masks)
    truth.append(row)
if args.essential_gates:
    for g in range(k):
        assert any(truth[q][n+g] for q in edge_masks)
        assert any(not truth[q][n+g] for q in negative)
if args.symmetry_first and not args.fixed_star_baseline:
    assert tuple(gates[0][1:]) in first_pairs
if args.ordered_independent:
    for g in range(2,k):
        previous=sum(truth[q][n+g-1]<<r for r,q in enumerate(samples))
        current=sum(truth[q][n+g]<<r for r,q in enumerate(samples))
        assert n+g-1 in gates[g][1:] or previous<=current
if args.unique_signatures:
    signatures=[tuple(truth[q][i] for q in samples) for i in range(n+k)]
    target_signature=tuple([True]*len(edges)+[False]*len(negative))
    earlier_target_seen=False
    for g in range(k):
        if not earlier_target_seen:assert signatures[n+g] not in signatures[:n+g]
        if args.at_most and signatures[n+g]==target_signature:earlier_target_seen=True
if args.undominated_signatures:
    earlier_target_seen=False
    for g in range(k):
        if not earlier_target_seen:
            for i in range(n+g):
                assert any(truth[q][n+g] and not truth[q][i] for q in edge_masks) or any(not truth[q][n+g] and truth[q][i] for q in negative)
        if args.at_most and all(truth[q][n+g]==(r<len(edges)) for r,q in enumerate(samples)):earlier_target_seen=True
owned=[]
for g,(op,_,_) in enumerate(gates):
    owned.append([e for e,q in enumerate(edge_masks) if op=='and' and truth[q][n+g] and
                  all(gates[i][0]!='and' or not truth[q][n+i] for i in actual_cones[g])])
star=all(not own or any(all(v in edges[e] for e in own) for v in range(n)) for own in owned)
assert args.profile=='any' or star==(args.profile=='star')
first_target_gate=next(g for g in range(k) if all(truth[q][n+g]==(r<len(edges)) for r,q in enumerate(samples)))
assert all(truth[q][n+first_target_gate]==any(q&e==e for e in edge_masks) for q in range(1<<n))
prefix_star=all(not own or any(all(v in edges[e] for e in own) for v in range(n)) for own in owned[:first_target_gate+1])
if args.count_bounds:
    assert sum(op=='and' for op,_,_ in gates[:first_target_gate+1])>=and_lower_bound
    assert sum(op=='or' for op,_,_ in gates[:first_target_gate+1])>=or_lower_bound
sensitivity_checks=[]
if args.bypass_sensitive or args.constant_sensitive:
    for g in range(first_target_gate+1):
        kinds=[]
        if args.bypass_sensitive:kinds += ['operand0','operand1']
        if args.constant_sensitive:kinds += ['false','true']
        for kind in kinds:
            lost=[];gained=[]
            for r,q in enumerate(samples):
                shadow=truth[q][:n+g]
                replacement=(truth[q][gates[g][1+int(kind[-1])]] if kind.startswith('operand') else kind=='true')
                shadow.append(replacement)
                for op,a,b in gates[g+1:first_target_gate+1]:shadow.append(shadow[a] and shadow[b] if op=='and' else shadow[a] or shadow[b])
                if r<len(edges) and not shadow[-1]:lost.append(q)
                if r>=len(edges) and shadow[-1]:gained.append(q)
            if kind.startswith('operand'):assert (gained if gates[g][0]=='and' else lost)
            elif kind=='false':assert lost
            else:assert gained
            sensitivity_checks.append({'gate':g,'replacement':kind,'lost_positive_inputs':lost,'gained_negative_inputs':gained})
if args.nonstar_prefix:assert not prefix_star
witness={'sensitivity_checks':sensitivity_checks,'effective_prefix_has_star_profile':prefix_star,'first_target_gate':first_target_gate,'effective_prefix_gate_count':first_target_gate+1,'graph':args.graph,'input_count':n,'edges':edges,'gate_count':k,'gates':gates,
         'owned_edge_indices':owned,'has_star_profile':star,'checked_assignments':1<<n}
stem.with_suffix('.witness.json').write_text(json.dumps(witness,indent=2)+'\n')
print('WITNESS',json.dumps(witness),flush=True)
