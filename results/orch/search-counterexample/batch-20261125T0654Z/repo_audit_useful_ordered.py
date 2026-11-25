import ast
import hashlib
import itertools
import json
from pathlib import Path

B=Path('/tmp/oec/pequalnp-pilot-62')
source=(B/'multi_output_useful_ordered_cnf.py').read_text()
old=(B/'global_ordered_cnf.py').read_text()
getfun=lambda s: next(n for n in ast.parse(s).body if isinstance(n,ast.FunctionDef) and n.name=='normalize_adjacent_order')
assert ast.dump(getfun(source))==ast.dump(getfun(old))
start='    if args.ordered_independent and gate>=2:'
newblock=source.split(start,1)[1].split('for target in target_masks:',1)[0]
oldblock=old.split(start,1)[1].split('full_positive =',1)[0]
assert newblock==oldblock.replace('[:np]','[:nv]').replace('for sig in branches]','for sig in branch_signatures]')
runner=(B/'solve_multi_cnf_v3.py').read_text()
assert runner==(B/'solve_multi_cnf_v2.py').read_text().replace('assert address_limit>0','assert 0<address_limit<=4*1024**3')

pencils=[sum(1<<l for l in range(13) if (p-l)%13 in {0,1,3,9}) for p in range(13)]
caps=[q for q in range(8192) if all((q&t).bit_count()<=2 for t in pencils)]
assert len(caps)==560
allbits=(1<<len(caps))-1
input_values=[sum(1<<r for r,q in enumerate(caps) if q>>i&1) for i in range(13)]
pairs=[]
for t in pencils:
    ids=[i for i in range(13) if t>>i&1]
    a,b=(1<<ids[0])|(1<<ids[1]),(1<<ids[2])|(1<<ids[3])
    pairs += [sorted([1<<ids[0],1<<ids[1]]),sorted([1<<ids[2],1<<ids[3]]),sorted([a,b])]
assert len(pairs)==len(set(map(tuple,pairs)))==39
first=pairs[0][:]
def canonical(ps):
    positive=[1<<i for i in range(13)];values=input_values[:];ops=[]
    for a,b in ps:
        branches=[];chosen=[]
        for s in [a,b]:
            refs=[i for i,w in enumerate(positive) if w&s==s];assert refs
            support=(1<<13)-1;value=allbits
            for i in refs:support&=positive[i];value&=values[i]
            assert support==s
            branches.append(value);chosen.append(refs)
        ops.append(chosen);positive.append(a|b);values.append(branches[0]|branches[1])
    outs=[]
    for t in pencils:
        refs=[i for i,w in enumerate(positive) if w&t==t];assert refs
        value=allbits
        for i in refs:value&=values[i]
        assert value==sum(1<<r for r,q in enumerate(caps) if q&t)
        outs.append(refs)
    exact=[i for i,w in enumerate(positive) if w==pencils[0]];assert exact
    assert any(any(not(values[i]>>r&1) for r,q in enumerate(caps) if q.bit_count()==4 and not q&pencils[0]) for i in exact)
    return {tuple(pair):values[13+i] for i,pair in enumerate(ps)},ops,outs
previous,_,_=canonical(pairs);swaps=[];changed=True
while changed:
    changed=False
    for g in range(2,len(pairs)):
        a=pairs[g-1][0]|pairs[g-1][1];b=pairs[g][0]|pairs[g][1]
        if a>b and all(s&a!=s for s in pairs[g]):
            pairs[g-1],pairs[g]=pairs[g],pairs[g-1]
            current,_,_=canonical(pairs)
            assert all(current[key]&~value==0 for key,value in previous.items())
            previous=current;swaps.append([g-1,g]);changed=True
assert pairs[0]==first
mapping=json.loads((B/'useful-ordered-pencil39-control.mapping.json').read_text())
assert mapping['fixed_baseline_order_swaps']==swaps
assert mapping['ordered_independent'] and mapping['useful_exact_pencil'] and mapping['exact_pencil_required']==0
assert mapping['variables']==777656 and mapping['clauses']==2848065
_,ops,outs=canonical(pairs)
ref=lambda i:13+i if i<13 else 26+i-13
global_ops=[[[ref(i) for i in branch] for branch in pair] for pair in ops]
terms=[[p]+[ref(i) for i in refs] for p,refs in enumerate(outs)];output=terms[0]
for term in terms[1:]:global_ops.append([output,term]);output=[26+len(global_ops)-1]
assert len(global_ops)==51
def ev(q):
    vs=[bool(q>>i&1) for i in range(26)]
    for a,b in global_ops:vs.append(all(vs[i] for i in a) or all(vs[i] for i in b))
    return all(vs[i] for i in output)
geom=json.loads((B/'geometry-data.json').read_text())
positive=[(1<<p)|(1<<(13+l)) for p in range(13) for l in range(13) if (p-l)%13 in {0,1,3,9}]
negative=[r['S']|(r['D']<<13) for r in geom['generic']]+[1<<i for i in range(26)]+[0]
assert all(ev(q) for q in positive) and not any(ev(q) for q in negative)
names=['multi_output_useful_ordered_cnf.py','solve_multi_cnf_v3.py','useful-ordered-pencil39-control.mapping.json','useful-ordered-pencil39-control.encode.log','useful-pencil39-unrun-input-recovery.json']
report={'reviewer':'repo_audit','status':'PASS combined ordering source and guarded multioutput runner; no solver or Lean run','scope':'Restricted13-output39-OR baseline control and preparation for38-OR query.39 control embeds to51 and is not a counterexample.','checks':{'normalizer_ast_identical_to_approved_global':True,'comparator_identical_modulo_dimension_and_branch_name':True,'normalization_swaps':len(swaps),'all560cap_values_checked_after_every_swap':True,'each_gate_values_only_decrease_after_swaps':True,'gate_zero_unchanged':True,'useful_exact_P0_retained':True,'output_cap_pairs_checked_each_time':560*13,'final_global_control_samples':547,'global_control_or_count':51,'runner_ceiling_restored_gib':4},'runner_review':['Same owned process-group memory guard, reader cleanup and nonzero-reader verdict suppression as reviewed runner. Gzip input digest verified before launch.','Reconstructs actual canonical references from signatures, checks exact positive closure/incomparability, all encoded output rows and false-OR bounds, useful exact-support row predicate, and adjacent ordering assertions.','Independently regenerates all560 geometric caps and replays7280 output-cap pairs. Full13-output model lifts through12point-weighted OR joins and checks all52positive/468generic/26singleton global samples; this audit additionally checked empty.','Address-space default1.25GiB with restored0<cap<=4GiB; parent chooses actual cap/shared thresholds. No arbitrary process termination or credential access.'],'files':{n:hashlib.sha256((B/n).read_bytes()).hexdigest() for n in names}}
(B/'useful-ordered-independent-audit.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
