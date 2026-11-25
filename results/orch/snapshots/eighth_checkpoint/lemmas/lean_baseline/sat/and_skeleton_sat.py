import argparse,json,time
from pathlib import Path
from grid_taps_synthesis import CNF,Solver,stamp
from core_tap_cost import thresholds
from core_tap_synthesis import truth_columns


def boundary(inputs,edges):
    left=sorted({a for a,b in edges});right=sorted({b for a,b in edges})
    assert not set(left)&set(right) and set(left)|set(right)==set(range(inputs))
    negatives=set()
    for choice in range(1<<len(left)):
        selected={left[i] for i in range(len(left)) if choice>>i&1}
        allowed={b for b in right if not any(a in selected and v==b for a,v in edges)}
        closure={a for a in left if not any(u==a and b in allowed for u,b in edges)}
        negatives.add(sum(1<<v for v in closure|allowed))
    return {(1<<a)|(1<<b) for a,b in edges},negatives


def validate_problem(data):
    n=data['inputs'];edges=[tuple(e) for e in data['edges']]
    assert all(0<=a<n and 0<=b<n and a!=b for a,b in edges)
    positive,negative=boundary(n,edges)
    wanted={(m,1) for m in positive}|{(m,0) for m in negative}
    actual={(t['mask'],t['label']) for t in data['tests']}
    assert actual==wanted and len(actual)==len(data['tests'])
    return edges


def normalize(skeleton):
    n=skeleton['inputs'];gates=[]
    for i,gate in enumerate(skeleton['and_gates']):
        left=sorted(set(gate['left']));right=sorted(set(gate['right']))
        assert all(0<=v<n+i for v in left+right)
        if tuple(v in left for v in range(n+i))<tuple(v in right for v in range(n+i)):
            left,right=right,left
        gates.append({'left':left,'right':right})
    output=sorted(set(skeleton['output']))
    assert all(0<=v<n+len(gates) for v in output)
    return {'inputs':n,'and_gates':gates,'output':output}


def evaluate(skeleton,mask):
    n=skeleton['inputs'];values=[bool(mask>>v&1) for v in range(n)]
    for gate in skeleton['and_gates']:
        values.append(any(values[v] for v in gate['left']) and any(values[v] for v in gate['right']))
    return values,any(values[v] for v in skeleton['output'])


def conjunction(cnf,a,b,hint):
    if a==-1 or b==-1:return -1
    if a==1:return b
    if b==1 or a==b:return a
    z=cnf.var(hint)
    cnf.clause(-z,a);cnf.clause(-z,b);cnf.clause(z,-a,-b)
    return z


def disjunction(cnf,terms,hint):
    if not terms:return -1
    if len(terms)==1:return terms[0]
    z=cnf.var(hint)
    cnf.clause(-z,*terms)
    for term in terms:cnf.clause(-term,z)
    return z


def side_value(cnf,selectors,values,hint_selected,hint_values):
    terms=[]
    for i,(selector,value) in enumerate(zip(selectors,values)):
        if value==-1:continue
        term=selector if value==1 else conjunction(cnf,selector,value,i in hint_selected and hint_values[i])
        terms.append(term)
    return disjunction(cnf,terms,any(hint_values[v] for v in hint_selected))


def encode_assignment(cnf,selected,output,seed,input_literals,hint_mask):
    n=seed['inputs'];hints,hint_output=evaluate(seed,hint_mask)
    values=input_literals.copy()
    for i,((left,right),gate) in enumerate(zip(selected,seed['and_gates'])):
        a=side_value(cnf,left,values,gate['left'],hints)
        b=side_value(cnf,right,values,gate['right'],hints)
        values.append(conjunction(cnf,a,b,hints[n+i]))
    final=side_value(cnf,output,values,seed['output'],hints)
    return values,final


def emit(path,data,seed,dirty=False,side_order=True):
    n=data['inputs'];edges=validate_problem(data);seed=normalize(seed)
    assert n==seed['inputs']
    cnf=CNF(path);selected=[]
    for i,gate in enumerate(seed['and_gates']):
        left=[cnf.var(v in gate['left']) for v in range(n+i)]
        right=[cnf.var(v in gate['right']) for v in range(n+i)]
        selected.append((left,right))
        if side_order:
            equal=1;hint_equal=True
            for v,(a,b) in enumerate(zip(left,right)):
                cnf.clause(-equal,a,-b)
                hint_equal=hint_equal and ((v in gate['left'])==(v in gate['right']))
                next_equal=cnf.var(hint_equal)
                cnf.clause(-next_equal,equal)
                cnf.clause(-next_equal,-a,b);cnf.clause(-next_equal,a,-b)
                cnf.clause(-equal,-a,-b,next_equal);cnf.clause(-equal,a,b,next_equal)
                equal=next_equal
    output=[cnf.var(v in seed['output']) for v in range(n+len(selected))]
    for test in data['tests']:
        mask=test['mask']
        values,final=encode_assignment(cnf,selected,output,seed,
                                      [1 if mask>>v&1 else -1 for v in range(n)],mask)
        cnf.clause(final if test['label'] else -final)
    dirty_inputs=None
    if dirty:
        possibilities=[0]+[1<<v for v in range(n)]+[(1<<a)|(1<<b) for a in range(n) for b in range(a+1,n)]
        possibilities=[m for m in possibilities if not any(m>>a&1 and m>>b&1 for a,b in edges)]
        def hint_score(mask):
            values,out=evaluate(seed,mask)
            return (not any(values[n:]),out,mask.bit_count(),mask)
        hint_mask=min(possibilities,key=hint_score)
        dirty_inputs=[cnf.var(bool(hint_mask>>v&1)) for v in range(n)]
        count=thresholds(cnf,[(v,bool(hint_mask>>i&1)) for i,v in enumerate(dirty_inputs)],2)
        cnf.clause(-count[3])
        for a,b in edges:cnf.clause(-dirty_inputs[a],-dirty_inputs[b])
        values,final=encode_assignment(cnf,selected,output,seed,dirty_inputs,hint_mask)
        cnf.clause(-final)
        cnf.clause(*values[n:])
    cnf.finish()
    return selected,output,dirty_inputs,cnf.variables,cnf.clauses,seed


def decode(solver,selected,output,n):
    gates=[{'left':[v for v,lit in enumerate(left) if solver.truth(lit)],
            'right':[v for v,lit in enumerate(right) if solver.truth(lit)]}
           for left,right in selected]
    return {'inputs':n,'and_gates':gates,'output':[v for v,lit in enumerate(output) if solver.truth(lit)]}


def verify(data,skeleton,dirty_mask=None,full=True):
    n=data['inputs'];edges=validate_problem(data)
    assert skeleton['inputs']==n
    for i,gate in enumerate(skeleton['and_gates']):
        for side in ('left','right'):
            assert gate[side]==sorted(set(gate[side]))
            assert all(0<=v<n+i for v in gate[side])
    assert skeleton['output']==sorted(set(skeleton['output']))
    assert all(0<=v<n+len(skeleton['and_gates']) for v in skeleton['output'])
    for test in data['tests']:assert evaluate(skeleton,test['mask'])[1]==bool(test['label'])
    if dirty_mask is not None:
        assert 0<=dirty_mask<(1<<n) and dirty_mask.bit_count()<=2
        assert not any(dirty_mask>>a&1 and dirty_mask>>b&1 for a,b in edges)
        values,final=evaluate(skeleton,dirty_mask)
        assert not final and any(values[n:])
    if full:
        values=truth_columns(n);expected=0
        for a,b in edges:expected|=values[a]&values[b]
        for gate in skeleton['and_gates']:
            a=b=0
            for v in gate['left']:a|=values[v]
            for v in gate['right']:b|=values[v]
            values.append(a&b)
        actual=0
        for v in skeleton['output']:actual|=values[v]
        assert actual==expected
    return True


def solve(data,seed,folder,seconds,attempts=1,dirty=False,calibration=False):
    folder.mkdir(parents=True,exist_ok=True)
    selected,output,dirty_inputs,nvars,nclauses,seed=emit(folder/'model.cnf',data,seed,dirty)
    (folder/'phase.json').write_text(json.dumps(seed))
    spec={'declared_binary_AND_nodes':len(selected),'OR_subsets':'arbitrary raw and earlierAND subsets; empty means false',
          'constants':'false via emptyOR; no trueconstant','unused_nodes':'allowed','fanin_cardinality_caps':None,
          'side_order':'commutative lexicographic orientation only','dirty_required':dirty,
          'total_gate_bound_established':False,'UNSAT_scope':'this declaredANDcount abstraction with stated constraints'}
    (folder/'model-spec.json').write_text(json.dumps(spec,indent=2))
    solver=Solver(57189)
    for left,right in selected:
        for literal in left+right:solver.freeze(literal)
    for literal in output+(dirty_inputs or []):solver.freeze(literal)
    with (folder/'model.cnf').open() as source:
        for line in source:
            if not line.startswith('p'):solver.add(*map(int,line.split()[:-1]))
    stamp('AND-SKELETON','inputs',data['inputs'],'ANDnodes',len(selected),'tests',len(data['tests']),
          'dirty',dirty,'variables',nvars,'clauses',nclauses,'NO-TOTAL-GATE-BOUND')
    result=0
    for attempt in range(attempts):
        begin=time.monotonic();result=solver.solve(seconds)
        stamp('ATTEMPT',attempt,'SOLVER',result,'SECONDS',round(time.monotonic()-begin,4))
        if result!=0:break
    if result==10:
        answer=decode(solver,selected,output,data['inputs'])
        dirty_mask=sum(1<<i for i,lit in enumerate(dirty_inputs) if solver.truth(lit)) if dirty_inputs is not None else None
        assert verify(data,answer,dirty_mask,full=True)
        answer.update({'edges':data['edges'],'input_original':data.get('input_original',list(range(data['inputs']))),
                       'and_count':len(selected),'exact_boundary_verified':True,'full_truth_verified':True,
                       'dirty_input':dirty_mask,'calibration':calibration,'total_gate_bound_established':False,
                       'status':'exact AND skeleton; OR assembly and total gate count are not established'})
        name='BASELINE-AND-SKELETON.json' if calibration else 'EXACT-AND-SKELETON.json'
        (folder/name).write_text(json.dumps(answer))
        stamp('EXACT AND SKELETON','ANDnodes',len(selected),'dirty_input',dirty_mask,'NO-TOTAL-GATE-BOUND')
    elif result==20:stamp('UNSAT FOR STATED AND-COUNT ABSTRACTION; NOT A FULL GATE LOWER BOUND')
    else:stamp('UNKNOWN FOR STATED AND-COUNT ABSTRACTION')
    solver.close()
    return result


def main():
    parser=argparse.ArgumentParser(description='AND-node synthesis with unrestricted OR subsets; no total-gate cost bound')
    parser.add_argument('problem',type=Path);parser.add_argument('seed',type=Path);parser.add_argument('output',type=Path)
    parser.add_argument('--seconds',type=int,default=300);parser.add_argument('--attempts',type=int,default=1)
    parser.add_argument('--dirty',action='store_true');parser.add_argument('--calibrate',action='store_true')
    args=parser.parse_args();assert not (args.calibrate and args.dirty)
    data=json.loads(args.problem.read_text());seed=json.loads(args.seed.read_text())
    if args.calibrate:verify(data,seed,full=False)
    solve(data,seed,args.output,args.seconds,args.attempts,args.dirty,args.calibrate)

if __name__=='__main__':main()
