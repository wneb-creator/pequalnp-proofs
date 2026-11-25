"""Assemble an AND-count skeleton with optionally correlated OR-feature inputs.

Every optimization preserves complete Boolean gate functions. OR sharing uses
sets of raw/prior-AND atoms; lazy emission enforces availability. Exact DNF
dominance is optional and is skipped whenever its bounded calculation is unknown.
"""
import argparse,json,itertools
from collections import Counter
from pathlib import Path

class DNF:
    def __init__(self,cap=20000):self.cap=cap;self.skipped=0
    def normalize(self,terms):
        terms=set(terms)
        if len(terms)>self.cap:self.skipped+=1;return None
        result=[]
        for x in sorted(terms,key=lambda x:(x.bit_count(),x)):
            if not any(y&x==y for y in result):result.append(x)
        return tuple(result)
    def union(self,children):
        if any(x is None for x in children):return None
        return self.normalize(t for child in children for t in child)
    def product(self,left,right):
        if left==() or right==():return ()
        if left is None or right is None:return None
        if len(left)*len(right)>self.cap*8:self.skipped+=1;return None
        return self.normalize(x|y for x in left for y in right)
    @staticmethod
    def implies(left,right):
        return left is not None and right is not None and all(any(y&x==y for y in right) for x in left)

def compact(inputs,gates,output):
    mapping={i:i for i in range(inputs)};made=[];cache={}
    for i,(op,a,b) in enumerate(gates):
        a,b=sorted((mapping[a],mapping[b]));key=(op,a,b)
        if a==b:mapping[inputs+i]=a
        else:
            if key not in cache:cache[key]=inputs+len(made);made.append(list(key))
            mapping[inputs+i]=cache[key]
    output=mapping[output];live={output}
    for i in range(len(made)-1,-1,-1):
        if inputs+i in live:live.update(made[i][1:])
    ren={i:i for i in range(inputs)};out=[]
    for i,(op,a,b) in enumerate(made):
        if inputs+i in live:ren[inputs+i]=inputs+len(out);out.append([op,ren[a],ren[b]])
    return out,ren[output]

def assemble_skeleton(skeleton,semantic=True,sharing=True,dnf_cap=20000,input_dnfs=None,semantic_inputs=None):
    n=skeleton['inputs'];ands=skeleton['and_gates'];k=len(ands);base=n+k
    assert n>0 and k==skeleton.get('and_count',k)
    for i,g in enumerate(ands):
        for side in ('left','right'):
            assert g[side]==sorted(set(g[side]))
            assert all(0<=x<n+i for x in g[side])
    assert all(0<=x<base for x in skeleton['output'])
    dnf=DNF(dnf_cap)
    semantic_n=n if semantic_inputs is None else semantic_inputs
    initial_dnfs=[(1<<i,) for i in range(n)] if input_dnfs is None else [dnf.normalize(x) for x in input_dnfs]
    assert len(initial_dnfs)==n and all(x is not None for x in initial_dnfs)
    assert all(0<=term<(1<<semantic_n) for x in initial_dnfs for term in x)
    atom_dnf=initial_dnfs[:]
    original_sides=[]
    for g in ands:
        left=dnf.union([atom_dnf[x] for x in g['left']]);right=dnf.union([atom_dnf[x] for x in g['right']])
        original_sides.extend([left,right]);atom_dnf.append(dnf.product(left,right))
    original_output=dnf.union([atom_dnf[x] for x in skeleton['output']])
    original_sides.append(original_output)
    expressions=[set(g[side]) for g in ands for side in ('left','right')]+[set(skeleton['output'])]
    naive_or=sum(max(0,len(x)-1) for x in expressions)
    dominance=[]
    if semantic:
        for task,expression in enumerate(expressions):
            for source in sorted(expression,reverse=True):
                targets=[x for x in sorted(expression) if x!=source and DNF.implies(atom_dnf[source],atom_dnf[x])]
                if targets:
                    target=targets[0];expression.remove(source)
                    dominance.append({'task':task,'removed':source,'dominating':target})
    supports={i:frozenset([i]) for i in range(base)}
    definitions={};factors=[]
    if sharing:
        while True:
            frequencies=Counter(pair for expression in expressions for pair in itertools.combinations(sorted(expression),2))
            eligible=[pair for pair,count in frequencies.items() if count>=2]
            if not eligible:break
            pair=max(eligible,key=lambda pair:(frequencies[pair]-1,len(supports[pair[0]]|supports[pair[1]]),tuple(-x for x in pair)))
            logical=base+len(definitions);definitions[logical]=pair
            supports[logical]=supports[pair[0]]|supports[pair[1]]
            tasks=[]
            for task,expression in enumerate(expressions):
                if set(pair)<=expression:
                    expression.difference_update(pair);expression.add(logical);tasks.append(task)
                    # Exact idempotence: a newly factored union absorbs atom/subunion children.
                    for other in list(expression):
                        if other!=logical and supports[other]<=supports[logical]:expression.remove(other)
            factors.append({'symbol':logical,'children':list(pair),'tasks':tasks,'atoms':sorted(supports[logical])})
    made=[];wire_dnf=initial_dnfs[:];cache={};atom_wire={i:i for i in range(n)};symbol_wire={}
    folds=[];gate_function_checks=[]
    def function(wire):return () if wire is None else wire_dnf[wire]
    def gate(op,a,b):
        if op and (a is None or b is None):return b if a is None else a
        if not op and (a is None or b is None):return None
        if a==b:return a
        a,b=sorted((a,b));left,right=wire_dnf[a],wire_dnf[b]
        if semantic:
            if DNF.implies(left,right):
                result=b if op else a;folds.append({'op':op,'left':a,'right':b,'result':result});return result
            if DNF.implies(right,left):
                result=a if op else b;folds.append({'op':op,'left':a,'right':b,'result':result});return result
        key=op,a,b
        if key in cache:return cache[key]
        cache[key]=n+len(made);made.append(list(key))
        wire_dnf.append(dnf.union([left,right]) if op else dnf.product(left,right))
        return cache[key]
    def emit(symbol,stage):
        if symbol<base:
            assert symbol in atom_wire,('future AND referenced',symbol,stage)
            return atom_wire[symbol]
        if symbol not in symbol_wire:
            assert all(x<n+stage for x in supports[symbol]),('OR availability violated',symbol,stage)
            a,b=definitions[symbol];symbol_wire[symbol]=gate(1,emit(a,stage),emit(b,stage))
        return symbol_wire[symbol]
    def expression(task,stage):
        children=sorted(expressions[task]);wire=emit(children[0],stage) if children else None
        for child in children[1:]:wire=gate(1,wire,emit(child,stage))
        expected=original_sides[task];actual=function(wire)
        if expected is not None and actual is not None:assert expected==actual,('OR cone changed',task)
        gate_function_checks.append({'kind':'OR cone','index':task,'precompact_wire':wire,'verified':expected is not None and actual is not None})
        return wire
    for i in range(k):
        left=expression(2*i,i);right=expression(2*i+1,i)
        atom_wire[n+i]=gate(0,left,right)
        expected=atom_dnf[n+i];actual=function(atom_wire[n+i])
        if expected is not None and actual is not None:assert expected==actual,('AND gate changed',i)
        gate_function_checks.append({'kind':'AND gate','index':i,'precompact_wire':atom_wire[n+i],'verified':expected is not None and actual is not None})
    output=expression(2*k,k)
    assert original_output is None or function(output) is None or original_output==function(output)
    if output is None:
        return {'inputs':n,'gates':[],'output':None,'gate_count':0,'and_count':0,'or_count':0,
                'skeleton_and_count':k,'naive_or_count':naive_or,'naive_total':k+naive_or,
                'all_gate_functions_dnf_verified':all(x['verified'] for x in gate_function_checks),
                'gate_function_checks':gate_function_checks,'dnf_skipped_computations':dnf.skipped,
                'output_minimal_terms':[],'exact_target_dnf':False if skeleton.get('edges') else None,
                'within63':False,'assembled':False,
                'status':'Skeleton output is false; no constant-free Monotone2 circuit is emitted.'}
    gates,output=compact(n,made,output)
    # Independently recompute every emitted wire after dead/copy/duplicate cleanup.
    checked=initial_dnfs[:]
    for op,a,b in gates:checked.append(dnf.union([checked[a],checked[b]]) if op else dnf.product(checked[a],checked[b]))
    if original_output is not None and checked[output] is not None:assert original_output==checked[output]
    desired={1<<a|1<<b for a,b in skeleton.get('edges',[])}
    exact=(set(checked[output])==desired) if checked[output] is not None and 'edges' in skeleton else None
    return {'inputs':n,'semantic_inputs':semantic_n,'gates':gates,'output':output,'gate_count':len(gates),'assembled':True,
        'and_count':sum(g[0]==0 for g in gates),'or_count':sum(g[0]==1 for g in gates),
        'skeleton_and_count':k,'naive_or_count':naive_or,'naive_total':k+naive_or,
        'semantic_optimization':semantic,'greedy_sharing':sharing,'shared_factors':factors,
        'dominance_rewrites':dominance,'semantic_gate_folds':folds,
        'all_gate_functions_dnf_verified':all(x['verified'] for x in gate_function_checks),
        'gate_function_checks':gate_function_checks,'precompact_gates':made,'dnf_skipped_computations':dnf.skipped,
        'output_minimal_terms':None if checked[output] is None else [[i for i in range(semantic_n) if m>>i&1] for m in checked[output]],
        'exact_target_dnf':exact,'within63':len(gates)<=63,
        'status':'Assembled skeleton; gate bound and exact target are separate reported checks.'}

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('source');parser.add_argument('destination')
    parser.add_argument('--no-semantic',action='store_true');parser.add_argument('--no-sharing',action='store_true')
    parser.add_argument('--dnf-cap',type=int,default=20000)
    args=parser.parse_args();source=json.loads(Path(args.source).read_text())
    result=assemble_skeleton(source,not args.no_semantic,not args.no_sharing,args.dnf_cap)
    result['source']=args.source;Path(args.destination).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({key:result[key] for key in ['gate_count','and_count','or_count','naive_total','all_gate_functions_dnf_verified','exact_target_dnf','within63','dnf_skipped_computations']}))
