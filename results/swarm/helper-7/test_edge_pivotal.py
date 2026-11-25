"""Exact cut-replay checks; no external SAT solver is launched."""
import importlib.util
import itertools
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parent
def load(name,file):
    spec=importlib.util.spec_from_file_location(name,ROOT/file)
    obj=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(obj)
    return obj
q=load('count_query','count_query.py')
t=load('counter_tests','test_input_budget.py')
p=load('planted','planted_check.py')
single=load('single_query','single_query.py')


def replay(n,gates,mask,removed=None):
    wires=[bool(mask & (1<<v)) for v in range(n)]
    for j,g in enumerate(gates):
        a,b=wires[g['left']],wires[g['right']]
        wires.append(False if j==removed else a and b if g['op']=='and' else a or b)
    return wires


def mapping_formula(n,k,rows):
    f=q.s.CNF()
    mp={'left':[],'right':[],'op':[],'val':[]}
    for j in range(k):
        for side in ['left','right']:
            selectors=[f.var() for _ in range(n+j)]
            f.one(selectors)
            mp[side].append(selectors)
        mp['op'].append(f.var())
        mp['val'].append([f.var() for _ in rows])
    return f,mp


def assignment(info,gates,mp,data):
    n,k=info['n'],len(gates)
    original=[replay(n,gates,mask) for mask,_ in info['rows']]
    values={}
    for j,g in enumerate(gates):
        for side in ['left','right']:
            values.update({var:source==g[side] for source,var in enumerate(mp[side][j])})
        values[mp['op'][j]]=g['op']=='and'
        values.update({var:original[r][n+j] for r,var in enumerate(mp['val'][j])})
    pivot_truth=[]
    for removed,cut in enumerate(data['cuts']):
        truths=[]
        for e,r in enumerate(data['positive_row_indices']):
            wires=replay(n,gates,info['rows'][r][0],removed)
            for j in range(removed+1,k):
                values[cut['left_values'][j][e]]=wires[gates[j]['left']]
                values[cut['right_values'][j][e]]=wires[gates[j]['right']]
                values[cut['values'][j][e]]=wires[n+j]
            pivot=original[r][-1] and not wires[-1]
            values[data['pivotal_flags'][removed][e]]=pivot
            truths.append(pivot)
        pivot_truth.append(truths)
    dirty_truth=[]
    if 'dirty_and_flags' in data:
        for j,dirty_var in enumerate(data['dirty_and_flags']):
            dirty=gates[j]['op']=='and' and any(original[r][n+j] for r in data['negative_row_indices'])
            values[dirty_var]=dirty
            dirty_truth.append(dirty)
            for i,states in enumerate(data['dirty_and_counter_states'][j],start=1):
                count=sum(not pivot for pivot in pivot_truth[j][:i])
                values.update({var:count>=threshold for threshold,var in states.items()})
    return values,pivot_truth,dirty_truth


def satisfied(f,values):
    assert set(values)==set(range(1,f.nvars+1))
    return all(any(values[abs(lit)]==(lit>0) for lit in clause) for clause in f.clauses)


def circuits(n,k):
    choices=[]
    for j in range(k):
        choices.append([{'op':op,'left':a,'right':b,'pad':False}
                        for a in range(n+j) for b in range(a,n+j) for op in ['and','or']])
    return itertools.product(*choices)


def main():
    exact_cases=0
    clause_checks=0
    for k in range(1,4):
        info={'n':2,'rows':[(mask,True) for mask in range(4)]}
        f,mp=mapping_formula(2,k,info['rows'])
        data=q.pivotal_edge_flags(f,mp,info,k)
        for gates in circuits(2,k):
            values,pivots,_=assignment(info,gates,mp,data)
            assert satisfied(f,values)
            for group in data['pivotal_flags']:
                for pivot in group:
                    values[pivot]=not values[pivot]
                    assert not satisfied(f,values)
                    values[pivot]=not values[pivot]
            exact_cases+=1
            clause_checks+=len(f.clauses)
    dirty_cases=0
    dirty_allowed=dirty_rejected=0
    for n,edges,max_k in [(2,[(0,1)],3),(3,[(0,1),(1,2)],2)]:
        info=q.s.graph_info(n,edges)
        for k in range(1,max_k+1):
            f,mp=mapping_formula(n,k,info['rows'])
            data=q.add_edge_pivotal(f,mp,info,k,dirty_and_two=True)
            for gates in circuits(n,k):
                values,pivots,dirty=assignment(info,gates,mp,data)
                expected=all(any(row) for row in pivots) and all(not d or sum(row)>=2 for d,row in zip(dirty,pivots))
                assert satisfied(f,values)==expected,(n,k,gates)
                dirty_cases+=1
                if any(dirty):
                    if expected: dirty_allowed+=1
                    else: dirty_rejected+=1
                clause_checks+=len(f.clauses)
    shared_info=q.s.graph_info(4,[(0,1),(2,3)])
    shared=[{'op':op,'left':a,'right':b,'pad':False} for op,a,b in
            [('and',0,1),('and',2,3),('or',4,5),('or',4,6)]]
    q.s.verify(shared_info,shared)
    f,mp=mapping_formula(4,4,shared_info['rows'])
    data=q.add_edge_pivotal(f,mp,shared_info,4,dirty_and_two=True)
    values,pivots,_=assignment(shared_info,shared,mp,data)
    assert pivots[0][0] and satisfied(f,values)
    planted=[]
    for name in ['C6','C8']:
        graph=json.loads((ROOT/'graphs'/f'{name}.json').read_text())
        info=q.s.graph_info(graph['n'],graph['edges'])
        group=q.s.first_pair_symmetry(info)
        _,original=p.star_cover(info)
        choices=[p.normalize(info['n'],original,auto) for auto in group['automorphisms']]
        gates=min(choices,key=lambda gs:tuple((g['right'],g['left'],g['op']=='and') for g in gs))
        k=len(gates)
        q.s.verify(info,gates)
        f,mp=q.s.encode(info,k,normalized=True,symmetry=group,undominated=True,oriented=True)
        single.add_lex(f,mp,info['n'],k)
        for pad,op in zip(mp['pad'],mp['op']): f.add(-pad,-op)
        budget=q.add_input_budget(f,mp,info['n'],k)
        q.add_primary_reader_bound(f,mp,info['n'],k,budget['flags'])
        _,minimum=q.maximal_false_and_bound(info)
        q.at_most_sequential(f,[-op for op in mp['op']],k-minimum)
        q.add_edge_pivotal(f,mp,info,k,dirty_and_two=True)
        fixed={}
        for j,g in enumerate(gates):
            for side in ['left','right']:
                fixed.update({var:source==g[side] for source,var in enumerate(mp[side][j])})
            fixed[mp['op'][j]]=g['op']=='and'
            fixed[mp['pad'][j]]=False
        assert t.satisfiable(f.clauses,fixed),name
        planted.append({'graph':name,'gates':k,'vars':f.nvars,'clauses':len(f.clauses),'truth_rows':1<<info['n']})
    result={'status':'PASS','exact_cut_circuits':exact_cases,'dirty_condition_circuits':dirty_cases,
            'dirty_allowed_cases':dirty_allowed,'dirty_rejected_cases':dirty_rejected,
            'CNF_clause_checks':clause_checks,'sharing_fork':True,'planted':planted,
            'external_solver_processes':0}
    print(json.dumps(result))


if __name__=='__main__': main()
