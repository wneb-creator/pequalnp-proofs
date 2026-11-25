"""Finite exact-witness and valid-circuit checks; no external solver is launched."""
import importlib.util
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parent
def load(name,file):
    spec=importlib.util.spec_from_file_location(name,ROOT/file)
    obj=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(obj)
    return obj
q=load('count_query','count_query.py')
e=load('edge_tests','test_edge_pivotal.py')
t=load('counter_tests','test_input_budget.py')
p=load('planted','planted_check.py')
single=load('single_query','single_query.py')


def assign(info,gates,mp,data):
    n=info['n']
    original=[e.replay(n,gates,mask) for mask,_ in info['rows']]
    values={}
    for j,g in enumerate(gates):
        for side in ['left','right']:
            values.update({var:source==g[side] for source,var in enumerate(mp[side][j])})
            values.update({var:original[r][g[side]]
                           for r,var in enumerate(data['operand_values'][side][j])})
        values[mp['op'][j]]=g['op']=='and'
        values.update({var:original[r][n+j] for r,var in enumerate(mp['val'][j])})
    existence=[]
    disallowed=[]
    for pair in data['pairs']:
        first,second=pair['row_indices']
        possible=[]
        for j,(g,witness) in enumerate(zip(gates,pair['witness_flags'])):
            states=(original[first][g['left']],original[first][g['right']],
                    original[second][g['left']],original[second][g['right']])
            good=g['op']==pair['operation'] and states in [
                (True,False,False,True),(False,True,True,False)]
            values[witness]=good
            possible.append(good)
            if not good: disallowed.append(witness)
        existence.append(any(possible))
    return values,all(existence),disallowed


def computes_graph(info,gates):
    for mask in range(1<<info['n']):
        actual=e.replay(info['n'],gates,mask)[-1]
        target=any(mask & (1<<a) and mask & (1<<b) for a,b in info['edges'])
        if actual != bool(target): return False
    return True


def main():
    circuit_cases=valid_cases=clause_checks=flipped_witnesses=0
    for n,edges in [(2,[(0,1)]),(3,[(0,1),(1,2)])]:
        info=q.s.graph_info(n,edges)
        for k in range(1,4):
            f,mp=e.mapping_formula(n,k,info['rows'])
            data=q.add_pair_separation(f,mp,info,k)
            for gates in e.circuits(n,k):
                values,expected,disallowed=assign(info,gates,mp,data)
                assert e.satisfied(f,values)==expected
                if expected:
                    for witness in disallowed:
                        values[witness]=True
                        assert not e.satisfied(f,values)
                        values[witness]=False
                        flipped_witnesses+=1
                if computes_graph(info,gates):
                    assert expected
                    valid_cases+=1
                circuit_cases+=1
                clause_checks+=len(f.clauses)
    shared_info=q.s.graph_info(4,[(0,1),(2,3)])
    shared=[{'op':op,'left':a,'right':b,'pad':False} for op,a,b in
            [('and',0,1),('and',2,3),('or',4,5),('or',4,6)]]
    assert computes_graph(shared_info,shared)
    f,mp=e.mapping_formula(4,4,shared_info['rows'])
    data=q.add_pair_separation(f,mp,shared_info,4)
    values,expected,_=assign(shared_info,shared,mp,data)
    assert expected and e.satisfied(f,values)
    planted=[]
    for name in ['C6','C8']:
        graph=json.loads((ROOT/'graphs'/f'{name}.json').read_text())
        info=q.s.graph_info(graph['n'],graph['edges'])
        group=q.s.first_pair_symmetry(info)
        _,original=p.star_cover(info)
        candidates=[p.normalize(info['n'],original,auto) for auto in group['automorphisms']]
        gates=min(candidates,key=lambda gs:tuple((g['right'],g['left'],g['op']=='and') for g in gs))
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
        data=q.add_pair_separation(f,mp,info,k)
        fixed,expected,_=assign(info,gates,mp,data)
        assert expected
        fixed.update({pad:False for pad in mp['pad']})
        assert t.satisfiable(f.clauses,fixed)
        planted.append({'graph':name,'gates':k,'pair_count':len(data['pairs']),
                        'vars':f.nvars,'clauses':len(f.clauses),'truth_rows':1<<info['n']})
    result={'status':'PASS','exhaustive_circuit_cases':circuit_cases,
            'valid_graph_circuits':valid_cases,'CNF_clause_checks':clause_checks,
            'incorrect_witness_flips_rejected':flipped_witnesses,
            'sharing_fork':True,'planted':planted,'external_solver_processes':0}
    print(json.dumps(result))


if __name__=='__main__': main()
