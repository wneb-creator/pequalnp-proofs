"""Finite projection and explicit-circuit checks; does not launch an external solver."""
import importlib.util
import itertools
import json
from pathlib import Path
import random

ROOT=Path(__file__).resolve().parent
def module(name,filename):
    spec=importlib.util.spec_from_file_location(name,ROOT/filename)
    obj=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(obj)
    return obj
q=module('count_query','count_query.py')
t=module('counter_tests','test_input_budget.py')
p=module('planted','planted_check.py')
single=module('single_query','single_query.py')


def graph_info(name):
    graph=json.loads((ROOT/'graphs'/f'{name}.json').read_text())
    return q.s.graph_info(graph['n'],graph['edges'])


def property_check(info,gates):
    n=info['n']
    counts=[sum(source==v for gate in gates for source in (gate['left'],gate['right'])) for v in range(n)]
    assert all(counts)
    for gate in gates:
        a,b=gate['left'],gate['right']
        if a<n and b<n:
            assert a!=b
            assert counts[a]>=2 and counts[b]>=2,(gate,counts)
    primary_readers=sum(gate['left']<n or gate['right']<n for gate in gates)
    assert primary_readers>=n
    return primary_readers


def random_star_circuit(info,rng):
    n=info['n']
    owned=[[] for _ in range(n)]
    for a,b in info['edges']:
        if rng.randrange(2): a,b=b,a
        owned[a].append(b)
    gates=[]
    def add(op,a,b):
        a,b=sorted((a,b))
        result=n+len(gates)
        gates.append({'op':op,'left':a,'right':b,'pad':False})
        return result
    def join(values):
        values=list(values)
        while len(values)>1:
            a=values.pop(rng.randrange(len(values)))
            b=values.pop(rng.randrange(len(values)))
            values.append(add('or',a,b))
        return values[0]
    centers=[v for v in range(n) if owned[v]]
    rng.shuffle(centers)
    terms=[add('and',v,join(owned[v])) for v in centers]
    assert join(terms)==n+len(gates)-1
    return gates


def main():
    assert q.validate_primary_reader_graph(graph_info('C6'))['no_four_cycle']
    assert q.validate_primary_reader_graph(graph_info('C8'))['minimum_degree']==2
    for bad in [graph_info('C4'),q.s.graph_info(3,[(0,1),(1,2)])]:
        try: q.validate_primary_reader_graph(bad)
        except ValueError: pass
        else: raise AssertionError('Invalid graph hypothesis was accepted')
    projections=0
    for n,k in [(2,3),(3,2),(3,3),(3,4)]:
        f=q.s.CNF()
        mapping={'left':[],'right':[]}
        for j in range(k):
            for side in ('left','right'):
                selectors=[f.var() for _ in range(n+j)]
                f.one(selectors)
                mapping[side].append(selectors)
        q.add_primary_reader_bound(f,mapping,n,k)
        options=[list(itertools.combinations(range(n+j),2)) for j in range(k)]
        for choices in itertools.product(*options):
            fixed={selector:source==chosen
                   for j,(a,b) in enumerate(choices)
                   for side,chosen in [('left',a),('right',b)]
                   for source,selector in enumerate(mapping[side][j])}
            local=all(any(v in pair for i,pair in enumerate(choices) if i!=j)
                      for j,(a,b) in enumerate(choices) if a<n and b<n for v in (a,b))
            readers=sum(a<n or b<n for a,b in choices)
            assert t.satisfiable(f.clauses,fixed)==(local and readers>=n),(n,k,choices)
            projections+=1
    planted=[]
    random_stats={}
    rng=random.Random(0)
    for name in ['C6','C8']:
        info=graph_info(name)
        group=q.s.first_pair_symmetry(info)
        cover,original=p.star_cover(info)
        choices=[p.normalize(info['n'],original,auto) for auto in group['automorphisms']]
        gates=min(choices,key=lambda gs:tuple((g['right'],g['left'],g['op']=='and') for g in gs))
        q.s.verify(info,gates)
        readers=property_check(info,gates)
        k=len(gates)
        f,mapping=q.s.encode(info,k,normalized=True,symmetry=group,undominated=True,oriented=True)
        single.add_lex(f,mapping,info['n'],k)
        for pad,op in zip(mapping['pad'],mapping['op']): f.add(-pad,-op)
        budget=q.add_input_budget(f,mapping,info['n'],k)
        q.add_primary_reader_bound(f,mapping,info['n'],k,budget['flags'])
        _,minimum=q.maximal_false_and_bound(info)
        q.at_most_sequential(f,[-op for op in mapping['op']],k-minimum)
        fixed={}
        for j,gate in enumerate(gates):
            for side in ['left','right']:
                fixed.update({variable:source==gate[side] for source,variable in enumerate(mapping[side][j])})
            fixed[mapping['op'][j]]=gate['op']=='and'
            fixed[mapping['pad'][j]]=False
        assert t.satisfiable(f.clauses,fixed),name
        planted.append({'graph':name,'gates':k,'primary_readers':readers,'truth_rows':1<<info['n']})
        values=[]
        for _ in range(100):
            generated=random_star_circuit(info,rng)
            q.s.verify(info,generated)
            values.append(property_check(info,generated))
        random_stats[name]={'circuits':len(values),'minimum_primary_readers':min(values),
                            'maximum_primary_readers':max(values),'truth_rows_each':1<<info['n']}
    result={'status':'PASS','selector_projection_cases':projections,
            'planted_full_CNF_checks':planted,'random_valid_circuits':random_stats,
            'external_solver_processes':0}
    print(json.dumps(result))


if __name__=='__main__': main()
