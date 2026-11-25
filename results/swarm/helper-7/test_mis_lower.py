"""Finite checks of the generic maximal-false AND bound and its counter encoding."""
import importlib.util
import itertools
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('count_query',ROOT/'count_query.py')
q=importlib.util.module_from_spec(spec)
spec.loader.exec_module(q)
spec=importlib.util.spec_from_file_location('counter_test',ROOT/'test_input_budget.py')
t=importlib.util.module_from_spec(spec)
spec.loader.exec_module(t)


def main():
    expected={'C4':(2,1),'C6':(5,3),'C8':(10,4),
              'Heawood12noninc':(26,5),'GP8del_inc':(39,6),
              'GP8del_noninc':(44,6),'C6book3':(41,6)}
    calibrations={}
    for name,want in expected.items():
        graph=json.loads((ROOT/'graphs'/f'{name}.json').read_text())
        info=q.s.graph_info(graph['n'],graph['edges'])
        actual=q.maximal_false_and_bound(info)
        assert actual==want,(name,actual,want)
        calibrations[name]={'maximal_independent_sets':actual[0],'min_and':actual[1]}
    lower_cases=0
    for n in range(9):
        for minimum in range(n+2):
            f=q.s.CNF()
            operations=[f.var() for _ in range(n)]
            q.at_most_sequential(f,[-op for op in operations],n-minimum)
            for values in itertools.product((False,True),repeat=n):
                actual=t.satisfiable(f.clauses,dict(zip(operations,values)))
                assert actual==(sum(values)>=minimum),(n,minimum,values)
                lower_cases+=1
    n=3
    all_bits=(1<<(1<<n))-1
    inputs=[sum(1<<mask for mask in range(1<<n) if mask & (1<<v)) for v in range(n)]
    circuits=0
    def check(gates,wires):
        nonlocal circuits
        original=wires[-1]
        and_count=sum(op=='and' for op,_,_ in gates)
        clauses=[]
        for choices in itertools.product((0,1),repeat=and_count):
            selected=inputs.copy()
            choice=iter(choices)
            for op,a,b in gates:
                if op=='and': selected.append(selected[(a,b)[next(choice)]])
                else: selected.append(selected[a]|selected[b])
            clauses.append(selected[-1])
        cnf=all_bits
        for clause in clauses: cnf &= clause
        assert cnf==original,(gates,cnf,original)
        maximal_false=sum(not (original>>mask & 1) and all(mask & (1<<v) or original>>(mask|(1<<v)) & 1 for v in range(n)) for mask in range(1<<n))
        assert maximal_false<=1<<and_count,(gates,maximal_false,and_count)
        circuits+=1
    def visit(gates,wires):
        if gates: check(gates,wires)
        if len(gates)==3: return
        for a in range(len(wires)):
            for b in range(a,len(wires)):
                for op in ('and','or'):
                    value=wires[a]&wires[b] if op=='and' else wires[a]|wires[b]
                    visit(gates+[(op,a,b)],wires+[value])
    visit([],inputs)
    result={'status':'PASS','calibrations':calibrations,
            'lower_counter_cases':lower_cases,
            'circuits_checked_global_selection_identity_and_false_bound':circuits,
            'circuit_inputs':3,'max_gates':3}
    print(json.dumps(result))


if __name__=='__main__': main()
