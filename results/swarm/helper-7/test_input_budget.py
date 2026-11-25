"""Exhaustive finite checks of the sequential counter and input-slot projection."""
import importlib.util
import itertools
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('count_query',ROOT/'count_query.py')
q=importlib.util.module_from_spec(spec)
spec.loader.exec_module(q)


def satisfiable(clauses, fixed):
    assignment=dict(fixed)
    while True:
        changed=False
        unresolved=[]
        for clause in clauses:
            pending=[]
            satisfied=False
            for literal in clause:
                variable=abs(literal)
                if variable in assignment:
                    if assignment[variable] == (literal > 0):
                        satisfied=True
                        break
                else:
                    pending.append(literal)
            if satisfied:
                continue
            if not pending:
                return False
            if len(pending)==1:
                literal=pending[0]
                assignment[abs(literal)]=literal>0
                changed=True
            else:
                unresolved.append(pending)
        if not changed:
            if not unresolved:
                return True
            variable=abs(unresolved[0][0])
            return any(satisfiable(clauses,assignment | {variable:value})
                       for value in (False,True))


def main():
    cardinality_cases=0
    for n in range(9):
        for bound in range(-1,n+2):
            for sign_mode in range(2):
                f=q.s.CNF()
                inputs=[f.var() for _ in range(n)]
                literals=[-v if sign_mode and i%2 else v for i,v in enumerate(inputs)]
                q.at_most_sequential(f,literals,bound)
                for bits in itertools.product((False,True),repeat=n):
                    fixed=dict(zip(inputs,bits))
                    count=sum(fixed[abs(literal)] == (literal>0) for literal in literals)
                    actual=satisfiable(f.clauses,fixed)
                    assert actual==(count<=bound),(n,bound,literals,bits,actual)
                    cardinality_cases+=1
    projection_cases=0
    for n,k in [(2,1),(2,2),(2,3),(3,2)]:
        f=q.s.CNF()
        mp={'left':[],'right':[]}
        positions=[]
        for j in range(k):
            for side in ('left','right'):
                selectors=[f.var() for _ in range(n+j)]
                f.one(selectors)
                mp[side].append(selectors)
                positions.append(selectors)
        q.add_input_budget(f,mp,n,k)
        for choices in itertools.product(*(range(len(pos)) for pos in positions)):
            fixed={v:i==source for pos,source in zip(positions,choices) for i,v in enumerate(pos)}
            expected=sum(source<n for source in choices)<=k+1
            assert satisfiable(f.clauses,fixed)==expected,(n,k,choices)
            projection_cases+=1
    result={'status':'PASS','counter_cases':cardinality_cases,'selector_projection_cases':projection_cases,'counter_n_max':8}
    print(json.dumps(result))


if __name__=='__main__':
    main()
