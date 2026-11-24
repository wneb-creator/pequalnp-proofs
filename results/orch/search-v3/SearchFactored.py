import argparse
import itertools
import json
from pathlib import Path


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--ands', type=int, required=True)
    parser.add_argument('--size', type=int, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--baseline', action='store_true')
    parser.add_argument('--shared-or',type=int,default=0)
    parser.add_argument('--one-junk',action='store_true')
    parser.add_argument('--junk-count',type=int,default=0)
    args = parser.parse_args()
    junk_count=1 if args.one_junk else args.junk_count
    assert 0<=junk_count<args.ands
    left_count = 6
    pairs = list(itertools.combinations(range(left_count), 2))
    edges = [(u,left_count+j) for j,pair in enumerate(pairs) for u in pair]
    n = left_count+len(pairs)
    tests = {(1<<a)|(1<<b) for a,b in edges}
    for left in range(1<<left_count):
        allowed = [v for v in range(left_count,n) if not any(left&(1<<a) and b==v for a,b in edges)]
        closed = [u for u in range(left_count) if not any(a==u and b in allowed for a,b in edges)]
        tests.add(sum(1<<u for u in closed)+sum(1<<v for v in allowed))
    tests = sorted(tests)
    positives = {(1<<a)|(1<<b) for a,b in edges}
    negatives = set(tests)-positives
    count = 0
    variables = {}
    clauses = []
    selectors = []
    def var(key):
        nonlocal count
        if key not in variables:
            count += 1
            variables[key] = count
        return variables[key]
    def clause(*xs):
        clauses.append(xs)
    if args.baseline:
        if args.one_junk:
            assert (args.ands,args.shared_or)==(7,0)
        else:
            assert (args.ands,args.shared_or) in ((6,0),(7,1))
    for o in range(args.shared_or):
        row=[var(('lin-s',o,j)) for j in range(n)]
        selectors.extend(row)
        clause(*row)
        for selected in row:
            clause(-selected,*(other for other in row if other!=selected))
        if args.baseline:
            for j,selected in enumerate(row):clause(selected if j in (6,7) else -selected)
        for t in tests:
            value=var(('lin',o,t))
            terms=[row[j] for j in range(n) if t&(1<<j)]
            for term in terms:clause(-term,value)
            clause(-value,*terms)
        clause(*(-var(('lin',o,t)) for t in negatives))
    for i in range(args.ands):
        for side in (0,1):
            row = [var(('s',i,side,j)) for j in range(n+args.shared_or+i)]
            selectors.extend(row)
            clause(*row)
            if junk_count and i>=junk_count:
                for j in range(n+args.shared_or+junk_count,n+args.shared_or+i):
                    clause(-var(('s',i,side,j)))
            if args.baseline:
                for j,s in enumerate(row):
                    point=i if i<6 else 0
                    if args.one_junk and i==0:
                        selected=j==0
                    elif args.one_junk and i==6:
                        selected=((0,j) in edges) if side==0 else (j==n)
                    elif side==0:
                        selected=j==point
                    elif args.shared_or and point==0:
                        selected=j==n or ((point,j) in edges and j not in (6,7))
                    else:
                        selected=(point,j) in edges
                    clause(s if selected else -s)
        # Order operand inclusion vectors lexicographically, using 1 before 0.
        clause(var(('pre',i,0)))
        for j in range(n+args.shared_or+i):
            a=var(('s',i,0,j));b=var(('s',i,1,j))
            eq=var(('eq',i,j));p=var(('pre',i,j));q=var(('pre',i,j+1))
            clause(-eq,-a,b);clause(-eq,a,-b)
            clause(eq,a,b);clause(eq,-a,-b)
            clause(-q,p);clause(-q,eq);clause(q,-p,-eq)
            clause(-p,a,-b)
        for t in tests:
            rows=[]
            for side in (0,1):
                row_value=var(('arg',i,side,t));rows.append(row_value)
                terms=[]
                for j in range(n+args.shared_or+i):
                    selected=var(('s',i,side,j))
                    if j<n:
                        if t&(1<<j):terms.append(selected)
                    else:
                        source=var(('lin',j-n,t)) if j<n+args.shared_or else var(('v',j-n-args.shared_or,t))
                        term=var(('term',i,side,j,t))
                        clause(-term,selected);clause(-term,source);clause(term,-selected,-source)
                        terms.append(term)
                for term in terms:clause(-term,row_value)
                clause(-row_value,*terms)
            value=var(('v',i,t))
            clause(-value,rows[0]);clause(-value,rows[1]);clause(value,-rows[0],-rows[1])
        clause(*(var(('v',i,t)) for t in positives))
        clause(*(-var(('v',i,t)) for t in negatives))
    out_selectors=[var(('out',i)) for i in range(args.ands)]
    selectors.extend(out_selectors)
    clause(*out_selectors)
    if args.baseline:
        for i,s in enumerate(out_selectors):clause(-s if args.one_junk and i==0 else s)
    if junk_count:
        for s in out_selectors[:junk_count]:clause(-s)
        for s in out_selectors[junk_count:]:clause(s)
        for hidden in range(junk_count):
            clause(*(var(('v',hidden,t)) for t in negatives))
        width=n+args.shared_or+junk_count
        for i in range(junk_count,args.ands-1):
            clause(var(('top-pre',i,0)))
            for j in range(2*width):
                side,source=divmod(j,width)
                a=var(('s',i,side,source));b=var(('s',i+1,side,source))
                eq=var(('top-eq',i,j));p=var(('top-pre',i,j));q=var(('top-pre',i,j+1))
                clause(-eq,-a,b);clause(-eq,a,-b)
                clause(eq,a,b);clause(eq,-a,-b)
                clause(-q,p);clause(-q,eq);clause(q,-p,-eq)
                clause(-p,a,-b)
    for i in range(args.ands):
        clause(var(('out',i)),*(var(('s',j,side,n+args.shared_or+i)) for j in range(i+1,args.ands) for side in (0,1)))
    for o in range(args.shared_or):
        uses=[var(('s',i,side,n+o)) for i in range(args.ands) for side in (0,1)]
        clause(*uses)
        for use in uses:clause(-use,*(other for other in uses if other!=use))
    for t in tests:
        terms=[]
        for i in range(args.ands):
            selected=var(('out',i));source=var(('v',i,t));term=var(('outterm',i,t))
            clause(-term,selected);clause(-term,source);clause(term,-selected,-source)
            terms.append(term)
        if t in positives:
            clause(*terms)
        else:
            for term in terms:clause(-term)
    # Source selections = gates + AND nodes + shared OR forms + 1.
    threshold=args.size+args.ands+args.shared_or+2
    for i in range(len(selectors)+1):clause(var(('count',i,0)))
    for j in range(1,threshold+1):clause(-var(('count',0,j)))
    for i,selection in enumerate(selectors,1):
        for j in range(1,threshold+1):
            c=var(('count',i,j));a=var(('count',i-1,j));b=var(('count',i-1,j-1))
            clause(-c,a,selection);clause(-c,a,b);clause(c,-a);clause(c,-selection,-b)
    clause(-var(('count',len(selectors),threshold)))
    args.output.write_text(f'p cnf {count} {len(clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in clauses))
    args.output.with_suffix('.map.json').write_text(json.dumps({'n':n,'ands':args.ands,'shared_or':args.shared_or,'junk_count':junk_count,'size':args.size,'pairs':pairs,'edges':edges,'tests':tests,'variables':[[list(a),b] for a,b in variables.items()]}))
    print(json.dumps({'variables':count,'clauses':len(clauses),'ands':args.ands,'shared_or':args.shared_or,'junk_count':junk_count,'size':args.size,'tests':len(tests),'baseline':args.baseline}))


if __name__=='__main__':
    main()
