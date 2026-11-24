import argparse
import itertools
import json
import re
from pathlib import Path


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--case', choices=['c6', 'c6private', 'plane_local', 'k4', 'k5', 'k6'], required=True)
    parser.add_argument('--points', default='0,1,2')
    parser.add_argument('--statement', type=Path, default=Path('/tmp/oec/pequalnp-pilot-29/statement.txt'))
    parser.add_argument('--truth', choices=['exhaustive', 'extremal'], default='extremal')
    parser.add_argument('--ordering', action=argparse.BooleanOptionalAction, default=True)
    parser.add_argument('--pruning', action=argparse.BooleanOptionalAction, default=True)
    parser.add_argument('--incomparability', action=argparse.BooleanOptionalAction, default=True)
    parser.add_argument('--and-count', type=int)
    parser.add_argument('--dirty', action='store_true')
    parser.add_argument('--min-dirty',type=int,choices=(0,1,2),default=0)
    parser.add_argument('--tests-file',type=Path)
    parser.add_argument('--first-pair-orbits', type=Path)
    parser.add_argument('--gates', type=int, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    n = 6 if args.case == 'c6' else 9
    edges = [(0,3),(0,4),(1,4),(1,5),(2,5),(2,3)]
    if n == 9:
        edges += [(0,6),(1,7),(2,8)]
    metadata = {}
    left_count = 3
    if args.case in ('k4','k5','k6'):
        left_count = int(args.case[1:])
        pairs = list(itertools.combinations(range(left_count),2))
        edges = [(u,left_count+j) for j,pair in enumerate(pairs) for u in pair]
        n = left_count + len(pairs)
        metadata = {'complete_graph':left_count,'pairs':pairs,'standard_core':len(edges)+left_count-1}
    if args.case == 'plane_local':
        points = [int(a) for a in args.points.split(',')]
        original = [(int(a),int(b)) for a,b in re.findall(r'\((\d+), (\d+)\)', args.statement.read_text())]
        groups = {}
        for v in range(21,42):
            mask = sum(1<<i for i,u in enumerate(points) if (u,v) in original)
            if mask:
                groups.setdefault(mask, []).append(v)
        left_count = len(points)
        edges = [(i,left_count+j) for j,mask in enumerate(groups) for i in range(left_count) if mask&(1<<i)]
        n = left_count + len(groups)
        metadata = {'points':points, 'groups':list(groups.items()), 'outside_or_cost':sum(len(v)-1 for v in groups.values()), 'standard_core':len(edges)+left_count-1}
        assert len(edges) + metadata['outside_or_cost'] == 5*left_count
    if args.truth == 'exhaustive':
        tests = list(range(1<<n))
    else:
        tests = [(1<<a)|(1<<b) for a,b in edges]
        for left in range(1<<left_count):
            allowed = [v for v in range(left_count,n) if not any(left&(1<<a) and b==v for a,b in edges)]
            closed_left = [u for u in range(left_count) if not any(a==u and b in allowed for a,b in edges)]
            tests.append(sum(1<<u for u in closed_left) + sum(1<<v for v in allowed))
        tests = sorted(set(tests))
    if args.tests_file is not None:
        selected=json.loads(args.tests_file.read_text())
        assert isinstance(selected,list) and selected
        assert all(type(t) is int and t in tests for t in selected)
        assert set((1<<a)|(1<<b) for a,b in edges)<=set(selected)
        metadata['complete_test_count']=len(tests)
        tests=sorted(set(selected))
        metadata['test_subset']=True
    k = args.gates
    count = 0
    variables = {}
    clauses = []
    def var(key):
        nonlocal count
        if key not in variables:
            count += 1
            variables[key] = count
        return variables[key]
    def clause(*xs):
        clauses.append(xs)
    def exactly_one(xs):
        clause(*xs)
        for a,b in itertools.combinations(xs,2):
            clause(-a,-b)
    for i in range(k):
        left = [var(('s',i,0,a)) for a in range(n+i)]
        right = [var(('s',i,1,a)) for a in range(n+i)]
        exactly_one(left)
        exactly_one(right)
        for a in range(n+i):
            for b in range(a+1):
                clause(-left[a],-right[b])
        op = var(('op',i))
        for t in tests:
            lv = var(('arg',i,0,t))
            rv = var(('arg',i,1,t))
            out = var(('v',i,t))
            for side, selectors, value in [(0,left,lv),(1,right,rv)]:
                for a, selector in enumerate(selectors):
                    if a<n:
                        clause(-selector, value if t&(1<<a) else -value)
                    else:
                        previous = var(('v',a-n,t))
                        clause(-selector, -value, previous)
                        clause(-selector, value, -previous)
            clause(-op,-lv,-rv,out)
            clause(-op,lv,-out)
            clause(-op,rv,-out)
            clause(op,lv,rv,-out)
            clause(op,-lv,out)
            clause(op,-rv,out)
            if i == k-1:
                target = any(t&(1<<a) and t&(1<<b) for a,b in edges)
                clause(out if target else -out)
    # Every nonfinal gate participates in the output cone. A smaller circuit can
    # still be tested by an additional run at its own size.
    for i in range(k-1):
        clause(*(var(('s',j,side,n+i)) for j in range(i+1,k) for side in (0,1)))
    # Choose a lexicographically least topological serialization. Adjacent
    # independent gates must have nondecreasing ordered input pairs; dependent
    # neighbors may occur in either order of the first input index.
    if args.ordering:
        for i in range(k-1):
            for a in range(n+i):
                for b in range(a):
                    clause(-var(('s',i,0,a)),-var(('s',i+1,0,b)),var(('s',i+1,1,n+i)))
                for c in range(a+1,n+i):
                    for d in range(a+1,c):
                        clause(-var(('s',i,0,a)),-var(('s',i+1,0,a)),-var(('s',i,1,c)),-var(('s',i+1,1,d)))
    if args.pruning:
        positives = {(1<<a)|(1<<b) for a,b in edges}
        negatives = set(tests)-positives
        for i in range(k):
            clause(*(var(('v',i,t)) for t in positives))
            clause(*(-var(('v',i,t)) for t in negatives))
            if args.incomparability:
                for side in (0,1):
                    witnesses = []
                    for t in tests:
                        a = var(('arg',i,side,t))
                        b = var(('arg',i,1-side,t))
                        witness = var(('exclusive',i,side,t))
                        witnesses.append(witness)
                        clause(-witness,a)
                        clause(-witness,-b)
                        clause(witness,-a,b)
                    clause(*witnesses)
    if args.case in ('k4','k5','k6'):
        first_pairs = {(0,1),(0,left_count),(0,left_count+pairs.index((1,2))),
                       (left_count,left_count+1),(left_count,left_count+pairs.index((2,3)))}
        for a,b in itertools.combinations(range(n),2):
            if (a,b) not in first_pairs:
                clause(-var(('s',0,0,a)),-var(('s',0,1,b)))
    if args.first_pair_orbits:
        symmetry = json.loads(args.first_pair_orbits.read_text())
        automorphisms = symmetry['automorphisms']
        edge_set = {tuple(sorted(edge)) for edge in edges}
        for permutation in automorphisms:
            assert sorted(permutation) == list(range(n))
            assert {tuple(sorted((permutation[a],permutation[b]))) for a,b in edges} == edge_set
        first_pairs = set()
        covered = set()
        for orbit in symmetry['unordered_first_gate_orbits']:
            representative = tuple(orbit['representative'])
            images = {tuple(sorted((permutation[representative[0]],permutation[representative[1]]))) for permutation in automorphisms}
            assert representative == min(images)
            assert len(images) == orbit['size']
            assert not covered.intersection(images)
            covered.update(images)
            first_pairs.add(representative)
        assert covered == set(itertools.combinations(range(n),2))
        for a,b in itertools.combinations(range(n),2):
            if (a,b) not in first_pairs:
                clause(-var(('s',0,0,a)),-var(('s',0,1,b)))
        metadata['first_pair_orbits'] = len(first_pairs)
    min_dirty=max(int(args.dirty),args.min_dirty)
    if min_dirty:
        dirty_gates = []
        negatives = [t for t in tests if not any(t&(1<<a) and t&(1<<b) for a,b in edges)]
        for i in range(k):
            dirty_gate=var(('dirty_gate',i))
            dirty_gates.append(dirty_gate)
            operation=var(('op',i))
            negative_values=[]
            clause(-dirty_gate,operation)
            for t in negatives:
                value = var(('v',i,t))
                negative_values.append(value)
                clause(dirty_gate,-operation,-value)
            clause(-dirty_gate,*negative_values)
        clause(*dirty_gates)
        if min_dirty==2:
            for i,dirty_gate in enumerate(dirty_gates):
                clause(-dirty_gate,*(g for j,g in enumerate(dirty_gates) if j!=i))
    if args.and_count is not None:
        threshold = args.and_count+1
        for i in range(k+1):
            clause(var(('count',i,0)))
        for j in range(1,threshold+1):
            clause(-var(('count',0,j)))
        for i in range(1,k+1):
            for j in range(1,threshold+1):
                current = var(('count',i,j))
                same = var(('count',i-1,j))
                previous = var(('count',i-1,j-1))
                operation = var(('op',i-1))
                clause(-current,same,operation)
                clause(-current,same,previous)
                clause(current,-same)
                clause(current,-operation,-previous)
        clause(var(('count',k,args.and_count)))
        clause(-var(('count',k,args.and_count+1)))
    args.output.write_text(f'p cnf {count} {len(clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in clauses))
    args.output.with_suffix('.map.json').write_text(json.dumps({'n':n,'k':k,'edges':edges,'tests':tests,'metadata':metadata,'and_count':args.and_count,'dirty':args.dirty,'min_dirty':min_dirty,'ordering':args.ordering,'pruning':args.pruning,'incomparability':args.incomparability,'variables':[[list(a),b] for a,b in variables.items()]}))
    print(json.dumps({'variables':count,'clauses':len(clauses),'case':args.case,'gates':k,'tests':len(tests),'metadata':metadata}))


if __name__ == '__main__':
    main()
