from itertools import combinations, product
import json
import random

def truth_table(n, i):
    return sum(((x >> i) & 1) << x for x in range(1 << n))

def table_of_family(n, family):
    return sum(any((x & support) == support for support in family) << x for x in range(1 << n))

def check_output(n, q, family, table, edges):
    m=2*n
    accept=all((table >> ((1 << p) | (1 << (n+l)))) & 1 for p,l in edges)
    supports_accept=all(any(t & ~((1 << p) | (1 << (n+l))) == 0 for t in family) for p,l in edges)
    assert accept==supports_accept
    def hit(x):
        return any(x & (1<<p) and x & (1<<(n+l)) for p,l in edges)
    sound=all(not((table >> x)&1) for x in range(1<<m) if (x>>n).bit_count()<=q and not hit(x))
    supports_sound=all(hit(t) for t in family if (t>>n).bit_count()<=q)
    assert sound==supports_sound
    return accept and sound

report={}
count=0; checks=0; promise_cases=0
n=4
base_tables=[truth_table(n,i) for i in range(n)]
base_families=[frozenset({1<<i}) for i in range(n)]
# Exhaustive ordered gate lists with strictly sorted distinct backward reads.
def visit(tables,families,depth):
    global count,checks,promise_cases
    if depth==0:
        return
    for a,b in combinations(range(len(tables)),2):
        for op in ('and','or'):
            count+=1
            if op=='and':
                table=tables[a]&tables[b]
                family=frozenset(u|v for u in families[a] for v in families[b])
            else:
                table=tables[a]|tables[b]
                family=families[a]|families[b]
            assert table==table_of_family(n,family)
            checks+=1
            # All 2x2 incidence relations, q=0,1,2, on every generated gate.
            for relation in range(16):
                edges=[(p,l) for p,l in product(range(2),repeat=2) if relation&(1<<(2*p+l))]
                for q in range(3):
                    promise_cases+=check_output(2,q,family,table,edges)
            visit(tables+[table],families+[family],depth-1)
visit(base_tables,base_families,3)
report['exhaustive']={'input_count':n,'maximum_gates':3,'gate_prefixes':count,'truth_table_comparisons':checks,'relation_q_checks':checks*48,'successful_promise_instances':promise_cases}
# Random larger 3+3-input circuits; all roots checked, with random relations.
rng=random.Random(2870)
random_checks=0
for trial in range(2000):
    n=6
    tables=[truth_table(n,i) for i in range(n)]
    families=[frozenset({1<<i}) for i in range(n)]
    edges=[(p,l) for p,l in product(range(3),repeat=2) if rng.randrange(2)]
    for gate in range(12):
        a,b=sorted(rng.sample(range(len(tables)),2))
        if rng.randrange(2):
            table=tables[a]&tables[b];family=frozenset(u|v for u in families[a] for v in families[b])
        else:
            table=tables[a]|tables[b];family=families[a]|families[b]
        assert table==table_of_family(n,family)
        for q in range(4):check_output(3,q,family,table,edges)
        tables.append(table);families.append(family);random_checks+=1
report['random']={'seed':2870,'circuits':2000,'inputs':6,'gates_each':12,'truth_table_comparisons':random_checks,'relation_q_checks':random_checks*4}
print(json.dumps(report,indent=2))
