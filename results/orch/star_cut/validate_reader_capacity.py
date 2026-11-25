import datetime,itertools,json
from pathlib import Path
from reader_capacity import threshold
from synthesize_reference import CNF

checks=0
for n in range(1,7):
    for k in range(1,n+2):
        for bits in range(1<<n):
            c=CNF();xs=[c.var() for _ in range(n)];lit=threshold(c,xs,k)
            values={x:bool(bits>>i&1) for i,x in enumerate(xs)}
            previous=[True]+[False]*k;cursor=n
            for i in range(n):
                current=[True]
                for t in range(1,k+1):
                    cursor+=1
                    z=previous[t] or (bool(bits>>i&1) and previous[t-1])
                    current.append(z);values[cursor]=z
                previous=current
            assert cursor==c.n
            assert values[lit]==(bits.bit_count()>=k)
            assert all(any(values[abs(v)]==(v>0) for v in clause) for clause in c.clauses)
            checks+=1
capacity_checks=0
for n,s in [(2,2),(2,3),(3,3),(4,3)]:
    choices=[]
    for j in range(s):
        wires=list(range(n+j))+[-1]
        choices.append([(op,a,b) for op in [0,1] for a,b in itertools.combinations_with_replacement(wires,2)]
                       +[(2,a,-1) for a in wires])
    for gates in itertools.product(*choices):
        reads=[set() for _ in range(n+s-1)];false=0
        for j,(op,a,b) in enumerate(gates):
            false+=(a<0)+(b<0)
            for w in {a,b}:
                if w>=0:reads[w].add(j)
        if any(not r for r in reads):continue
        d=sum(len(reads[p])>=2 for p in range(n))
        assert d+false<=s+1-n
        capacity_checks+=1
result={'threshold_truth_assignments':checks,'exhaustive_cone_models':capacity_checks,
        'status':'PASS','timestamp':datetime.datetime.now(datetime.timezone.utc).isoformat()}
(Path(__file__).parent/'reader-capacity-validation.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
