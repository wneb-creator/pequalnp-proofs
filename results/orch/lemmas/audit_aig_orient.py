import importlib.util
import itertools
import json
from pathlib import Path
spec=importlib.util.spec_from_file_location("aig", "/tmp/oec/pequalnp-pilot-96/structural_aig_orient.py")
a=importlib.util.module_from_spec(spec)
spec.loader.exec_module(a)
cases=0
orientations=0
rows=0
for n in [0,1]:
    for b in range(3):
        possibilities=[]
        for j in range(b):
            literals=list(itertools.product(range(n+1+j),range(2)))
            possibilities.append(list(itertools.product(literals,repeat=2)))
        for gates in itertools.product(*possibilities):
            for output in itertools.product(range(n+1+b),range(2)):
                aig={"n":n,"gates":gates,"output":output}
                exact=[]
                for orientation in range(1<<b):
                    # Independent demand enumeration: retain each signed source
                    # required by the actual AND/OR realization.
                    needs=[set() for _ in range(n+1+b)]
                    for j,pair in enumerate(gates):
                        selected=(orientation>>j)&1
                        for source,polarity in pair:
                            needs[source].add(polarity ^ selected)
                    needs[output[0]].add(output[1])
                    independent=sum(any(p != (((orientation>>(s-n-1))&1) if s>n else 0) for p in ps) for s,ps in enumerate(needs))
                    assert independent==a.cost(aig,orientation)
                    circuit=a.reconstruct(aig,orientation)
                    assert sum(op=="not" for op,_ in circuit["gates"])==independent
                    for mask in range(1<<n):
                        assert a.eval_aig(aig,mask)==a.eval_circuit(circuit,mask)
                        rows+=1
                    exact.append(independent)
                    orientations+=1
                result=a.minimize(aig)
                assert result["not_count"]==min(exact)
                cases+=1
report={"status":"PASS","exhaustive_aigs":cases,"orientations":orientations,"truth_rows":rows,"scope":"All signed ordered AIGs with n=0 or 1 and at most 2 binary gates, including duplicate operands and arbitrary outputs; each orientation reconstructed and checked. This checks accounting and semantics, not synthesis completeness or preservation of a mandatory NOT."}
Path("/tmp/oec/pequalnp-pilot-96/aig-independent-audit.json").write_text(json.dumps(report,indent=2)+"\n")
print(json.dumps(report,indent=2))
