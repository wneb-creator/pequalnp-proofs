import itertools
import json
from pathlib import Path
import structural_aig_sat as sat

cases=0
clauses_checked=0
rows_checked=0
for n,b in [(0,1),(1,1),(0,2),(1,2)]:
    pairs=[]
    for j in range(b):
        literals=list(itertools.product(range(n+1+j),range(2)))
        pairs.append(list(itertools.combinations_with_replacement(literals,2)))
    for gates in itertools.product(*pairs):
        for phase in range(2):
            aig={'n':n,'gates':gates,'output':[n+b,phase]}
            truth_rows={}
            row_values={}
            for mask in range(1<<n):
                values=[bool(mask&(1<<i)) for i in range(n)]+[False]
                cells=[]
                for pair in gates:
                    left,right=[values[source]^bool(polarity) for source,polarity in pair]
                    z=left and right
                    cells.extend([left,right,z]);values.append(z)
                truth_rows[mask]=values[-1]^bool(phase)
                row_values[mask]=cells
            for maximum in range(n+b+2):
                cnf,selectors,output=sat.encode(n,b,list(truth_rows),lambda m:truth_rows[m],maximum,pinned=aig)
                for orientation in range(1<<b):
                    assignment={}
                    for (a,c),pair in zip(selectors,gates):
                        for variables,(source,polarity) in zip((a,c),pair):
                            literal=2*source+polarity
                            assignment.update({v:(k==literal) for k,v in enumerate(variables)})
                    assignment[output]=bool(phase)
                    bits=[bool(orientation&(1<<j)) for j in range(b)]
                    for j,bit in enumerate(bits):assignment[output+1+j]=bit
                    demands=[set() for _ in range(n+1+b)]
                    for j,pair in enumerate(gates):
                        for source,polarity in pair:demands[source].add(bool(polarity)^bits[j])
                    demands[-1].add(bool(phase))
                    own=[False]*(n+1)+bits
                    paid=[any(p!=own[i] for p in needs) for i,needs in enumerate(demands)]
                    for j,bit in enumerate(paid):assignment[output+1+b+j]=bit
                    cursor=output+1+b+len(paid)
                    for mask in truth_rows:
                        for bit in row_values[mask]:assignment[cursor]=bit;cursor+=1
                        rows_checked+=1
                    assert max(assignment)==cnf.variables
                    for flipped in [None]+list(range(len(paid))):
                        offered=list(paid)
                        if flipped is not None:offered[flipped]=not offered[flipped]
                        for j,bit in enumerate(offered):assignment[output+1+b+j]=bit
                        actual=all(any(assignment[abs(v)]==(v>0) for v in clause) for clause in cnf.clauses)
                        expected=sum(offered)<=maximum and all(not required or provided for required,provided in zip(paid,offered))
                        assert actual==expected,(n,b,gates,phase,orientation,maximum,flipped)
                        clauses_checked+=len(cnf.clauses)
                        cases+=1
report={'status':'PASS','assignment_cases':cases,'clauses_evaluated':clauses_checked,'row_assignments':rows_checked,'scope':'All sorted signed AIGs with n=0 or1 and b=1 or2, last-node output both phases, every orientation and every NOT cap; forward semantics and exact source-payment assignment, each single underpayment and each extra-payment perturbation checked. This audits encoding, not synthesis completeness or the Petersen lower bound.'}
Path('/tmp/oec/pequalnp-pilot-96/aig-sat-independent-audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
