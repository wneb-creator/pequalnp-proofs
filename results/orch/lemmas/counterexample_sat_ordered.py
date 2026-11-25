"""Witness-only SAT variant with adjacent-independent source-pair ordering."""
import importlib.util
import itertools
import os
from pathlib import Path

path=Path(__file__).with_name('counterexample_sat.py')
spec=importlib.util.spec_from_file_location('counterexample_sat',path)
module=importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
original_encode=module.encode

def encode(rows,gates,first,normalized=False):
    cnf,choices=original_encode(rows,gates,first,normalized)
    # Additional witness restriction motivated by the checked 15-binary-gate floor.
    # Together with the generic at-least-one constraint this searches 1 to 4 NOTs.
    for subset in itertools.combinations([n for a,b,n,o in choices],5):
        cnf.add(*(-n for n in subset))
    # Exclude the last pair unless every gate is required to feed the output.
    # Swapping the last independent pair could otherwise change the designated output.
    stop=gates-1 if normalized else gates-2
    for i in range(stop):
        a,b,n,o=choices[i]
        aa,bb,nn,oo=choices[i+1]
        for k in range(len(a)):
            for j in range(k):
                # If the second left input decreases, dependence is only possible
                # through the second right input (the first output is the largest index).
                cnf.add(-a[k],-aa[j],bb[11+i])
        for x in range(len(a)):
            for k in range(len(b)):
                for j in range(k):
                    # Both selected source pairs are then independent of each other.
                    cnf.add(-a[x],-aa[x],-b[k],-bb[j])
    return cnf,choices

module.encode=encode
if __name__=='__main__':
    os.nice(10)
    module.main()
