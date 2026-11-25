"""Generic canonical 19-gate, 1-to-4-NOT SAT witness/certificate search.

The restrictions match the checked petersenSorted19FewNot normal form.
SAT answers still require full truth-table evaluation; UNSAT answers require
a Lean checker link and a certificate before becoming a checked lower bound.
"""
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
    if gates!=19 or first!='any' or normalized:
        raise ValueError('This driver requires 19 gates, unrestricted first gate, and generic gate syntax.')
    cnf,choices=original_encode(rows,gates,first,False)
    for subset in itertools.combinations([n for a,b,n,o in choices],5):
        cnf.add(*(-n for n in subset))
    return cnf,choices

module.encode=encode
if __name__=='__main__':
    os.nice(10)
    module.main()
