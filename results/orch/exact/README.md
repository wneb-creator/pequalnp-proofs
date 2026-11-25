# Exact-synthesis artifacts

These scripts record counterexample searches for L-meta-2592. No script or solver verdict is a Lean proof. No verified19-gate counterexample has been found. The SAT control cases use20gates or incomplete input domains.

`manifest.json` records current verdicts and full-log checksums. Raw logs and CNFs are under the scratch paths listed there. `synth.py` supplies the shared CNF class. Solver execution paths are intentionally pinned to this job scratch installation of officialKissat.

The standard search model omits constants and repeated binary operands, makes the finalgate the output, and sometimes requires everygateactive and/or canonicalfanin order. Thus restrictedUNSAT results do not alone establish the postedstatement. Full-candidate validation always checks all1024 Petersen inputs.
