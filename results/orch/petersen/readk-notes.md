# Petersen ReadK work

Checked artifact: readk_bound.lean (1429lines,67KiB), inlined accepted6369 plus finite Petersen graph facts. It proves every AO2 circuit computing Petersen and satisfyingIsReadK1 has at least20gates. Main/root notified for immediate preservation.

The20-gate witness from gate_count_theory has exactlytwo nonread1edges:04and27, both cappedvector(2,2). Its dirtyANDs17and18 respectively accept singleton2andnonedge02. This shows that a 20-gate circuit matching the standard construction bound need not be read-1. Minimality at 20 is not established. Profile saved readk-twenty-profile.json.

A structural probe generated20-gate,exact6AND,14OR,circuit CNF with distinguishededge01 failingread1. It uses all30criticalassignments and backward binarygates. This tests an equality-case normal form, not thetarget≤19claim. Full CNF/JSON/solverlogs are in scratch readk-petersen-20-and6-nonread.*; generator readk_probe_cnf.py is in this folder.

Charge route: L1491/L4183 give size≥15+cover(GminusUstar)+2centreless+junk+nonlamOR−|Ustar|−1. For20witness:residualcover5,junk2,nonlamOR1,Ustar2, equality20. Petersen5vertexsets span≥2edges and6vertexsets≥3, so cover dropsatmostceil(U/2). A sufficient remainingstructural inequality wouldbe junk+nonlamOR+2centreless≥U+ceil(U/2). This wasnotproved. Library_route has independentlyformalizedfinitecoverdeletionprofile.

The exact-six-AND, 20-gate non-read-1 probe reached its 300-second limit with UNKNOWN; it produced no witness or impossibility result. No new proof/search work afterSTOP.

Probe final output:

```text
c setting time limit to 300 seconds real time (due to '-t 300')
c total process time since initialization:       198.49    seconds
```
