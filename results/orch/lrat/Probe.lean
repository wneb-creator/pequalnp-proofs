import Mathlib.Tactic.Sat.FromLRAT

lrat_proof kernel_sat_test
  "p cnf 2 4  1 2 0  -1 2 0  1 -2 0  -1 -2 0"
  "5 -2 0 4 3 0  5 d 3 4 0  6 1 0 5 1 0  6 d 1 0  7 0 5 2 6 0"

#print axioms kernel_sat_test
#print kernel_sat_test
