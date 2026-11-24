UNVERIFIED monotone normalization experiment for L-meta-670.

Use ONLY global t=0. No formal dominance/minimality/constant-elimination theorem
has been proved. Native EXCLUDED below must not be presented as a Lean result.

Compile: g++ -std=c++17 -O2 live_theta_dominance.cpp -o live_theta_dominance
Commands:
 ./live_theta_dominance 40 5000000 15 0 1
 ./live_theta_dominance 40 5000000 15 0 2

Both retain the original414 diagnostic rows and twelve projection-prefix
oracles. Mode1 compares all414 positive and negative coordinates. Mode2 compares
one representative for each of12 minimal edge-positive inputs and12 maximal
independent negative inputs. New gates are rejected when positive labels are
allzero, negative labels allone, or an existing wire dominates them under
(g.p subset h.p, h.n subset g.n). Retention of operand a is skipped when new g
dominates a. These search omissions require a new normal-form proof.

Baseline:1159421calls,25.059s.
Mode1:1073813calls,12.6483s (1.08x node reduction).
Mode2:651835calls,7.44117s (1.78x node reduction).
The gain did not meet the requested10x threshold; formalization was not pursued.
Wall/RSS caps sampled every1024calls; node cap5million; RSS cap600000KB.
Full stdout/stderr and the exact source are retained.
