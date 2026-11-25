# Lean route

- Definitions root gives standard circuits; no vulnerability found.
- All three reductions of L-meta-2592 already exist (_271, _318, _408); capacity appears full.
- L_meta_6194 proves at least 15 non-NOT gates for Petersen. Therefore only 1–4 NOT gates remain under budget19.
- L_meta_2517 proves Petersen-minus-vertex lower bound16 with exactly two NOT, via binary-gate lower bound14 and finite cover search. Generic machinery ~4600 lines.
- L_meta_11365 handles a different 7-vertex graph; its one-NOT elimination uses unconditional non-NOT floor10 plus explicit monotone witness11. Not enough for Petersen20.
- Last-NOT decomposition assigned to structural_proof.
- LeanRoute.lean adapts monotonicity helper from L_meta_6422 and adds exclusion of a monotone circuit complement computing Petersen, using all-false/all-true inputs. Awaiting environment compile.

## Pause at lease HTTP410, 2026-11-25T14:38:51Z

LeanRoute.lean is330lines. First compilation completed exit1; full diagnostics are in /tmp/oec/pequalnp-pilot-127/lean-route-build.log. Initial88-line monotonicity/complement segment elaborated without errors, but overall file is not checked. New lemmas prove intended readonce-NOT exclusion and rawprimaryinput AND/OR mask exclusion; they currently have simp/getD proof errors. No new proofwork after pause.

Likely repairs: use simp only for getD_ofFn (full simp expands concrete Fin10 list); NOT branch change directly to !U.getD v=false implication before rewriting atV; List.all_eq_false witness needs by decide for negated true equality; masked_gate_eval close by uu.trans vv.symm after change instead of simp; give explicit witness lambda to Exists.intro.
