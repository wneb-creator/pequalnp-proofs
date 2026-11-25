# Proof strategy investigation

Current task: L-meta-2592, Petersen edge function, total gate budget 19 and at least one NOT.

## Checked existing component

`lean/PEqualNP/Outside/L_meta_4725.lean` (3224 lines, 146284 bytes) proves exactly the binary floor required by reduction R_meta_2592_271: every fan-in-two circuit computing the Petersen function obeys `15 + PEqualNP.NotBracket.notCount C ≤ C.size`. It uses six necessary branching wires, a graph twin-removal certificate, and a generic fan-in budget. L_meta_6194 is an alternate formulation counting non-NOT gates. These are existing fleet work, not new results of this pilot. Copying under the target namespace is possible if the full proof needs them, since only PEqualNP.Defs is an allowed project dependency.

The bound reduces the current problem to 1–4 NOT gates. The three live reductions are already on main: R_meta_2592_318 (last-NOT factorization plus hard separator), R_meta_2592_408 (normalization plus legal finite bound), R_meta_2592_271 (binary floor plus few-NOT bound). A fourth reduction exceeds the published ceiling.

## Searches

Inspected final theorem statements of all 162 Outside files containing Petersen/petersen. Also scanned final statements of every Outside L_meta file with notCount/AtMostOneNot and ten-input types, and every file containing the explicit full-function tail on input9. No already checked full 19-gate exclusion was found. L_meta_8021 only proves a contradiction from simultaneously having no NOT and positive notCount, so it does not solve any genuine remaining case.

Additional nearby certificates: L_meta_5236 and L_meta_5238 constrain full Petersen circuits after giving OR(x0,x2) as an input, splitting by number of NOTs. They do not directly imply the unspecialized target. L_meta_10762 is a reusable finite-search engine for a seven-input graph but has thousands of lines and a function-specific certificate; increasing to ten inputs and19 gates is not a simple numeric substitution.

## Mathematical assessment

The circuit semantics have no obvious loophole: gates are evaluated topologically, forward/missing wires read false, NOT ignores operands after the first, and only AND/OR/NOT are admitted. Thus arbitrary natural wire indices do not create a counterexample by themselves.

The generic branch count gives at least n-1+6=15 binary gates. Proving a stronger count for active negations would require a new argument about reconvergence/cancellation. No sound proof that NOT gates can be eliminated without increasing size has been found; assuming that would be circular or potentially false.

## Independent review

LastNotFactor.lean from status_1035 reviewed mathematically: suffix initial wires preserve all absolute indices; the empty NOT operand case uses an absent wire to yield false before negation; extra NOT operands are correctly ignored; prefix/suffix basis and size bookkeeping are sound. Namespace must be adjusted if integrated into the final posted proof. Compilation still pending at review time.

Updated 2026-11-25T13:51:34.710113+00:00
