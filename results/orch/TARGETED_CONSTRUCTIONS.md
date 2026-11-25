# Targeted signed construction search for L-meta-2592

No19gate counterexample was found. The strongest new result is a small computational obstruction to compressing the OR-sum subnetworks of every existing20gate star-cover seed. This is not a Lean-checked statement and does not prove the posted gap.

## Star-cover shared-sum obstruction

Each of the40 validated20gate monotone seeds has6 final star AND gates,5 final aggregation OR gates, and9 gates computing6 neighborhood sums. Thus a circuit of at most8gates computing those6 sums, with1-3NOTs, would give a19gate Petersen counterexample while leaving the11assembly gates fixed.

The6 sums use7inputs. Four core inputs a,b,c,d occur3times each, and3private inputs p,q,r occur once each. Every core pair appears once. The3 privately augmented pairs form either a triangle or a star. Exact extraction from all40 seeds gives20of each family (star-sums-seed-classification.json):

Triangle family: a OR b OR p; a OR c OR q; b OR c OR r; a OR d; b OR d; c OR d.
Star family: a OR b OR p; a OR c OR q; a OR d OR r; b OR c; b OR d; c OR d.

The exact synthesis encoder search_star_sums.py has7inputs,8gates,6designated outputs, and all128truth-table rows. Gates are AND/OR with distinct existing input wires or unaryNOT. Each selector has exactly one choice; outputs are arbitrary distinct gate wires. The NOT count is1to3. The final padded runs permit unused gates, so a smaller normalized circuit can be padded with unused OR gates. This avoids the nonmonotonicity of an exact-size liveness constraint.

Results using CaDiCaL:
- Triangle, padded8gates: UNSAT; exit20;1.81seconds real time;44,849clauses.
- Star, padded8gates: UNSAT; exit20;1.80seconds real time;44,849clauses.
- Preliminary live8gate runs were also UNSAT in2.03/2.27seconds, but are unnecessary for the padded claim.
- Positive controls at9gates and0NOTs were SAT for both families. Independent decoding checked every128input assignment for all6outputs and every52,881CNFclause. Full circuits are saved in star-sums-positive-control-validation.json.

This rules out the indicated shared-sum replacement family in the encoded normalized model. It says nothing about circuits that alter the11assembly gates, interleave star products with sum computations, use different decompositions, or use more than3NOTs. It is computational evidence, not a kernel certificate.

Reproduction from repo root:

    python3 /tmp/oec/pequalnp-pilot-101/counterexample/search_star_sums.py /tmp/oec/pequalnp-pilot-101/counterexample/star-sums-triangle-padded8.cnf --family triangle --allow-unused
    /tmp/oec/pequalnp-pilot-101/toolchain/lean-4.36.0-linux/bin/cadical -t 30 -w /tmp/oec/pequalnp-pilot-101/counterexample/star-sums-triangle-padded8.sol /tmp/oec/pequalnp-pilot-101/counterexample/star-sums-triangle-padded8.cnf > /tmp/oec/pequalnp-pilot-101/counterexample/star-sums-triangle-padded8.log 2>&1

Replace triangle by star for the other family. For positive controls add --gates 9 --min-nots 0 --max-nots 0 and use the separate positive9 paths.

Frozen generator SHA256:591a7f6e233b5dd36c26b0511f258132ad7e4bf45934eb66528208c5db6188c8. Independent semantic-audit verdict: PASS within the stated ordinary-gate family. The auditor independently reconstructed all40 seed cores, decoded both positive controls on all128rows and all52,881clauses, checked the padded8UNSAT records, and reviewed constraints. Its full log is semantic-star-sums-audit.log. No unrestricted Petersen conclusion follows.

## Six-cycle care-output relaxation

The previous six-cycle search required exact antipodal pair ORs on all64rows. A less restrictive valid decomposition requires these outputs only on the18independent-set rows where the core H is false. H itself remains exact on all64rows. When H is true the Petersen wrapper already outputs true, masking all pair outputs.

The new search_hexagon_care.py implements this relaxation,10gates and1-3NOTs, H last. Results:
- All3pairoutputs arbitrary under the care set: UNKNOWN at60seconds real time.
- First2pairORs fixed exactly, third output arbitrary on care set: UNKNOWN at30seconds real time.

Neither UNKNOWN is an exclusion. Source, CNFs, maps, full stdout/stderr, and solution-status files are all saved in this directory as hexagon-care10*.

## Primary research read

Read2026-11-25: https://pequalnp.com/papers/note-1 , Lower bounds for the edge function: a readable account of ten Lean-checked statements. Saved complete HTML and extracted text as note-1.html and note-1.txt. Its discussion of Boolean sums observes that dense several-output sums can benefit from NOT gates; it does not provide a Petersen19gate construction or a theorem eliminating negations for Petersen. This motivated the narrowly targeted shared-sum test above. No externally quoted numerical claim was used as a proof premise.
