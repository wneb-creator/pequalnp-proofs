# Petersen searches: checkpoint2, stopped after lease invalidation

No counterexample to L-meta-1884 and no UNSAT exclusion certificate was obtained. All active searches were stopped at root's request at2026-11-25 17:09:56UTC after the desk returned410. No child solver remainsrunning. The earlier frozen checkpoint at results/orch/petersen-search is unchanged.

## Completed searches and controls

- Both010 (oneOR/raw0 reader andoneAND/freeNOT0 reader), at mostone paidNOT: rawreaderfirst UNKNOWN600.140s; auxiliaryreaderfirst UNKNOWN600.257s.
- Only10/twoAND (raw0unused, twoAND readers of freeNOT0), at mostone paidNOT: UNKNOWN600.105s.
- Compact AO-only both010, both freeconstants allowed, zero paidNOTs, exact38 cofactor-extreme rows: UNKNOWN300.035s. Giving bothconstants forfree is a relaxation; anySAT model is constant-propagated back to an actual11-input circuit and fullyverified. Its20-gate positivecontrol passed.
- Pv9 (Petersen-minus0), exact16gates with exactlyone paidNOT: interrupted after roughly331s on80 seedrows, no candidate ordecision. The query permits NOT(false) and excludes aterminal uniqueNOT by monotone-prefix/antitone-output reasoning. Outputverification coversall512 assignments.
- Pv16 AO positivecontrol: SAT0.292s, all512 inputsverified.
- Pv18 positivecontrol withone used NOT(false) andAND(output,true): SAT0.147s, all512 inputsverified. This controlkeeps everygate used; a17-gate version obtained by adding anunused NOT would fail that normalization condition.

The ≤1NOT case budgets depend on the independently derived Pv≥15 non-NOT lower bound and deletion of two binaryreaders without deletingNOTs. These are restricted case searches, not exclusion of the full gap.

## Canonical CNF and CaDiCaL

`petersen-enc2.py` emits the exact one-hot clause list of the team's compiled LinkN2 encoding for11inputs,18gates, and108 correlated rows, where input10 equals NOT(input0). The base query has232374 clauses andmaximumvariable311851. Its SHA256 is99eb8280d8b3bcf866034ab8b047fc770f13c2572ac1947d3ee1e15cc43df1d9.

The20-gate control was reordered using the canonical parent1,parent2,operation key. Every one of286004 baseclauses was independently evaluated under an explicit satisfying assignment; the complete1024-input truth table also passed. With992 fixedstructural units, CaDiCaL returnedSAT in0.24s. This validates the encoding against a knowncircuit, not the18-gate exclusion.

Base108-row CaDiCaL withASCII LRAT logging was terminated after77.217s when its proof exceeded the150MiB diskcap. Status UNKNOWN; the157761536-byte partialproof is NOT a completed certificate. It was losslesslycompressed to28583283 bytes, with decompressed SHA2567fc0f0865d61bb0260730807f6dbef3dfa9ec539be575665f8d88036a221d517 and compressed SHA2567374b6ca5469f0aa08cef7c5c632f00dedbff6e565a9ee8afc6cda1fb64d3dce. The full log, monitor metadata, and compressed partial are retained.

Proof-disabled CaDiCaL queries were then stopped for the lostlease:
- Base plus816 at-most-two-NOT clauses: interrupted after246.625s, UNKNOWN.
- Base plus153 at-most-one-NOT clauses: interrupted after191.379s, UNKNOWN. This stronger globalbudget depends on the team's new signed17 non-NOT component; its concrete accepted-premise wrapper was pending when the query started.

The exploratory budget clauses use lexicographic itertools.combinations order. The proven fNotOne/fNotTwo lists use outerlargestindex order. The logical clause sets are identical, but initial LRAT clauseIDs differ. These interrupted proof-disabled runs make no certificate claim. `petersen-add-budget.py --order canonical` reproduces the exact proved order for any future certificate replay; active inputfiles were never overwritten.

## Semantic-distinct extension control

`petersen-semantic-enc2.py` appends budgetclauses in canonical order, then nonconstant, difference-request, and difference-definition clauses matching the reviewed Lean definitions. The intended model property is minimumsize relative to the sampledrows, withpadding andan upperNOTbudget. It must not be transferred directly to exactreader cases or exactone-NOT classes, because semantic deletion can change those classes.

Only apositivecontrol was run: all351444 base/budget/semantic clauses were independently checked under the known20-gate model; plus992 structuralunits, CaDiCaL returnedSAT in0.52s. No18-gate semantic-distinct solver query was started before the lease stop. The sample-minimizer existence bridge was still being compiled when these artifacts were generated.

## Preservation and reproduction

All scripts, complete solver stdout/stderr logs, decoded positivecontrols, exact SMT/CNF queries, and stoprecords are retained. Queries are gzip-compressed; UNCOMPRESSED_HASHES.json gives exact raw hashes andsizes. The incompleteLRAT is also compressed and explicitlylabelled. No solverbinary, credential, environmentdump, or Lean/buildsource copy is included.

Python3/Z3 5.3.3 source details are in the first searchbundle. CaDiCaL comes from the installed Lean4.36.0 toolchain; run after sourcing the task's toolchain-env.sh. The monitor enforces a wall-time limit, proof-size cap, and200MiB free-disk floor. Externalstop records distinguish lease interruption from timeout andUNSAT. MonitorJSON corrects one initial start/finishlabel mixup from the preserved startline; the original complete monitorlog was not edited.

Reproduction examples: `python3 pv-one-not-cegis.py 16 600000 1 general`; `python3 petersen-both010-not1-cegis.py 18 600000 not rawfirst`; `python3 petersen-enc2.py --out petersen-enc2-108.cnf`; `python3 petersen-add-budget.py petersen-enc2-108.cnf budget.cnf --budget 1 --order canonical`. The supplied scripts retain their session scratch paths. No further searches should be started without the parent's recovered lease.
