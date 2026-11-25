# Research artifact review

Reviewed 2026-11-25T06:28:55.827565+00:00 by repo_review, read-only except this note. Coordinated stable-file lists with circuit_search, lower_bound and constructive. No desk calls, builds, solver runs, git mutations, installs or credential reads.

## Verdict and claims

PASS for preservation of the identified research artifacts, provided the final snapshot records capture times and hashes. No credential-shaped values, environment dumps or credential-reading commands were found in the inspected sources/configuration files. Current tracked modifications are restricted to results/orch research notes; no unexpected core source/config edits were present.

The factor result is a checked-by-enumeration36-gate candidate with14 degree-two shadow edges, not a26-gate solution. The factor-pair enumeration is exhaustive only over maximal compatible pairs, not all circuits or minimum circuit costs. Scoring and MILP objective are heuristics. UNKNOWN solver results and fixed-candidate UNSAT smoke outcomes must not be reported as a general lower bound. The strategy notes currently preserve these distinctions correctly.

## Factor snapshot

Stable programs in job scratch constructive/: factor_partition.py, factor_compatibility.py, factor_orbits.py, factor_score.py, factor_milp.py. These use same-directory imports and must remain together.

Preserve complete JSON/log pairs: compatible-pairs; factor-orbits; factor-score-smoke; factor-milp-run1. The initial factor-smoke pair is historical: its log used an earlier scorer revision and is not claimed byte-reproducible from the final source.

Reproduction sequence, with <dir> replaced by the saved directory:

- python3 <dir>/factor_compatibility.py --seconds 10 --output <dir>/compatible-pairs.json
- python3 <dir>/factor_orbits.py --input <dir>/compatible-pairs.json --output <dir>/factor-orbits.json
- python3 <dir>/factor_score.py --input <dir>/factor-orbits.json --output <dir>/factor-score-smoke.json --seconds 5 --passes 1
- python3 <dir>/factor_milp.py --input <dir>/factor-orbits.json --output <dir>/factor-milp-run1.json --seconds 90 --per-case 1

Capture complete stdout/stderr separately for each command. Owner reports Python3.12.14, NumPy2.3.5 and SciPy1.17.0 were preinstalled; no installation or network fetch occurred. Only factor_milp needs NumPy/SciPy. Enumeration counts should reproduce; timing, set iteration and MILP heuristics can alter retained scoring candidates.

Confirmed summary consistency:5033 maximal unordered pairs,168 side-preserving automorphisms,45orbits; first scoring pass45representatives; MILP109cases in90.169seconds, best36gates/14shadow edges. These agree between notes, JSON and logs.

## Shadow-three snapshot

Stable source/configuration dependencies: circuit-search/synthesize.py, phased.cpp, phases.py, shadow_smoke.py, near26.json, near26-shadow3.phases, solver-metadata.json; sat-review/verified_symmetry.json and verify_rows_symmetry.py are required by phase generation and must also be preserved.

shadow3-26.cnf and its mapping are regenerated with synthesize.py --gates 26 --dirty-and --shadow-missing 3. Saved encoding log reports11073variables,306744clauses,58rows. Preserve the exact generated files or their hashes plus exact generation command/source hash. Use the shadow-specific phase file; the earlier near26.phases belongs to a different encoding.

The separate active guided run uses live-dirty26.cnf, near26.phases and guided26-run.json. It adds liveness and dirty-AND restrictions. Do not conflate it with either the shadow-three run or unrestricted-output CEGIS. Completed shadow smoke logs show a fixed27gate star excluded and a fixed28gate absorbed circuit accepted and truth-table checked; neither is a general SAT/UNSAT claim.

## Hot-hint CEGIS snapshot

Stable sources: lower-bound/cegis-hints.cpp, cegis-hints.hpp, cegis-warm.hpp, prepare_cegis.py, biclique_warm.py. Preserve both included headers. Preserve cegis26.meta and the exact base CNF or source/hashes/commands required to regenerate it. Base preparation removes only the validated58output-unit clauses from heawood26.cnf and its mapping. The general encoder reproduction command is synthesize.py --gates 26 --no-liveness, matching the recorded original hash.

Preserve biclique30.json and biclique30.hint as stable hint inputs. Current cegis26-hints.hint, status, run log and iteration/warm models are LIVE: copy them with an explicit snapshot timestamp, and distinguish incomplete log prefixes from completed logs. Source files are frozen according to lower_bound. Smoke logs hint-accept, hint-fallback, hint-invalid, biclique30-fixed, final-accept and final-fallback are complete.

The driver validates hint format, gate count, backward references and active rows. Hint or warm UNSAT probes explicitly fall back to unconstrained solving; they do not become a false general UNSAT result. It uses bounded solving slices and reports UNKNOWN on exhaustion. Current owner report is31active rows and UNKNOWN; last SAT candidate satisfied30rows and retained false positives. General research encoding includes canonical65prefixes, adjacent independent order and boundary nontriviality, with tail copies allowed; it has no liveness/domination/dirty-AND/shadow restriction.

## Official checker capacity

Current filesystem:7.9GiB total,1.2GiB free. Toolchain3.1GiB, project .lake2.6GiB, Mathlib package2.2GiB. Compressed local Mathlib cache is already only136KiB, so removing archives cannot materially help.

The unchanged official local checker loads all Mathlib, including private/server module data and IR; focused dependencies are insufficient. No supported cache artifact-filter option exists. I found no realistic route to full checker readiness within this volume while preserving required artifacts. More local storage, a larger environment, or the unchanged official checker on a sufficiently provisioned runner is the credible route once a complete candidate exists. Do not fabricate a root Mathlib.olean, remove required runtime files, alter checker imports, or report focused compilation as official-checker acceptance.
