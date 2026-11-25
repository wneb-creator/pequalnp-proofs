# Stopped after desk lease failure

Pilot: pequalnp-pilot-93. Message acknowledged: msg-e24c394f684f728d121e81e5.
Own assigned gap: L-meta-2592. No proof PR was opened.

The last successful renewal at14:36:15.946UTC reported expiry14:56:15.946UTC. At14:39UTC the next renewal returned HTTP410. Repeating the identical call with curl-si confirmed410; complete headers/body are in desk-http410.txt. Exact body:

    {"error":"no such live lease: it expired or was released. Ask /desk/next again."}

Per the user's later410 instruction, all reviewed compiled work was pushed first (961cfb2b56a4c949346cfd40d71f107c1bd1ffd4), then recovery was requested with another=1 and hard=1. Both the recovery request and the one permitted retry returned the same L-meta-2583 lease, issued13:59:02.364UTC, before the recovery attempt. Exact desk note:

    you hold 5 gaps, the most one handle may hold at once; release one to get another

This is an existing other-pilot lease under the user's explicit shared-handle rule. It was neither worked, renewed, nor released. No further desk requests were made after the retry. The original lease was already invalid, so no release call was made for it. Null answers:0. Stopping before90minutes follows the explicit desk/other-pilot stop rule, not a claim that the mathematical task is complete.

Strongest checked partial: Structural17.lean proves17+notCount<=size, excluding at least3NOT gates at size<=19. Exactly1NOT/2NOT cases remain unproved. Full posted-statement lake build and tools/check-lean.mjs were not run because no full posted theorem exists. The source has4984lines; no final-proof cleanup pass was applicable.

Other checked components: weighted live-circuit normalization to a sole input reader; reader-count bounds; restricted mask classifications and gate transformations; a complete114-case matching certificate on a fixed seeded13-row problem. Complete compiler logs are archived. All pushed changes were independently reviewed before push.

Unchecked full research sources: finite/PackedBaseline.lean and lemmas/CompleteSeededMatch.lean. Their sources are preserved for continuation; neither full file has a successful Lean check. The constituent seeded certificate/row/semantic files are checked individually.

Native cap15 forest stopped UNKNOWN after300.116seconds, with74359 closed states and171800 visits. Saved closed-state data are in finite/live15-first.json. The cap14 native baseline was UNSAT but its generated Lean certificate was not compiled. Three sole-reader SAT cases ended UNKNOWN after180seconds each. No counterexample was found. These computations are not unrestricted lower-bound proofs.

No proof acceptance occurred. All searches/builds have stopped. Research artifacts remain on the pilot branch as explicitly authorized; they are not a single-file proof PR.

Sub-agents: special_status, structural_proof, counterexample_search, reduction_routes, finite_certificate, or_first_bound
TIMING total=59.9 subagents=6
