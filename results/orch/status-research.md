# Status and source research

Read 2026-11-25 UTC. Public map snapshot generated at 14:26:35.973Z.

## Exact status

- L-meta-1035 remains `conjecture`, with `seat: null` and no recorded attempts. Source: https://data.pequalnp.com/data/lemma/L-meta-1035.14ea345977c1.json . This does not establish whether an outside pilot currently leases it. Lease availability is UNVERIFIED because the public lemma record has no outside lease field.
- L-meta-2592 remains `conjecture`: https://data.pequalnp.com/data/lemma/L-meta-2592.bb62b8ddb8cf.json .
- Parent L-meta-651 remains `conjecture`: https://data.pequalnp.com/data/lemma/L-meta-651.7745f79d6eb9.json . Its plain statement records the 20-gate upper bound and conjectured 19-gate exclusion.

The public map is https://data.pequalnp.com/data/map/program/meta_complexity.99e59209e36f.json . Its compact nodes hold the lemma id suffix and the hash needed for the exact per-lemma URL. Search shard https://data.pequalnp.com/data/search/2.a8ce03dd8cee.json maps the token `2592` to all six reduction children and their negated twins.

## Existing reductions and children

| Reduction | First component | Remaining component |
| --- | --- | --- |
| R_meta_2592_271 | L-meta-4725, **checked**: 15 + NOT count is at most circuit size | L-meta-4727, conjecture: exclude size at most 19 with 1–4 NOT gates |
| R_meta_2592_408 | L-meta-7389, **checked**: normalize wires and trim output | L-meta-7391, conjecture: lower bound for normalized circuits |
| R_meta_2592_318 | L-meta-8295, **checked**: split at the last NOT gate | L-meta-8297, conjecture: Petersen separator for the two resulting pieces |

The last-NOT splitting statement is already checked exactly, with credit to MiguelTorresPerez: https://data.pequalnp.com/data/lemma/L-meta-8295.98923effade9.json . Its companion is https://data.pequalnp.com/data/lemma/L-meta-8297.2c2c98e766d2.json . Thus the generic cutLast lemma cannot produce a fresh accepted subsidiary proof.

Other component records:

- https://data.pequalnp.com/data/lemma/L-meta-4725.8de352159827.json
- https://data.pequalnp.com/data/lemma/L-meta-4727.ab7440e4a3db.json
- https://data.pequalnp.com/data/lemma/L-meta-7389.e30b41e04d5d.json
- https://data.pequalnp.com/data/lemma/L-meta-7391.4f1d1d7b8318.json

All exact fetched JSON is retained under `/tmp/oec/pequalnp-pilot-127/status-<id>.json`.

## Proof-source findings

- `L_meta_6194.lean` contains a 3255-line self-contained Petersen binary-gate lower bound. Its final theorem proves at least 15 non-NOT gates, so adapting it gives the high-NOT cases immediately but leaves the 1–4 NOT cases.
- New seven-vertex one-NOT proofs such as `L_meta_10778.lean` and `L_meta_10792.lean` use branch-group binary-gate bounds plus an explicit monotone upper bound. This method alone does not close Petersen's gap from 15 to 20.
- `L_meta_11179.lean`, `L_meta_11321.lean`, `L_meta_11399.lean`, `L_meta_11627.lean`, and `L_meta_11303.lean` adapt `L_meta_10458.lean`: one-NOT normal form, an input-fixing potential, and a four-clique search. Petersen has no clique of size four, so direct graph substitution does not apply.
- `OneNotSplit.lean`, `OneNotEval.lean`, `OneNotPiece.lean`, and `OneNotRelabel.lean` contain useful normal-form and restriction machinery, but no universal cost-preserving graph monotonicization theorem.
- `LocReadOne.lean` contains elaborate read-once elimination for a long-thread graph class. It relies on a six-vertex run with degree-two internal vertices, absent in Petersen.
- The source note `notes/note-1-edge-function-exact-size.md` and the public paper https://pequalnp.com/papers/note-1 describe exact AND/OR/NOT counts for forests, cycles, and separated high-degree vertices; their structural graph hypotheses exclude Petersen.

## Unproved possible direction

In a trimmed 19-gate circuit with at least one NOT, counting all gate-input wires yields at most `20 - numberOfNOTs` reads of input variables, because each nonoutput gate needs at least one reader. Hence some one of the ten essential input variables is read once. A strong elimination theorem for a read-once cubic Petersen vertex could conceivably reduce to the vertex-deleted graph, whose cover construction uses 16 gates. The missing mathematical step is proving enough gates become removable despite sharing of the neighbor-OR subcircuit. This is an idea only, not a checked lemma or a known theorem.
