# Existing seven-variable theta lower bounds

The requested eight-edge theta(2,3,3) graph already has a checked repository lower bound of eleven gates. The strongest matching source found here actually bounds eleven non-NOT gates. This was a read-only source search; no new Lean proof or compilation was run for these existing files.

## Exact canonical graph

`lean/PEqualNP/Outside/L_meta_517.lean:2766` states:

For every s, HasCircuitSize7 of the edge function with edges02,21,03,34,41,05,56,61 implies11≤s.

These are the three internally disjoint paths0–2–1,0–3–4–1,0–5–6–1, so the graph is exactly theta(2,3,3). HasCircuitSize uses the full FanInTwo basis, including NOT, and therefore implies the requested monotone lower bound. The source has2766 lines and260309bytes; SHA256 `bf8c6d77c9816f66f63b56bd3b3dc52b02c0b5134ef62a735f3a593c6174517a`.

`L_meta_3128.lean:2771` proves the same exact statement with fully qualified helper namespaces. It has2772 lines and260894bytes, so it is essentially a duplicate rather than a smaller certificate.

## Stronger non-NOT count

`lean/PEqualNP/Outside/L_meta_2960.lean:2506` assumes FanInTwo and exact computation of the graph with edges01,12,04,15,26,35,46,63, then proves at least eleven non-NOT gates. Its GateOp-rec counting predicate is true on AND/OR and false on NOT; the other constructors are excluded by FanInTwo.

The canonical theta vertices map to this source's vertices by `[1,6,2,0,4,5,3]`. The three source paths are1–2–6,1–0–4–6,1–5–3–6. Thus this is the same graph. The inverse permutation is `[3,0,2,6,4,5,1]`. A circuit with one NOT therefore needs at least twelve total gates once the input relabeling bridge is supplied.

This source has2507 lines and201746bytes; SHA256 `5533a4ad42c586e783e0885cf977de4458b56a2b65e87b240b443cd34f0d65a7`. It is substantially smaller than L517 and is the better reuse candidate when the relabeling can be handled cleanly.

## Direct nine-cofactor specialization

`lean/PEqualNP/Outside/L_meta_2014.lean:2934` proves11≤s for the same twelve-edge nine-input p9 used in ReaderBound, evaluated on `Fin.insertNth 0 false (Fin.insertNth 3 false x)`. This removes coordinates0 and4 in the old nine-variable numbering: the inner coordinate3 shifts to4 when coordinate0 is inserted. It does not mean removal of old coordinates0 and3. The source has2935 lines and267374bytes.

## Search scope

The existing monotone-final census and two upstream-refresh censuses were checked first. A subsequent narrow local-source census selected294 Outside files mentioning seven Boolean inputs or BitVec128, then inspected their final theorem segments. Seventeen candidates mentioned the relevant ten/eleven thresholds. Full selected theorem records are saved in job scratch `1884-seven-final-floor-sources.json`; the filename census is `1884-seven-source-files.txt`. The exact matching sources above were read directly. General one-NOT elimination statements and unrelated fourteen-variable Fano statements were excluded from these conclusions.

Final single-file submission still requires inlining and namespace/format cleanup under the current target, rather than importing an existing Outside proof.
