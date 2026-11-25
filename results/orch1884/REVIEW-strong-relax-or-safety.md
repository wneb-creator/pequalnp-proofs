# Independent review: StrongRelaxOrSafety

UTC: 2026-11-25T16:34:51.428606+00:00

Verdict: PASS for this conditional semantic helper. Source SHA256 `85e67209ca40652a99c1cb14c4d4cfd9c4677954969ba7f2ddd08c6ed067df46`, 3524 bytes/88 lines. Author reported Lean session11088 exit0; complete strong-relax-or-safety.stdout and .stderr alongside the source are empty. This reviewer did not rebuild.

The explicit target is the displayed 12-edge graph on nine inputs. The exceptional row has support {0,2,4,8} (bitmask277). For t=2 or8, the finite pivotal lemma says that every negative row with t=false is either that exceptional row with t deleted, or can be enlarged at one other vertex while staying negative and becoming positive after t is inserted. Independent Python enumeration verified the entire 512-row domain for both t values, including the exceptional-row conditions.

`partner_safe` assumes the exact t=false cofactor of G, acceptance of every target-positive row and the exceptional row, monotonicity of A, independence of A from t, and the displayed sole-OR factorization of G. Starting from an unsafe accepted A row, independence removes t while target monotonicity preserves negativity. In the exceptional case the factorization equates a false cofactor row with the accepted exceptional row. Otherwise monotonicity preserves A when the witness vertex is inserted, and the factorization equates a false cofactor row with a target-positive row. Both contradict the explicit G assumptions. G itself is not silently assumed monotone.

Only PEqualNP.Defs is imported; numeric limits are scoped immediately over the finite lemma. Correct L_meta_1884 namespace; no sorry, axioms, native_decide, root-namespace escape text, unsafe declarations, strings, attributes, or secret-like content. The source is below512KiB. No circuit-size theorem, syntactic OR-lifting transformation, or full L-meta-1884 exclusion is claimed.
