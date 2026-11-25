# Kernel-checked q=3 circuit certificates

`../lemmas/q3word_certificate.lean` is a self-contained, compiled preparation artifact importing only `PEqualNP.Defs`. It does not exhibit a circuit smaller than the canonical 64-gate construction.

The incidence relation on `Fin 13` is `p = l`, `l+1`, `l+3`, or `l+9`, with arithmetic modulo 13. Plane axioms and counts are checked: 52 incident pairs and 8192 point subsets.

For each point subset A, the canonical negative input selects exactly A and every line avoiding A. Every negative input lies below one of these inputs. Monotonicity therefore proves full incidence semantics from agreement on the 52 incident pairs and rejection of all 8192 canonical negatives.

The word evaluator runs all rows simultaneously. Each input is a BitVec word; gate AND and OR become bitwise AND and OR. A generic proof by list-map/fold commutation establishes that every output bit equals ordinary circuit evaluation on the corresponding input row. All concrete input words are verified against their intended rows inside Lean.

For a candidate circuit D, use `PEqualNP.Outside.L_meta_2583.Q3WordControl.full_semantics_of_words`. Its premises are `IsAO2 26 D`, `wordEval D positiveWords = 0xfffffffffffff`, and `wordEval D negativeWords = 0`. The positive and negative widths are 52 and 8192 respectively. The file tests this entire chain on the canonical 64-gate circuit and proves its full semantics.

Only ordinary kernel checking is used, including `decide +kernel`; there is no native_decide or bv_decide. The observed peak RSS for point-column packing was about 3.19 GB. Complete build output is in the job scratch log `q3word-certificate-build.log`.

The standalone generator `q3_word_certificate_generate.py` and data `q3_word_control.json` reproduce the numeric control tables. The Lean file contains all literals and proofs, so compilation does not depend on the generator or JSON.
