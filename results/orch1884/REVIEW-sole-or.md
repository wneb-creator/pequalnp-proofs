# Independent review: sole-OR partner restriction

UTC: 2026-11-25T15:44:44.896708+00:00
Verdict: PASS for the checked helper, explicit hypotheses, and format. This is a partial structural lemma, not the posted L-meta-1884 theorem.

Source: `results/orch1884/lemmas/SoleOrPartner.lean`
SHA256: `3c15df98085121ffa83c0e6e672feb9f96883a52ef190e38c30e44378fb83939`
Size: 3759 bytes.

The author/root reports Lean exit 0. Complete logs `/tmp/oec/pequalnp-pilot-103/1884-soleor-first.stdout` and `.stderr` are empty (both SHA256 e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855).

The target lists exactly the fifteen Petersen edges. The finite witness proposition covers every v other than 0 and every w distinct from v; it finds u outside {0,v,w} for which {w,u} is independent but {v,w,u} contains an edge. Lean proves it by ordinary decide; I also independently checked all 81 cases directly from the edge set.

The first lemma assumes H is monotone within each fixed-x0 fiber and assumes the explicit factorization property through v OR H. If H accepts singleton w, monotonicity makes H accept the independent pair {w,u}, while adjoining v forces the OR output true. Both assignments agree off v and have the same OR output, contradicting their different Petersen values. The choice u != 0 is exactly what preserves the x0 fiber. The zero rejection lemma reduces to a singleton at a vertex outside {0,v}. The final singleton lemma additionally assumes H is independent of v, which handles singleton v by comparison with zero. Every hypothesis needed by those arguments is explicit.

The source does not prove that an arbitrary circuit supplies such an H, that the input has a sole OR reader, or that these conditions hold for a minimal circuit. Deriving these structural hypotheses remains separate work. There is no assumption of whole-function monotonicity in input 0, which could be false with a free unary input.

Only import: PEqualNP.Defs. All declarations are under PEqualNP.Outside.L_meta_1884.SoleOrPartner. No sorry, axiom, native_decide, forbidden namespace substring, string literal, attribute, or set_option occurs. No credential material was observed. The reviewer did not author this helper.
