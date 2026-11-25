# Checked case2 modular coprimality

The exact-source audit compiled with exit0 in12.861s, peak4,330,956KiB under60s/5GiB. All five exported lemmas use only propext, Classical.choice, and Quot.sound. This proves degree bounds54/82 for the two specific integer polynomials, exact maps to ZMod11 preserving those degrees, and explicit modular IsCoprime. It does not by itself prove the full scalar norm implication, the C4 chart, or gap L-gct-231.

The concrete lists and an integer quotient witness are in the JSON. The Lean proof checks their exact modular Bezout identity with ring arithmetic; ordinary decide is used only for closed small finite arithmetic, never native_decide. The generic coefficient-list API is copied unchanged from its separately reviewed checked source. The generic integer-resultant transfer is a separate checked component.

Failed development attempts are segregated in ../c4-case2-modular-experiments/. No named proof file was changed.
