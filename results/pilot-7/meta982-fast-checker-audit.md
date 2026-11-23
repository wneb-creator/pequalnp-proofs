# Independent review of Fast982Append.lean.txt

Verdict: source audit PASS, conditional on root completing the combined Lean compile.

Every fast helper is related by an unconditional equality theorem to the previously checked implementation. Arithmetic right shift uses Nat.shiftRight_eq_div_pow; bit testing uses Nat.testBit_eq_decide_div_mod_eq; masking the low k bits uses Nat.and_two_pow_sub_one_eq_mod. These identities also cover zero width and zero index. There are no assumptions about word boundedness, nonzero k, or particular graph functions.

The cov/covUp list folds preserve their operations and initial value. covers switches predicates at the same exact live-source equality. fld retains the same field offset/width. scoreCheck preserves the zero-code guard, zero-slack guard, six-coordinate score, target score, and strict comparison. scr preserves the pool existential. rejectDepth preserves both recursion parameters and all base/step guards; the equality proof inducts on depth while generalizing remaining budget and state. pairedBar preserves child index bound, orientation call, and full isPerm check. Fresh move enumeration is delegated unchanged to Reduced.next.

No additional import, axiom, sorry, native_decide, or runtime evaluation escape is introduced. Caller-provided ori is unchanged, so any recursive bit operations there remain a possible runtime cost. This is a performance caveat, not a soundness issue.

Snapshot SHA256: 3cafeef72928fe946cd6eca3fc08c846b1909575ccb82af78309dec23aadad93
