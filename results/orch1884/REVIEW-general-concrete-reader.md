# Independent review: general concrete effective-reader bound

UTC: 2026-11-25T16:14:22.385811+00:00
Verdict: PASS as a checked dependency wrapper. The exact posted impossibility remains unproved.

Source: `results/orch1884/lemmas/GeneralConcreteReaderBound.lean`
SHA256: `078cb21543e9f4f0433b65f3fbd04adacfa4556de41873d6587d684b6c380a43`
Size: 1158 bytes; 30 lines.
Author reports first-run Lean exit0. Complete /tmp/oec/pequalnp-pilot-103/1884-general-concrete-first.stdout and .stderr were independently verified empty.

The cofactor identity is the same exact twelve-edge equality used by the monotone wrapper, with only GeneralReaderBound names substituted. The general contraction theorem's lower-bound premise is now discharged by NineGeneralFloor.nine_circuit_floor for every FanInTwo circuit, including paid NOT gates. The resulting theorem has no unproved cofactor assumption: it gives16 plus the number of effective reader gates of source positions0 and10 at most C.size, and hence at most2 such reader gates when C.size<=18.

The remaining hypotheses are explicit: FanInTwo, identity-ordered ten inputs followed by free negation of input0, and exact computation on every assignment. Arbitrary maps and other unary functions still require normalization. At most two readers is a structural consequence, not a contradiction.

Dependencies are GeneralReaderBound67ed300c2ceb05f5f4ddff3a318b6a0db467ad7b2d8c16ea69820cf645629e4d and NineGeneralFloorf1b11610b17cdde28749ae7841f9079528fe9e5071729ce8598dfa78b2513370. Both were independently reviewed and successfully checked. The scratch-module imports make this a dependency test; the assembled Defs-only source needs its own build. No options, attributes, forbidden constructs, or observed credential material occur. The reviewer did not author this wrapper.
