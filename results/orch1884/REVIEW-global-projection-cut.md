# Independent GlobalProjectionCut review

Verdict: PASS for the conditional replay and projection-cut lemmas and preservation. These lemmas do not yet provide an actual-circuit decomposition or prove the posted gap.

Reviewed source: `lemmas/GlobalProjectionCut.lean`,171 lines,8283bytes. SHA256 `611940656f2d9362f02572810252eb801aa61faa27e34646a9e898d4d771d372`. Copied complete compilation logs `global-projection-cut.stdout` and `.stderr` are empty; root reports exit0.

`projected_available_of_supply` correctly handles a supplied wire, a constant, and a complemented available wire. In the last case it complements the supplied projection of the inverse and uses double negation. `replay` rebuilds each binary Reach step after restricting rows, starting from the supplied projected roots, and charges exactly the original number of steps.

`replay_skip_constant` omits exactly one specified binary step whose projected operand is constant. The existing `from_constant` lemma supplies the projected result without a new step; the separately assumed suffix is then replayed. Its conclusion charges before+after, not the omitted step. The original prefix and suffix Reach witnesses remain explicit assumptions.

`two_constant_cut` requires both the original pin and a distinct extra signature r to be present in the live suffix frontier, with both projecting to zero. Every other live root must be available from the given prefix. The two constant entries contribute mass at least two after projection. The checked nine-input fifteen-step floor and contraction bound give p+k≥17, hence the stated p+1+k≥18. The extra signature is not asserted to arise from an actual circuit gate; connecting the added one to a circuit is a separate obligation.

`one_constant_after_skipped_step` combines one omitted constant-input binary step with one constant projected suffix root. The projected prefix costs p+q and the suffix has mass at least one, giving p+q+k≥16 and the stated p+1+q+1+k≥18. Again, all prefix, skipped-step, suffix, coverage, and live-root conditions are explicitly assumed.

The finite frontier lists are correctly reconstructed from the live Finset and use the supplied membership and distinctness hypotheses. Projected target and original-input identities come from the checked Binary17 Geometry helpers. No unrestricted eighteen-binary-gate conclusion is stated.

Format scan found no options, attributes, strings, forbidden root qualifier, additional axioms, sorry, native_decide, unsafe code, credentials, or binary content. The scratch import TwoPrefixFloor transitively imports Binary17; final standalone integration must inline the required base and helpers rather than submit that scratch import.
