# Independent review: DirectFilterBridge

UTC: 2026-11-25T16:49:42.978996+00:00

Verdict: PASS. Exact source SHA256 `18358a7407bf8e7ed8df76642bfa601ffa6c98efd4e2fbfefedd75cbc60bb0db`, 18120 bytes/393 lines. Author reported Lean exit0; complete second-run stdout has inherited warnings only and stderr is empty. This reviewer did not rebuild. The source contains the exact previously reviewed SoleReaderFree body and SafeNotRaise body with the duplicate import removed.

The new DirectFilter namespace explicitly evaluates ten primary inputs plus the free NOT(x0) input. operand_independent uses t≠0 to keep that extra rail equal and requires rawt absent from every prefix gate and the entire NOT operand list. operand_fiber_mono requires an AND/OR prefix and fixesx0 between the compared rows, so both original rails compare monotonically. It then selects the first NOT operand, with empty-listfalse handled separately.

not_value proves the stored NOT output at original index11+prefix.length remains the complement of the operand throughout the middle list. factor assumes a canonical later AND[t,NOTwire] reader, rawt absent from prefix/middle/postfix and the NOT operand list, output≠t, and exact computation of an arbitraryf. Independence makes both operand values equal; the Boolean identity turns equality of t OR H into equality of t AND NOT H. The reviewed sole-reader factorization then yields f(x)=f(y).

The assumptions are stronger than an effective-reader statement if a multi-input NOT has discarded later operands containingt: hi excludes all listed operands. This is explicit and sound; the caller must either normalize NOT lists to their first operand or prove the stronger omission property. The theorem does not itself infer any sole-reader topology, forward validity, size bound or two-filter case.

Only PEqualNP.Defs is imported. Correct L_meta_1884 namespaces, no options, attributes, strings, forbidden constructs, new axioms, unsafe declarations or secret-like content; below512KiB. No full posted target is claimed.
