# Independent review: SoleReaderFree

UTC: 2026-11-25T16:44:36.411592+00:00

Verdict: PASS. Source SHA256 `dd96143a83e112da08c5427943cc14d673efced23759c5e70305201bfc4cce64`, 8282 bytes/171 lines. Author reported session77478 exit0; second-run stdout contains only inherited unused-simp warnings and stderr is empty. No new Lean run was performed by this reviewer.

The prefix before free_input_agree is byte-identical to the previously reviewed SoleReaderFactor body, except trailing whitespace before the new lemmas. The extension retains the exact input list of ten primary pins followed by NOT(x0). The explicit t≠0 premise means inputs differing only at rawt agree atx0, so the free negative rail is equal. Appending that equal rail preserves bank agreement outside rawt. Input lookup remains the original primary pin because t<10.

The new partner-independence and OR/AND factorization statements are direct instantiations of the reviewed generic prefix/suffix lemmas on these eleven-element input lists. They explicitly retain no-reader premises for both surrounding gate lists, output≠t, and equality of the selected reader outputs. a=10 is allowed and is correctly independent oft under t≠0. No hypothesis is supplied automatically for t=0 or for arbitrary duplicated/permuted primary inputs.

Only PEqualNP.Defs is imported; correct L_meta_1884.SoleReader namespace. No options, attributes, strings, forbidden constructs, new axioms, native_decide, unsafe declarations, or secret-like content. Below512KiB. This helper establishes semantic factorization only; it does not extract a reader or prove the full posted target.
