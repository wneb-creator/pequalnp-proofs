# Existing monotone cleanup and sole-reader helper sources

UTC: 2026-11-25T16:43:37.941440+00:00

`PEqualNP.MetaComplexity.Loc.Clean.mclean_of`, Helpers/LocClean.lean66–97, takes a nonconstant function and HasMonoSize n f s and returns HasMClean n f s. HasMonoSize (LocModel.lean26–28) is an arbitrary standard FanInTwo circuit, NotFree gates, size≤s, exact computation. The cleanup runs Elim using invalid-wire false defaults, creates no NOT gates, and does not grow the list.

CleanL (Parity3.lean33–34) gives CleanGate at n+index. CleanGate28–30 is either a unary NOT of an earlier valid wire, or an AND/OR of exactly two earlier valid wires. NotFree excludes the NOT case. Therefore the cleanup output gives IsAO2 and ReadsBack by direct destructuring. Nonconstancy follows from the relaxation's positive and negative rows. ToolLeast_proof99–109 minimizes among clean circuits; if a globally minimal Monotone2 representative is required, select the global minimum first and then clean (size equality follows), or transfer minimum size against any equivalent competitor by cleaning that competitor.

`PEqualNP.MetaComplexity.LiftFix.fold_agree`, Helpers/NormalForm.lean162–186, proves evaluation preserves agreement outside an indexm whenever every gate avoidsm. It works for arbitrary gate operations. Apply it before and after the sole reader to derive partner independence and output factorization. Root's new independently reviewed SoleReaderFactor provides these exact lemmas in a small Defs-only file, avoiding a larger dependency copy.
