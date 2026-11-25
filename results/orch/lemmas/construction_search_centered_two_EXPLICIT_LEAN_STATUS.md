# Explicit certificate Lean trial did not finish

`CenteredTwoCertificate3.lean.txt` is a failing research source snapshot. It did not compile and proves no Lean theorem. It is1179159bytes and therefore also exceeds the512KiB final proof source cap.

The source introduces the eleven nonzero multiplier polynomials from the independently verified exact chart3 certificate, then attempts `linear_combination` followed by explicit unfolding and `ring`. This uses the known certificate rather than a new Gröbner-basis search. The trial used narrow imports, one thread, Lean's6000MiB allocation limit, a6GiB process-tree RSS cap, and a300-second wall cap. It was killed at the RSS cap after68.67seconds; the complete diagnostic log was empty. The process was reaped and no further trial was launched.

The generator, exact source, runner, complete output, and resource metadata are archived for reproducibility. Separate chunk statistics show that splitting only by original equation is insufficient to reduce expression size substantially: product normal forms contain up to3325monomials and greedy cancellation-aware merging peaks at3351–3371monomials. A future checked implementation should use finer coefficient checks, a verified sparse normalizer, or another compact derivation. None of those alternatives has been implemented here.
