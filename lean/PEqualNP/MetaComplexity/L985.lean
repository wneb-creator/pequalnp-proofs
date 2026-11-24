import PEqualNP.MetaComplexity.Helpers.Guard985

/-- The symmetric guard lemma: on an incidence of N points and N lines with no two points on two
common lines, an AND/OR circuit of fan-in at most two, and J pairs of its wires, the first of
line-degree at most 2, each pair true together only where an incident point and line are both
on, and a set W of lines: the incident pairs (p, w) with w outside W and p on no line of W such
that, for some pair, the second wire is true at p and the lines of W and the first wire is true
at p and w, number at most 48 (2 size + 2 J) + 2 N. -/
theorem PEqualNP.MetaComplexity.L985 : ∀ (N Jn : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (Ckt : PEqualNP.CircuitLowerBounds.Circuit) (fa fb : Fin Jn → ℕ) (Wz : Finset (Fin N)), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 Ckt → (∀ jd : Fin Jn, (Ckt.lineDegrees (N + N) (Finset.Ico N (N + N))).getD (fa jd) 0 ≤ 2) → (∀ (jb : Fin Jn) (zz : Fin (N + N) → Bool), (Ckt.wires (List.ofFn zz)).getD (fa jb) false = true → (Ckt.wires (List.ofFn zz)).getD (fb jb) false = true → ∃ (pa lb : Fin N), I pa lb ∧ zz (Fin.castAdd N pa) = true ∧ zz (Fin.natAdd N lb) = true) → (Finset.univ.filter (fun e2 : Fin N × Fin N => I e2.1 e2.2 ∧ e2.2 ∉ Wz ∧ (∀ uu ∈ Wz, ¬ I e2.1 uu) ∧ ∃ jc : Fin Jn, (Ckt.wires (List.ofFn (fun vv : Fin (N + N) => if vv = Fin.castAdd N e2.1 then true else decide (∃ ww ∈ Wz, vv = Fin.natAdd N ww)))).getD (fb jc) false = true ∧ (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fa jc) false = true)).card ≤ 48 * (2 * Ckt.size + 2 * Jn) + 2 * N :=
  PEqualNP.MetaComplexity.G985.guard
