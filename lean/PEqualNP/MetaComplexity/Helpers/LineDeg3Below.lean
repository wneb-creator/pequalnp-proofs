import PEqualNP.MetaComplexity.Helpers.LineDeg3All

/-!
# The line-degree-3 bound for a circuit only below the incidence function (helper for L-meta-1380)

The checked proof of L-meta-1341 (`Ld3c.ld3c_main`) with the iff weakened to its forward half;
the backward use (D is true at the pair's two-hot input) is the new acceptance clause of the count.
-/

namespace PEqualNP.MetaComplexity.Ld3b

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Ld3c

theorem ld3b_main : (∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (T Z : Finset (Fin n)), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (r : ℕ → ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ gates'.length ≤ gates.length ∧ ∀ o : ℕ, (∃ x y : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else y i))) → ∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', r o⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i))) → (∀ (P1 L1 : ℕ) (C1 : PEqualNP.CircuitLowerBounds.Circuit) (N1 : Finset (Fin L1)), PEqualNP.CircuitLowerBounds.IsMonotoneCircuit C1 → (∀ g1 ∈ C1.gates, g1.inputs.length ≤ 2) → PEqualNP.CircuitLowerBounds.HasLineDegree (P1 + L1) (Finset.Ico P1 (P1 + L1)) C1 1 → (∀ j1 : Fin C1.gates.length, Relation.ReflTransGen (fun a1 b1 : ℕ => a1 < b1 ∧ ∃ i1 : Fin C1.gates.length, b1 = P1 + L1 + i1.val ∧ a1 ∈ (C1.gates.get i1).inputs) (P1 + L1 + j1.val) C1.output) → (∀ w1 : Fin L1, w1 ∈ N1 ↔ Relation.ReflTransGen (fun r1 s1 : ℕ => r1 < s1 ∧ ∃ k1 : Fin C1.gates.length, s1 = P1 + L1 + k1.val ∧ r1 ∈ (C1.gates.get k1).inputs) (P1 + w1.val) C1.output) → ∃ (D1 : PEqualNP.CircuitLowerBounds.Circuit) (T1 : Finset (Fin L1)) (o1 : Fin L1 → ℕ), PEqualNP.CircuitLowerBounds.IsMonotoneCircuit D1 ∧ (∀ h1 ∈ D1.gates, h1.inputs.length ≤ 2) ∧ D1.size + N1.card ≤ C1.size + 1 ∧ ∀ (x1 : Fin P1 → Bool) (y1 : Fin L1 → Bool), C1.eval (List.ofFn x1 ++ List.ofFn y1) = (C1.eval (List.ofFn x1 ++ List.ofFn (fun v1 : Fin L1 => false)) || decide (∃ u1 : Fin L1, y1 u1 = true ∧ (u1 ∈ T1 ∨ (D1.wires (List.ofFn x1)).getD (o1 u1) false = true)))) → (∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true → p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → ∑ i : Fin m, c i ≤ C.size) → (∀ (N Jn : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (Ckt : PEqualNP.CircuitLowerBounds.Circuit) (fa fb : Fin Jn → ℕ) (fr : ℕ), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 Ckt → (∀ jd : Fin Jn, (Ckt.lineDegrees (N + N) (Finset.Ico N (N + N))).getD (fa jd) 0 ≤ 2 ∧ (Ckt.lineDegrees (N + N) (Finset.Ico N (N + N))).getD (fb jd) 0 ≤ 1) → (∀ (jb : Fin Jn) (zz : Fin (N + N) → Bool), (Ckt.wires (List.ofFn zz)).getD (fa jb) false = true → (Ckt.wires (List.ofFn zz)).getD (fb jb) false = true → ∃ (pa lb : Fin N), I pa lb ∧ zz (Fin.castAdd N pa) = true ∧ zz (Fin.natAdd N lb) = true) → (Finset.univ.filter (fun e2 : Fin N × Fin N => I e2.1 e2.2 ∧ (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD fr false = false ∧ (∃ jc : Fin Jn, (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fa jc) false = true ∧ (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fb jc) false = true) ∧ ∀ jk : Fin Jn, (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fa jk) false = true → (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fb jk) false = true → (Ckt.wires (List.ofFn (fun vp : Fin (N + N) => decide (vp = Fin.castAdd N e2.1)))).getD (fa jk) false = false ∧ (Ckt.wires (List.ofFn (fun vp : Fin (N + N) => decide (vp = Fin.castAdd N e2.1)))).getD (fb jk) false = false)).card ≤ 100 * (Ckt.size + Jn) + 4 * N) → (∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (Ckt : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 Ckt → PEqualNP.CircuitLowerBounds.HasLineDegree (N + N) (Finset.Ico N (N + N)) Ckt 3 → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) Ckt z = true → ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → (Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2 ∧ PEqualNP.MetaComplexity.circuitFun (N + N) Ckt (fun k => decide (k = Fin.castAdd N e.1 ∨ k = Fin.natAdd N e.2)) = true)).card ≤ 888 * Ckt.size + 9 * N + 444) := by
  intro h669 h738 h782 hE3 N I _ Ckt h4 hM hdeg hF
  obtain ⟨D, J, a, b, u, r, hDM, hDsz, hJ, hDdeg, hlast, hout, hab, hr, hz⟩ :=
    PEqualNP.MetaComplexity.L1017 N N Ckt hM hdeg
  have hlastD : ∀ z : Fin (N + N) → Bool,
      (D.eval (List.ofFn z) = true →
        (D.wires (List.ofFn z)).getD u false = true ∨ (D.wires (List.ofFn z)).getD r false = true) ∧
      (∀ t, (t = u ∨ t = r) → (D.wires (List.ofFn z)).getD t false = true →
        D.eval (List.ofFn z) = true) :=
    fun z => ld3c_last D u r (List.ofFn z) hlast (by simpa [List.length_ofFn] using hout)
  have hbelow : ∀ z : Fin (N + N) → Bool, D.eval (List.ofFn z) = true →
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true := by
    intro z h
    refine hF z ?_
    rw [← (hz z).1]
    exact h
  have hwir : ∀ (z : Fin (N + N) → Bool) (t : ℕ), (t = u ∨ t = r) →
      (D.wires (List.ofFn z)).getD t false = true →
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true :=
    fun z t ht h => hbelow z ((hlastD z).2 t ht h)
  have hprod : ∀ (jb : Fin J) (z : Fin (N + N) → Bool),
      (D.wires (List.ofFn z)).getD (a jb) false = true →
      (D.wires (List.ofFn z)).getD (b jb) false = true →
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true :=
    fun jb z h1 h2 => hwir z u (Or.inl rfl) (((hz z).2).mpr ⟨jb, h1, h2⟩)
  have hne : ∀ p l : Fin N, Fin.castAdd N p ≠ Fin.natAdd N l := by
    intro p l h
    have h1 := congrArg Fin.val h
    have h2 := p.isLt
    simp at h1
    omega
  have hDc : PEqualNP.CircuitLowerBounds.HasLineDegree (N + N) (Finset.Ico N (N + N))
      (⟨D.gates, r⟩ : PEqualNP.CircuitLowerBounds.Circuit) 2 := hr
  have b963 := PEqualNP.MetaComplexity.L963 N I (⟨D.gates, r⟩ : PEqualNP.CircuitLowerBounds.Circuit)
    h4 hDM hDc (fun z h => hwir z r (Or.inr rfl) h)
  have b965 := PEqualNP.MetaComplexity.L965 N N J I D a b ∅ h669 h738 h782 h4 hDM
    (fun jd => (hab jd).2) hprod
  have b985 := PEqualNP.MetaComplexity.L985 N J I D a b ∅ h4 hDM
    (fun jd => (hab jd).1) hprod
  have b1020 := hE3 N J I D a b r h4 hDM (fun jd => hab jd) hprod
  have hN : (Finset.univ.filter (fun lc : Fin N => lc ∉ (∅ : Finset (Fin N)))).card = N := by simp
  refine le_trans (ld3c_cover4 _ _ _ _ _ ?_) (le_trans (add_le_add (add_le_add (add_le_add b963 b965) b985) b1020) ?_)
  · intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
    obtain ⟨he, hacc0⟩ := he
    obtain ⟨X, hXdef⟩ : ∃ X : Fin (N + N) → Bool, X = fun vq : Fin (N + N) =>
        if vq = Fin.castAdd N e.1 then true else if vq = Fin.natAdd N e.2 then true else false :=
      ⟨_, rfl⟩
    obtain ⟨P, hPdef⟩ : ∃ P : Fin (N + N) → Bool, P = fun vp : Fin (N + N) =>
        decide (vp = Fin.castAdd N e.1) := ⟨_, rfl⟩
    have hXeq : (fun k : Fin (N + N) => decide (k = Fin.castAdd N e.1 ∨ k = Fin.natAdd N e.2)) = X := by
      rw [hXdef]; funext k
      by_cases h1 : k = Fin.castAdd N e.1
      · simp [h1]
      · by_cases h2 : k = Fin.natAdd N e.2 <;> simp [h1, h2]
    have hPw : (fun vv : Fin (N + N) => if vv = Fin.castAdd N e.1 then true
        else decide (∃ ww ∈ (∅ : Finset (Fin N)), vv = Fin.natAdd N ww)) = P := by
      rw [hPdef]; funext vv; by_cases h1 : vv = Fin.castAdd N e.1 <;> simp [h1]
    have hX1 : X (Fin.castAdd N e.1) = true := by rw [hXdef]; simp
    have hX2 : X (Fin.natAdd N e.2) = true := by
      rw [hXdef]; simp [(hne e.1 e.2).symm]
    rw [hXeq, hPw]
    rw [← hXdef, ← hPdef]
    have hDX : D.eval (List.ofFn X) = true :=
      (hz X).1.trans (by rw [← hXeq]; exact hacc0)
    by_cases hrX : (D.wires (List.ofFn X)).getD r false = true
    · left
      exact ⟨he, hrX⟩
    · have hu : (D.wires (List.ofFn X)).getD u false = true := by
        rcases (hlastD X).1 hDX with h | h
        · exact h
        · exact absurd h hrX
      obtain ⟨i, hia, hib⟩ := ((hz X).2).mp hu
      by_cases h1 : ∃ j : Fin J, (D.wires (List.ofFn X)).getD (a j) false = true ∧
          (D.wires (List.ofFn X)).getD (b j) false = true ∧
          (D.wires (List.ofFn P)).getD (a j) false = true
      · obtain ⟨j, ja, jb, jp⟩ := h1
        right; left
        exact ⟨he, by simp, by simp, j, jp, jb⟩
      · by_cases h2 : ∃ j : Fin J, (D.wires (List.ofFn X)).getD (a j) false = true ∧
            (D.wires (List.ofFn X)).getD (b j) false = true ∧
            (D.wires (List.ofFn P)).getD (b j) false = true
        · obtain ⟨j, ja, jb, jp⟩ := h2
          right; right; left
          exact ⟨he, by simp, by simp, j, jp, ja⟩
        · right; right; right
          refine ⟨he, by simpa using hrX, ⟨i, hia, hib⟩, fun jk ha hb => ⟨?_, ?_⟩⟩
          · simpa using fun h => h1 ⟨jk, ha, hb, h⟩
          · simpa using fun h => h2 ⟨jk, ha, hb, h⟩
  · rw [hN]
    have h1 : D.size ≤ 2 * Ckt.size + 1 := hDsz
    have h2 : (⟨D.gates, r⟩ : PEqualNP.CircuitLowerBounds.Circuit).size = D.size := rfl
    rw [h2]
    have h3 : J ≤ D.size := hJ
    omega

end PEqualNP.MetaComplexity.Ld3b
