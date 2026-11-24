import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_105

namespace Pcx106K4Lower

open PEqualNP.ProofComplexity MvPolynomial

private noncomputable def factor {V : Type} (l : V × Bool) : MvPolynomial V (ZMod 2) :=
  if l.2 = true then 1 + X l.1 else X l.1

private lemma factor_degree {V : Type} (l : V × Bool) : (factor l).totalDegree = 1 := by
  unfold factor
  split_ifs
  · rw [totalDegree_add_eq_right_of_totalDegree_lt (by simp), totalDegree_X]
  · simp

private lemma factor_ne_zero {V : Type} (l : V × Bool) : factor l ≠ 0 := by
  intro h
  have hh := factor_degree l
  simp [h] at hh

lemma degree_clause {V : Type} (c : Clause V) : (clausePoly c).totalDegree = c.card := by
  classical
  change (∏ l ∈ c, factor l).totalDegree = _
  induction c using Finset.induction_on with
  | empty => simp
  | insert l c h ih =>
    rw [Finset.prod_insert h, totalDegree_mul_of_isDomain (factor_ne_zero l)
      (Finset.prod_ne_zero_iff.mpr (fun l _ => factor_ne_zero l)), factor_degree, ih,
      Finset.card_insert_of_notMem h]
    omega

lemma no_refutation {V : Type} (F : Set (MvPolynomial V (ZMod 2))) (d : ℕ)
    (t : V → ZMod 2) (h : ∀ p ∈ F, p.totalDegree ≤ d → eval t p = 0) : ¬ PCRefutable F d := by
  have aux {p : MvPolynomial V (ZMod 2)} (hp : PCDerivable F d p) : eval t p = 0 := by
    induction hp with
    | ax hx hd => exact h _ hx hd
    | zero => simp
    | add _ _ ih ij => simp [ih, ij]
    | mulX _ _ _ ih => simp [ih]
  intro hp
  have hh := aux hp
  simp at hh

abbrev Var := Fin 8 ⊕ (ℕ × ℕ)
def assign : Var → ZMod 2
  | .inl _ => 1
  | .inr (_,j) => if j = 0 then 1 else 0

private lemma satisfied (c : Clause Var) (l : Var × Bool) (hl : l ∈ c)
    (hv : eval assign (factor l) = 0) : eval assign (clausePoly c) = 0 := by
  change eval assign (∏ q ∈ c, factor q) = 0
  rw [map_prod]
  exact Finset.prod_eq_zero hl hv

def formula : Set (Clause Var) :=
  {Cei | ∃ eei ∈ ([(0, 1), (0, 3), (0, 5), (0, 7), (2, 1), (2, 3), (2, 5), (2, 7), (4, 1), (4, 3), (4, 5), (4, 7), (6, 1), (6, 3), (6, 5), (6, 7)] : List (Fin 8 × Fin 8)), Cei = {(((Sum.inl eei.1) : Fin 8 ⊕ (ℕ × ℕ)), true), (((Sum.inl eei.2) : Fin 8 ⊕ (ℕ × ℕ)), true)}} ∪ {Cai | ∃ iai : Fin 8, iai.val + 1 < 8 ∧ Cai = {(((Sum.inl iai) : Fin 8 ⊕ (ℕ × ℕ)), false), (((Sum.inr (iai.val, 0)) : Fin 8 ⊕ (ℕ × ℕ)), true)}} ∪ {Cbi | ∃ (ibi : Fin 8) (hbi jbi : ℕ), ibi.val = hbi + 1 ∧ ibi.val + 1 < 8 ∧ jbi < 3 ∧ Cbi = {(((Sum.inr (hbi, jbi)) : Fin 8 ⊕ (ℕ × ℕ)), false), (((Sum.inr (ibi.val, jbi)) : Fin 8 ⊕ (ℕ × ℕ)), true)}} ∪ {Cci | ∃ (ici : Fin 8) (hci gci : ℕ), ici.val = hci + 1 ∧ ici.val + 1 < 8 ∧ gci + 1 < 3 ∧ Cci = {(((Sum.inl ici) : Fin 8 ⊕ (ℕ × ℕ)), false), (((Sum.inr (hci, gci)) : Fin 8 ⊕ (ℕ × ℕ)), false), (((Sum.inr (ici.val, gci + 1)) : Fin 8 ⊕ (ℕ × ℕ)), true)}} ∪ {Cdi | ∃ (idi : Fin 8) (hdi : ℕ), idi.val = hdi + 1 ∧ Cdi = {(((Sum.inl idi) : Fin 8 ⊕ (ℕ × ℕ)), false), (((Sum.inr (hdi, 2)) : Fin 8 ⊕ (ℕ × ℕ)), false)}} ∪ {Cfi | ∃ jfi : ℕ, 1 ≤ jfi ∧ jfi < 3 ∧ Cfi = {(((Sum.inr (0, jfi)) : Fin 8 ⊕ (ℕ × ℕ)), false)}}

theorem lower : ¬ PCRefutable (cnfSystem formula) 2 := by
  apply no_refutation _ _ assign
  intro p hp hd
  rcases hp with ⟨v,rfl⟩ | ⟨c,hc,rfl⟩
  · rcases v with i | ⟨i,j⟩
    · norm_num [assign]
      decide
    · by_cases h : j = 0
      · norm_num [assign,h]
        decide
      · norm_num [assign,h]
  rw [degree_clause] at hd
  rcases hc with (((((he | ha) | hb) | hc) | ho) | hf)
  · obtain ⟨e,_,rfl⟩ := he
    apply satisfied _ ((Sum.inl e.1),true) (by simp)
    norm_num [factor,assign]
    decide
  · obtain ⟨i,_,rfl⟩ := ha
    apply satisfied _ ((Sum.inr (i.val,0)),true) (by simp)
    norm_num [factor,assign]
    decide
  · obtain ⟨i,k,j,_,_,_,rfl⟩ := hb
    by_cases h : j = 0
    · apply satisfied _ ((Sum.inr (i.val,j)),true) (by simp)
      norm_num [factor,assign,h]
      decide
    · apply satisfied _ ((Sum.inr (k,j)),false) (by simp)
      norm_num [factor,assign,h]
  · obtain ⟨i,k,j,_,_,_,rfl⟩ := hc
    simp at hd
  · obtain ⟨i,k,_,rfl⟩ := ho
    apply satisfied _ ((Sum.inr (k,2)),false) (by simp)
    norm_num [factor,assign]
  · obtain ⟨j,hj,_,rfl⟩ := hf
    apply satisfied _ ((Sum.inr (0,j)),false) (by simp)
    have hj' : j ≠ 0 := by omega
    norm_num [factor,assign,hj']
end Pcx106K4Lower

namespace Pcx106PC

open PEqualNP.ProofComplexity MvPolynomial

private noncomputable def factor {V : Type} (l : Literal V) : MvPolynomial V (ZMod 2) :=
  if l.2 = true then 1 + X l.1 else X l.1

private noncomputable def word {V : Type} (ls : List (Literal V)) : MvPolynomial V (ZMod 2) :=
  (ls.map factor).prod

private theorem word_cons {V : Type} (l : Literal V) (ls : List (Literal V)) :
    word (l :: ls) = factor l * word ls := by simp [word]

private theorem degree_factor {V : Type} (l : Literal V) : (factor l).totalDegree ≤ 1 := by
  unfold factor
  split
  · exact (totalDegree_add _ _).trans (by simp)
  · simp

private theorem degree_word {V : Type} (ls : List (Literal V)) :
    (word ls).totalDegree ≤ ls.length := by
  induction ls with
  | nil => simp [word]
  | cons l ls ih =>
    rw [word_cons, List.length_cons]
    exact (totalDegree_mul _ _).trans (by have := degree_factor l; omega)

private theorem word_clause {V : Type} [DecidableEq V] {ls : List (Literal V)} (hn : ls.Nodup) :
    word ls = clausePoly ls.toFinset := by
  induction ls with
  | nil => simp [word, clausePoly]
  | cons l ls ih =>
    obtain ⟨ha,ht⟩ := List.nodup_cons.mp hn
    rw [word_cons, ih ht]
    simp [factor, clausePoly, List.toFinset_cons, ha]

private theorem baseWord {V : Type} [DecidableEq V] {F : Set (Clause V)} {B : ℕ}
    {ls : List (Literal V)} (hm : ls.toFinset ∈ F) (hn : ls.Nodup) (hB : ls.length ≤ B) :
    PCDerivable (cnfSystem F) B (word ls) := by
  apply PCDerivable.ax
  · exact Or.inr ⟨ls.toFinset, hm, word_clause hn⟩
  · exact (degree_word ls).trans hB

private theorem addLiteral {V : Type} {F : Set (MvPolynomial V (ZMod 2))} {B : ℕ}
    (l : Literal V) {ls : List (Literal V)} (hB : ls.length + 1 ≤ B)
    (h : PCDerivable F B (word ls)) : PCDerivable F B (word (l :: ls)) := by
  rw [word_cons]
  have hx := PCDerivable.mulX l.1 h ((totalDegree_mul _ _).trans
    (show (X l.1 : MvPolynomial V (ZMod 2)).totalDegree + (word ls).totalDegree ≤ B by
      simpa using (show 1 + (word ls).totalDegree ≤ B by have := degree_word ls; omega)))
  unfold factor
  split
  · simpa [add_mul] using h.add hx
  · exact hx

private theorem resolveWord {V : Type} {F : Set (MvPolynomial V (ZMod 2))} {B : ℕ}
    (v : V) (ls : List (Literal V))
    (hp : PCDerivable F B (word ((v,true) :: ls)))
    (hn : PCDerivable F B (word ((v,false) :: ls))) : PCDerivable F B (word ls) := by
  simpa [word_cons, factor, add_mul, add_assoc, CharTwo.add_self_eq_zero] using hp.add hn


namespace K4
private abbrev V := Fin 8 ⊕ (ℕ × ℕ)
private def x (i : Fin 8) : V := Sum.inl i
private def y (i j : ℕ) : V := Sum.inr (i,j)
def formula : Set (Clause V) := {Cei | ∃ eei ∈ ([(0, 1), (0, 3), (0, 5), (0, 7), (2, 1), (2, 3), (2, 5), (2, 7), (4, 1), (4, 3), (4, 5), (4, 7), (6, 1), (6, 3), (6, 5), (6, 7)] : List (Fin 8 × Fin 8)), Cei = {(((Sum.inl eei.1) : Fin 8 ⊕ (ℕ × ℕ)), true), (((Sum.inl eei.2) : Fin 8 ⊕ (ℕ × ℕ)), true)}} ∪ {Cai | ∃ iai : Fin 8, iai.val + 1 < 8 ∧ Cai = {(((Sum.inl iai) : Fin 8 ⊕ (ℕ × ℕ)), false), (((Sum.inr (iai.val, 0)) : Fin 8 ⊕ (ℕ × ℕ)), true)}} ∪ {Cbi | ∃ (ibi : Fin 8) (hbi jbi : ℕ), ibi.val = hbi + 1 ∧ ibi.val + 1 < 8 ∧ jbi < 3 ∧ Cbi = {(((Sum.inr (hbi, jbi)) : Fin 8 ⊕ (ℕ × ℕ)), false), (((Sum.inr (ibi.val, jbi)) : Fin 8 ⊕ (ℕ × ℕ)), true)}} ∪ {Cci | ∃ (ici : Fin 8) (hci gci : ℕ), ici.val = hci + 1 ∧ ici.val + 1 < 8 ∧ gci + 1 < 3 ∧ Cci = {(((Sum.inl ici) : Fin 8 ⊕ (ℕ × ℕ)), false), (((Sum.inr (hci, gci)) : Fin 8 ⊕ (ℕ × ℕ)), false), (((Sum.inr (ici.val, gci + 1)) : Fin 8 ⊕ (ℕ × ℕ)), true)}} ∪ {Cdi | ∃ (idi : Fin 8) (hdi : ℕ), idi.val = hdi + 1 ∧ Cdi = {(((Sum.inl idi) : Fin 8 ⊕ (ℕ × ℕ)), false), (((Sum.inr (hdi, 2)) : Fin 8 ⊕ (ℕ × ℕ)), false)}} ∪ {Cfi | ∃ jfi : ℕ, 1 ≤ jfi ∧ jfi < 3 ∧ Cfi = {(((Sum.inr (0, jfi)) : Fin 8 ⊕ (ℕ × ℕ)), false)}}

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem upper : PCRefutable (cnfSystem formula) 3 := by
  have h0 : PCDerivable (cnfSystem formula) 3 (word [(x 0, true), (x 1, true)]) := by
    apply baseWord _ (by decide) (by decide)
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (⟨(0,1), by decide, by decide⟩)))))
  have h1 : PCDerivable (cnfSystem formula) 3 (word [(x 0, false), (y 0 0, true)]) := by
    apply baseWord _ (by decide) (by decide)
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨0, by decide, by decide⟩)))))
  have h2 : PCDerivable (cnfSystem formula) 3 (word [(x 1, false), (y 1 0, true)]) := by
    apply baseWord _ (by decide) (by decide)
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, by decide, by decide⟩)))))
  have h3 : PCDerivable (cnfSystem formula) 3 (word [(y 0 0, false), (y 1 0, true)]) := by
    apply baseWord _ (by decide) (by decide)
    exact Or.inl (Or.inl (Or.inl (Or.inr (⟨1, 0, 0, by decide, by decide, by decide, by decide⟩))))
  have h4 : PCDerivable (cnfSystem formula) 3 (word [(x 0, false), (y 1 0, true)]) := by
    apply resolveWord (y 0 0)
    · simpa only [word_cons, mul_comm, mul_left_comm, mul_assoc] using (addLiteral (y 1 0, true) (by decide) h1)
    · simpa only [word_cons, mul_comm, mul_left_comm, mul_assoc] using (addLiteral (x 0, false) (by decide) h3)
  have h5 : PCDerivable (cnfSystem formula) 3 (word [(x 1, true), (y 1 0, true)]) := by
    apply resolveWord (x 0)
    · simpa only [word_cons, mul_comm, mul_left_comm, mul_assoc] using (addLiteral (y 1 0, true) (by decide) h0)
    · simpa only [word_cons, mul_comm, mul_left_comm, mul_assoc] using (addLiteral (x 1, true) (by decide) h4)
  have h6 : PCDerivable (cnfSystem formula) 3 (word [(y 1 0, true)]) := by
    apply resolveWord (x 1)
    · simpa only [word_cons, mul_comm, mul_left_comm, mul_assoc] using h5
    · simpa only [word_cons, mul_comm, mul_left_comm, mul_assoc] using h2
  have h7 : PCDerivable (cnfSystem formula) 3 (word [(x 2, true), (x 3, true)]) := by
    apply baseWord _ (by decide) (by decide)
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (⟨(2,3), by decide, by decide⟩)))))
  have h8 : PCDerivable (cnfSystem formula) 3 (word [(y 1 0, false), (y 2 0, true)]) := by
    apply baseWord _ (by decide) (by decide)
    exact Or.inl (Or.inl (Or.inl (Or.inr (⟨2, 1, 0, by decide, by decide, by decide, by decide⟩))))
  have h9 : PCDerivable (cnfSystem formula) 3 (word [(y 2 0, true)]) := by
    apply resolveWord (y 1 0)
    · simpa only [word_cons, mul_comm, mul_left_comm, mul_assoc] using (addLiteral (y 2 0, true) (by decide) h6)
    · simpa only [word_cons, mul_comm, mul_left_comm, mul_assoc] using h8
  have h10 : PCDerivable (cnfSystem formula) 3 (word [(x 2, false), (y 1 0, false), (y 2 1, true)]) := by
    apply baseWord _ (by decide) (by decide)
    exact Or.inl (Or.inl (Or.inr (⟨2, 1, 0, by decide, by decide, by decide, by decide⟩)))
  have h11 : PCDerivable (cnfSystem formula) 3 (word [(x 2, false), (y 2 1, true)]) := by
    apply resolveWord (y 1 0)
    · simpa only [word_cons, mul_comm, mul_left_comm, mul_assoc] using (addLiteral (y 2 1, true) (by decide) (addLiteral (x 2, false) (by decide) h6))
    · simpa only [word_cons, mul_comm, mul_left_comm, mul_assoc] using h10
  have h12 : PCDerivable (cnfSystem formula) 3 (word [(x 3, false), (y 2 0, false), (y 3 1, true)]) := by
    apply baseWord _ (by decide) (by decide)
    exact Or.inl (Or.inl (Or.inr (⟨3, 2, 0, by decide, by decide, by decide, by decide⟩)))
  have h13 : PCDerivable (cnfSystem formula) 3 (word [(x 3, false), (y 3 1, true)]) := by
    apply resolveWord (y 2 0)
    · simpa only [word_cons, mul_comm, mul_left_comm, mul_assoc] using (addLiteral (y 3 1, true) (by decide) (addLiteral (x 3, false) (by decide) h9))
    · simpa only [word_cons, mul_comm, mul_left_comm, mul_assoc] using h12
  have h14 : PCDerivable (cnfSystem formula) 3 (word [(y 2 1, false), (y 3 1, true)]) := by
    apply baseWord _ (by decide) (by decide)
    exact Or.inl (Or.inl (Or.inl (Or.inr (⟨3, 2, 1, by decide, by decide, by decide, by decide⟩))))
  have h15 : PCDerivable (cnfSystem formula) 3 (word [(x 2, false), (y 3 1, true)]) := by
    apply resolveWord (y 2 1)
    · simpa only [word_cons, mul_comm, mul_left_comm, mul_assoc] using (addLiteral (y 3 1, true) (by decide) h11)
    · simpa only [word_cons, mul_comm, mul_left_comm, mul_assoc] using (addLiteral (x 2, false) (by decide) h14)
  have h16 : PCDerivable (cnfSystem formula) 3 (word [(x 3, true), (y 3 1, true)]) := by
    apply resolveWord (x 2)
    · simpa only [word_cons, mul_comm, mul_left_comm, mul_assoc] using (addLiteral (y 3 1, true) (by decide) h7)
    · simpa only [word_cons, mul_comm, mul_left_comm, mul_assoc] using (addLiteral (x 3, true) (by decide) h15)
  have h17 : PCDerivable (cnfSystem formula) 3 (word [(y 3 1, true)]) := by
    apply resolveWord (x 3)
    · simpa only [word_cons, mul_comm, mul_left_comm, mul_assoc] using h16
    · simpa only [word_cons, mul_comm, mul_left_comm, mul_assoc] using h13
  have h18 : PCDerivable (cnfSystem formula) 3 (word [(x 4, true), (x 5, true)]) := by
    apply baseWord _ (by decide) (by decide)
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (⟨(4,5), by decide, by decide⟩)))))
  have h19 : PCDerivable (cnfSystem formula) 3 (word [(y 3 1, false), (y 4 1, true)]) := by
    apply baseWord _ (by decide) (by decide)
    exact Or.inl (Or.inl (Or.inl (Or.inr (⟨4, 3, 1, by decide, by decide, by decide, by decide⟩))))
  have h20 : PCDerivable (cnfSystem formula) 3 (word [(y 4 1, true)]) := by
    apply resolveWord (y 3 1)
    · simpa only [word_cons, mul_comm, mul_left_comm, mul_assoc] using (addLiteral (y 4 1, true) (by decide) h17)
    · simpa only [word_cons, mul_comm, mul_left_comm, mul_assoc] using h19
  have h21 : PCDerivable (cnfSystem formula) 3 (word [(x 4, false), (y 3 1, false), (y 4 2, true)]) := by
    apply baseWord _ (by decide) (by decide)
    exact Or.inl (Or.inl (Or.inr (⟨4, 3, 1, by decide, by decide, by decide, by decide⟩)))
  have h22 : PCDerivable (cnfSystem formula) 3 (word [(x 4, false), (y 4 2, true)]) := by
    apply resolveWord (y 3 1)
    · simpa only [word_cons, mul_comm, mul_left_comm, mul_assoc] using (addLiteral (y 4 2, true) (by decide) (addLiteral (x 4, false) (by decide) h17))
    · simpa only [word_cons, mul_comm, mul_left_comm, mul_assoc] using h21
  have h23 : PCDerivable (cnfSystem formula) 3 (word [(x 5, false), (y 4 1, false), (y 5 2, true)]) := by
    apply baseWord _ (by decide) (by decide)
    exact Or.inl (Or.inl (Or.inr (⟨5, 4, 1, by decide, by decide, by decide, by decide⟩)))
  have h24 : PCDerivable (cnfSystem formula) 3 (word [(x 5, false), (y 5 2, true)]) := by
    apply resolveWord (y 4 1)
    · simpa only [word_cons, mul_comm, mul_left_comm, mul_assoc] using (addLiteral (y 5 2, true) (by decide) (addLiteral (x 5, false) (by decide) h20))
    · simpa only [word_cons, mul_comm, mul_left_comm, mul_assoc] using h23
  have h25 : PCDerivable (cnfSystem formula) 3 (word [(y 4 2, false), (y 5 2, true)]) := by
    apply baseWord _ (by decide) (by decide)
    exact Or.inl (Or.inl (Or.inl (Or.inr (⟨5, 4, 2, by decide, by decide, by decide, by decide⟩))))
  have h26 : PCDerivable (cnfSystem formula) 3 (word [(x 4, false), (y 5 2, true)]) := by
    apply resolveWord (y 4 2)
    · simpa only [word_cons, mul_comm, mul_left_comm, mul_assoc] using (addLiteral (y 5 2, true) (by decide) h22)
    · simpa only [word_cons, mul_comm, mul_left_comm, mul_assoc] using (addLiteral (x 4, false) (by decide) h25)
  have h27 : PCDerivable (cnfSystem formula) 3 (word [(x 5, true), (y 5 2, true)]) := by
    apply resolveWord (x 4)
    · simpa only [word_cons, mul_comm, mul_left_comm, mul_assoc] using (addLiteral (y 5 2, true) (by decide) h18)
    · simpa only [word_cons, mul_comm, mul_left_comm, mul_assoc] using (addLiteral (x 5, true) (by decide) h26)
  have h28 : PCDerivable (cnfSystem formula) 3 (word [(y 5 2, true)]) := by
    apply resolveWord (x 5)
    · simpa only [word_cons, mul_comm, mul_left_comm, mul_assoc] using h27
    · simpa only [word_cons, mul_comm, mul_left_comm, mul_assoc] using h24
  have h29 : PCDerivable (cnfSystem formula) 3 (word [(x 6, true), (x 7, true)]) := by
    apply baseWord _ (by decide) (by decide)
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (⟨(6,7), by decide, by decide⟩)))))
  have h30 : PCDerivable (cnfSystem formula) 3 (word [(y 5 2, false), (y 6 2, true)]) := by
    apply baseWord _ (by decide) (by decide)
    exact Or.inl (Or.inl (Or.inl (Or.inr (⟨6, 5, 2, by decide, by decide, by decide, by decide⟩))))
  have h31 : PCDerivable (cnfSystem formula) 3 (word [(y 6 2, true)]) := by
    apply resolveWord (y 5 2)
    · simpa only [word_cons, mul_comm, mul_left_comm, mul_assoc] using (addLiteral (y 6 2, true) (by decide) h28)
    · simpa only [word_cons, mul_comm, mul_left_comm, mul_assoc] using h30
  have h32 : PCDerivable (cnfSystem formula) 3 (word [(x 6, false), (y 5 2, false)]) := by
    apply baseWord _ (by decide) (by decide)
    exact Or.inl (Or.inr (⟨6, 5, by decide, by decide⟩))
  have h33 : PCDerivable (cnfSystem formula) 3 (word [(x 6, false)]) := by
    apply resolveWord (y 5 2)
    · simpa only [word_cons, mul_comm, mul_left_comm, mul_assoc] using (addLiteral (x 6, false) (by decide) h28)
    · simpa only [word_cons, mul_comm, mul_left_comm, mul_assoc] using h32
  have h34 : PCDerivable (cnfSystem formula) 3 (word [(x 7, false), (y 6 2, false)]) := by
    apply baseWord _ (by decide) (by decide)
    exact Or.inl (Or.inr (⟨7, 6, by decide, by decide⟩))
  have h35 : PCDerivable (cnfSystem formula) 3 (word [(x 7, false)]) := by
    apply resolveWord (y 6 2)
    · simpa only [word_cons, mul_comm, mul_left_comm, mul_assoc] using (addLiteral (x 7, false) (by decide) h31)
    · simpa only [word_cons, mul_comm, mul_left_comm, mul_assoc] using h34
  have h36 : PCDerivable (cnfSystem formula) 3 (word [(x 7, true)]) := by
    apply resolveWord (x 6)
    · simpa only [word_cons, mul_comm, mul_left_comm, mul_assoc] using h29
    · simpa only [word_cons, mul_comm, mul_left_comm, mul_assoc] using (addLiteral (x 7, true) (by decide) h33)
  have h37 : PCDerivable (cnfSystem formula) 3 (word []) := by
    apply resolveWord (x 7)
    · simpa only [word_cons, mul_comm, mul_left_comm, mul_assoc] using h36
    · simpa only [word_cons, mul_comm, mul_left_comm, mul_assoc] using h35
  simpa [PCRefutable, word] using h37
end K4
end Pcx106PC

namespace Pcx106Transfer

open PEqualNP.ProofComplexity MvPolynomial

variable {V : Type}

private noncomputable def fact (l : Literal V) : MvPolynomial V (ZMod 2) :=
  if l.2 = true then 1 + X l.1 else X l.1

private lemma fact_deg (l : Literal V) : (fact l).totalDegree ≤ 1 := by
  unfold fact
  split
  · exact (totalDegree_add _ _).trans (by simp)
  · simp

private lemma multiply {F : Set (MvPolynomial V (ZMod 2))} {B : ℕ}
    (l : Literal V) {p : MvPolynomial V (ZMod 2)} (hb : 1 + p.totalDegree ≤ B)
    (h : PCDerivable F B p) : PCDerivable F B (fact l * p) := by
  have hx := PCDerivable.mulX l.1 h ((totalDegree_mul _ _).trans (by simpa using hb))
  unfold fact
  split
  · simpa [add_mul] using h.add hx
  · exact hx

variable [DecidableEq V]

private lemma insert_clause (k : Literal V) (A : Clause V) (hk : k ∉ A) :
    clausePoly (insert k A) = fact k * clausePoly A := by simp [clausePoly,fact,hk]

private lemma degree_clause (C : Clause V) : (clausePoly C).totalDegree ≤ C.card := by
  induction C using Finset.induction_on with
  | empty => simp [clausePoly]
  | insert l s hn ih =>
    rw [insert_clause l s hn, Finset.card_insert_of_notMem hn]
    exact (totalDegree_mul _ _).trans (by have := fact_deg l; omega)

private lemma extend {F : Set (MvPolynomial V (ZMod 2))} {B : ℕ}
    (pivot : Literal V) (A T : Clause V)
    (h : PCDerivable F B (fact pivot * clausePoly A)) (bound : (A ∪ T).card + 1 ≤ B) :
    PCDerivable F B (fact pivot * clausePoly (A ∪ T)) := by
  induction T using Finset.induction_on with
  | empty => simpa using h
  | insert k s _ ih =>
    rw [Finset.union_insert] at bound ⊢
    by_cases hk : k ∈ A ∪ s
    · rw [Finset.insert_eq_of_mem hk] at bound ⊢
      exact ih bound
    · rw [Finset.card_insert_of_notMem hk] at bound
      rw [insert_clause k _ hk,mul_left_comm (fact pivot)]
      apply multiply
      · have d := totalDegree_mul (fact pivot) (clausePoly (A ∪ s))
        have := fact_deg pivot
        have := degree_clause (A ∪ s)
        omega
      · exact ih (by omega)

private lemma pad {F : Set (MvPolynomial V (ZMod 2))} {B : ℕ}
    (P R : Clause V) (l : Literal V) (hm : l ∈ P) (incl : P.erase l ⊆ R)
    (hw : R.card + 1 ≤ B) (h : PCDerivable F B (clausePoly P)) :
    PCDerivable F B (fact l * clausePoly R) := by
  have eq : clausePoly P = fact l * clausePoly (P.erase l) := by
    calc
      clausePoly P = clausePoly (insert l (P.erase l)) := by rw [Finset.insert_erase hm]
      _ = _ := insert_clause _ _ (Finset.notMem_erase _ _)
  rw [eq] at h
  have u := Finset.union_eq_right.mpr incl
  simpa only [u] using extend l (P.erase l) R h (u.symm ▸ hw)

private theorem derivable {F : Set (Clause V)} {w : ℕ} {π : List (Clause V)}
    (h : IsDerivation F π) (hw : ∀ C ∈ π, C.card ≤ w) :
    ∀ C ∈ π, PCDerivable (cnfSystem F) (w + 1) (clausePoly C) := by
  induction h with
  | nil => simp
  | @ax π C hd hc ih =>
    intro D hm
    rcases List.mem_cons.mp hm with rfl | ht
    · exact PCDerivable.ax (Or.inr ⟨D,hc,rfl⟩) ((degree_clause D).trans ((hw D (by simp)).trans (by omega)))
    · exact ih (fun E hh => hw E (List.mem_cons_of_mem _ hh)) D ht
  | @res π P Q R hd hp hq hr ih =>
    have prev := ih (fun E hh => hw E (List.mem_cons_of_mem _ hh))
    intro D hm
    rcases List.mem_cons.mp hm with rfl | ht
    · obtain ⟨v,hv,hn,he⟩ := hr
      have d := hw D (by simp)
      have a := pad P D (v,true) hv (by rw [he]; exact Finset.subset_union_left) (by omega) (prev P hp)
      have b := pad Q D (v,false) hn (by rw [he]; exact Finset.subset_union_right) (by omega) (prev Q hq)
      simpa [fact,add_mul,add_assoc,CharTwo.add_self_eq_zero] using a.add b
    · exact prev D ht

theorem resolution_to_PC {F : Set (Clause V)} {w : ℕ} {π : List (Clause V)}
    (h : IsRefutation F π) (hw : ∀ C ∈ π, C.card ≤ w) : PCRefutable (cnfSystem F) (w+1) := by
  simpa [PCRefutable,clausePoly] using derivable h.1 hw ∅ h.2

end Pcx106Transfer

namespace Pcx106Width
open PEqualNP.ProofComplexity
abbrev V := Fin 12 ⊕ (ℕ × ℕ)
def sides : Set (Clause V) := {Ces | ∃ ees ∈ ([(0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11)] : List (Fin 12 × Fin 12)), Ces = {(((Sum.inl ees.1) : Fin 12 ⊕ (ℕ × ℕ)), true), (((Sum.inl ees.2) : Fin 12 ⊕ (ℕ × ℕ)), true)}} ∪ {Cas | ∃ ias : Fin 12, ias.val + 1 < 12 ∧ Cas = {(((Sum.inl ias) : Fin 12 ⊕ (ℕ × ℕ)), false), (((Sum.inr (ias.val, 0)) : Fin 12 ⊕ (ℕ × ℕ)), true)}} ∪ {Cbs | ∃ (ibs : Fin 12) (hbs jbs : ℕ), ibs.val = hbs + 1 ∧ ibs.val + 1 < 12 ∧ jbs < 5 ∧ Cbs = {(((Sum.inr (hbs, jbs)) : Fin 12 ⊕ (ℕ × ℕ)), false), (((Sum.inr (ibs.val, jbs)) : Fin 12 ⊕ (ℕ × ℕ)), true)}} ∪ {Ccs | ∃ (ics : Fin 12) (hcs gcs : ℕ), ics.val = hcs + 1 ∧ ics.val + 1 < 12 ∧ gcs + 1 < 5 ∧ Ccs = {(((Sum.inl ics) : Fin 12 ⊕ (ℕ × ℕ)), false), (((Sum.inr (hcs, gcs)) : Fin 12 ⊕ (ℕ × ℕ)), false), (((Sum.inr (ics.val, gcs + 1)) : Fin 12 ⊕ (ℕ × ℕ)), true)}} ∪ {Cds | ∃ (ids : Fin 12) (hds : ℕ), ids.val = hds + 1 ∧ Cds = {(((Sum.inl ids) : Fin 12 ⊕ (ℕ × ℕ)), false), (((Sum.inr (hds, 4)) : Fin 12 ⊕ (ℕ × ℕ)), false)}} ∪ {Cfs | ∃ jfs : ℕ, 1 ≤ jfs ∧ jfs < 5 ∧ Cfs = {(((Sum.inr (0, jfs)) : Fin 12 ⊕ (ℕ × ℕ)), false)}}

private def x (i : Fin 12) : V := .inl i
private def y (i j : ℕ) : V := .inr (i,j)


private lemma der_append {a b : List (Clause V)} (ha : IsDerivation sides a)
    (hb : IsDerivation sides b) : IsDerivation sides (a++b) := by
  induction ha with
  | nil => exact hb
  | ax _ h ih => exact IsDerivation.ax ih h
  | res _ h j t ih => exact IsDerivation.res ih (List.mem_append_left _ h) (List.mem_append_left _ j) t


private def derived (C : Clause V) : Prop :=
  ∃ d : List (Clause V), IsDerivation sides d ∧ C ∈ d ∧ ∀ c ∈ d, c.card ≤ 3

private theorem base {C : Clause V} (hm : C ∈ sides) (hw : C.card ≤ 3) : derived C := by
  refine ⟨[C], IsDerivation.ax IsDerivation.nil hm, by simp, ?_⟩
  intro c h
  simpa [List.mem_singleton.mp h] using hw

private theorem join (v : V) {P Q R : Clause V} (hp : derived P) (hq : derived Q)
    (hl : (v,true) ∈ P) (hr : (v,false) ∈ Q)
    (he : R = P.erase (v,true) ∪ Q.erase (v,false)) (hw : R.card ≤ 3) : derived R := by
  obtain ⟨p,pd,pm,pw⟩ := hp
  obtain ⟨q,qd,qm,qw⟩ := hq
  refine ⟨R :: (p ++ q), IsDerivation.res (der_append pd qd)
    (List.mem_append_left _ pm) (List.mem_append_right _ qm) ⟨v,hl,hr,he⟩, by simp, ?_⟩
  intro c hc
  rcases List.mem_cons.mp hc with rfl | h
  · exact hw
  · exact (List.mem_append.mp h).elim (pw c) (qw c)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem width_three : ∃ π, IsRefutation sides π ∧ ∀ c ∈ π, c.card ≤ 3 := by
  have h0 : derived {(x 0, true), (x 6, true)} := by
    apply base _ (by decide)
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (⟨(0,6), by decide, by decide⟩)))))
  have h1 : derived {(x 0, true), (x 7, true)} := by
    apply base _ (by decide)
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (⟨(0,7), by decide, by decide⟩)))))
  have h2 : derived {(x 0, true), (x 8, true)} := by
    apply base _ (by decide)
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (⟨(0,8), by decide, by decide⟩)))))
  have h3 : derived {(x 0, true), (x 9, true)} := by
    apply base _ (by decide)
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (⟨(0,9), by decide, by decide⟩)))))
  have h4 : derived {(x 0, true), (x 10, true)} := by
    apply base _ (by decide)
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (⟨(0,10), by decide, by decide⟩)))))
  have h5 : derived {(x 0, true), (x 11, true)} := by
    apply base _ (by decide)
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (⟨(0,11), by decide, by decide⟩)))))
  have h6 : derived {(x 6, false), (y 6 0, true)} := by
    apply base _ (by decide)
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨6, by decide, by decide⟩)))))
  have h7 : derived {(x 0, true), (y 6 0, true)} := join (x 6) h0 h6 (by decide) (by decide) (by decide) (by decide)
  have h8 : derived {(x 7, false), (y 6 0, false), (y 7 1, true)} := by
    apply base _ (by decide)
    exact Or.inl (Or.inl (Or.inr (⟨7, 6, 0, by decide, by decide, by decide, by decide⟩)))
  have h9 : derived {(x 0, true), (y 6 0, false), (y 7 1, true)} := join (x 7) h1 h8 (by decide) (by decide) (by decide) (by decide)
  have h10 : derived {(x 0, true), (y 7 1, true)} := join (y 6 0) h7 h9 (by decide) (by decide) (by decide) (by decide)
  have h11 : derived {(x 8, false), (y 7 1, false), (y 8 2, true)} := by
    apply base _ (by decide)
    exact Or.inl (Or.inl (Or.inr (⟨8, 7, 1, by decide, by decide, by decide, by decide⟩)))
  have h12 : derived {(x 0, true), (y 7 1, false), (y 8 2, true)} := join (x 8) h2 h11 (by decide) (by decide) (by decide) (by decide)
  have h13 : derived {(x 0, true), (y 8 2, true)} := join (y 7 1) h10 h12 (by decide) (by decide) (by decide) (by decide)
  have h14 : derived {(x 9, false), (y 8 2, false), (y 9 3, true)} := by
    apply base _ (by decide)
    exact Or.inl (Or.inl (Or.inr (⟨9, 8, 2, by decide, by decide, by decide, by decide⟩)))
  have h15 : derived {(x 0, true), (y 8 2, false), (y 9 3, true)} := join (x 9) h3 h14 (by decide) (by decide) (by decide) (by decide)
  have h16 : derived {(x 0, true), (y 9 3, true)} := join (y 8 2) h13 h15 (by decide) (by decide) (by decide) (by decide)
  have h17 : derived {(x 10, false), (y 9 3, false), (y 10 4, true)} := by
    apply base _ (by decide)
    exact Or.inl (Or.inl (Or.inr (⟨10, 9, 3, by decide, by decide, by decide, by decide⟩)))
  have h18 : derived {(x 0, true), (y 9 3, false), (y 10 4, true)} := join (x 10) h4 h17 (by decide) (by decide) (by decide) (by decide)
  have h19 : derived {(x 0, true), (y 10 4, true)} := join (y 9 3) h16 h18 (by decide) (by decide) (by decide) (by decide)
  have h20 : derived {(x 11, false), (y 10 4, false)} := by
    apply base _ (by decide)
    exact Or.inl (Or.inr (⟨11, 10, by decide, by decide⟩))
  have h21 : derived {(x 0, true), (y 10 4, false)} := join (x 11) h5 h20 (by decide) (by decide) (by decide) (by decide)
  have h22 : derived {(x 0, true)} := join (y 10 4) h19 h21 (by decide) (by decide) (by decide) (by decide)
  have h23 : derived {(x 1, true), (x 6, true)} := by
    apply base _ (by decide)
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (⟨(1,6), by decide, by decide⟩)))))
  have h24 : derived {(x 1, true), (x 7, true)} := by
    apply base _ (by decide)
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (⟨(1,7), by decide, by decide⟩)))))
  have h25 : derived {(x 1, true), (x 8, true)} := by
    apply base _ (by decide)
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (⟨(1,8), by decide, by decide⟩)))))
  have h26 : derived {(x 1, true), (x 9, true)} := by
    apply base _ (by decide)
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (⟨(1,9), by decide, by decide⟩)))))
  have h27 : derived {(x 1, true), (x 10, true)} := by
    apply base _ (by decide)
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (⟨(1,10), by decide, by decide⟩)))))
  have h28 : derived {(x 1, true), (x 11, true)} := by
    apply base _ (by decide)
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (⟨(1,11), by decide, by decide⟩)))))
  have h29 : derived {(x 1, true), (y 6 0, true)} := join (x 6) h23 h6 (by decide) (by decide) (by decide) (by decide)
  have h30 : derived {(x 1, true), (y 6 0, false), (y 7 1, true)} := join (x 7) h24 h8 (by decide) (by decide) (by decide) (by decide)
  have h31 : derived {(x 1, true), (y 7 1, true)} := join (y 6 0) h29 h30 (by decide) (by decide) (by decide) (by decide)
  have h32 : derived {(x 1, true), (y 7 1, false), (y 8 2, true)} := join (x 8) h25 h11 (by decide) (by decide) (by decide) (by decide)
  have h33 : derived {(x 1, true), (y 8 2, true)} := join (y 7 1) h31 h32 (by decide) (by decide) (by decide) (by decide)
  have h34 : derived {(x 1, true), (y 8 2, false), (y 9 3, true)} := join (x 9) h26 h14 (by decide) (by decide) (by decide) (by decide)
  have h35 : derived {(x 1, true), (y 9 3, true)} := join (y 8 2) h33 h34 (by decide) (by decide) (by decide) (by decide)
  have h36 : derived {(x 1, true), (y 9 3, false), (y 10 4, true)} := join (x 10) h27 h17 (by decide) (by decide) (by decide) (by decide)
  have h37 : derived {(x 1, true), (y 10 4, true)} := join (y 9 3) h35 h36 (by decide) (by decide) (by decide) (by decide)
  have h38 : derived {(x 1, true), (y 10 4, false)} := join (x 11) h28 h20 (by decide) (by decide) (by decide) (by decide)
  have h39 : derived {(x 1, true)} := join (y 10 4) h37 h38 (by decide) (by decide) (by decide) (by decide)
  have h40 : derived {(x 2, true), (x 6, true)} := by
    apply base _ (by decide)
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (⟨(2,6), by decide, by decide⟩)))))
  have h41 : derived {(x 2, true), (x 7, true)} := by
    apply base _ (by decide)
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (⟨(2,7), by decide, by decide⟩)))))
  have h42 : derived {(x 2, true), (x 8, true)} := by
    apply base _ (by decide)
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (⟨(2,8), by decide, by decide⟩)))))
  have h43 : derived {(x 2, true), (x 9, true)} := by
    apply base _ (by decide)
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (⟨(2,9), by decide, by decide⟩)))))
  have h44 : derived {(x 2, true), (x 10, true)} := by
    apply base _ (by decide)
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (⟨(2,10), by decide, by decide⟩)))))
  have h45 : derived {(x 2, true), (x 11, true)} := by
    apply base _ (by decide)
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (⟨(2,11), by decide, by decide⟩)))))
  have h46 : derived {(x 2, true), (y 6 0, true)} := join (x 6) h40 h6 (by decide) (by decide) (by decide) (by decide)
  have h47 : derived {(x 2, true), (y 6 0, false), (y 7 1, true)} := join (x 7) h41 h8 (by decide) (by decide) (by decide) (by decide)
  have h48 : derived {(x 2, true), (y 7 1, true)} := join (y 6 0) h46 h47 (by decide) (by decide) (by decide) (by decide)
  have h49 : derived {(x 2, true), (y 7 1, false), (y 8 2, true)} := join (x 8) h42 h11 (by decide) (by decide) (by decide) (by decide)
  have h50 : derived {(x 2, true), (y 8 2, true)} := join (y 7 1) h48 h49 (by decide) (by decide) (by decide) (by decide)
  have h51 : derived {(x 2, true), (y 8 2, false), (y 9 3, true)} := join (x 9) h43 h14 (by decide) (by decide) (by decide) (by decide)
  have h52 : derived {(x 2, true), (y 9 3, true)} := join (y 8 2) h50 h51 (by decide) (by decide) (by decide) (by decide)
  have h53 : derived {(x 2, true), (y 9 3, false), (y 10 4, true)} := join (x 10) h44 h17 (by decide) (by decide) (by decide) (by decide)
  have h54 : derived {(x 2, true), (y 10 4, true)} := join (y 9 3) h52 h53 (by decide) (by decide) (by decide) (by decide)
  have h55 : derived {(x 2, true), (y 10 4, false)} := join (x 11) h45 h20 (by decide) (by decide) (by decide) (by decide)
  have h56 : derived {(x 2, true)} := join (y 10 4) h54 h55 (by decide) (by decide) (by decide) (by decide)
  have h57 : derived {(x 3, true), (x 6, true)} := by
    apply base _ (by decide)
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (⟨(3,6), by decide, by decide⟩)))))
  have h58 : derived {(x 3, true), (x 7, true)} := by
    apply base _ (by decide)
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (⟨(3,7), by decide, by decide⟩)))))
  have h59 : derived {(x 3, true), (x 8, true)} := by
    apply base _ (by decide)
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (⟨(3,8), by decide, by decide⟩)))))
  have h60 : derived {(x 3, true), (x 9, true)} := by
    apply base _ (by decide)
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (⟨(3,9), by decide, by decide⟩)))))
  have h61 : derived {(x 3, true), (x 10, true)} := by
    apply base _ (by decide)
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (⟨(3,10), by decide, by decide⟩)))))
  have h62 : derived {(x 3, true), (x 11, true)} := by
    apply base _ (by decide)
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (⟨(3,11), by decide, by decide⟩)))))
  have h63 : derived {(x 3, true), (y 6 0, true)} := join (x 6) h57 h6 (by decide) (by decide) (by decide) (by decide)
  have h64 : derived {(x 3, true), (y 6 0, false), (y 7 1, true)} := join (x 7) h58 h8 (by decide) (by decide) (by decide) (by decide)
  have h65 : derived {(x 3, true), (y 7 1, true)} := join (y 6 0) h63 h64 (by decide) (by decide) (by decide) (by decide)
  have h66 : derived {(x 3, true), (y 7 1, false), (y 8 2, true)} := join (x 8) h59 h11 (by decide) (by decide) (by decide) (by decide)
  have h67 : derived {(x 3, true), (y 8 2, true)} := join (y 7 1) h65 h66 (by decide) (by decide) (by decide) (by decide)
  have h68 : derived {(x 3, true), (y 8 2, false), (y 9 3, true)} := join (x 9) h60 h14 (by decide) (by decide) (by decide) (by decide)
  have h69 : derived {(x 3, true), (y 9 3, true)} := join (y 8 2) h67 h68 (by decide) (by decide) (by decide) (by decide)
  have h70 : derived {(x 3, true), (y 9 3, false), (y 10 4, true)} := join (x 10) h61 h17 (by decide) (by decide) (by decide) (by decide)
  have h71 : derived {(x 3, true), (y 10 4, true)} := join (y 9 3) h69 h70 (by decide) (by decide) (by decide) (by decide)
  have h72 : derived {(x 3, true), (y 10 4, false)} := join (x 11) h62 h20 (by decide) (by decide) (by decide) (by decide)
  have h73 : derived {(x 3, true)} := join (y 10 4) h71 h72 (by decide) (by decide) (by decide) (by decide)
  have h74 : derived {(x 4, true), (x 6, true)} := by
    apply base _ (by decide)
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (⟨(4,6), by decide, by decide⟩)))))
  have h75 : derived {(x 4, true), (x 7, true)} := by
    apply base _ (by decide)
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (⟨(4,7), by decide, by decide⟩)))))
  have h76 : derived {(x 4, true), (x 8, true)} := by
    apply base _ (by decide)
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (⟨(4,8), by decide, by decide⟩)))))
  have h77 : derived {(x 4, true), (x 9, true)} := by
    apply base _ (by decide)
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (⟨(4,9), by decide, by decide⟩)))))
  have h78 : derived {(x 4, true), (x 10, true)} := by
    apply base _ (by decide)
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (⟨(4,10), by decide, by decide⟩)))))
  have h79 : derived {(x 4, true), (x 11, true)} := by
    apply base _ (by decide)
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (⟨(4,11), by decide, by decide⟩)))))
  have h80 : derived {(x 4, true), (y 6 0, true)} := join (x 6) h74 h6 (by decide) (by decide) (by decide) (by decide)
  have h81 : derived {(x 4, true), (y 6 0, false), (y 7 1, true)} := join (x 7) h75 h8 (by decide) (by decide) (by decide) (by decide)
  have h82 : derived {(x 4, true), (y 7 1, true)} := join (y 6 0) h80 h81 (by decide) (by decide) (by decide) (by decide)
  have h83 : derived {(x 4, true), (y 7 1, false), (y 8 2, true)} := join (x 8) h76 h11 (by decide) (by decide) (by decide) (by decide)
  have h84 : derived {(x 4, true), (y 8 2, true)} := join (y 7 1) h82 h83 (by decide) (by decide) (by decide) (by decide)
  have h85 : derived {(x 4, true), (y 8 2, false), (y 9 3, true)} := join (x 9) h77 h14 (by decide) (by decide) (by decide) (by decide)
  have h86 : derived {(x 4, true), (y 9 3, true)} := join (y 8 2) h84 h85 (by decide) (by decide) (by decide) (by decide)
  have h87 : derived {(x 4, true), (y 9 3, false), (y 10 4, true)} := join (x 10) h78 h17 (by decide) (by decide) (by decide) (by decide)
  have h88 : derived {(x 4, true), (y 10 4, true)} := join (y 9 3) h86 h87 (by decide) (by decide) (by decide) (by decide)
  have h89 : derived {(x 4, true), (y 10 4, false)} := join (x 11) h79 h20 (by decide) (by decide) (by decide) (by decide)
  have h90 : derived {(x 4, true)} := join (y 10 4) h88 h89 (by decide) (by decide) (by decide) (by decide)
  have h91 : derived {(x 5, true), (x 6, true)} := by
    apply base _ (by decide)
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (⟨(5,6), by decide, by decide⟩)))))
  have h92 : derived {(x 5, true), (x 7, true)} := by
    apply base _ (by decide)
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (⟨(5,7), by decide, by decide⟩)))))
  have h93 : derived {(x 5, true), (x 8, true)} := by
    apply base _ (by decide)
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (⟨(5,8), by decide, by decide⟩)))))
  have h94 : derived {(x 5, true), (x 9, true)} := by
    apply base _ (by decide)
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (⟨(5,9), by decide, by decide⟩)))))
  have h95 : derived {(x 5, true), (x 10, true)} := by
    apply base _ (by decide)
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (⟨(5,10), by decide, by decide⟩)))))
  have h96 : derived {(x 5, true), (x 11, true)} := by
    apply base _ (by decide)
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (⟨(5,11), by decide, by decide⟩)))))
  have h97 : derived {(x 5, true), (y 6 0, true)} := join (x 6) h91 h6 (by decide) (by decide) (by decide) (by decide)
  have h98 : derived {(x 5, true), (y 6 0, false), (y 7 1, true)} := join (x 7) h92 h8 (by decide) (by decide) (by decide) (by decide)
  have h99 : derived {(x 5, true), (y 7 1, true)} := join (y 6 0) h97 h98 (by decide) (by decide) (by decide) (by decide)
  have h100 : derived {(x 5, true), (y 7 1, false), (y 8 2, true)} := join (x 8) h93 h11 (by decide) (by decide) (by decide) (by decide)
  have h101 : derived {(x 5, true), (y 8 2, true)} := join (y 7 1) h99 h100 (by decide) (by decide) (by decide) (by decide)
  have h102 : derived {(x 5, true), (y 8 2, false), (y 9 3, true)} := join (x 9) h94 h14 (by decide) (by decide) (by decide) (by decide)
  have h103 : derived {(x 5, true), (y 9 3, true)} := join (y 8 2) h101 h102 (by decide) (by decide) (by decide) (by decide)
  have h104 : derived {(x 5, true), (y 9 3, false), (y 10 4, true)} := join (x 10) h95 h17 (by decide) (by decide) (by decide) (by decide)
  have h105 : derived {(x 5, true), (y 10 4, true)} := join (y 9 3) h103 h104 (by decide) (by decide) (by decide) (by decide)
  have h106 : derived {(x 5, true), (y 10 4, false)} := join (x 11) h96 h20 (by decide) (by decide) (by decide) (by decide)
  have h107 : derived {(x 5, true)} := join (y 10 4) h105 h106 (by decide) (by decide) (by decide) (by decide)
  have h108 : derived {(x 0, false), (y 0 0, true)} := by
    apply base _ (by decide)
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨0, by decide, by decide⟩)))))
  have h109 : derived {(y 0 0, true)} := join (x 0) h22 h108 (by decide) (by decide) (by decide) (by decide)
  have h110 : derived {(x 1, false), (y 0 0, false), (y 1 1, true)} := by
    apply base _ (by decide)
    exact Or.inl (Or.inl (Or.inr (⟨1, 0, 0, by decide, by decide, by decide, by decide⟩)))
  have h111 : derived {(y 0 0, false), (y 1 1, true)} := join (x 1) h39 h110 (by decide) (by decide) (by decide) (by decide)
  have h112 : derived {(y 1 1, true)} := join (y 0 0) h109 h111 (by decide) (by decide) (by decide) (by decide)
  have h113 : derived {(x 2, false), (y 1 1, false), (y 2 2, true)} := by
    apply base _ (by decide)
    exact Or.inl (Or.inl (Or.inr (⟨2, 1, 1, by decide, by decide, by decide, by decide⟩)))
  have h114 : derived {(y 1 1, false), (y 2 2, true)} := join (x 2) h56 h113 (by decide) (by decide) (by decide) (by decide)
  have h115 : derived {(y 2 2, true)} := join (y 1 1) h112 h114 (by decide) (by decide) (by decide) (by decide)
  have h116 : derived {(x 3, false), (y 2 2, false), (y 3 3, true)} := by
    apply base _ (by decide)
    exact Or.inl (Or.inl (Or.inr (⟨3, 2, 2, by decide, by decide, by decide, by decide⟩)))
  have h117 : derived {(y 2 2, false), (y 3 3, true)} := join (x 3) h73 h116 (by decide) (by decide) (by decide) (by decide)
  have h118 : derived {(y 3 3, true)} := join (y 2 2) h115 h117 (by decide) (by decide) (by decide) (by decide)
  have h119 : derived {(x 4, false), (y 3 3, false), (y 4 4, true)} := by
    apply base _ (by decide)
    exact Or.inl (Or.inl (Or.inr (⟨4, 3, 3, by decide, by decide, by decide, by decide⟩)))
  have h120 : derived {(y 3 3, false), (y 4 4, true)} := join (x 4) h90 h119 (by decide) (by decide) (by decide) (by decide)
  have h121 : derived {(y 4 4, true)} := join (y 3 3) h118 h120 (by decide) (by decide) (by decide) (by decide)
  have h122 : derived {(x 5, false), (y 4 4, false)} := by
    apply base _ (by decide)
    exact Or.inl (Or.inr (⟨5, 4, by decide, by decide⟩))
  have h123 : derived {(y 4 4, false)} := join (x 5) h107 h122 (by decide) (by decide) (by decide) (by decide)
  have h124 : derived ∅ := join (y 4 4) h121 h123 (by decide) (by decide) (by decide) (by decide)
  obtain ⟨π, h, m, w⟩ := h124
  exact ⟨π, ⟨h,m⟩, w⟩

end Pcx106Width

namespace Pcx106Moments

open MvPolynomial

private def sample {V : Type*} (L : List (V → ZMod 2)) :
    MvPolynomial V (ZMod 2) →+ ZMod 2 where
  toFun p := (L.map (fun a => eval a p)).sum
  map_zero' := by induction L <;> simp_all
  map_add' p q := by
    induction L with
    | nil => simp
    | cons a l ih =>
      simp only [List.map_cons, List.sum_cons, map_add] at ih ⊢
      rw [ih]
      abel

private theorem small_exponent {V : Type*} (d : V →₀ ℕ)
    (hd : (Finsupp.toMultiset d).card ≤ 2) :
    d = 0 ∨ (∃ i, d = Finsupp.single i 1) ∨
      (∃ i j, d = Finsupp.single i 1 + Finsupp.single j 1) := by
  classical
  have inj := (Multiset.toFinsupp (α := V)).symm.injective
  have h : (Finsupp.toMultiset d).card = 0 ∨ (Finsupp.toMultiset d).card = 1 ∨
      (Finsupp.toMultiset d).card = 2 := by omega
  rcases h with h | h | h
  · left
    apply inj
    exact Multiset.card_eq_zero.mp h
  · obtain ⟨i, hi⟩ := Multiset.card_eq_one.mp h
    right; left; refine ⟨i, inj ?_⟩
    change Finsupp.toMultiset d = Finsupp.toMultiset (Finsupp.single i 1)
    simpa using hi
  · obtain ⟨i, j, hij⟩ := Multiset.card_eq_two.mp h
    right; right; refine ⟨i, j, inj ?_⟩
    change Finsupp.toMultiset d = Finsupp.toMultiset (Finsupp.single i 1 + Finsupp.single j 1)
    simpa [Finsupp.toMultiset_add] using hij

private theorem nonzero_one (k : ZMod 2) (hk : k ≠ 0) : k = 1 := by
  fin_cases k <;> first | rfl | exact (hk rfl).elim

theorem interpolate {V : Type*} (c : V → ZMod 2) (L : List (V → ZMod 2))
    (h0 : (L.map (fun _ => (1 : ZMod 2))).sum = 1)
    (h1 : ∀ i, (L.map (fun a => a i)).sum = c i)
    (h2 : ∀ i j, (L.map (fun a => a i * a j)).sum = c i * c j)
    (p : MvPolynomial V (ZMod 2)) (hp : p.totalDegree ≤ 2) :
    (L.map (fun a => eval a p)).sum = eval c p := by
  classical
  change sample L p = eval c p
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hk := nonzero_one (p.coeff d) (mem_support_iff.mp hd)
  rw [hk]
  have hs : (Finsupp.toMultiset d).card ≤ 2 :=
    (Finsupp.card_toMultiset d).trans_le ((le_totalDegree hd).trans hp)
  rcases small_exponent d hs with rfl | ⟨i, rfl⟩ | ⟨i, j, rfl⟩
  · change sample L 1 = eval c 1
    simpa [sample] using h0
  · change sample L (X i) = eval c (X i)
    simpa [sample] using h1 i
  · have hm : monomial (Finsupp.single i 1 + Finsupp.single j 1) (1 : ZMod 2) = X i * X j := by
      simp [X, monomial_mul_monomial]
    rw [hm]
    simpa [sample] using h2 i j

end Pcx106Moments

namespace Pcx106Barrier

open MvPolynomial PEqualNP.ProofComplexity

def Fits {V : Type} (c : V → ZMod 2) (L R : List (V → ZMod 2))
    (p : MvPolynomial V (ZMod 2)) : Prop :=
  ∃ u v : ZMod 2, (∀ a ∈ L, eval a p = u) ∧ (∀ a ∈ R, eval a p = v) ∧ eval c p = u + v

private theorem sum_constant {T : Type} (L : List T) (u : ZMod 2)
    (ho : (L.map (fun _ => (1 : ZMod 2))).sum = 1) :
    (L.map (fun _ => u)).sum = u := by
  have h : (L.map (fun _ => u)).sum = (L.map (fun _ => (1 : ZMod 2))).sum * u := by
    clear ho
    induction L with
    | nil => simp
    | cons a t ih => simp [add_mul]
  rwa [ho, one_mul] at h

private theorem all_zero {V : Type} (c : V → ZMod 2) (L R : List (V → ZMod 2))
    (lo : (L.map (fun _ => (1 : ZMod 2))).sum = 1)
    (ro : (R.map (fun _ => (1 : ZMod 2))).sum = 1)
    (lp : ∀ p : MvPolynomial V (ZMod 2), p.totalDegree ≤ 2 →
      (L.map (fun a => eval a p)).sum = eval c p)
    (rp : ∀ p : MvPolynomial V (ZMod 2), p.totalDegree ≤ 2 →
      (R.map (fun a => eval a p)).sum = eval c p)
    {p : MvPolynomial V (ZMod 2)} (hf : Fits c L R p) (hd : p.totalDegree ≤ 2) :
    (∀ a ∈ L, eval a p = 0) ∧ (∀ a ∈ R, eval a p = 0) ∧ eval c p = 0 := by
  obtain ⟨u,v,hl,hr,hc⟩ := hf
  have h₁ : eval c p = u := by
    rw [← lp p hd, List.map_congr_left hl]
    exact sum_constant L u lo
  have h₂ : eval c p = v := by
    rw [← rp p hd, List.map_congr_left hr]
    exact sum_constant R v ro
  have hu := add_left_cancel (show u + v = u + 0 by simpa using hc.symm.trans h₁)
  have hv := add_right_cancel (show u + v = 0 + v by simpa using hc.symm.trans h₂)
  exact ⟨fun a ha => (hl a ha).trans hv, fun a ha => (hr a ha).trans hu, h₁.trans hv⟩

theorem reject {V : Type} {F : Set (MvPolynomial V (ZMod 2))}
    (c : V → ZMod 2) (L R : List (V → ZMod 2))
    (lo : (L.map (fun _ => (1 : ZMod 2))).sum = 1)
    (ro : (R.map (fun _ => (1 : ZMod 2))).sum = 1)
    (lp : ∀ p : MvPolynomial V (ZMod 2), p.totalDegree ≤ 2 →
      (L.map (fun a => eval a p)).sum = eval c p)
    (rp : ∀ p : MvPolynomial V (ZMod 2), p.totalDegree ≤ 2 →
      (R.map (fun a => eval a p)).sum = eval c p)
    (hF : ∀ p ∈ F, Fits c L R p) : ¬ PCRefutable F 3 := by
  have stable : ∀ {p : MvPolynomial V (ZMod 2)}, PCDerivable F 3 p → Fits c L R p := by
    intro p h
    induction h with
    | ax hm hd => exact hF _ hm
    | zero => exact ⟨0,0,by simp, by simp, by simp⟩
    | add h k ih ik =>
      obtain ⟨u,v,hl,hr,hc⟩ := ih
      obtain ⟨u',v',hl',hr',hc'⟩ := ik
      refine ⟨u+u',v+v',fun a ha => ?_,fun a ha => ?_,?_⟩
      · simp [hl a ha, hl' a ha]
      · simp [hr a ha, hr' a ha]
      · simp [hc,hc',add_left_comm,add_comm]
    | @mulX i p h hd ih =>
      by_cases hz : p = 0
      · subst p
        exact ⟨0,0,by simp, by simp, by simp⟩
      · rw [totalDegree_mul_of_isDomain (X_ne_zero i) hz, totalDegree_X] at hd
        obtain ⟨hl,hr,hc⟩ := all_zero c L R lo ro lp rp ih (by omega)
        exact ⟨0,0,fun a ha => by simp [hl a ha],fun a ha => by simp [hr a ha],by simp [hc]⟩
  intro h
  have hzero := (all_zero c L R lo ro lp rp (stable h) (by simp)).2.2
  simp at hzero

end Pcx106Barrier

namespace Pcx106Data

open PEqualNP.ProofComplexity MvPolynomial
abbrev V := Fin 12 ⊕ (ℕ × ℕ)
abbrev K := ZMod 2
abbrev Index := Fin 68
def idx : V → Index
  | .inl i => ⟨i.val, by omega⟩
  | .inr (i,j) => if h : i<11 ∧ j<5 then ⟨12+5*i+j,by omega⟩ else 67
def val (m : ℕ) (i : Index) : K := if m.testBit i.val then 1 else 0
def assignment (m : ℕ) (v : V) : K := val m (idx v)
def leftMasks : List ℕ := [70216638155689299952,
  70216638155689299936,
  70216638155823517672,
  70216638155823517664,
  70216638155827711972,
  70216638155827711968,
  70216638155827843042,
  70216638155827843040,
  70216638155827847137,
  70216638164279234512,
  70216638164279234496,
  70216638164413452248,
  70216638164413452240,
  70216638164413452232,
  70216638164413452224,
  70216638164417646548,
  70216638164417646544,
  70216638164417646532,
  70216638164417646528,
  70216638164417777618,
  70216638164417777616,
  70216638164417777602,
  70216638164417777600,
  70216638164417781713,
  70216638164417781697,
  70216638164681887688,
  70216638164681887680,
  70216638164686081996,
  70216638164686081992,
  70216638164686081988,
  70216638164686081984,
  70216638164686213066,
  70216638164686213064,
  70216638164686213058,
  70216638164686213056,
  70216638164686217161,
  70216638164686217153,
  70216638164694470596,
  70216638164694470592,
  70216638164694601670,
  70216638164694601668,
  70216638164694601666,
  70216638164694601664,
  70216638164694605765,
  70216638164694605761,
  70216638164694863810,
  70216638164694863808,
  70216638164694867907,
  70216638164694867905]
def rightMasks : List ℕ := [70198043215178899007,
  70198043215178898495,
  70216057613688380735,
  70216057613688380479,
  70216620563641801919,
  70216620563641801791,
  70216638155827846271,
  71350964719785744959,
  71350964719785744447,
  71368979118295227199,
  71368979118295226943,
  71368979118295226687,
  71368979118295226431,
  71369542068248648383,
  71369542068248648255,
  71369542068248647871,
  71369542068248647743,
  71369559660434692735,
  71369559660434692223,
  71405007915314190655,
  71405007915314190399,
  71405570865267612095,
  71405570865267611967,
  71405570865267611839,
  71405570865267611711,
  71405588457453656447,
  71405588457453656191,
  71406696765174454463,
  71406696765174454335,
  71406714357360498943,
  71406714357360498815]
def middle : ℕ := 70216638155827847167

def corner := assignment middle
def left := leftMasks.map assignment
def right := rightMasks.map assignment


theorem left0 : (left.map (fun _ => (1 : K))).sum = 1 := by decide +kernel
theorem right0 : (right.map (fun _ => (1 : K))).sum = 1 := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem left1 (v : V) : (left.map (fun a => a v)).sum = corner v := by
  simpa only [left,corner,assignment,List.map_map, Function.comp_def] using
    (show ∀ i : Index, (leftMasks.map (fun m => val m i)).sum = val middle i by decide +kernel) (idx v)

private def leftClass : Index → Fin 15 := ![0,1,2,3,4,5,6,6,6,6,6,6,0,7,7,7,7,8,9,7,7,7,10,11,7,7,7,12,13,7,7,7,6,14,7,7,7,6,6,7,7,7,6,6,6,7,7,6,6,6,7,7,6,6,6,7,7,6,6,6,7,7,6,6,6,6,7,7]
private def leftRep : Fin 15 → Index := ![0,1,2,3,4,5,6,13,17,18,22,23,27,28,33]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem left2 (v w : V) : (left.map (fun a => a v * a w)).sum = corner v * corner w := by
  have rep : ∀ (i : Index) (m : ℕ), m ∈ middle :: leftMasks →
      val m i = val m (leftRep (leftClass i)) := by decide +kernel
  have prop : ∀ i j : Fin 15,
      (leftMasks.map (fun m => val m (leftRep i) * val m (leftRep j))).sum =
        val middle (leftRep i) * val middle (leftRep j) := by decide +kernel
  simp only [left,corner,assignment,List.map_map,Function.comp_def]
  rw [rep (idx v) middle (by simp),rep (idx w) middle (by simp),← prop]
  apply congrArg List.sum
  apply List.map_congr_left
  intro m hm
  rw [rep (idx v) m (List.mem_cons_of_mem _ hm), rep (idx w) m (List.mem_cons_of_mem _ hm)]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem right1 (v : V) : (right.map (fun a => a v)).sum = corner v := by
  simpa only [right,corner,assignment,List.map_map, Function.comp_def] using
    (show ∀ i : Index, (rightMasks.map (fun m => val m i)).sum = val middle i by decide +kernel) (idx v)

private def rightClass : Index → Fin 12 := ![0,0,0,0,0,0,1,2,3,4,5,0,0,6,6,6,6,0,6,6,6,6,0,6,6,6,6,0,6,6,6,6,0,6,6,6,6,0,0,6,6,6,0,0,1,6,6,0,0,7,8,6,0,0,9,10,6,0,0,0,11,6,0,0,0,0,6,6]
private def rightRep : Fin 12 → Index := ![0,6,7,8,9,10,13,49,50,54,55,60]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem right2 (v w : V) : (right.map (fun a => a v * a w)).sum = corner v * corner w := by
  have rep : ∀ (i : Index) (m : ℕ), m ∈ middle :: rightMasks →
      val m i = val m (rightRep (rightClass i)) := by decide +kernel
  have prop : ∀ i j : Fin 12,
      (rightMasks.map (fun m => val m (rightRep i) * val m (rightRep j))).sum =
        val middle (rightRep i) * val middle (rightRep j) := by decide +kernel
  simp only [right,corner,assignment,List.map_map,Function.comp_def]
  rw [rep (idx v) middle (by simp),rep (idx w) middle (by simp),← prop]
  apply congrArg List.sum
  apply List.map_congr_left
  intro m hm
  rw [rep (idx v) m (List.mem_cons_of_mem _ hm), rep (idx w) m (List.mem_cons_of_mem _ hm)]

end Pcx106Data

namespace Pcx106Axioms
open PEqualNP.ProofComplexity MvPolynomial Pcx106Data

def wrap (i : ℕ) : Fin 12 := ⟨i % 12, Nat.mod_lt _ (by decide)⟩
def zz (i : ℕ) : V := .inl (wrap i)
def ss (i j : ℕ) : V := .inr (i,j)

@[local simp] lemma wrap_val (i : Fin 12) : wrap i.val = i := by
  apply Fin.ext; simp [wrap,Nat.mod_eq_of_lt i.isLt]

abbrev Label := (Fin 6 × Fin 6) ⊕ Fin 11 ⊕ (Fin 10 × Fin 5) ⊕ (Fin 10 × Fin 4) ⊕ Fin 11 ⊕ Fin 4

namespace Label
def edge (a b : Fin 6) : Label := .inl (a,b)
def first (i : Fin 11) : Label := .inr (.inl i)
def carry (i : Fin 10) (j : Fin 5) : Label := .inr (.inr (.inl (i,j)))
def advance (i : Fin 10) (j : Fin 4) : Label := .inr (.inr (.inr (.inl (i,j))))
def cap (i : Fin 11) : Label := .inr (.inr (.inr (.inr (.inl i))))
def init (j : Fin 4) : Label := .inr (.inr (.inr (.inr (.inr j))))

def clause : Label → Clause V
  | .inl (a,b) => {(zz a,true),(zz (6+b.val),true)}
  | .inr (.inl i) => {(zz i,false),(ss i 0,true)}
  | .inr (.inr (.inl (i,j))) => {(ss i j,false),(ss (i.val+1) j,true)}
  | .inr (.inr (.inr (.inl (i,j)))) => {(zz (i.val+1),false),(ss i j,false),(ss (i.val+1) (j.val+1),true)}
  | .inr (.inr (.inr (.inr (.inl i)))) => {(zz (i.val+1),false),(ss i 4,false)}
  | .inr (.inr (.inr (.inr (.inr j)))) => {(ss 0 (j.val+1),false)}
end Label

lemma cover (c : Clause V) (h : c ∈ Pcx106Width.sides) : ∃ a : Label, Label.clause a = c := by
  rcases h with (((((he | ha) | hb) | hc) | ho) | hf)
  · obtain ⟨⟨a,b⟩,hab,rfl⟩ := he
    have ranged : a.val < 6 ∧ 6 ≤ b.val := by
      have lemma' : ∀ x y : Fin 12,
          (x,y) ∈ ([(0,6),(0,7),(0,8),(0,9),(0,10),(0,11),(1,6),(1,7),(1,8),(1,9),(1,10),(1,11),
                     (2,6),(2,7),(2,8),(2,9),(2,10),(2,11),(3,6),(3,7),(3,8),(3,9),(3,10),(3,11),
                     (4,6),(4,7),(4,8),(4,9),(4,10),(4,11),(5,6),(5,7),(5,8),(5,9),(5,10),(5,11)] :
                    List (Fin 12 × Fin 12)) → x.val<6 ∧ 6≤y.val := by decide
      exact lemma' _ _ hab
    refine ⟨Label.edge ⟨a.val,ranged.1⟩ ⟨b.val-6,by omega⟩,?_⟩
    simp [Label.clause,Label.edge,zz, show 6+(b.val-6)=b.val by omega]
  · obtain ⟨i,hi,rfl⟩ := ha
    exact ⟨Label.first ⟨i.val,by omega⟩,by simp [Label.clause,Label.first,zz,ss]⟩
  · obtain ⟨i,k,j,hk,hi,hj,rfl⟩ := hb
    exact ⟨Label.carry ⟨k,by omega⟩ ⟨j,hj⟩,by simp [Label.clause,Label.carry,ss,← hk]⟩
  · obtain ⟨i,k,j,hk,hi,hj,rfl⟩ := hc
    exact ⟨Label.advance ⟨k,by omega⟩ ⟨j,by omega⟩,by simp [Label.clause,Label.advance,zz,ss,← hk]⟩
  · obtain ⟨i,k,hk,rfl⟩ := ho
    exact ⟨Label.cap ⟨k,by omega⟩,by simp [Label.clause,Label.cap,zz,ss,← hk]⟩
  · obtain ⟨j,h1,h2,rfl⟩ := hf
    exact ⟨Label.init ⟨j-1,by omega⟩,by simp [Label.clause,Label.init,ss,show j-1+1=j by omega]⟩

def scalar (m : ℕ) (c : Clause V) : K :=
  ∏ l ∈ c, if l.2 = true then 1 + assignment m l.1 else assignment m l.1

lemma eval_clause (m : ℕ) (c : Clause V) : eval (assignment m) (clausePoly c) = scalar m c := by
  simp only [clausePoly, scalar, map_prod]
  apply Finset.prod_congr rfl
  intro l _
  split_ifs <;> simp

def uniform (m : ℕ) (c : Clause V) (vs : List ℕ) : Bool :=
  vs.all (fun a => decide (scalar a c = scalar m c))

def check (a : Label) : Bool :=
  uniform leftMasks.head! (Label.clause a) leftMasks && uniform rightMasks.head! (Label.clause a) rightMasks &&
    decide (scalar middle (Label.clause a) = scalar leftMasks.head! (Label.clause a) + scalar rightMasks.head! (Label.clause a))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma checked : ∀ a : Label, check a = true := by decide +kernel

theorem hf (p : MvPolynomial V K) (hp : p ∈ cnfSystem Pcx106Width.sides) :
    ∃ u v : K, (∀ a ∈ left, eval a p = u) ∧ (∀ a ∈ right, eval a p = v) ∧ eval corner p = u+v := by
  rcases hp with ⟨w,rfl⟩ | ⟨c,hc,rfl⟩
  · have z : ∀ x : K, x*x+x=0 := by decide
    exact ⟨0,0,by intro _ _; simp [z],by intro _ _; simp [z],by simp [z]⟩
  · obtain ⟨b,rfl⟩ := cover c hc
    have h := checked b
    simp only [check,uniform,Bool.and_eq_true, List.all_eq_true,decide_eq_true_eq] at h
    refine ⟨scalar leftMasks.head! (Label.clause b),scalar rightMasks.head! (Label.clause b), ?_,?_,?_⟩
    · intro a ha; obtain ⟨m,hm,rfl⟩ := List.mem_map.mp ha; rw [eval_clause]; exact h.1.1 m hm
    · intro a ha; obtain ⟨m,hm,rfl⟩ := List.mem_map.mp ha; rw [eval_clause]; exact h.1.2 m hm
    · exact (eval_clause middle (Label.clause b)).trans h.2

end Pcx106Axioms

open PEqualNP.ProofComplexity

open Pcx106Data in
lemma larger_lower : ¬ PCRefutable (cnfSystem Pcx106Width.sides) 3 := by
  exact Pcx106Barrier.reject corner left right left0 right0
      (Pcx106Moments.interpolate corner left left0 left1 left2)
      (Pcx106Moments.interpolate corner right right0 right1 right2)
      Pcx106Axioms.hf

end PEqualNP.Outside.L_pcx_105

open PEqualNP.Outside.L_pcx_105 in
theorem PEqualNP.Outside.L_pcx_105 : (∀ Fi : Set (PEqualNP.ProofComplexity.Clause (Fin 8 ⊕ (ℕ × ℕ))), Fi = {Cei | ∃ eei ∈ ([(0, 1), (0, 3), (0, 5), (0, 7), (2, 1), (2, 3), (2, 5), (2, 7), (4, 1), (4, 3), (4, 5), (4, 7), (6, 1), (6, 3), (6, 5), (6, 7)] : List (Fin 8 × Fin 8)), Cei = {(((Sum.inl eei.1) : Fin 8 ⊕ (ℕ × ℕ)), true), (((Sum.inl eei.2) : Fin 8 ⊕ (ℕ × ℕ)), true)}} ∪ {Cai | ∃ iai : Fin 8, iai.val + 1 < 8 ∧ Cai = {(((Sum.inl iai) : Fin 8 ⊕ (ℕ × ℕ)), false), (((Sum.inr (iai.val, 0)) : Fin 8 ⊕ (ℕ × ℕ)), true)}} ∪ {Cbi | ∃ (ibi : Fin 8) (hbi jbi : ℕ), ibi.val = hbi + 1 ∧ ibi.val + 1 < 8 ∧ jbi < 3 ∧ Cbi = {(((Sum.inr (hbi, jbi)) : Fin 8 ⊕ (ℕ × ℕ)), false), (((Sum.inr (ibi.val, jbi)) : Fin 8 ⊕ (ℕ × ℕ)), true)}} ∪ {Cci | ∃ (ici : Fin 8) (hci gci : ℕ), ici.val = hci + 1 ∧ ici.val + 1 < 8 ∧ gci + 1 < 3 ∧ Cci = {(((Sum.inl ici) : Fin 8 ⊕ (ℕ × ℕ)), false), (((Sum.inr (hci, gci)) : Fin 8 ⊕ (ℕ × ℕ)), false), (((Sum.inr (ici.val, gci + 1)) : Fin 8 ⊕ (ℕ × ℕ)), true)}} ∪ {Cdi | ∃ (idi : Fin 8) (hdi : ℕ), idi.val = hdi + 1 ∧ Cdi = {(((Sum.inl idi) : Fin 8 ⊕ (ℕ × ℕ)), false), (((Sum.inr (hdi, 2)) : Fin 8 ⊕ (ℕ × ℕ)), false)}} ∪ {Cfi | ∃ jfi : ℕ, 1 ≤ jfi ∧ jfi < 3 ∧ Cfi = {(((Sum.inr (0, jfi)) : Fin 8 ⊕ (ℕ × ℕ)), false)}} → PEqualNP.ProofComplexity.PCRefutable (PEqualNP.ProofComplexity.cnfSystem Fi) 3 ∧ ¬ PEqualNP.ProofComplexity.PCRefutable (PEqualNP.ProofComplexity.cnfSystem Fi) 2) ∧ (∀ Fs : Set (PEqualNP.ProofComplexity.Clause (Fin 12 ⊕ (ℕ × ℕ))), Fs = {Ces | ∃ ees ∈ ([(0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11)] : List (Fin 12 × Fin 12)), Ces = {(((Sum.inl ees.1) : Fin 12 ⊕ (ℕ × ℕ)), true), (((Sum.inl ees.2) : Fin 12 ⊕ (ℕ × ℕ)), true)}} ∪ {Cas | ∃ ias : Fin 12, ias.val + 1 < 12 ∧ Cas = {(((Sum.inl ias) : Fin 12 ⊕ (ℕ × ℕ)), false), (((Sum.inr (ias.val, 0)) : Fin 12 ⊕ (ℕ × ℕ)), true)}} ∪ {Cbs | ∃ (ibs : Fin 12) (hbs jbs : ℕ), ibs.val = hbs + 1 ∧ ibs.val + 1 < 12 ∧ jbs < 5 ∧ Cbs = {(((Sum.inr (hbs, jbs)) : Fin 12 ⊕ (ℕ × ℕ)), false), (((Sum.inr (ibs.val, jbs)) : Fin 12 ⊕ (ℕ × ℕ)), true)}} ∪ {Ccs | ∃ (ics : Fin 12) (hcs gcs : ℕ), ics.val = hcs + 1 ∧ ics.val + 1 < 12 ∧ gcs + 1 < 5 ∧ Ccs = {(((Sum.inl ics) : Fin 12 ⊕ (ℕ × ℕ)), false), (((Sum.inr (hcs, gcs)) : Fin 12 ⊕ (ℕ × ℕ)), false), (((Sum.inr (ics.val, gcs + 1)) : Fin 12 ⊕ (ℕ × ℕ)), true)}} ∪ {Cds | ∃ (ids : Fin 12) (hds : ℕ), ids.val = hds + 1 ∧ Cds = {(((Sum.inl ids) : Fin 12 ⊕ (ℕ × ℕ)), false), (((Sum.inr (hds, 4)) : Fin 12 ⊕ (ℕ × ℕ)), false)}} ∪ {Cfs | ∃ jfs : ℕ, 1 ≤ jfs ∧ jfs < 5 ∧ Cfs = {(((Sum.inr (0, jfs)) : Fin 12 ⊕ (ℕ × ℕ)), false)}} → (∃ πas, PEqualNP.ProofComplexity.IsRefutation Fs πas ∧ ∀ Das ∈ πas, Das.card ≤ 3) ∧ PEqualNP.ProofComplexity.PCRefutable (PEqualNP.ProofComplexity.cnfSystem Fs) 4 ∧ ¬ PEqualNP.ProofComplexity.PCRefutable (PEqualNP.ProofComplexity.cnfSystem Fs) 3) := by
  constructor
  · intro Fi h
    subst Fi
    exact ⟨Pcx106PC.K4.upper, Pcx106K4Lower.lower⟩
  · intro Fs h
    subst Fs
    obtain ⟨π, href, hw⟩ := Pcx106Width.width_three
    exact ⟨⟨π, href, hw⟩, Pcx106Transfer.resolution_to_PC (w := 3) href hw, larger_lower⟩
