import Mathlib
import PEqualNP.Defs

open PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_222

private abbrev Input (n : ℕ) := Fin n → Bool

private def gate (g : Bool) (a b : Bool) : Bool :=
  if g then a || b else a && b

private def join {n : ℕ} (g : Bool) (a b : DMFormula n) : DMFormula n :=
  if g then .or a b else .and a b

private theorem join_eval {n : ℕ} (g : Bool) (a b : DMFormula n) (x : Input n) :
    (join g a b).eval x = gate g (a.eval x) (b.eval x) := by
  cases g <;> rfl

private theorem join_leaves {n : ℕ} (g : Bool) (a b : DMFormula n) :
    (join g a b).leaves = a.leaves + b.leaves := by
  cases g <;> rfl

private theorem join_induct {n : ℕ} {P : DMFormula n → Prop}
    (lit : ∀ i b, P (.lit i b))
    (bin : ∀ g a b, P a → P b → P (join g a b)) (φ : DMFormula n) : P φ := by
  induction φ with
  | lit i b => exact lit i b
  | and a b ha hb => exact bin false a b ha hb
  | or a b ha hb => exact bin true a b ha hb

private def count {n : ℕ} (D : Finset (Fin n)) : DMFormula n → ℕ
  | .lit v _ => if v ∈ D then 1 else 0
  | .and a b | .or a b => count D a + count D b

private theorem count_join {n : ℕ} (D : Finset (Fin n)) (g : Bool) (a b : DMFormula n) :
    count D (join g a b) = count D a + count D b := by
  cases g <;> rfl

private abbrev outside {n : ℕ} (D : Finset (Fin n)) (φ : DMFormula n) := count Dᶜ φ

private theorem outside_join {n : ℕ} (D : Finset (Fin n)) (g : Bool) (a b : DMFormula n) :
    outside D (join g a b) = outside D a + outside D b :=
  count_join Dᶜ g a b

private theorem count_add_outside {n : ℕ} (D : Finset (Fin n)) (φ : DMFormula n) :
    count D φ + outside D φ = φ.leaves := by
  induction φ using join_induct with
  | lit i b => by_cases h : i ∈ D <;> simp [count, DMFormula.leaves, h]
  | bin g a b ha hb => rw [join_leaves, count_join, outside_join]; omega

private def splice {n : ℕ} (D : Finset (Fin n)) (x y : Input n) : Input n :=
  fun v => if v ∈ D then x v else y v

private theorem eval_agree {n : ℕ} (D : Finset (Fin n)) (φ : DMFormula n) (x y : Input n)
    (h : ∀ v ∈ D, x v = y v) (hφ : outside D φ = 0) : φ.eval x = φ.eval y := by
  induction φ using join_induct with
  | lit i b =>
    have hi : i ∈ D := by by_contra hi; simp [count, hi] at hφ
    simp [DMFormula.eval, h i hi]
  | bin g a b ha hb =>
    rw [outside_join] at hφ
    rw [join_eval, join_eval, ha (by omega), hb (by omega)]

private theorem essential {n : ℕ} {φ : DMFormula n} {v : Fin n}
    {x y : Input n} (ha : ∀ w, w ≠ v → x w = y w)
    (hne : φ.eval x ≠ φ.eval y) : 0 < count {v} φ := by
  by_contra! hz
  apply hne
  refine eval_agree ({v}ᶜ) φ x y (by simpa using ha) ?_
  change count ({v}ᶜ)ᶜ φ = 0
  rw [compl_compl]
  omega

private theorem count_sum {n : ℕ} (D : Finset (Fin n)) (φ : DMFormula n) :
    count D φ = ∑ v ∈ D, count {v} φ := by
  induction φ using join_induct with
  | lit i b => simp [count]
  | bin g a b ha hb => simp only [count_join, Finset.sum_add_distrib, ha, hb]

-- Restrictions simplify constant branches. The weight of a constant is zero.
private abbrev Reduced (n : ℕ) := Bool ⊕ DMFormula n

private def weight {n : ℕ} : Reduced n → ℕ
  | .inl _ => 0
  | .inr φ => φ.leaves

private def value {n : ℕ} (x : Input n) : Reduced n → Bool
  | .inl c => c
  | .inr φ => φ.eval x

private def combine {n : ℕ} (g : Bool) : Reduced n → Reduced n → Reduced n
  | .inl c, b => if c = g then .inl g else b
  | a, .inl c => if c = g then .inl g else a
  | .inr a, .inr b => .inr (join g a b)

private theorem combine_eval {n : ℕ} (g : Bool) (a b : Reduced n) (x : Input n) :
    value x (combine g a b) = gate g (value x a) (value x b) := by
  cases a with
  | inl c => cases g <;> cases c <;> cases b <;> simp [combine, value, gate]
  | inr a =>
    cases b with
    | inl c => cases g <;> cases c <;> simp [combine, value, gate]
    | inr b => exact join_eval _ _ _ _

private theorem combine_le {n : ℕ} (g : Bool) (a b : Reduced n) :
    weight (combine g a b) ≤ weight a + weight b := by
  cases a with
  | inl c => cases c <;> cases g <;> cases b <;> simp [combine, weight]
  | inr a =>
    cases b with
    | inl c => cases c <;> cases g <;> simp [combine, weight]
    | inr b => simp [combine, weight, join_leaves]

private def reduce {n : ℕ} (D : Finset (Fin n)) (x : Input n) : DMFormula n → Reduced n
  | .lit v b => if v ∈ D then .inl ((DMFormula.lit v b).eval x) else .inr (.lit v b)
  | .and a b => combine false (reduce D x a) (reduce D x b)
  | .or a b => combine true (reduce D x a) (reduce D x b)

private theorem reduce_join {n : ℕ} (D : Finset (Fin n)) (x : Input n)
    (g : Bool) (a b : DMFormula n) :
    reduce D x (join g a b) = combine g (reduce D x a) (reduce D x b) := by
  cases g <;> rfl

private theorem reduce_eval {n : ℕ} (D : Finset (Fin n)) (φ : DMFormula n) (x y : Input n) :
    value y (reduce D x φ) = φ.eval (splice D x y) := by
  induction φ using join_induct with
  | lit v b => by_cases h : v ∈ D <;> simp [reduce, splice, DMFormula.eval, h, value]
  | bin g a b ha hb => rw [reduce_join, combine_eval, ha, hb, join_eval]

private theorem reduce_le {n : ℕ} (D : Finset (Fin n)) (φ : DMFormula n) (x : Input n) :
    weight (reduce D x φ) ≤ outside D φ := by
  induction φ using join_induct with
  | lit v b => by_cases h : v ∈ D <;> simp [reduce, count, h, weight, DMFormula.leaves]
  | bin g a b ha hb =>
    rw [reduce_join, outside_join]
    exact (combine_le _ _ _).trans (Nat.add_le_add ha hb)

private theorem reduce_pure {n : ℕ} (D : Finset (Fin n)) (φ : DMFormula n) (x : Input n)
    (h : outside D φ = 0) : reduce D x φ = .inl (φ.eval x) := by
  induction φ using join_induct with
  | lit v b =>
    have hv : v ∈ D := by by_contra hv; simp [count, hv] at h
    simp [reduce, hv]
  | bin g a b ha hb =>
    rw [outside_join] at h
    rw [reduce_join, ha (by omega), hb (by omega), join_eval]
    cases g <;> cases a.eval x <;> cases b.eval x <;> rfl

-- A maximal subtree using only vertices in D can be pruned with its sibling
-- whenever its value absorbs their parent gate.
private def chunks {n : ℕ} (D : Finset (Fin n)) (φ : DMFormula n) : List (DMFormula n) :=
  if outside D φ = 0 then [φ] else
    match φ with
    | .lit _ _ => []
    | .and a b | .or a b => chunks D a ++ chunks D b

private theorem chunks_join {n : ℕ} (D : Finset (Fin n)) (g : Bool) (a b : DMFormula n) :
    chunks D (join g a b) =
      if outside D a + outside D b = 0 then [join g a b] else chunks D a ++ chunks D b := by
  cases g <;> rw [chunks.eq_def, outside_join] <;> rfl

private theorem chunks_pure {n : ℕ} (D : Finset (Fin n)) (φ ψ : DMFormula n)
    (h : ψ ∈ chunks D φ) : outside D ψ = 0 := by
  induction φ using join_induct with
  | lit v b =>
    rw [chunks] at h
    split at h <;> simp_all
  | bin g a b ha hb =>
    rw [chunks_join] at h
    split at h
    · obtain rfl := List.mem_singleton.mp h
      rw [outside_join]; assumption
    · exact (List.mem_append.mp h).elim ha hb

private theorem chunks_sum {n : ℕ} (D : Finset (Fin n)) (φ : DMFormula n) :
    ((chunks D φ).map DMFormula.leaves).sum = count D φ := by
  induction φ using join_induct with
  | lit v b => by_cases h : v ∈ D <;> simp [chunks, count, h, DMFormula.leaves]
  | bin g a b ha hb =>
    rw [chunks_join, count_join]
    split
    · have hab := count_add_outside D (join g a b)
      rw [count_join, outside_join] at hab
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
      omega
    · simp [ha, hb]

private theorem chunks_agree {n : ℕ} (D : Finset (Fin n)) (φ : DMFormula n) (x y : Input n)
    (h : ∀ v ∉ D, x v = y v) (hs : ∀ ψ ∈ chunks D φ, ψ.eval x = ψ.eval y) :
    φ.eval x = φ.eval y := by
  induction φ using join_induct with
  | lit v b =>
    by_cases hv : v ∈ D
    · exact hs _ (by simp [chunks, count, hv])
    · simp [DMFormula.eval, h v hv]
  | bin g a b ha hb =>
    rw [chunks_join] at hs
    split at hs
    · exact hs _ (by simp)
    · rw [join_eval, join_eval, ha (fun ψ hψ => hs ψ (List.mem_append_left _ hψ)),
        hb (fun ψ hψ => hs ψ (List.mem_append_right _ hψ))]

private theorem chunks_fixed {n : ℕ} (D : Finset (Fin n)) (φ : DMFormula n) (x y : Input n)
    (hφ : 0 < outside D φ)
    (hx : outside D φ ≤ weight (reduce D x φ)) (hy : outside D φ ≤ weight (reduce D y φ)) :
    ∀ ψ ∈ chunks D φ, ψ.eval x = ψ.eval y := by
  induction φ using join_induct with
  | lit v b =>
    have hv : v ∉ D := by intro hv; simp [count, hv] at hφ
    simp [chunks, count, hv]
  | bin g a b ha hb =>
    rw [outside_join] at hφ hx hy
    rw [reduce_join] at hx hy
    have hm : outside D a + outside D b ≠ 0 := by omega
    simp only [chunks_join, hm, ite_false]
    have hax := reduce_le D a x
    have hay := reduce_le D a y
    have hbx := reduce_le D b x
    have hby := reduce_le D b y
    have hx' := combine_le g (reduce D x a) (reduce D x b)
    have hy' := combine_le g (reduce D y a) (reduce D y b)
    have pure_left (z : Input n) (hz : outside D a + outside D b ≤
        weight (combine g (reduce D z a) (reduce D z b))) (h : outside D a = 0) :
        a.eval z ≠ g := by
      rw [reduce_pure D a z h] at hz
      intro he
      simp [combine, he, weight] at hz
      omega
    have pure_right (z : Input n) (hz : outside D a + outside D b ≤
        weight (combine g (reduce D z a) (reduce D z b))) (h : outside D b = 0) :
        b.eval z ≠ g := by
      rw [reduce_pure D b z h] at hz
      intro he
      cases he' : reduce D z a <;> cases g <;> cases b.eval z <;>
        simp_all [combine, weight] <;> omega
    intro ψ hψ
    rcases List.mem_append.mp hψ with hψ | hψ
    · by_cases h : outside D a = 0
      · obtain rfl : ψ = a := List.mem_singleton.mp (by simpa [chunks.eq_def, h] using hψ)
        have h₁ := pure_left x hx h
        have h₂ := pure_left y hy h
        exact (Bool.eq_not_of_ne h₁).trans (Bool.eq_not_of_ne h₂).symm
      · exact ha (by omega) (by omega) (by omega) ψ hψ
    · by_cases h : outside D b = 0
      · obtain rfl : ψ = b := List.mem_singleton.mp (by simpa [chunks.eq_def, h] using hψ)
        have h₁ := pure_right x hx h
        have h₂ := pure_right y hy h
        exact (Bool.eq_not_of_ne h₁).trans (Bool.eq_not_of_ne h₂).symm
      · exact hb (by omega) (by omega) (by omega) ψ hψ

private theorem leaves_pos {n : ℕ} (φ : DMFormula n) : 0 < φ.leaves := by
  induction φ using join_induct with
  | lit i b => exact Nat.one_pos
  | bin g a b ha hb => rw [join_leaves]; omega

private theorem eval_occ_agree {n : ℕ} (φ : DMFormula n) (x y : Input n)
    (h : ∀ v, 0 < count {v} φ → x v = y v) : φ.eval x = φ.eval y := by
  induction φ using join_induct with
  | lit v b => simp [DMFormula.eval, h v (by simp [count])]
  | bin g a b ha hb =>
    simp only [count_join] at h
    rw [join_eval, join_eval, ha (fun v hv => h v (by omega)),
      hb (fun v hv => h v (by omega))]

private theorem scope_in {n : ℕ} (D : Finset (Fin n)) (φ : DMFormula n)
    (h : outside D φ = 0) (v : Fin n) (hv : 0 < count {v} φ) : v ∈ D := by
  by_contra hv'
  have hmem : v ∈ Dᶜ := by simpa
  change count Dᶜ φ = 0 at h
  rw [count_sum] at h
  have := Finset.single_le_sum (f := fun v => count {v} φ) (fun _ _ => Nat.zero_le _) hmem
  omega

private theorem read_once_range {n : ℕ} (φ : DMFormula n)
    (h : ∀ v, count {v} φ ≤ 1) (c : Bool) : ∃ x, φ.eval x = c := by
  induction φ using join_induct with
  | lit v b => exact ⟨fun _ => if b then c else !c, by cases b <;> simp [DMFormula.eval]⟩
  | bin g a b ha hb =>
    simp only [count_join] at h
    obtain ⟨x, hx⟩ := ha (fun v => by have := h v; omega)
    obtain ⟨y, hy⟩ := hb (fun v => by have := h v; omega)
    let z : Input n := fun v => if 0 < count {v} a then x v else y v
    have hz₁ : a.eval z = c :=
      (eval_occ_agree a z x (fun v hv => by simp [z, hv])).trans hx
    have hz₂ : b.eval z = c :=
      (eval_occ_agree b z y (fun v hv => by have := h v; simp [z, show ¬0 < count {v} a by omega])).trans hy
    exact ⟨z, by cases g <;> cases c <;> simp [join_eval, hz₁, hz₂, gate]⟩

private theorem chunks_subcount {n : ℕ} (D S : Finset (Fin n)) (φ : DMFormula n) :
    ((chunks D φ).map (count S)).sum ≤ count S φ := by
  induction φ using join_induct with
  | lit v b => rw [chunks.eq_def]; split <;> simp
  | bin g a b ha hb =>
    rw [chunks_join]
    split
    · simp
    · simp only [List.map_append, List.sum_append, count_join]
      omega

private theorem chunk_count_le {n : ℕ} (D S : Finset (Fin n)) (φ ψ : DMFormula n)
    (h : ψ ∈ chunks D φ) : count S ψ ≤ count S φ :=
  (List.le_sum_of_mem (List.mem_map.mpr ⟨ψ, h, rfl⟩)).trans (chunks_subcount D S φ)

private def cofactorNe {n : ℕ} (D : Finset (Fin n)) (φ : DMFormula n) (x y : Input n) : Prop :=
  ∃ z, φ.eval (splice D x z) ≠ φ.eval (splice D y z)

private theorem chunks_dist {n : ℕ} (D : Finset (Fin n)) (φ : DMFormula n) (x y : Input n)
    (h : cofactorNe D φ x y) : ∃ ψ ∈ chunks D φ, ψ.eval x ≠ ψ.eval y := by
  by_contra! h'
  obtain ⟨z, hz⟩ := h
  apply hz
  apply chunks_agree D φ _ _ (by simp +contextual [splice])
  intro ψ hψ
  have hp := chunks_pure D φ ψ hψ
  have hx : ψ.eval (splice D x z) = ψ.eval x :=
    eval_agree D ψ _ _ (fun v hv => by simp [splice, hv]) hp
  have hy : ψ.eval (splice D y z) = ψ.eval y :=
    eval_agree D ψ _ _ (fun v hv => by simp [splice, hv]) hp
  exact hx.trans ((h' ψ hψ).trans hy.symm)

private theorem three_cofactors {n : ℕ} (D : Finset (Fin n)) (φ : DMFormula n) (x y z : Input n)
    (hxy : cofactorNe D φ x y) (hxz : cofactorNe D φ x z) (hyz : cofactorNe D φ y z) :
    2 ≤ (chunks D φ).length := by
  obtain ⟨a, ha, hxy'⟩ := chunks_dist D φ x y hxy
  obtain ⟨b, hb, hxz'⟩ := chunks_dist D φ x z hxz
  obtain ⟨c, hc, hyz'⟩ := chunks_dist D φ y z hyz
  cases h : chunks D φ with
  | nil => simp [h] at ha
  | cons head tail =>
    cases tail with
    | nil =>
      rw [h, List.mem_singleton] at ha hb hc
      subst a b c
      cases hx' : head.eval x <;> cases hy' : head.eval y <;>
        cases hz' : head.eval z <;> simp_all
    | cons head' tail => simp

private theorem count_essential {n : ℕ} (D : Finset (Fin n)) (φ : DMFormula n)
    (h : ∀ v ∈ D, 0 < count {v} φ) : D.card ≤ count D φ := by
  rw [count_sum]
  simpa using (Finset.sum_le_sum (s := D) (fun v hv => h v hv) :
    (∑ _ ∈ D, (1 : ℕ)) ≤ ∑ v ∈ D, count {v} φ)

private theorem count_once {n : ℕ} (D : Finset (Fin n)) (φ : DMFormula n)
    (h : ∀ v ∈ D, 0 < count {v} φ) (hb : count D φ ≤ D.card) {v : Fin n} (hv : v ∈ D) :
    count {v} φ ≤ 1 := by
  have he := count_essential (D.erase v) φ (fun w hw => h w (Finset.mem_of_mem_erase hw))
  rw [count_sum] at hb he
  rw [← Finset.sum_erase_add _ _ hv] at hb
  rw [Finset.card_erase_of_mem hv] at he
  have := Finset.card_pos.mpr ⟨v, hv⟩
  omega

private theorem star_saving {n : ℕ} (D : Finset (Fin n)) (φ : DMFormula n) (v : Fin n)
    (hv : v ∈ D) (h : ∀ w ∈ D, 0 < count {w} φ) (ho : 0 < outside D φ)
    (hthree : ∃ x y z, cofactorNe D φ x y ∧ cofactorNe D φ x z ∧ cofactorNe D φ y z) :
    ∃ x : Input n, x v = false ∧ weight (reduce D x φ) + (D.card + 1) ≤ φ.leaves := by
  have hc := count_essential D φ h
  have ht := count_add_outside D φ
  by_cases hb : D.card < count D φ
  · exact ⟨fun _ => false, rfl, by have := reduce_le D φ (fun _ => false); omega⟩
  push Not at hb
  by_contra! hn
  have hfull (x : Input n) (hx : x v = false) : outside D φ ≤ weight (reduce D x φ) := by
    have := hn x hx
    omega
  have hchunk : ∀ ψ ∈ chunks D φ, 1 ≤ count {v} ψ := by
    intro ψ hp
    by_contra! hz
    have hpure := chunks_pure D φ ψ hp
    have hro (w : Fin n) : count {w} ψ ≤ 1 := by
      by_cases hw : 0 < count {w} ψ
      · exact (chunk_count_le D {w} φ ψ hp).trans (count_once D φ h hb (scope_in D ψ hpure w hw))
      · omega
    obtain ⟨x, hx⟩ := read_once_range ψ hro false
    obtain ⟨y, hy⟩ := read_once_range ψ hro true
    let x' := splice {v} (fun _ => false) x
    let y' := splice {v} (fun _ => false) y
    have hxx := eval_occ_agree ψ x' x (fun w hw => by
      have hne : w ≠ v := by rintro rfl; omega
      simp [x', splice, hne])
    have hyy := eval_occ_agree ψ y' y (fun w hw => by
      have hne : w ≠ v := by rintro rfl; omega
      simp [y', splice, hne])
    have hs := chunks_fixed D φ x' y' ho (hfull x' (by simp [x', splice]))
      (hfull y' (by simp [y', splice])) ψ hp
    rw [hxx, hyy, hx, hy] at hs
    contradiction
  obtain ⟨x, y, z, hxy, hxz, hyz⟩ := hthree
  have hlen := three_cofactors D φ x y z hxy hxz hyz
  have hsum := chunks_subcount D {v} φ
  have hv' := count_once D φ h hb hv
  have hl : (chunks D φ).length ≤ ((chunks D φ).map (count {v})).sum := by
    generalize chunks D φ = l at hchunk ⊢
    induction l with
    | nil => simp
    | cons ψ l ih =>
      have hψ := hchunk ψ (by simp)
      have hl := ih (fun a ha => hchunk a (List.mem_cons_of_mem _ ha))
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      omega
  omega

private def rename {n m : ℕ} (r : Fin n → Fin m) : DMFormula n → DMFormula m
  | .lit v b => .lit (r v) b
  | .and a b => .and (rename r a) (rename r b)
  | .or a b => .or (rename r a) (rename r b)

private theorem rename_eval {n m : ℕ} (r : Fin n → Fin m) (φ : DMFormula n) (x : Input m) :
    (rename r φ).eval x = φ.eval (x ∘ r) := by
  induction φ <;> simp_all [rename, DMFormula.eval, Function.comp_def]

private theorem rename_leaves {n m : ℕ} (r : Fin n → Fin m) (φ : DMFormula n) :
    (rename r φ).leaves = φ.leaves := by
  induction φ <;> simp_all [rename, DMFormula.leaves]

private theorem reduce_scope {n : ℕ} (D : Finset (Fin n)) (x : Input n) (φ ψ : DMFormula n)
    (h : reduce D x φ = .inr ψ) : count D ψ = 0 := by
  induction φ using join_induct generalizing ψ with
  | lit v b =>
    by_cases hv : v ∈ D
    · simp [reduce, hv] at h
    · simp [reduce, hv] at h
      subst ψ
      simp [count, hv]
  | bin g a b ha hb =>
    rw [reduce_join] at h
    cases he₁ : reduce D x a with
    | inl c =>
      cases c <;> cases g <;> simp [combine, he₁] at h
      all_goals exact hb ψ h
    | inr a' =>
      cases he₂ : reduce D x b with
      | inl c =>
        cases c <;> cases g <;> simp [combine, he₁, he₂] at h
        all_goals subst ψ; exact ha _ he₁
      | inr b' =>
        simp [combine, he₁, he₂] at h
        subst ψ
        rw [count_join, ha _ he₁, hb _ he₂]

private def vals (i : ℕ) : Input 3 := fun v => i.testBit v.val

private def table : DMFormula 3 → ℕ
  | .lit v b => if b then (![170, 204, 240] : Fin 3 → ℕ) v else
      (![85, 51, 15] : Fin 3 → ℕ) v
  | .and a b => table a &&& table b
  | .or a b => table a ||| table b

private theorem table_eval (φ : DMFormula 3) (i : ℕ) (hi : i < 8) :
    (table φ).testBit i = φ.eval (vals i) := by
  induction φ with
  | lit v b =>
    have h : ∀ (v : Fin 3) (b : Bool) (i : Fin 8),
        (table (.lit v b)).testBit i.val = (DMFormula.lit v b).eval (vals i.val) := by decide
    exact h v b ⟨i, hi⟩
  | and a b ha hb => simp [table, DMFormula.eval, ha, hb]
  | or a b ha hb => simp [table, DMFormula.eval, ha, hb]

-- Bit i of each set records whether truth table i is attainable at that leaf count.
-- The checks below certify that the sets contain all literals and are closed under gates.
private def tableSet : ℕ → ℕ
  | 1 => 0x1000000001000000004000000000000000000002000000008000000008000
  | 2 => 0x9429400020009001080084010000010000800000802100108009000400029429
  | 3 => 0xfdbfd401b021f1118c09cd050000950180a90000a0b39031888f840d802bfdbf
  | 4 => 0xfdbfd415b123f5398d0bdd2d0200bd0180bd0040b4bbd0b19cafc48da82bfdbf
  | 5 => 0xfffffd7df7bbfdbfdfaffdbfab03ff3dbcffc0d5fdbff5fbfdbfddefbebfffff
  | _ => 0

private def tables (k : ℕ) : List ℕ :=
  (List.range 256).filter (tableSet k).testBit

private theorem tables_iff {k t : ℕ} : t ∈ tables k ↔ t < 256 ∧ (tableSet k).testBit t = true := by
  simp [tables]

private def goodTables (k l : ℕ) : Bool :=
  (tables k).all fun x => (tables l).all fun y =>
    ((tableSet (k + l)).testBit (x &&& y) && (tableSet (k + l)).testBit (x ||| y))

set_option maxHeartbeats 2000000 in
private theorem tables_join {k l x y : ℕ} (hk : 0 < k) (hl : 0 < l) (hs : k + l ≤ 5)
    (hx : x ∈ tables k) (hy : y ∈ tables l) (g : Bool) :
    (if g then x ||| y else x &&& y) ∈ tables (k + l) := by
  have hkl : goodTables k l = true ∨ goodTables l k = true := by
    have h11 : goodTables 1 1 = true := by decide +kernel
    have h12 : goodTables 1 2 = true := by decide +kernel
    have h13 : goodTables 1 3 = true := by decide +kernel
    have h14 : goodTables 1 4 = true := by decide +kernel
    have h22 : goodTables 2 2 = true := by decide +kernel
    have h23 : goodTables 2 3 = true := by decide +kernel
    have hk' : k ≤ 4 := by omega
    have hl' : l ≤ 4 := by omega
    interval_cases k <;> interval_cases l <;> first | omega | tauto
  have hx' := (tables_iff.mp hx).1
  have hy' := (tables_iff.mp hy).1
  apply tables_iff.mpr
  constructor
  · cases g
    · exact Nat.lt_of_le_of_lt Nat.and_le_left hx'
    · exact Nat.or_lt_two_pow (n := 8) hx' hy'
  · rcases hkl with h | h
    · have hh := List.all_eq_true.mp (List.all_eq_true.mp h x hx) y hy
      simp only [Bool.and_eq_true] at hh
      cases g
      · exact hh.1
      · exact hh.2
    · have hh := List.all_eq_true.mp (List.all_eq_true.mp h y hy) x hx
      rw [Nat.add_comm l k, Nat.and_comm y x, Nat.or_comm y x] at hh
      simp only [Bool.and_eq_true] at hh
      cases g
      · exact hh.1
      · exact hh.2

private theorem table_mem (φ : DMFormula 3) (h : φ.leaves ≤ 5) :
    table φ ∈ tables φ.leaves := by
  induction φ using join_induct with
  | lit v b => apply tables_iff.mpr; fin_cases v <;> cases b <;> decide +kernel
  | bin g a b ha hb =>
    rw [join_leaves] at h ⊢
    have h' := tables_join (leaves_pos a) (leaves_pos b) h (ha (by omega)) (hb (by omega)) g
    cases g <;> exact h'

-- The attached triangle has three kinds of cofactors. These six pairs must be separated
-- by the subtrees confined to the triangle.
private def trianglePairs : List (ℕ × ℕ) :=
  [(1, 0), (3, 0), (3, 1), (5, 0), (5, 1), (6, 0)]

private def coversPair (t : ℕ) (p : ℕ × ℕ) : Bool := t.testBit p.1 != t.testBit p.2

private def stable (t : ℕ) : Bool :=
  (t.testBit 0 == t.testBit 2) && (t.testBit 0 == t.testBit 4)

private def mask (t : ℕ) : ℕ :=
    (if coversPair t (1, 0) then 1 else 0) |||
    (if coversPair t (3, 0) then 2 else 0) |||
    (if coversPair t (3, 1) then 4 else 0) |||
    (if coversPair t (5, 0) then 8 else 0) |||
    (if coversPair t (5, 1) then 16 else 0) |||
    (if coversPair t (6, 0) then 32 else 0)

private def stableMasks : ℕ → List ℕ
  | 1 => [11]
  | 2 => [0, 6, 11, 13, 19, 24, 32]
  | 3 => [0, 6, 11, 13, 19, 21, 24, 30, 32, 38, 43, 56]
  | 4 => [0, 6, 11, 13, 19, 21, 24, 30, 32, 38, 43, 45, 51, 56]
  | 5 => [0, 6, 11, 13, 19, 21, 24, 30, 32, 38, 43, 45, 51, 53, 56, 62]
  | _ => []

set_option maxHeartbeats 1500000 in
private theorem stableMasks_mem {k t : ℕ} (hk : k ≤ 5) (ht : t ∈ tables k)
    (hs : stable t = true) : mask t ∈ stableMasks k := by
  have h : ∀ i : Fin 6, (tables i.val).all
      (fun t => !stable t || (stableMasks i.val).contains (mask t)) = true := by decide +kernel
  have hh := List.all_eq_true.mp (h ⟨k, by omega⟩) t ht
  simpa [hs] using hh

private def masksWith (k : ℕ) (ms : List ℕ) : List ℕ :=
  ((stableMasks k).flatMap fun t => ms.map fun m => t ||| m).eraseDups

private def masks0 : List ℕ := [0]
private def masks1 : List ℕ := masksWith 1 masks0
private def masks2 : List ℕ := (masksWith 1 masks1 ++ masksWith 2 masks0).eraseDups
private def masks3 : List ℕ :=
  (masksWith 1 masks2 ++ masksWith 2 masks1 ++ masksWith 3 masks0).eraseDups
private def masks4 : List ℕ :=
  (masksWith 1 masks3 ++ masksWith 2 masks2 ++ masksWith 3 masks1 ++ masksWith 4 masks0).eraseDups
private def masks5 : List ℕ :=
  (masksWith 1 masks4 ++ masksWith 2 masks3 ++ masksWith 3 masks2 ++ masksWith 4 masks1 ++
    masksWith 5 masks0).eraseDups

private def masks : ℕ → List ℕ
  | 0 => masks0
  | 1 => masks1
  | 2 => masks2
  | 3 => masks3
  | 4 => masks4
  | 5 => masks5
  | _ => []

set_option maxRecDepth 4096 in
private theorem masks_step {k l t m : ℕ} (hk : 0 < k) (hs : k + l ≤ 5)
    (ht : t ∈ tables k) (hb : stable t = true) (hm : m ∈ masks l) :
    mask t ||| m ∈ masks (k + l) := by
  have h : mask t ||| m ∈ masksWith k (masks l) := by
    simp only [masksWith, List.mem_eraseDups, List.mem_flatMap, List.mem_map]
    exact ⟨mask t, stableMasks_mem (by omega) ht hb, m, hm, rfl⟩
  have hk' : k ≤ 5 := by omega
  have hl' : l ≤ 5 := by omega
  interval_cases k <;> interval_cases l <;>
    first | omega | (simp only [masks, masks2, masks3, masks4, masks5, List.mem_eraseDups,
      List.mem_append] at h ⊢; tauto)

private def totalMask (fs : List (DMFormula 3)) : ℕ :=
  (fs.map (mask ∘ table)).foldr (· ||| ·) 0

private theorem totalMask_mem (fs : List (DMFormula 3))
    (h : (fs.map DMFormula.leaves).sum ≤ 5) (hs : ∀ φ ∈ fs, stable (table φ) = true) :
    totalMask fs ∈ masks (fs.map DMFormula.leaves).sum := by
  induction fs with
  | nil => exact List.mem_singleton.mpr rfl
  | cons a fs ih =>
    simp only [List.map_cons, List.sum_cons] at h ⊢
    change mask (table a) ||| totalMask fs ∈ _
    exact masks_step (leaves_pos a) h (table_mem a (by omega)) (hs a (by simp))
      (ih (by omega) (fun φ hφ => hs φ (List.mem_cons_of_mem _ hφ)))

private theorem mask_bit (t : ℕ) (i : Fin 6) :
    (mask t).testBit i.val = coversPair t (trianglePairs.get i) := by
  have ht (c : Bool) (m j : ℕ) :
      (if c then m else 0).testBit j = (c && m.testBit j) := by
    cases c <;> simp
  have hb : ∀ j : Fin 6,
      (1 : ℕ).testBit j.val = decide (j = 0) ∧ (2 : ℕ).testBit j.val = decide (j = 1) ∧
      (4 : ℕ).testBit j.val = decide (j = 2) ∧ (8 : ℕ).testBit j.val = decide (j = 3) ∧
      (16 : ℕ).testBit j.val = decide (j = 4) ∧ (32 : ℕ).testBit j.val = decide (j = 5) := by decide
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hb i
  simp only [mask, Nat.testBit_or, ht, h1, h2, h3, h4, h5, h6]
  fin_cases i <;> simp (config := { decide := true }) [trianglePairs]

private theorem totalMask_bit (fs : List (DMFormula 3)) (i : Fin 6)
    (h : ∃ φ ∈ fs, coversPair (table φ) (trianglePairs.get i) = true) :
    (totalMask fs).testBit i.val = true := by
  induction fs with
  | nil => simp at h
  | cons φ fs ih =>
    obtain ⟨ψ, hψ, hbit⟩ := h
    change ((mask (table φ)) ||| totalMask fs).testBit i.val = true
    rw [Nat.testBit_or, mask_bit, Bool.or_eq_true]
    rcases List.mem_cons.mp hψ with hψ | hψ
    · exact .inl (hψ ▸ hbit)
    · exact .inr (ih ⟨ψ, hψ, hbit⟩)

set_option maxHeartbeats 3000000 in
private theorem mask_excludes_full (k : ℕ) (hk : k ≤ 5) (m : ℕ) (h : m ∈ masks k) :
    ¬ ∀ i : Fin 6, m.testBit i.val = true := by
  have hc : ∀ k : Fin 6,
      ((masks k.val).all fun m => !(List.ofFn fun i : Fin 6 => m.testBit i.val).all id) = true := by
    decide +kernel
  have ht := List.all_eq_true.mp (hc ⟨k, by omega⟩) m h
  intro hb
  simp [List.all_eq_true, hb] at ht

private theorem triangle_chunks (fs : List (DMFormula 3))
    (hs : ∀ φ ∈ fs, stable (table φ) = true)
    (hd : ∀ i : Fin 6, ∃ φ ∈ fs, coversPair (table φ) (trianglePairs.get i) = true) :
    6 ≤ (fs.map DMFormula.leaves).sum := by
  by_contra! h
  exact mask_excludes_full _ (by omega) _ (totalMask_mem fs (by omega) hs)
    (fun i => totalMask_bit fs i (hd i))

private theorem majority_leaves (φ : DMFormula 3)
    (h : ∀ i : Fin 8, φ.eval (vals i.val) = (232 : ℕ).testBit i.val) : 5 ≤ φ.leaves := by
  by_contra! hb
  have ht := tables_iff.mp (table_mem φ (by omega))
  have ht' : table φ = 232 := by
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < 8
    · exact (table_eval φ i hi).trans (h ⟨i, hi⟩)
    · have hw : 8 ≤ i := by omega
      rw [Nat.testBit_eq_false_of_lt (n := table φ) (by
        exact ht.1.trans_le (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hw)),
        Nat.testBit_eq_false_of_lt (n := 232) (by
        exact (show 232 < 2 ^ 8 by decide).trans_le (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hw))]
  rw [ht'] at ht
  have he : ∀ k : Fin 5, (tableSet k.val).testBit 232 = false := by decide
  have hh := he ⟨φ.leaves, hb⟩
  rw [hh] at ht
  contradiction


open SimpleGraph

private abbrev Graph (n : ℕ) := SimpleGraph (Fin n)

private def cut {n : ℕ} (G : Graph n) (D : Finset (Fin n)) : Graph n where
  Adj u v := G.Adj u v ∧ u ∉ D ∧ v ∉ D
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

private def cutDec {n : ℕ} (G : Graph n) [DecidableRel G.Adj] (D : Finset (Fin n)) :
    DecidableRel (cut G D).Adj :=
  fun u v => inferInstanceAs (Decidable (G.Adj u v ∧ u ∉ D ∧ v ∉ D))

private theorem cut_adj {n : ℕ} (G : Graph n) (D : Finset (Fin n)) (u v : Fin n) :
    (cut G D).Adj u v ↔ G.Adj u v ∧ u ∉ D ∧ v ∉ D := Iff.rfl

private theorem cut_le {n : ℕ} (G : Graph n) (D : Finset (Fin n)) : cut G D ≤ G :=
  fun _ _ h => h.1

private def funOf {n : ℕ} (G : Graph n) [DecidableRel G.Adj] (x : Input n) : Bool :=
  decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)

private def active {n : ℕ} (G : Graph n) (x : Input n) : Prop :=
  ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true

private theorem funOf_true {n : ℕ} (G : Graph n) [DecidableRel G.Adj] (x : Input n) :
    funOf G x = true ↔ active G x := by simp [funOf, active]

private theorem funOf_false {n : ℕ} (G : Graph n) [DecidableRel G.Adj] (x : Input n) :
    funOf G x = false ↔ ¬active G x := by simp [funOf, active]

private def bits {n : ℕ} (S : Finset (Fin n)) : Input n := fun v => decide (v ∈ S)

private theorem bits_true {n : ℕ} (S : Finset (Fin n)) (v : Fin n) :
    bits S v = true ↔ v ∈ S := by simp [bits]

private theorem splice_bits {n : ℕ} (D X Y : Finset (Fin n)) :
    splice D (bits X) (bits Y) = bits ((X ∩ D) ∪ (Y \ D)) := by
  funext v
  by_cases h : v ∈ D <;> simp [splice, bits, h]

private theorem active_pair {n : ℕ} (G : Graph n) (a b : Fin n) :
    active G (bits {a, b}) ↔ G.Adj a b := by
  simp only [active, bits_true, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨u, v, huv, rfl | rfl, rfl | rfl⟩
    · exact (huv.ne rfl).elim
    · exact huv
    · exact huv.symm
    · exact (huv.ne rfl).elim
  · intro h
    exact ⟨a, b, h, .inl rfl, .inr rfl⟩

private theorem inactive_singleton {n : ℕ} (G : Graph n) (a : Fin n) :
    ¬active G (bits {a}) := by
  rw [show ({a} : Finset (Fin n)) = {a, a} by simp, active_pair]
  exact G.irrefl

private theorem inactive_empty {n : ℕ} (G : Graph n) :
    ¬active G (bits ∅) := by simp [active, bits_true]

private theorem graph_essential {n : ℕ} (G : Graph n) [DecidableRel G.Adj] (φ : DMFormula n)
    (hφ : ∀ x, φ.eval x = funOf G x) {v w : Fin n} (h : G.Adj v w) :
    0 < count {v} φ := by
  apply essential (x := bits {v, w}) (y := bits {w})
  · intro u hu
    simp [bits, hu]
  · rw [hφ, hφ, (funOf_true _ _).2 ((active_pair _ _ _).2 h),
      (funOf_false _ _).2 (inactive_singleton G w)]
    decide

private theorem cut_eval {n : ℕ} (G : Graph n) [DecidableRel G.Adj]
    (D : Finset (Fin n)) (x : Input n) (h : ∀ u v, G.Adj u v →
      u ∈ D → x u = true → v ∈ D ∧ x v = false)
    [DecidableRel (cut G D).Adj] (y : Input n) :
    funOf G (splice D x y) = funOf (cut G D) y := by
  apply Bool.eq_iff_iff.mpr
  rw [funOf_true, funOf_true]
  constructor
  · rintro ⟨u, v, ha, hu, hv⟩
    by_cases h₁ : u ∈ D
    · obtain ⟨h₂, hx⟩ := h u v ha h₁ (by simpa [splice, h₁] using hu)
      simp [splice, h₂, hx] at hv
    by_cases h₂ : v ∈ D
    · exact (h₁ (h v u ha.symm h₂ (by simpa [splice, h₂] using hv)).1).elim
    exact ⟨u, v, ⟨ha, h₁, h₂⟩, by simpa [splice, h₁] using hu,
      by simpa [splice, h₂] using hv⟩
  · rintro ⟨u, v, ⟨ha, h₁, h₂⟩, hu, hv⟩
    exact ⟨u, v, ha, by simpa [splice, h₁] using hu, by simpa [splice, h₂] using hv⟩

private theorem card_cut {n : ℕ} (G : Graph n) [DecidableRel G.Adj] (D : Finset (Fin n))
    [DecidableRel (cut G D).Adj] :
    G.edgeFinset.card = (cut G D).edgeFinset.card +
      (G.edgeFinset \ (cut G D).edgeFinset).card := by
  have hsub : (cut G D).edgeFinset ⊆ G.edgeFinset := by
    intro e
    induction e using Sym2.ind
    simp only [mem_edgeFinset, mem_edgeSet]
    exact fun h => h.1
  have h := Finset.card_sdiff_add_card_eq_card hsub
  omega

private theorem removed_iff {n : ℕ} (G : Graph n) [DecidableRel G.Adj] (D : Finset (Fin n))
    [DecidableRel (cut G D).Adj] (u v : Fin n) :
    s(u, v) ∈ G.edgeFinset \ (cut G D).edgeFinset ↔ G.Adj u v ∧ (u ∈ D ∨ v ∈ D) := by
  simp only [Finset.mem_sdiff, mem_edgeFinset, mem_edgeSet, cut_adj]
  tauto

private theorem cut_lt {n : ℕ} (G : Graph n) [DecidableRel G.Adj] (D : Finset (Fin n))
    [DecidableRel (cut G D).Adj] {u v : Fin n} (h : G.Adj u v) (hu : u ∈ D) :
    (cut G D).edgeFinset.card < G.edgeFinset.card := by
  have hp := Finset.card_pos.mpr ⟨_, (removed_iff G D u v).2 ⟨h, Or.inl hu⟩⟩
  rw [card_cut G D]
  omega

private abbrev Tri {n : ℕ} (G : Graph n) (a b c : Fin n) : Prop :=
  G.Adj a b ∧ G.Adj b c ∧ G.Adj c a

private abbrev OnTri {n : ℕ} (G : Graph n) (a : Fin n) : Prop :=
  ∃ b c, Tri G a b c


private abbrev Good {n : ℕ} (G : Graph n) : Prop :=
  (∀ (u : Fin n) (p : G.Walk u u), p.IsCycle → p.length = 3) ∧
  (∀ a b c d e : Fin n, Tri G a b c → Tri G a d e →
    (b = d ∧ c = e) ∨ (b = e ∧ c = d))

private theorem tri_rotate {n : ℕ} {G : Graph n} {a b c : Fin n} (h : Tri G a b c) :
    Tri G b c a := ⟨h.2.1, h.2.2, h.1⟩

private theorem neighbor_container {n : ℕ} (G : Graph n) [DecidableRel G.Adj]
    {a : Fin n} {N : Finset (Fin n)} (hs : ∀ b ∈ N, G.Adj a b)
    (hc : G.degree a ≤ N.card) : ∀ b, G.Adj a b ↔ b ∈ N := by
  have hsub : N ⊆ G.neighborFinset a := by
    intro v hv
    rw [mem_neighborFinset]
    exact hs v hv
  have he := Finset.eq_of_subset_of_card_le hsub hc
  simp [he]

private theorem degree_le_of_cut {n : ℕ} (G : Graph n) [DecidableRel G.Adj] (D : Finset (Fin n))
    [DecidableRel (cut G D).Adj] (u : Fin n) :
    (cut G D).degree u ≤ G.degree u := by
  apply Finset.card_le_card
  intro w
  simp only [mem_neighborFinset]
  exact fun h => h.1


private theorem good_cut {n : ℕ} (G : Graph n) (D : Finset (Fin n)) (h : Good G) :
    Good (cut G D) := by
  refine ⟨?_, ?_⟩
  · intro u p hp
    simpa using h.1 u (p.mapLe (cut_le G D)) ((Walk.isCycle_mapLe _).2 hp)
  · intro a b c d e ht1 ht2
    exact h.2 a b c d e ⟨ht1.1.1, ht1.2.1.1, ht1.2.2.1⟩ ⟨ht2.1.1, ht2.2.1.1, ht2.2.2.1⟩

private def triRow {n : ℕ} (a b c : Fin n) (i : ℕ) : Input n :=
  match i with
  | 0 => bits ∅
  | 1 => bits {a}
  | 2 => bits {b}
  | 3 => bits {a, b}
  | 4 => bits {c}
  | 5 => bits {a, c}
  | 6 => bits {b, c}
  | _ => bits {a, b, c}

private def triIndex {n : ℕ} (a b : Fin n) (v : Fin n) : Fin 3 :=
  if v = a then 0 else if v = b then 1 else 2

private theorem triRow_rename {n : ℕ} {G : Graph n} {a b c : Fin n} (ht : Tri G a b c)
    (φ : DMFormula n) (hp : outside {a, b, c} φ = 0) (i : Fin 8) :
    (rename (triIndex a b) φ).eval (vals i.val) = φ.eval (triRow a b c i.val) := by
  rw [rename_eval]
  apply eval_agree {a, b, c} _ _ _ _ hp
  intro v hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  have hab := ht.1.ne
  have hbc := ht.2.1.ne
  have hca := ht.2.2.ne
  rcases hv with rfl | rfl | rfl <;> fin_cases i <;>
    simp [vals, triIndex, triRow, bits, hab, hab.symm, hbc, hbc.symm, hca, hca.symm] <;> decide

private theorem tri_eval {n : ℕ} (G : Graph n) [DecidableRel G.Adj] {a b c : Fin n}
    (ht : Tri G a b c) (i : Fin 8) :
    funOf G (triRow a b c i.val) = (232 : ℕ).testBit i.val := by
  fin_cases i
  · exact (funOf_false _ _).2 (inactive_empty G)
  · exact (funOf_false _ _).2 (inactive_singleton G a)
  · exact (funOf_false _ _).2 (inactive_singleton G b)
  · exact (funOf_true _ _).2 ((active_pair _ _ _).2 ht.1)
  · exact (funOf_false _ _).2 (inactive_singleton G c)
  · exact (funOf_true _ _).2 ((active_pair _ _ _).2 ht.2.2.symm)
  · exact (funOf_true _ _).2 ((active_pair _ _ _).2 ht.2.1)
  · exact (funOf_true _ _).2 ⟨a, b, ht.1, by simp [triRow, bits], by simp [triRow, bits]⟩

private theorem restrict_triangle {n : ℕ} (G : Graph n) [DecidableRel G.Adj] {a b c : Fin n}
    (ht : Tri G a b c) (φ : DMFormula n) (hφ : ∀ x, φ.eval x = funOf G x) :
    5 ≤ count {a, b, c} φ := by
  let D : Finset (Fin n) := {a, b, c}
  have he (i : Fin 8) : value (triRow a b c i.val) (reduce Dᶜ (bits ∅) φ) =
      (232 : ℕ).testBit i.val := by
    rw [reduce_eval, hφ]
    convert tri_eval G ht i using 2
    funext v
    by_cases hv : v ∈ D
    · simp [splice, hv]
    · have ha : v ≠ a := by intro h; apply hv; simp [D, h]
      have hb : v ≠ b := by intro h; apply hv; simp [D, h]
      have hc : v ≠ c := by intro h; apply hv; simp [D, h]
      fin_cases i <;> simp [splice, hv, triRow, bits, ha, hb, hc]
  have hb := reduce_le Dᶜ φ (bits ∅)
  change weight (reduce Dᶜ (bits ∅) φ) ≤ count Dᶜᶜ φ at hb
  rw [compl_compl] at hb
  cases h : reduce Dᶜ (bits ∅) φ with
  | inl q =>
    rw [h] at he
    have h0 := he 0
    have h3 := he 3
    change q = false at h0
    change q = true at h3
    rw [h0] at h3
    contradiction
  | inr ψ =>
    have hs := reduce_scope Dᶜ (bits ∅) φ ψ h
    have hm := majority_leaves (rename (triIndex a b) ψ) (fun i => by
      rw [triRow_rename ht ψ hs]
      simpa [h, value] using he i)
    rw [rename_leaves] at hm
    rw [h] at hb
    exact hm.trans hb

private theorem triRow_splice_empty {n : ℕ} (a b c : Fin n) (i : Fin 8) :
    splice {a, b, c} (triRow a b c i.val) (bits ∅) = triRow a b c i.val := by
  funext v
  by_cases hv : v ∈ ({a, b, c} : Finset (Fin n))
  · simp [splice, hv]
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hv
    fin_cases i <;> simp [triRow, splice, bits, hv.1, hv.2.1, hv.2.2]

private theorem attached_triangle_saving {n : ℕ} (G : Graph n) [DecidableRel G.Adj]
    {a b c p : Fin n} (ht : Tri G a b c) (hp : G.Adj a p)
    (hpn : p ∉ ({a, b, c} : Finset (Fin n)))
    (φ : DMFormula n) (hφ : ∀ x, φ.eval x = funOf G x) :
    ∃ i : Fin 8, (i = 0 ∨ i = 2 ∨ i = 4) ∧
      weight (reduce {a, b, c} (triRow a b c i.val) φ) + 6 ≤ φ.leaves := by
  let D : Finset (Fin n) := {a, b, c}
  have ho : 0 < outside D φ := by
    apply (graph_essential G φ hφ hp.symm).trans_le
    change count {p} φ ≤ count Dᶜ φ
    rw [count_sum Dᶜ]
    apply Finset.single_le_sum (f := fun w => count {w} φ) (fun _ _ => Nat.zero_le _)
    simpa
  have hd := count_add_outside D φ
  have hc : 5 ≤ count D φ := restrict_triangle G ht φ hφ
  by_cases hlarge : 6 ≤ count D φ
  · refine ⟨0, .inl rfl, ?_⟩
    change weight (reduce D (triRow a b c 0) φ) + 6 ≤ φ.leaves
    have := reduce_le D φ (triRow a b c 0)
    omega
  by_contra! h
  have hfull (i : Fin 8) (hi : i = 0 ∨ i = 2 ∨ i = 4) :
      outside D φ ≤ weight (reduce D (triRow a b c i.val) φ) := by
    have := h i hi
    change φ.leaves < weight (reduce D (triRow a b c i.val) φ) + 6 at this
    omega
  let fs := (chunks D φ).map (rename (triIndex a b))
  have hstable : ∀ ψ ∈ fs, stable (table ψ) = true := by
    intro ψ hψ
    obtain ⟨ψ', hp', rfl⟩ := List.mem_map.mp hψ
    have hpur := chunks_pure D φ ψ' hp'
    simp only [stable, Bool.and_eq_true, beq_iff_eq]
    have hbit (i : Fin 8) : (table (rename (triIndex a b) ψ')).testBit i.val =
        ψ'.eval (triRow a b c i.val) := by
      rw [table_eval _ _ i.isLt, triRow_rename ht ψ' hpur]
    constructor
    · change (table (rename (triIndex a b) ψ')).testBit (0 : Fin 8).val =
        (table (rename (triIndex a b) ψ')).testBit (2 : Fin 8).val
      rw [hbit 0, hbit 2]
      exact chunks_fixed D φ _ _ ho (hfull 0 (.inl rfl)) (hfull 2 (.inr (.inl rfl))) ψ' hp'
    · change (table (rename (triIndex a b) ψ')).testBit (0 : Fin 8).val =
        (table (rename (triIndex a b) ψ')).testBit (4 : Fin 8).val
      rw [hbit 0, hbit 4]
      exact chunks_fixed D φ _ _ ho (hfull 0 (.inl rfl)) (hfull 4 (.inr (.inr rfl))) ψ' hp'
  have hdiff (i j : Fin 8) (hj : (232 : ℕ).testBit i.val ≠ (232 : ℕ).testBit j.val) :
      cofactorNe D φ (triRow a b c i.val) (triRow a b c j.val) := by
    refine ⟨bits ∅, ?_⟩
    simpa only [D, triRow_splice_empty, hφ, tri_eval G ht] using hj
  have hspecial : cofactorNe D φ (triRow a b c 1) (triRow a b c 0) := by
    refine ⟨bits {p}, ?_⟩
    have hL : splice D (triRow a b c 1) (bits {p}) = bits {a, p} := by
      change splice D (bits {a}) (bits {p}) = _
      rw [splice_bits]
      congr 1
      ext v
      simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff,
        Finset.mem_insert, Finset.mem_singleton]
      have ha : a ∈ D := by simp [D]
      grind
    have hR : splice D (triRow a b c 0) (bits {p}) = bits {p} := by
      change splice D (bits ∅) (bits {p}) = _
      rw [splice_bits]
      congr 1
      ext w
      simp only [Finset.empty_inter, Finset.empty_union, Finset.mem_sdiff, Finset.mem_singleton]
      exact ⟨And.left, fun hw => ⟨hw, hw.symm ▸ hpn⟩⟩
    rw [hL, hR, hφ, hφ, (funOf_true _ _).2 ((active_pair _ _ _).2 hp),
      (funOf_false _ _).2 (inactive_singleton G p)]
    decide
  have hsep : ∀ i : Fin 6, ∃ ψ ∈ fs, coversPair (table ψ) (trianglePairs.get i) = true := by
    have hpair (i j : Fin 8) (hij : cofactorNe D φ (triRow a b c i.val) (triRow a b c j.val)) :
        ∃ ψ ∈ fs, coversPair (table ψ) (i.val, j.val) = true := by
      obtain ⟨ψ, hψ, hne⟩ := chunks_dist D φ _ _ hij
      refine ⟨rename (triIndex a b) ψ, List.mem_map.mpr ⟨ψ, hψ, rfl⟩, ?_⟩
      have hpur := chunks_pure D φ ψ hψ
      simp only [coversPair, bne_iff_ne]
      rw [table_eval _ _ i.isLt, table_eval _ _ j.isLt, triRow_rename ht ψ hpur,
        triRow_rename ht ψ hpur]
      exact hne
    intro i
    fin_cases i
    · exact hpair 1 0 hspecial
    · exact hpair 3 0 (hdiff 3 0 (by decide))
    · exact hpair 3 1 (hdiff 3 1 (by decide))
    · exact hpair 5 0 (hdiff 5 0 (by decide))
    · exact hpair 5 1 (hdiff 5 1 (by decide))
    · exact hpair 6 0 (hdiff 6 0 (by decide))
  have hm := triangle_chunks fs hstable hsep
  unfold fs at hm
  simp only [List.map_map, Function.comp_def, rename_leaves, chunks_sum] at hm
  omega

private theorem tri_flip {n : ℕ} {G : Graph n} {a b c : Fin n} (h : Tri G a b c) :
    Tri G a c b := ⟨h.2.2.symm, h.2.1.symm, h.1.symm⟩

private theorem two_neighbors {n : ℕ} (G : Graph n) [DecidableRel G.Adj] {a b c : Fin n}
    (hab : G.Adj a b) (hac : G.Adj a c) (hne : b ≠ c) : 2 ≤ G.degree a := by
  have hsub : ({b, c} : Finset (Fin n)) ⊆ G.neighborFinset a := by
    intro w hw
    simp only [mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton] at *
    rcases hw with rfl | rfl <;> assumption
  calc
    2 = ({b, c} : Finset (Fin n)).card := by simp [hne]
    _ ≤ G.degree a := Finset.card_le_card hsub

private theorem degree_two_neighbors {n : ℕ} {G : Graph n} [DecidableRel G.Adj]
    {a b c : Fin n} (ht : Tri G a b c) (hd : G.degree a = 2) (w : Fin n) :
    G.Adj a w ↔ w = b ∨ w = c := by
  have hne := ht.2.1.ne
  have h₀ : ∀ u ∈ ({b, c} : Finset (Fin n)), G.Adj a u := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro u (rfl | rfl)
    · exact ht.1
    · exact ht.2.2.symm
  simpa only [Finset.mem_insert, Finset.mem_singleton] using
    neighbor_container G h₀ (by simp [hne, hd]) w

private theorem degree_three_neighbors {n : ℕ} {G : Graph n} [DecidableRel G.Adj]
    {a b c p : Fin n} (ht : Tri G a b c) (hd : G.degree a ≤ 3)
    (hp : G.Adj a p) (hpb : p ≠ b) (hpc : p ≠ c) (w : Fin n) :
    G.Adj a w ↔ w = b ∨ w = c ∨ w = p := by
  have hne := ht.2.1.ne
  have h₀ : ∀ u ∈ ({b, c, p} : Finset (Fin n)), G.Adj a u := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro u (rfl | rfl | rfl)
    · exact ht.1
    · exact ht.2.2.symm
    · exact hp
  simpa only [Finset.mem_insert, Finset.mem_singleton] using
    neighbor_container G h₀ (by simpa [hne, hpb.symm, hpc.symm]) w
private theorem triangle_of_three_cycle {n : ℕ} {G : Graph n} {u : Fin n} (p : G.Walk u u)
    (h : p.length = 3) : ∃ v w, Tri G u v w := by
  cases p with
  | nil => simp at h
  | cons huv p =>
    cases p with
    | nil => simp at h
    | cons hvw p =>
      cases p with
      | nil => simp at h
      | cons hwx p =>
        cases p with
        | nil => exact ⟨_, _, huv, hvw, hwx⟩
        | cons hadj p => simp at h

private theorem path_start_leaf {n : ℕ} {G : Graph n} (hG : G.IsAcyclic)
    {u v : Fin n} {p : G.Walk u v} (hp : p.IsPath)
    (hmax : ∀ (a b : Fin n) (q : G.Walk a b), q.IsPath → q.length ≤ p.length)
    {w : Fin n} (hw : G.Adj u w) : w = p.snd := by
  apply hG.eq_snd_of_adj_start hp hw
  by_contra hn
  have hh := hmax _ _ (p.cons hw.symm) (hp.cons hn)
  simp at hh

private theorem peripheral_star {n : ℕ} (G : Graph n) (h : G.IsAcyclic)
    (he : ∃ u v, G.Adj u v) :
    ∃ u v p, G.Adj u v ∧
      (∀ w, G.Adj u w → w = v) ∧
      (∀ w, G.Adj v w → (∀ z, G.Adj w z → z = v) ∨ w = p) := by
  obtain ⟨a, b, hab⟩ := he
  letI : Nonempty (Fin n) := ⟨a⟩
  obtain ⟨u, t, q, hq, hmax⟩ := Walk.exists_isPath_forall_isPath_length_le_length G
  have hlen := hmax a b hab.toWalk hab.isPath_toWalk
  cases q with
  | nil => simp at hlen
  | cons huv q =>
    refine ⟨u, _, q.snd, huv, ?_, ?_⟩
    · intro w hw
      simpa only [Walk.snd_cons] using path_start_leaf h hq hmax hw
    · intro w hvw
      by_cases hw : w = q.snd
      · exact .inr hw
      · left
        have htail := hq.of_cons
        have hn : w ∉ q.support := fun hm => hw (h.eq_snd_of_adj_start htail hvw hm)
        have hp : (q.cons hvw.symm).IsPath := htail.cons hn
        have hm (a b : Fin n) (r : G.Walk a b) (hr : r.IsPath) :
            r.length ≤ (q.cons hvw.symm).length := by
          simpa using hmax a b r hr
        intro z hz
        simpa only [Walk.snd_cons] using path_start_leaf h hp hm hz

private theorem no_four_cycle {n : ℕ} {G : Graph n} (h : Good G) {u v w x : Fin n}
    (huv : G.Adj u v) (hvw : G.Adj v w) (hwx : G.Adj w x) (hxu : G.Adj x u)
    (huw : u ≠ w) (hvx : v ≠ x) : False := by
  let p : G.Walk u u := .cons huv (.cons hvw (.cons hwx (.cons hxu .nil)))
  have hp : p.IsCycle := by
    rw [Walk.isCycle_iff_isPath_tail_and_le_length]
    have huv' := huv.ne
    have hvw' := hvw.ne
    have hwx' := hwx.ne
    have hxu' := hxu.ne
    simp [p, Walk.isPath_def, huv', hvw', hwx', hxu', huw, hvx,
      huv'.symm, hvw'.symm, hwx'.symm, hxu'.symm, huw.symm, hvx.symm]
  have hh := h.1 u p hp
  change 4 = 3 at hh
  omega

private theorem tri_swap12 {n : ℕ} {G : Graph n} {a b c : Fin n} (h : Tri G a b c) :
    Tri G b a c := tri_flip (tri_rotate h)

private def sameClass {n : ℕ} (G : Graph n) (u v : Fin n) : Prop :=
  u = v ∨ ∃ z, Tri G u v z

private theorem sameClass_refl {n : ℕ} (G : Graph n) (u : Fin n) : sameClass G u u :=
  .inl rfl

private theorem sameClass_symm {n : ℕ} {G : Graph n} {u v : Fin n} (h : sameClass G u v) :
    sameClass G v u := by
  rcases h with rfl | ⟨z, ht⟩
  · exact .inl rfl
  · exact .inr ⟨z, tri_swap12 ht⟩

private theorem sameClass_trans {n : ℕ} {G : Graph n} (hg : Good G) {u v w : Fin n}
    (h1 : sameClass G u v) (h2 : sameClass G v w) : sameClass G u w := by
  rcases h1 with rfl | ⟨z1, ht1⟩
  · exact h2
  rcases h2 with rfl | ⟨z2, ht2⟩
  · exact .inr ⟨z1, ht1⟩
  have ht1' : Tri G v u z1 := tri_swap12 ht1
  rcases hg.2 v u z1 w z2 ht1' ht2 with ⟨rfl, _⟩ | ⟨rfl, rfl⟩
  · exact .inl rfl
  · exact .inr ⟨v, tri_rotate (tri_flip ht2)⟩

private theorem sameClass_adj_or_eq {n : ℕ} {G : Graph n} {u v : Fin n} (h : sameClass G u v) :
    u = v ∨ G.Adj u v :=
  h.imp_right fun ⟨_, ht⟩ => ht.1

private theorem unique_bridge {n : ℕ} {G : Graph n} (hg : Good G) {u1 v1 u2 v2 : Fin n}
    (h1 : G.Adj u1 v1) (h2 : G.Adj u2 v2)
    (hu : sameClass G u1 u2) (hv : sameClass G v1 v2)
    (hdiff : ¬ sameClass G u1 v1) : u1 = u2 ∧ v1 = v2 := by
  rcases sameClass_adj_or_eq hu with rfl | hu'
  · rcases sameClass_adj_or_eq hv with rfl | hv'
    · exact ⟨rfl, rfl⟩
    · exact (hdiff (.inr ⟨v2, h1, hv', h2.symm⟩)).elim
  · rcases sameClass_adj_or_eq hv with rfl | hv'
    · exact (hdiff (.inr ⟨u2, h1, h2.symm, hu'.symm⟩)).elim
    · have hu1v2 : u1 ≠ v2 := fun heq => hdiff (heq ▸ sameClass_symm hv)
      have hv1u2 : v1 ≠ u2 := fun heq => hdiff (heq ▸ hu)
      exact (no_four_cycle hg h1 hv' h2.symm hu'.symm hu1v2 hv1u2).elim

private theorem structural222 {n : ℕ} (G : Graph n) [DecidableRel G.Adj] (hg : Good G)
    (he : ∃ u v, G.Adj u v) :
    (∃ u1 u2 v, G.Adj u1 v ∧ G.Adj u2 v ∧ u1 ≠ u2 ∧
      (∀ w, G.Adj u1 w → w = v) ∧ (∀ w, G.Adj u2 w → w = v)) ∨
    (∃ u v b c, G.Adj u v ∧ (∀ w, G.Adj u w → w = v) ∧
      Tri G v b c ∧ G.degree c = 2) ∨
    (∃ a b c, Tri G a b c ∧ G.degree b = 2 ∧ G.degree c = 2 ∧ G.degree a ≤ 3) ∨
    (∃ u v p, G.Adj u v ∧ (∀ w, G.Adj u w → w = v) ∧
      (∀ w, G.Adj v w → (∀ z, G.Adj w z → z = v) ∨ w = p)) ∨
    (∃ a b c ub uc, Tri G a b c ∧ G.Adj b ub ∧ G.Adj c uc ∧
      (∀ w, G.Adj ub w → w = b) ∧ (∀ w, G.Adj uc w → w = c) ∧
      G.degree b = 3 ∧ G.degree c = 3) := by
  classical
  let triClass : Fin n → Finset (Fin n) := fun u => Finset.univ.filter (sameClass G u)
  have hmem (u v : Fin n) : v ∈ triClass u ↔ sameClass G u v := by simp [triClass]
  have hclass_eq {u v : Fin n} (h : sameClass G u v) : triClass u = triClass v := by
    ext w
    rw [hmem, hmem]
    exact ⟨fun huw => sameClass_trans hg (sameClass_symm h) huw,
      fun hvw => sameClass_trans hg h hvw⟩
  let rep : Fin n → Fin n := fun u => (triClass u).min' ⟨u, (hmem u u).2 (sameClass_refl G u)⟩
  have hrep_same (u : Fin n) : sameClass G u (rep u) := (hmem u _).1 (Finset.min'_mem _ _)
  have hrep_iff (u v : Fin n) : rep u = rep v ↔ sameClass G u v := by
    constructor
    · intro h
      exact sameClass_trans hg (hrep_same u) (h ▸ sameClass_symm (hrep_same v))
    · intro h
      simp only [rep]
      congr 1
      exact hclass_eq h
  have hrep_idem (u : Fin n) : rep (rep u) = rep u :=
    (hrep_iff _ _).2 (sameClass_symm (hrep_same u))
  let H : Graph n := {
    Adj := fun x y => x ≠ y ∧ ∃ u v, rep u = x ∧ rep v = y ∧ G.Adj u v
    symm := ⟨fun _ _ ⟨hne, u, v, hu, hv, hadj⟩ => ⟨hne.symm, v, u, hv, hu, hadj.symm⟩⟩
    loopless := ⟨fun _ h => h.1 rfl⟩
  }
  have hbridge {u1 v1 u2 v2 : Fin n} (h1 : G.Adj u1 v1) (h2 : G.Adj u2 v2)
      (hu : rep u1 = rep u2) (hv : rep v1 = rep v2) (hne : rep u1 ≠ rep v1) :
      u1 = u2 ∧ v1 = v2 :=
    unique_bridge hg h1 h2 ((hrep_iff _ _).1 hu) ((hrep_iff _ _).1 hv)
      (fun hs => hne ((hrep_iff _ _).2 hs))
  have hlift : ∀ {u v : Fin n} (r : H.Walk u v), r.IsPath → ∀ a : Fin n, rep a = u →
      ∃ b : Fin n, rep b = v ∧ ∃ q : G.Walk a b,
        r.length ≤ q.length ∧ q.IsPath ∧
        (∀ w ∈ q.support, rep w ∈ r.support) ∧
        (∀ w ∈ q.support.dropLast, rep w ∈ r.support.dropLast) := by
    intro u v r
    induction r with
    | nil =>
      intro _ a ha
      exact ⟨a, ha, .nil, le_rfl, Walk.IsPath.nil, by simp [ha], by simp⟩
    | @cons u u' v h1 r1 ih =>
      intro hr a ha
      have hr1 : r1.IsPath := hr.of_cons
      have hu_not : u ∉ r1.support := by
        have hnd := hr.support_nodup
        rw [Walk.support_cons, List.nodup_cons] at hnd
        exact hnd.1
      obtain ⟨_, c, d, hc, hd, hcd⟩ := h1
      obtain ⟨b, hb, q1, hlen1, hpath1, hsup1, hdl1⟩ := ih hr1 d hd
      have hne_q1 : q1.support ≠ [] := by simp
      have hne_r1 : r1.support ≠ [] := by simp
      have hnot_in_q1 (z : Fin n) (hz : rep z = u) : z ∉ q1.support :=
        fun hm => hu_not (hz ▸ hsup1 z hm)
      by_cases hac : a = c
      · subst hac
        refine ⟨b, hb, .cons hcd q1, by simp; omega, hpath1.cons (hnot_in_q1 a ha), ?_, ?_⟩
        · intro w hw
          rw [Walk.support_cons, List.mem_cons] at hw
          rw [Walk.support_cons, List.mem_cons]
          rcases hw with rfl | hw
          · exact .inl ha
          · exact .inr (hsup1 w hw)
        · intro w hw
          rw [Walk.support_cons, List.dropLast_cons_of_ne_nil hne_q1, List.mem_cons] at hw
          rw [Walk.support_cons, List.dropLast_cons_of_ne_nil hne_r1, List.mem_cons]
          rcases hw with rfl | hw
          · exact .inl ha
          · exact .inr (hdl1 w hw)
      · have hadj_ac : G.Adj a c :=
          (sameClass_adj_or_eq ((hrep_iff a c).1 (ha.trans hc.symm))).resolve_left hac
        have hq' : (Walk.cons hcd q1).IsPath := hpath1.cons (hnot_in_q1 c hc)
        have ha_not : a ∉ (Walk.cons hcd q1).support := by
          rw [Walk.support_cons, List.mem_cons, not_or]
          exact ⟨hac, hnot_in_q1 a ha⟩
        refine ⟨b, hb, .cons hadj_ac (.cons hcd q1), by simp; omega, hq'.cons ha_not, ?_, ?_⟩
        · intro w hw
          rw [Walk.support_cons, Walk.support_cons, List.mem_cons, List.mem_cons] at hw
          rw [Walk.support_cons, List.mem_cons]
          rcases hw with rfl | rfl | hw
          · exact .inl ha
          · exact .inl hc
          · exact .inr (hsup1 w hw)
        · intro w hw
          have hne_c : (Walk.cons hcd q1).support ≠ [] := by simp
          rw [Walk.support_cons, List.dropLast_cons_of_ne_nil hne_c,
            Walk.support_cons, List.dropLast_cons_of_ne_nil hne_q1,
            List.mem_cons, List.mem_cons] at hw
          rw [Walk.support_cons, List.dropLast_cons_of_ne_nil hne_r1, List.mem_cons]
          rcases hw with rfl | rfl | hw
          · exact .inl ha
          · exact .inl hc
          · exact .inr (hdl1 w hw)
  have hacy : H.IsAcyclic := by
    intro x p hp
    cases p with
    | nil => exact hp.ne_nil rfl
    | @cons _ y _ hxy p' =>
      have hlen : 3 ≤ (Walk.cons hxy p').length := hp.three_le_length
      have hp'_path : p'.IsPath := by simpa using (Walk.isCycle_iff_isPath_tail_and_le_length.1 hp).1
      obtain ⟨hxy_ne, a0, b0, ha0, hb0, ha0b0⟩ := hxy
      obtain ⟨b1, hb1, q', hqlen, hqpath, _, hqdl⟩ := hlift p' hp'_path b0 hb0
      have hx_not_dl : x ∉ p'.support.dropLast := by
        have hnd := hp'_path.support_nodup
        have hcat : p'.support.dropLast ++ [x] = p'.support := by
          have hlast := Walk.getLast_support p'
          have hne : p'.support ≠ [] := by simp
          simpa [hlast] using List.dropLast_append_getLast hne
        rw [← hcat, List.nodup_append] at hnd
        intro hx
        exact hnd.2.2 x hx x (by simp) rfl
      by_cases hba : b1 = a0
      · subst b1
        let q : G.Walk a0 a0 := .cons ha0b0 q'
        have hqcyc : q.IsCycle := by
          rw [Walk.isCycle_iff_isPath_tail_and_le_length]
          exact ⟨by simpa [q] using hqpath, by simp [q] at hlen ⊢; omega⟩
        have h3 := hg.1 a0 q hqcyc
        cases q' with
        | nil => simp [q] at h3
        | cons h1 q2 =>
          cases q2 with
          | nil => simp [q] at h3
          | cons h2 q3 =>
            cases q3 with
            | nil =>
              have hsame : sameClass G a0 b0 := .inr ⟨_, ha0b0, h1, h2⟩
              exact hxy_ne (ha0.symm.trans (((hrep_iff _ _).2 hsame).trans hb0))
            | cons _ _ => simp [q] at h3
      · have hba_adj : G.Adj b1 a0 :=
          (sameClass_adj_or_eq ((hrep_iff b1 a0).1 (hb1.trans ha0.symm))).resolve_left hba
        have ha0_not : a0 ∉ q'.support := by
          intro hm
          have hcat : q'.support.dropLast ++ [b1] = q'.support := by
            have hlast := Walk.getLast_support q'
            have hne : q'.support ≠ [] := by simp
            simpa [hlast] using List.dropLast_append_getLast hne
          rw [← hcat, List.mem_append, List.mem_singleton] at hm
          rcases hm with hdl | rfl
          · exact hx_not_dl (ha0 ▸ hqdl a0 hdl)
          · exact hba rfl
        let q'' : G.Walk b0 a0 := q'.concat hba_adj
        have hq''_path : q''.IsPath := hqpath.concat ha0_not hba_adj
        let q : G.Walk a0 a0 := .cons ha0b0 q''
        have hqcyc : q.IsCycle := by
          rw [Walk.isCycle_iff_isPath_tail_and_le_length]
          exact ⟨by simpa [q] using hq''_path, by simp [q, q''] at hlen ⊢; omega⟩
        have h3 := hg.1 a0 q hqcyc
        simp [q, q''] at h3 hlen
        omega
  by_cases hH : ∃ x y, H.Adj x y
  · obtain ⟨x, y, pH, hxy, hx_leaf, hy_star⟩ := peripheral_star H hacy hH
    have hleaf_case {z : Fin n} (hzy : H.Adj z y) (hz : ∀ w, H.Adj z w → w = y) :
        (∃ a b c, Tri G a b c ∧ G.degree b = 2 ∧ G.degree c = 2 ∧ G.degree a ≤ 3) ∨
        (∃ v, rep v = y ∧ G.Adj z v ∧ ¬ OnTri G z ∧ ∀ w, G.Adj z w → w = v) := by
      obtain ⟨hzy_ne, u, v, hu, hv, huv⟩ := hzy
      by_cases hot : OnTri G u
      · left
        obtain ⟨b, c, ht⟩ := hot
        have hrb : rep b = z := ((hrep_iff b u).2 (.inr ⟨c, tri_swap12 ht⟩)).trans hu
        have hrc : rep c = z := ((hrep_iff c u).2 (.inr ⟨b, tri_rotate (tri_rotate ht)⟩)).trans hu
        have hout {r w : Fin n} (hr : rep r = z) (hrw : G.Adj r w) (hdiff : rep w ≠ z) :
            r = u ∧ w = v := by
          have hzw : H.Adj z (rep w) := ⟨hdiff.symm, r, w, hr, rfl, hrw⟩
          have hrwy : rep w = y := hz (rep w) hzw
          exact hbridge hrw huv (hr.trans hu.symm) (hrwy.trans hv.symm) (hr ▸ hdiff.symm)
        have hb_deg : G.degree b = 2 := by
          have hsub : G.neighborFinset b ⊆ ({c, u} : Finset (Fin n)) := by
            intro w hw
            rw [mem_neighborFinset] at hw
            by_cases hrw : rep w = z
            · rcases (hrep_iff u w).1 (hu.trans hrw.symm) with rfl | ⟨q, ht'⟩
              · simp
              · rcases hg.2 u b c w q ht ht' with ⟨rfl, _⟩ | ⟨_, rfl⟩
                · exact (hw.ne rfl).elim
                · simp
            · exact (ht.1.ne (hout hrb hw hrw).1.symm).elim
          have hge := two_neighbors G ht.2.1 ht.1.symm ht.2.2.ne
          have hle : G.degree b ≤ 2 := (Finset.card_le_card hsub).trans (by simp [ht.2.2.ne])
          omega
        have hc_deg : G.degree c = 2 := by
          have hsub : G.neighborFinset c ⊆ ({u, b} : Finset (Fin n)) := by
            intro w hw
            rw [mem_neighborFinset] at hw
            by_cases hrw : rep w = z
            · rcases (hrep_iff u w).1 (hu.trans hrw.symm) with rfl | ⟨q, ht'⟩
              · simp
              · rcases hg.2 u b c w q ht ht' with ⟨rfl, _⟩ | ⟨_, rfl⟩
                · simp
                · exact (hw.ne rfl).elim
            · exact (ht.2.2.ne (hout hrc hw hrw).1).elim
          have hge := two_neighbors G ht.2.2 ht.2.1.symm ht.1.ne
          have hle : G.degree c ≤ 2 := (Finset.card_le_card hsub).trans (by simp [ht.1.ne])
          omega
        have hu_deg : G.degree u ≤ 3 := by
          have hsub : G.neighborFinset u ⊆ ({b, c, v} : Finset (Fin n)) := by
            intro w hw
            rw [mem_neighborFinset] at hw
            by_cases hrw : rep w = z
            · rcases (hrep_iff u w).1 (hu.trans hrw.symm) with rfl | ⟨q, ht'⟩
              · exact (hw.ne rfl).elim
              · rcases hg.2 u b c w q ht ht' with ⟨rfl, _⟩ | ⟨_, rfl⟩ <;> simp
            · rw [(hout hu hw hrw).2]; simp
          calc G.degree u ≤ ({b, c, v} : Finset (Fin n)).card := Finset.card_le_card hsub
            _ ≤ 3 := by
              have h1 := Finset.card_insert_le b ({c, v} : Finset (Fin n))
              have h2 := Finset.card_insert_le c ({v} : Finset (Fin n))
              simp only [Finset.card_singleton] at h2
              omega
        exact ⟨u, b, c, ht, hb_deg, hc_deg, hu_deg⟩
      · right
        have huz : u = z := by
          rcases (hrep_iff u z).1 (hu.trans (by rw [← hu, hrep_idem])) with rfl | ⟨q, ht⟩
          · rfl
          · exact (hot ⟨z, q, ht⟩).elim
        subst u
        refine ⟨v, hv, huv, hot, fun w huw => ?_⟩
        have hrw : rep w ≠ z := by
          intro heq
          rcases (hrep_iff z w).1 (hu.trans heq.symm) with rfl | ⟨q, ht⟩
          · exact huw.ne rfl
          · exact hot ⟨w, q, ht⟩
        have hzw : H.Adj z (rep w) := ⟨hrw.symm, z, w, hu, rfl, huw⟩
        have hrwy : rep w = y := hz (rep w) hzw
        exact (hbridge huw huv rfl (hrwy.trans hv.symm) (by rw [hu]; exact hrw.symm)).2
    rcases hleaf_case hxy hx_leaf with htri | ⟨v, hvy, hxv, _, hx_adj⟩
    · exact .inr (.inr (.inl htri))
    by_cases hvt : OnTri G v
    · obtain ⟨b, c, ht⟩ := hvt
      have hrb : rep b = y := ((hrep_iff b v).2 (.inr ⟨c, tri_swap12 ht⟩)).trans hvy
      have hrc : rep c = y := ((hrep_iff c v).2 (.inr ⟨b, tri_rotate (tri_rotate ht)⟩)).trans hvy
      have hclass_y (w : Fin n) : rep w = y ↔ w = v ∨ w = b ∨ w = c := by
        constructor
        · intro hw
          rcases (hrep_iff v w).1 (hvy.trans hw.symm) with rfl | ⟨q, ht'⟩
          · exact .inl rfl
          · rcases hg.2 v b c w q ht ht' with ⟨rfl, _⟩ | ⟨_, rfl⟩
            · exact .inr (.inl rfl)
            · exact .inr (.inr rfl)
        · rintro (rfl | rfl | rfl) <;> assumption
      -- Check if Case 3 holds on any H-leaf neighbor of y
      by_cases hcase3 : ∃ a1 b1 c1, Tri G a1 b1 c1 ∧ G.degree b1 = 2 ∧ G.degree c1 = 2 ∧ G.degree a1 ≤ 3
      · exact .inr (.inr (.inl hcase3))
      -- Every edge leaving {v, b, c} to a class != pH goes to a leaf of G attached to that vertex
      have hleaf_out {r w : Fin n} (hr : rep r = y) (hrw : G.Adj r w) (hwy : rep w ≠ y)
          (hwp : rep w ≠ pH) : ∀ z, G.Adj w z → z = r := by
        have hyw : H.Adj y (rep w) := ⟨hwy.symm, r, w, hr, rfl, hrw⟩
        have hleaf_w : ∀ q, H.Adj (rep w) q → q = y := (hy_star (rep w) hyw).resolve_right hwp
        rcases hleaf_case hyw.symm hleaf_w with h3 | ⟨v', hv', hwv', hnt, hw_adj⟩
        · exact (hcase3 h3).elim
        · have hw_eq : w = rep w := by
            rcases (hrep_iff (rep w) w).1 (hrep_idem w) with h | ⟨q, htr⟩
            · exact h.symm
            · exact (hnt ⟨w, q, htr⟩).elim
          have hr_eq : r = v' :=
            (hbridge hrw hwv'.symm (hr.trans hv'.symm) (hrep_idem w).symm (hr ▸ hwy.symm)).1
          rw [hr_eq, hw_eq]
          exact hw_adj
      -- Check Case 1 (twin leaf) and Case 2 (triangle pendant)
      by_cases hcase1 : ∃ u1 u2 r, G.Adj u1 r ∧ G.Adj u2 r ∧ u1 ≠ u2 ∧
          (∀ w, G.Adj u1 w → w = r) ∧ (∀ w, G.Adj u2 w → w = r)
      · exact .inl hcase1
      by_cases hcase2 : ∃ u r b1 c1, G.Adj u r ∧ (∀ w, G.Adj u w → w = r) ∧
          Tri G r b1 c1 ∧ G.degree c1 = 2
      · exact .inr (.inl hcase2)
      -- Helper: if r in {v, b, c} has no edge to pH, then r has a unique outside neighbor (a leaf) and degree 3
      have hnon_pH {r s1 s2 : Fin n} (htr : Tri G r s1 s2) (hrr : rep r = y)
          (hno_pH : ∀ w, G.Adj r w → rep w ≠ y → rep w ≠ pH) (hdeg_ne2 : G.degree r ≠ 2) :
          ∃ u, G.Adj r u ∧ (∀ w, G.Adj u w → w = r) ∧ G.degree r = 3 := by
        have houts : ∃ u, G.Adj r u ∧ rep u ≠ y := by
          by_contra! hall
          have hsub : G.neighborFinset r ⊆ ({s1, s2} : Finset (Fin n)) := by
            intro w hw
            rw [mem_neighborFinset] at hw
            have hwy := hall w hw
            rcases (hrep_iff r w).1 (hrr.trans hwy.symm) with rfl | ⟨q, htr'⟩
            · exact (hw.ne rfl).elim
            · rcases hg.2 r s1 s2 w q htr htr' with ⟨rfl, _⟩ | ⟨_, rfl⟩ <;> simp
          have hge := two_neighbors G htr.1 htr.2.2.symm htr.2.1.ne
          have hle : G.degree r ≤ 2 := (Finset.card_le_card hsub).trans (by simp [htr.2.1.ne])
          exact hdeg_ne2 (by omega)
        obtain ⟨u, hru, huy⟩ := houts
        have hu_leaf := hleaf_out hrr hru huy (hno_pH u hru huy)
        have huniq : ∀ w, G.Adj r w → rep w ≠ y → w = u := by
          intro w hrw hwy
          by_contra hwu
          have hw_leaf := hleaf_out hrr hrw hwy (hno_pH w hrw hwy)
          exact hcase1 ⟨w, u, r, hrw.symm, hru.symm, hwu, hw_leaf, hu_leaf⟩
        have hsub : G.neighborFinset r ⊆ ({s1, s2, u} : Finset (Fin n)) := by
          intro w hw
          rw [mem_neighborFinset] at hw
          by_cases hwy : rep w = y
          · rcases (hrep_iff r w).1 (hrr.trans hwy.symm) with rfl | ⟨q, htr'⟩
            · exact (hw.ne rfl).elim
            · rcases hg.2 r s1 s2 w q htr htr' with ⟨rfl, _⟩ | ⟨_, rfl⟩ <;> simp
          · rw [huniq w hw hwy]; simp
        have hus1 : u ≠ s1 := fun heq => huy (heq ▸ ((hrep_iff s1 r).2 (.inr ⟨s2, tri_swap12 htr⟩)).trans hrr)
        have hus2 : u ≠ s2 := fun heq => huy (heq ▸ ((hrep_iff s2 r).2 (.inr ⟨s1, tri_rotate (tri_rotate htr)⟩)).trans hrr)
        have hsup : ({s1, s2, u} : Finset (Fin n)) ⊆ G.neighborFinset r := by
          intro w hw
          rw [mem_neighborFinset]
          simp only [Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl | rfl
          · exact htr.1
          · exact htr.2.2.symm
          · exact hru
        have hcard : ({s1, s2, u} : Finset (Fin n)).card = 3 := by
          simp [htr.2.1.ne, hus1.symm, hus2.symm]
        have hdeg : G.degree r = 3 := by
          have heq := Finset.Subset.antisymm hsub hsup
          change (G.neighborFinset r).card = 3
          rw [heq, hcard]
        exact ⟨u, hru, hu_leaf, hdeg⟩
      have hxrep : rep x = x := by
        obtain ⟨u0, _, hu0, _, _⟩ := hxy.2
        rw [← hu0, hrep_idem]
      have hv_deg_ne2 : G.degree v ≠ 2 := by
        intro h2
        rcases (degree_two_neighbors ht h2 x).1 hxv.symm with rfl | rfl
        · exact hxy.1 (hxrep.symm.trans hrb)
        · exact hxy.1 (hxrep.symm.trans hrc)
      have hb_deg_ne2 : G.degree b ≠ 2 := fun h2 => hcase2 ⟨x, v, c, b, hxv, hx_adj, tri_flip ht, h2⟩
      have hc_deg_ne2 : G.degree c ≠ 2 := fun h2 => hcase2 ⟨x, v, b, c, hxv, hx_adj, ht, h2⟩
      -- Produce Case 5 (D4) depending on which vertex of {v, b, c}, if any, has an edge to pH
      right; right; right; right
      by_cases hpH : ∃ r w, rep r = y ∧ G.Adj r w ∧ rep w = pH ∧ pH ≠ y
      · obtain ⟨r0, w0, hr0, hr0w0, hw0, hpHy⟩ := hpH
        have hother_no_pH {r : Fin n} (hr : rep r = y) (hne : r ≠ r0) :
            ∀ w, G.Adj r w → rep w ≠ y → rep w ≠ pH := by
          intro w hrw _ hwp
          have := hbridge hrw hr0w0 (hr.trans hr0.symm) (hwp.trans hw0.symm) (hr ▸ hwp ▸ hpHy.symm)
          exact hne this.1
        rcases (hclass_y r0).1 hr0 with hr0_eq | hr0_eq | hr0_eq
        · subst r0
          obtain ⟨ub, hbub, hubl, hdb⟩ := hnon_pH (tri_rotate ht) hrb (hother_no_pH hrb ht.1.ne.symm) hb_deg_ne2
          obtain ⟨uc, hcuc, hucl, hdc⟩ := hnon_pH (tri_rotate (tri_rotate ht)) hrc (hother_no_pH hrc ht.2.2.ne) hc_deg_ne2
          exact ⟨v, b, c, ub, uc, ht, hbub, hcuc, hubl, hucl, hdb, hdc⟩
        · subst r0
          obtain ⟨uv, hvuv, huvl, hdv⟩ := hnon_pH ht hvy (hother_no_pH hvy ht.1.ne) hv_deg_ne2
          obtain ⟨uc, hcuc, hucl, hdc⟩ := hnon_pH (tri_rotate (tri_rotate ht)) hrc (hother_no_pH hrc ht.2.1.ne.symm) hc_deg_ne2
          exact ⟨b, c, v, uc, uv, tri_rotate ht, hcuc, hvuv, hucl, huvl, hdc, hdv⟩
        · subst r0
          obtain ⟨uv, hvuv, huvl, hdv⟩ := hnon_pH ht hvy (hother_no_pH hvy ht.2.2.ne.symm) hv_deg_ne2
          obtain ⟨ub, hbub, hubl, hdb⟩ := hnon_pH (tri_rotate ht) hrb (hother_no_pH hrb ht.2.1.ne) hb_deg_ne2
          exact ⟨c, v, b, uv, ub, tri_rotate (tri_rotate ht), hvuv, hbub, huvl, hubl, hdv, hdb⟩
      · push Not at hpH
        have hno_pH (r : Fin n) (hr : rep r = y) (w : Fin n) (hrw : G.Adj r w) (hwy : rep w ≠ y) : rep w ≠ pH := by
          intro hwp
          exact hwy (hwp.trans (hpH r w hr hrw hwp))
        obtain ⟨ub, hbub, hubl, hdb⟩ := hnon_pH (tri_rotate ht) hrb (hno_pH b hrb) hb_deg_ne2
        obtain ⟨uc, hcuc, hucl, hdc⟩ := hnon_pH (tri_rotate (tri_rotate ht)) hrc (hno_pH c hrc) hc_deg_ne2
        exact ⟨v, b, c, ub, uc, ht, hbub, hcuc, hubl, hucl, hdb, hdc⟩
    · -- ¬ OnTri G v: class y is singleton {v}; peel_star!
      by_cases hcase3 : ∃ a1 b1 c1, Tri G a1 b1 c1 ∧ G.degree b1 = 2 ∧ G.degree c1 = 2 ∧ G.degree a1 ≤ 3
      · exact .inr (.inr (.inl hcase3))
      right; right; right; left
      by_cases hwp : ∃ wp, G.Adj v wp ∧ rep wp = pH
      · obtain ⟨wp, hvwp, hrep_wp⟩ := hwp
        refine ⟨x, v, wp, hxv, hx_adj, fun w hvw => ?_⟩
        have hwy : rep w ≠ y := by
          intro heq
          rcases (hrep_iff v w).1 (hvy.trans heq.symm) with rfl | ⟨q, htr⟩
          · exact hvw.ne rfl
          · exact hvt ⟨w, q, htr⟩
        by_cases hw_pH : rep w = pH
        · right
          exact (hbridge hvw hvwp rfl (hw_pH.trans hrep_wp.symm) (hvy ▸ hwy.symm)).2
        · left
          have hyw : H.Adj y (rep w) := ⟨hwy.symm, v, w, hvy, rfl, hvw⟩
          have hleaf_w : ∀ q, H.Adj (rep w) q → q = y := (hy_star (rep w) hyw).resolve_right hw_pH
          rcases hleaf_case hyw.symm hleaf_w with h3 | ⟨v', hv', hwv', hnt, hw_adj⟩
          · exact (hcase3 h3).elim
          · have hw_eq : w = rep w := by
              rcases (hrep_iff (rep w) w).1 (hrep_idem w) with h | ⟨q, htr⟩
              · exact h.symm
              · exact (hnt ⟨w, q, htr⟩).elim
            have hv_eq : v = v' := (hbridge hvw hwv'.symm (hvy.trans hv'.symm) (hrep_idem w).symm (hvy ▸ hwy.symm)).1
            rw [hv_eq, hw_eq]
            exact hw_adj
      · push Not at hwp
        refine ⟨x, v, v, hxv, hx_adj, fun w hvw => .inl ?_⟩
        have hwy : rep w ≠ y := by
          intro heq
          rcases (hrep_iff v w).1 (hvy.trans heq.symm) with rfl | ⟨q, htr⟩
          · exact hvw.ne rfl
          · exact hvt ⟨w, q, htr⟩
        have hyw : H.Adj y (rep w) := ⟨hwy.symm, v, w, hvy, rfl, hvw⟩
        have hleaf_w : ∀ q, H.Adj (rep w) q → q = y := (hy_star (rep w) hyw).resolve_right (hwp w hvw)
        rcases hleaf_case hyw.symm hleaf_w with h3 | ⟨v', hv', hwv', hnt, hw_adj⟩
        · exact (hcase3 h3).elim
        · have hw_eq : w = rep w := by
            rcases (hrep_iff (rep w) w).1 (hrep_idem w) with h | ⟨q, htr⟩
            · exact h.symm
            · exact (hnt ⟨w, q, htr⟩).elim
          have hv_eq : v = v' := (hbridge hvw hwv'.symm (hvy.trans hv'.symm) (hrep_idem w).symm (hvy ▸ hwy.symm)).1
          rw [hv_eq, hw_eq]
          exact hw_adj
  · -- No edges in H: every edge of G is inside a single rep-class, i.e., an isolated triangle!
    push Not at hH
    obtain ⟨a, b, hab⟩ := he
    have hrab : rep a = rep b := by
      by_contra hne
      exact hH (rep a) (rep b) ⟨hne, a, b, rfl, rfl, hab⟩
    rcases (hrep_iff a b).1 hrab with rfl | ⟨c, ht⟩
    · exact (hab.ne rfl).elim
    have hdeg2 {u s1 s2 : Fin n} (htu : Tri G u s1 s2) : G.degree u = 2 := by
      have hsub : G.neighborFinset u ⊆ ({s1, s2} : Finset (Fin n)) := by
        intro w hw
        rw [mem_neighborFinset] at hw
        have hruw : rep u = rep w := by
          by_contra hne
          exact hH (rep u) (rep w) ⟨hne, u, w, rfl, rfl, hw⟩
        rcases (hrep_iff u w).1 hruw with rfl | ⟨q, ht'⟩
        · exact (hw.ne rfl).elim
        · rcases hg.2 u s1 s2 w q htu ht' with ⟨rfl, _⟩ | ⟨_, rfl⟩ <;> simp
      have hge := two_neighbors G htu.1 htu.2.2.symm htu.2.1.ne
      have hle : G.degree u ≤ 2 := (Finset.card_le_card hsub).trans (by simp [htu.2.1.ne])
      omega
    exact .inr (.inr (.inl ⟨a, b, c, ht, hdeg2 (tri_rotate ht), hdeg2 (tri_rotate (tri_rotate ht)),
      by have := hdeg2 ht; omega⟩))


-- Certified tables for the D4 = {b, c, ub, uc} gadget on rows8 = [1, 2, 3, 5, 10, 6, 9, 12]
-- and rows7 = [0, 12, 1, 2, 3, 5, 10] with outside evaluations y0 = bits ∅ and ya = bits {a}.
private def c8cum : ℕ → ℕ
  | 1 => 414590015802317520725455145560666851710374657409956749791723520
  | 2 => 62314280380625952026340247755924909254663260918496918541110698336330298237841
  | 3 => 108466154676415810531712631082747660223610786292525175653236091544925736645623
  | 4 => 115731546895521203966666683948672650208073932436040623872698147212843735170047
  | _ => 0

private def cost8 (v : ℕ) : ℕ :=
  if (c8cum 1).testBit v then 1
  else if (c8cum 2).testBit v then 2
  else if (c8cum 3).testBit v then 3
  else if (c8cum 4).testBit v then 4
  else 5

private def c8exact : ℕ → List ℕ
  | 1 => [47, 54, 77, 87, 168, 178, 201, 208]
  | 2 => [0, 4, 7, 8, 9, 13, 16, 18, 22, 32, 34, 38, 40, 50, 63, 64, 65, 69, 73, 80, 95, 111, 119, 127, 128, 136, 144, 160, 175, 182, 186, 190, 191, 192, 205, 215, 217, 221, 223, 233, 237, 239, 242, 246, 247, 248, 251, 255]
  | 3 => [1, 2, 5, 6, 12, 15, 20, 23, 36, 39, 41, 42, 43, 45, 46, 48, 55, 62, 68, 71, 72, 79, 81, 82, 83, 85, 86, 93, 109, 118, 137, 146, 162, 169, 170, 172, 173, 174, 176, 183, 184, 187, 193, 200, 207, 209, 210, 212, 213, 214, 216, 219, 232, 235, 240, 243, 249, 250, 253, 254]
  | 4 => [3, 11, 19, 24, 25, 26, 27, 29, 30, 31, 35, 44, 52, 56, 58, 59, 67, 76, 84, 88, 89, 91, 96, 97, 98, 99, 101, 102, 103, 104, 105, 107, 112, 114, 115, 120, 123, 125, 126, 129, 130, 132, 135, 140, 141, 143, 148, 150, 151, 152, 153, 154, 156, 157, 158, 159, 164, 166, 167, 171, 179, 188, 196, 197, 199, 203, 211, 220, 224, 225, 226, 228, 229, 230, 231, 236, 244, 252]
  | _ => []

private def checkC8Pair (k1 k2 : ℕ) : Bool :=
  let m := c8cum (k1 + k2)
  (c8exact k1).all fun a => (c8exact k2).all fun b =>
    m.testBit (a &&& b) && m.testBit (a ||| b)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem c8_exact_mem :
    (List.range 256).all (fun v => let c := cost8 v; c ≥ 5 || v ∈ c8exact c) = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem c8_pairs_ok :
    checkC8Pair 1 1 && checkC8Pair 1 2 && checkC8Pair 1 3 && checkC8Pair 2 2 = true := by
  decide +kernel

private theorem c8_cum_le (k v : ℕ) (hk : 1 ≤ k) (hk4 : k ≤ 4) (h : (c8cum k).testBit v = true) :
    cost8 v ≤ k := by
  unfold cost8
  interval_cases k <;> split_ifs <;> first | omega | contradiction

private theorem c8_mem_exact (x : ℕ) (hx : x < 256) (hc : cost8 x < 5) : x ∈ c8exact (cost8 x) := by
  have := List.all_eq_true.mp c8_exact_mem x (List.mem_range.mpr hx)
  simp only [Bool.or_eq_true, decide_eq_true_eq] at this
  exact this.resolve_left (by omega)

private theorem cost8_pos (x : ℕ) : 1 ≤ cost8 x := by
  unfold cost8; split_ifs <;> omega

private theorem cost8_le5 (x : ℕ) : cost8 x ≤ 5 := by
  unfold cost8; split_ifs <;> omega

private theorem cost8_gates (a b : ℕ) (ha : a < 256) (hb : b < 256) :
    cost8 (a &&& b) ≤ cost8 a + cost8 b ∧ cost8 (a ||| b) ≤ cost8 a + cost8 b := by
  have hpa := cost8_pos a
  have hpb := cost8_pos b
  by_cases hsum : 5 ≤ cost8 a + cost8 b
  · exact ⟨(cost8_le5 _).trans hsum, (cost8_le5 _).trans hsum⟩
  have hca3 : cost8 a ≤ 3 := by omega
  have hcb3 : cost8 b ≤ 3 := by omega
  have hma := c8_mem_exact a ha (by omega)
  have hmb := c8_mem_exact b hb (by omega)
  have hcheck : checkC8Pair (cost8 a) (cost8 b) = true ∨ checkC8Pair (cost8 b) (cost8 a) = true := by
    have hp := c8_pairs_ok
    simp only [Bool.and_eq_true] at hp
    rcases hp with ⟨⟨⟨h11, h12⟩, h13⟩, h22⟩
    generalize cost8 a = ca at hpa hca3 hsum ⊢
    generalize cost8 b = cb at hpb hcb3 hsum ⊢
    interval_cases ca <;> interval_cases cb <;> first | omega | exact .inl ‹_› | exact .inr ‹_›
  have hbits : (c8cum (cost8 a + cost8 b)).testBit (a &&& b) = true ∧
      (c8cum (cost8 a + cost8 b)).testBit (a ||| b) = true := by
    rcases hcheck with h | h
    · have hh := List.all_eq_true.mp (List.all_eq_true.mp h a hma) b hmb
      simpa [Bool.and_eq_true] using hh
    · have hh := List.all_eq_true.mp (List.all_eq_true.mp h b hmb) a hma
      rw [Nat.add_comm (cost8 b), Nat.and_comm b a, Nat.or_comm b a] at hh
      simpa [Bool.and_eq_true] using hh
  exact ⟨c8_cum_le _ _ (by omega) (by omega) hbits.1, c8_cum_le _ _ (by omega) (by omega) hbits.2⟩

private def pcum : ℕ → ℕ
  | 1 => 10213043179133573695694438400
  | 2 => 239596115159595593349926933232708813357
  | 3 => 337377535805438549210144002877500230591
  | 4 => 340223953422811154576507285585841172479
  | 5 => 340230443793894070075465861045973659647
  | 6 => 340271982327221393808117546439109754879
  | _ => 0

private def pcost7 (v : ℕ) : ℕ :=
  if (pcum 1).testBit v then 1
  else if (pcum 2).testBit v then 2
  else if (pcum 3).testBit v then 3
  else if (pcum 4).testBit v then 4
  else if (pcum 5).testBit v then 5
  else if (pcum 6).testBit v then 6
  else 7

private def pexact : ℕ → List ℕ
  | 1 => [34, 39, 52, 61, 66, 75, 88, 93]
  | 2 => [0, 2, 3, 5, 9, 16, 20, 24, 29, 32, 36, 37, 54, 55, 63, 64, 72, 73, 90, 91, 95, 98, 103, 107, 111, 118, 122, 124, 125, 127]
  | 3 => [1, 4, 7, 8, 11, 21, 25, 35, 38, 41, 43, 45, 47, 48, 50, 53, 56, 58, 60, 67, 69, 71, 74, 77, 79, 80, 82, 84, 86, 89, 92, 102, 106, 116, 119, 120, 123, 126]
  | 4 => [6, 10, 13, 18, 19, 22, 23, 26, 27, 28, 31, 33, 40, 42, 57, 59, 62, 65, 68, 70, 85, 87, 94, 96, 99, 100, 101, 104, 105, 108, 109, 114, 117, 121]
  | 5 => [15, 17, 44, 51, 76, 83, 110, 112]
  | 6 => [12, 30, 46, 49, 78, 81, 97, 115]
  | _ => []

private def checkPPair (k1 k2 : ℕ) : Bool :=
  let m := pcum (k1 + k2)
  (pexact k1).all fun a => (pexact k2).all fun b =>
    m.testBit (a &&& b) && m.testBit (a ||| b)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem p_exact_mem :
    (List.range 128).all (fun v => let c := pcost7 v; c ≥ 7 || v ∈ pexact c) = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem p_pairs_ok :
    checkPPair 1 1 && checkPPair 1 2 && checkPPair 1 3 && checkPPair 1 4 && checkPPair 1 5 &&
    checkPPair 2 2 && checkPPair 2 3 && checkPPair 2 4 && checkPPair 3 3 = true := by
  decide +kernel

private theorem p_cum_le (k v : ℕ) (hk : 1 ≤ k) (hk6 : k ≤ 6) (h : (pcum k).testBit v = true) :
    pcost7 v ≤ k := by
  unfold pcost7
  interval_cases k <;> split_ifs <;> first | omega | contradiction

private theorem p_mem_exact (x : ℕ) (hx : x < 128) (hc : pcost7 x < 7) : x ∈ pexact (pcost7 x) := by
  have := List.all_eq_true.mp p_exact_mem x (List.mem_range.mpr hx)
  simp only [Bool.or_eq_true, decide_eq_true_eq] at this
  exact this.resolve_left (by omega)

private theorem pcost7_pos (x : ℕ) : 1 ≤ pcost7 x := by
  unfold pcost7; split_ifs <;> omega

private theorem pcost7_le7 (x : ℕ) : pcost7 x ≤ 7 := by
  unfold pcost7; split_ifs <;> omega

private theorem pcost7_gates (a b : ℕ) (ha : a < 128) (hb : b < 128) :
    pcost7 (a &&& b) ≤ pcost7 a + pcost7 b ∧ pcost7 (a ||| b) ≤ pcost7 a + pcost7 b := by
  have hpa := pcost7_pos a
  have hpb := pcost7_pos b
  by_cases hsum : 7 ≤ pcost7 a + pcost7 b
  · exact ⟨(pcost7_le7 _).trans hsum, (pcost7_le7 _).trans hsum⟩
  have hca5 : pcost7 a ≤ 5 := by omega
  have hcb5 : pcost7 b ≤ 5 := by omega
  have hma := p_mem_exact a ha (by omega)
  have hmb := p_mem_exact b hb (by omega)
  have hcheck : checkPPair (pcost7 a) (pcost7 b) = true ∨ checkPPair (pcost7 b) (pcost7 a) = true := by
    have hp := p_pairs_ok
    simp only [Bool.and_eq_true] at hp
    rcases hp with ⟨⟨⟨⟨⟨⟨⟨⟨h11, h12⟩, h13⟩, h14⟩, h15⟩, h22⟩, h23⟩, h24⟩, h33⟩
    generalize pcost7 a = ca at hpa hca5 hsum ⊢
    generalize pcost7 b = cb at hpb hcb5 hsum ⊢
    interval_cases ca <;> interval_cases cb <;> first | omega | exact .inl ‹_› | exact .inr ‹_›
  have hbits : (pcum (pcost7 a + pcost7 b)).testBit (a &&& b) = true ∧
      (pcum (pcost7 a + pcost7 b)).testBit (a ||| b) = true := by
    rcases hcheck with h | h
    · have hh := List.all_eq_true.mp (List.all_eq_true.mp h a hma) b hmb
      simpa [Bool.and_eq_true] using hh
    · have hh := List.all_eq_true.mp (List.all_eq_true.mp h b hmb) a hma
      rw [Nat.add_comm (pcost7 b), Nat.and_comm b a, Nat.or_comm b a] at hh
      simpa [Bool.and_eq_true] using hh
  exact ⟨p_cum_le _ _ (by omega) (by omega) hbits.1, p_cum_le _ _ (by omega) (by omega) hbits.2⟩

private def mcum : ℕ → ℕ
  | 0 => 6703903964971298550513851223398529954289006718184201223215422082548200075318263687581576437196849637171206979807006590987639463012239472130123462986432513
  | 1 => 6703916851598472648849553240392664321095326061437728254573257692118666821239955293022950564918197943328093431471170270860344927671772006791128937147138049
  | 2 => 10090367357016048709144200361023499905685947141611430621489262404509274768593447264136234581046149704839937029503318566374712105818097235835075267073479939
  | 3 => 13232877914959495150136253343739105514099383429193373545053554390309104470681452201152566629298537590027319507820992787077670584039577727503070715312018751
  | 4 => 13250683382608979925122268476955983274976785232249537464988053396978970869701391929932206668388252729010309621457877329517246486993388334305268119461953343
  | 5 => 13303059430489920513207373226399736458417993504029097607925143048986837578153683147561985611474676792906934626697867085019590214029243790441064160781402047
  | 6 => 13407807929942597099565507356905506979187284139080212485414887576207826954504416636910649008011942990032600670059291174479584620601684521471857445119721471
  | _ => 0

private def mcost9 (v : ℕ) : ℕ :=
  if (mcum 0).testBit v then 0
  else if (mcum 1).testBit v then 1
  else if (mcum 2).testBit v then 2
  else if (mcum 3).testBit v then 3
  else if (mcum 4).testBit v then 4
  else if (mcum 5).testBit v then 5
  else if (mcum 6).testBit v then 6
  else 7

private def mexact : ℕ → List ℕ
  | 0 => [0, 63, 448, 511]
  | 1 => [19, 26, 37, 44, 128, 154, 191, 192, 211, 255, 256, 300, 319, 320, 357, 383, 467, 474, 485, 492]
  | 2 => [1, 8, 10, 12, 16, 18, 27, 31, 32, 36, 45, 47, 51, 53, 55, 62, 64, 65, 83, 101, 127, 136, 138, 146, 147, 155, 165, 172, 190, 193, 210, 218, 219, 229, 236, 243, 247, 264, 268, 275, 282, 292, 293, 301, 318, 321, 339, 346, 356, 364, 365, 373, 375, 384, 410, 428, 446, 447, 449, 456, 458, 460, 464, 466, 475, 479, 480, 484, 493, 495, 499, 501, 503, 510]
  | 3 => [2, 3, 4, 5, 17, 21, 23, 24, 28, 30, 33, 35, 39, 40, 42, 46, 58, 59, 60, 61, 81, 82, 90, 91, 97, 100, 108, 109, 115, 117, 119, 129, 130, 140, 144, 158, 159, 160, 164, 170, 173, 174, 175, 179, 181, 183, 186, 187, 194, 195, 200, 202, 204, 208, 209, 223, 224, 225, 227, 228, 237, 239, 245, 251, 254, 257, 260, 266, 272, 274, 283, 284, 286, 287, 288, 302, 303, 307, 309, 311, 316, 317, 324, 325, 328, 330, 332, 336, 337, 338, 341, 347, 351, 352, 353, 367, 371, 381, 382, 392, 394, 396, 402, 403, 411, 414, 420, 421, 429, 430, 450, 451, 452, 453, 465, 469, 471, 472, 476, 478, 481, 483, 487, 488, 490, 494, 506, 507, 508, 509]
  | 4 => [9, 11, 13, 14, 15, 20, 29, 34, 43, 48, 49, 50, 52, 54, 66, 67, 68, 69, 72, 73, 74, 75, 76, 77, 80, 85, 95, 96, 99, 111, 113, 123, 125, 126, 131, 132, 133, 137, 139, 142, 145, 149, 151, 152, 156, 161, 162, 163, 167, 168, 178, 180, 182, 188, 189, 196, 197, 201, 203, 205, 213, 215, 216, 220, 222, 231, 232, 234, 235, 238, 241, 242, 246, 250, 252, 253, 258, 259, 261, 265, 269, 270, 273, 276, 277, 279, 280, 289, 291, 295, 296, 298, 306, 308, 310, 314, 315, 322, 323, 329, 331, 333, 343, 344, 348, 349, 350, 355, 359, 360, 362, 366, 369, 372, 374, 378, 379, 380, 385, 386, 388, 398, 400, 412, 415, 416, 426, 431, 434, 435, 436, 437, 438, 439, 442, 443, 444, 445, 457, 459, 461, 462, 463, 468, 477, 482, 491, 496, 497, 498, 500, 502]
  | 5 => [7, 22, 25, 38, 41, 56, 87, 88, 89, 92, 93, 94, 103, 104, 105, 106, 107, 110, 114, 116, 118, 122, 124, 141, 143, 148, 150, 153, 157, 166, 169, 171, 176, 177, 206, 207, 212, 214, 217, 221, 226, 230, 233, 240, 244, 267, 271, 278, 281, 285, 290, 294, 297, 299, 304, 305, 334, 335, 340, 342, 345, 354, 358, 361, 363, 368, 370, 387, 389, 393, 395, 397, 401, 404, 405, 406, 407, 408, 417, 418, 419, 422, 423, 424, 455, 470, 473, 486, 489, 504]
  | 6 => [6, 57, 78, 79, 84, 86, 98, 102, 112, 121, 134, 135, 184, 185, 198, 199, 248, 249, 262, 263, 312, 313, 326, 327, 376, 377, 390, 399, 409, 413, 425, 427, 432, 433, 454, 505]
  | _ => []

private def pack7 (p : ℕ) : ℕ :=
  let f0 := (p &&& 1) ||| ((p >>> 1) &&& 62)
  let f1 := (p &&& 1) ||| ((p >>> 1) &&& 6)
  f0 ||| (f1 <<< 6)

private def checkMPair (k1 k2 : ℕ) : Bool :=
  let m := mcum (k1 + k2)
  (mexact k1).all fun a => (mexact k2).all fun b =>
    m.testBit (a &&& b) && m.testBit (a ||| b)

private def checkPMix (kp km : ℕ) : Bool :=
  let m := mcum (kp + km)
  (pexact kp).all fun p =>
    let pk := pack7 p
    let c0 := (p &&& 3) == 0
    let c3 := (p &&& 3) == 3
    (!c0 && !c3) || (mexact km).all fun b =>
      (!c0 || m.testBit (pk ||| b)) && (!c3 || m.testBit (pk &&& b))

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem m_exact_mem :
    (List.range 512).all (fun v => let c := mcost9 v; c ≥ 7 || v ∈ mexact c) = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
private theorem m_pairs_ok :
    checkMPair 0 0 && checkMPair 0 1 && checkMPair 0 2 && checkMPair 0 3 &&
    checkMPair 0 4 && checkMPair 0 5 && checkMPair 0 6 &&
    checkMPair 1 1 && checkMPair 1 2 && checkMPair 1 3 && checkMPair 1 4 &&
    checkMPair 1 5 && checkMPair 2 2 && checkMPair 2 3 && checkMPair 2 4 &&
    checkMPair 3 3 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
private theorem pmix_ok :
    checkPMix 1 0 && checkPMix 1 1 && checkPMix 1 2 && checkPMix 1 3 && checkPMix 1 4 && checkPMix 1 5 &&
    checkPMix 2 0 && checkPMix 2 1 && checkPMix 2 2 && checkPMix 2 3 && checkPMix 2 4 &&
    checkPMix 3 0 && checkPMix 3 1 && checkPMix 3 2 && checkPMix 3 3 &&
    checkPMix 4 0 && checkPMix 4 1 && checkPMix 4 2 &&
    checkPMix 5 0 && checkPMix 5 1 &&
    checkPMix 6 0 = true := by
  decide +kernel

private theorem m_cum_le (k v : ℕ) (hk6 : k ≤ 6) (h : (mcum k).testBit v = true) :
    mcost9 v ≤ k := by
  unfold mcost9
  interval_cases k <;> split_ifs <;> first | omega | contradiction

private theorem m_mem_exact (x : ℕ) (hx : x < 512) (hc : mcost9 x < 7) : x ∈ mexact (mcost9 x) := by
  have := List.all_eq_true.mp m_exact_mem x (List.mem_range.mpr hx)
  simp only [Bool.or_eq_true, decide_eq_true_eq] at this
  exact this.resolve_left (by omega)

private theorem mcost9_le7 (x : ℕ) : mcost9 x ≤ 7 := by
  unfold mcost9; split_ifs <;> omega

set_option maxRecDepth 2048 in
private theorem mcost9_gates (a b : ℕ) (ha : a < 512) (hb : b < 512) :
    mcost9 (a &&& b) ≤ mcost9 a + mcost9 b ∧ mcost9 (a ||| b) ≤ mcost9 a + mcost9 b := by
  by_cases hsum : 7 ≤ mcost9 a + mcost9 b
  · exact ⟨(mcost9_le7 _).trans hsum, (mcost9_le7 _).trans hsum⟩
  have hma := m_mem_exact a ha (by omega)
  have hmb := m_mem_exact b hb (by omega)
  have hcheck : checkMPair (mcost9 a) (mcost9 b) = true ∨ checkMPair (mcost9 b) (mcost9 a) = true := by
    have hp := m_pairs_ok
    simp only [Bool.and_eq_true] at hp
    rcases hp with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h00, h01⟩, h02⟩, h03⟩, h04⟩, h05⟩, h06⟩,
      h11⟩, h12⟩, h13⟩, h14⟩, h15⟩, h22⟩, h23⟩, h24⟩, h33⟩
    match hca : mcost9 a with
    | 0 => match hcb : mcost9 b with
      | 0 => exact .inl h00 | 1 => exact .inl h01 | 2 => exact .inl h02 | 3 => exact .inl h03
      | 4 => exact .inl h04 | 5 => exact .inl h05 | 6 => exact .inl h06 | _ + 7 => omega
    | 1 => match hcb : mcost9 b with
      | 0 => exact .inr h01 | 1 => exact .inl h11 | 2 => exact .inl h12 | 3 => exact .inl h13
      | 4 => exact .inl h14 | 5 => exact .inl h15 | _ + 6 => omega
    | 2 => match hcb : mcost9 b with
      | 0 => exact .inr h02 | 1 => exact .inr h12 | 2 => exact .inl h22 | 3 => exact .inl h23
      | 4 => exact .inl h24 | _ + 5 => omega
    | 3 => match hcb : mcost9 b with
      | 0 => exact .inr h03 | 1 => exact .inr h13 | 2 => exact .inr h23 | 3 => exact .inl h33
      | _ + 4 => omega
    | 4 => match hcb : mcost9 b with
      | 0 => exact .inr h04 | 1 => exact .inr h14 | 2 => exact .inr h24 | _ + 3 => omega
    | 5 => match hcb : mcost9 b with
      | 0 => exact .inr h05 | 1 => exact .inr h15 | _ + 2 => omega
    | 6 => match hcb : mcost9 b with
      | 0 => exact .inr h06 | _ + 1 => omega
    | _ + 7 => omega
  have hbits : (mcum (mcost9 a + mcost9 b)).testBit (a &&& b) = true ∧
      (mcum (mcost9 a + mcost9 b)).testBit (a ||| b) = true := by
    rcases hcheck with h | h
    · have hh := List.all_eq_true.mp (List.all_eq_true.mp h a hma) b hmb
      simpa [Bool.and_eq_true] using hh
    · have hh := List.all_eq_true.mp (List.all_eq_true.mp h b hmb) a hma
      rw [Nat.add_comm (mcost9 b), Nat.and_comm b a, Nat.or_comm b a] at hh
      simpa [Bool.and_eq_true] using hh
  exact ⟨m_cum_le _ _ (by omega) hbits.1, m_cum_le _ _ (by omega) hbits.2⟩

private theorem mcost9_pure (p b : ℕ) (hp : p < 128) (hb : b < 512) :
    (p &&& 3 = 0 → mcost9 (pack7 p ||| b) ≤ pcost7 p + mcost9 b) ∧
    (p &&& 3 = 3 → mcost9 (pack7 p &&& b) ≤ pcost7 p + mcost9 b) := by
  by_cases hsum : 7 ≤ pcost7 p + mcost9 b
  · exact ⟨fun _ => (mcost9_le7 _).trans hsum, fun _ => (mcost9_le7 _).trans hsum⟩
  have hpp := pcost7_pos p
  have hcp6 : pcost7 p ≤ 6 := by omega
  have hcb5 : mcost9 b ≤ 5 := by omega
  have hmp := p_mem_exact p hp (by omega)
  have hmb := m_mem_exact b hb (by omega)
  have hcheck : checkPMix (pcost7 p) (mcost9 b) = true := by
    have hm := pmix_ok
    simp only [Bool.and_eq_true] at hm
    rcases hm with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h10, h11⟩, h12⟩, h13⟩, h14⟩, h15⟩,
      h20⟩, h21⟩, h22⟩, h23⟩, h24⟩, h30⟩, h31⟩, h32⟩, h33⟩,
      h40⟩, h41⟩, h42⟩, h50⟩, h51⟩, h60⟩
    generalize pcost7 p = cp at hpp hcp6 hsum ⊢
    generalize mcost9 b = cb at hcb5 hsum ⊢
    interval_cases cp <;> interval_cases cb <;> first | omega | assumption
  have hline := List.all_eq_true.mp hcheck p hmp
  constructor
  · intro h0
    simp only [h0, beq_self_eq_true, Bool.not_true, Bool.false_and, Bool.false_or,
      Bool.false_or] at hline
    have hres := List.all_eq_true.mp hline b hmb
    have hbit : (mcum (pcost7 p + mcost9 b)).testBit (pack7 p ||| b) = true := by
      simpa using (Bool.and_eq_true _ _ |>.mp hres).1
    exact m_cum_le _ _ (by omega) hbit
  · intro h3
    simp only [h3, beq_self_eq_true, Bool.not_true, Bool.and_false, Bool.false_or] at hline
    have hres := List.all_eq_true.mp hline b hmb
    have hbit : (mcum (pcost7 p + mcost9 b)).testBit (pack7 p &&& b) = true := by
      simpa using (Bool.and_eq_true _ _ |>.mp hres).2
    exact m_cum_le _ _ (by omega) hbit

private def checkSplit28 : Bool :=
  (c8exact 1 ++ c8exact 2 ++ c8exact 3 ++ c8exact 4).all fun a =>
    (c8exact 1 ++ c8exact 2 ++ c8exact 3 ++ c8exact 4).all fun b =>
      if cost8 a + cost8 b ≤ 5 then
        ((a ||| b) != 28 || (a == 8 && b == 20) || (a == 20 && b == 8) || (a == 16 && b == 12) || (a == 12 && b == 16)) &&
        ((a &&& b) != 28 || (a == 221 && b == 62) || (a == 62 && b == 221) || (a == 190 && b == 93) || (a == 93 && b == 190))
      else true

private def checkSplit3 : Bool :=
  (c8exact 1 ++ c8exact 2).all fun a =>
    (c8exact 1 ++ c8exact 2).all fun b =>
      if cost8 a + cost8 b ≤ 3 then
        ((a ||| b) != 20) &&
        ((a &&& b) != 20 || (a == 54 && b == 221) || (a == 221 && b == 54)) &&
        ((a &&& b) != 62) &&
        ((a ||| b) != 62 || (a == 54 && b == 8) || (a == 8 && b == 54) || (a == 54 && b == 40) || (a == 40 && b == 54))
      else true

private def checkSplit2 : Bool :=
  (c8exact 1).all fun a => (c8exact 1).all fun b =>
    ((a ||| b) != 8) &&
    ((a &&& b) != 8 || (a == 77 && b == 168) || (a == 168 && b == 77)) &&
    ((a &&& b) != 221) &&
    ((a ||| b) != 221 || (a == 77 && b == 208) || (a == 208 && b == 77)) &&
    ((a ||| b) != 40) &&
    ((a &&& b) != 40 || (a == 168 && b == 47) || (a == 47 && b == 168))

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem splits_ok : checkSplit28 && checkSplit3 && checkSplit2 = true := by
  decide +kernel

private theorem c8_mem_14 (x : ℕ) (hx : x < 256) (hc : cost8 x ≤ 4) :
    x ∈ c8exact 1 ++ c8exact 2 ++ c8exact 3 ++ c8exact 4 := by
  have hm := c8_mem_exact x hx (by omega)
  have hp := cost8_pos x
  generalize cost8 x = c at hp hc hm
  interval_cases c <;> simp [hm]

private theorem c8_mem_12 (x : ℕ) (hx : x < 256) (hc : cost8 x ≤ 2) :
    x ∈ c8exact 1 ++ c8exact 2 := by
  have hm := c8_mem_exact x hx (by omega)
  have hp := cost8_pos x
  generalize cost8 x = c at hp hc hm
  interval_cases c <;> simp [hm]

private theorem split28_or {a b : ℕ} (ha : a < 256) (hb : b < 256)
    (hsum : cost8 a + cost8 b ≤ 5) (heq : a ||| b = 28) :
    (a = 8 ∧ b = 20) ∨ (a = 20 ∧ b = 8) ∨ (a = 16 ∧ b = 12) ∨ (a = 12 ∧ b = 16) := by
  have h1 := ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp splits_ok).1).1
  have hpa := cost8_pos a
  have hpb := cost8_pos b
  have h := List.all_eq_true.mp (List.all_eq_true.mp h1 a (c8_mem_14 a ha (by omega))) b (c8_mem_14 b hb (by omega))
  simp only [hsum, ite_true, heq, bne_self_eq_false, Bool.false_or, Bool.and_eq_true,
    Bool.or_eq_true, beq_iff_eq] at h
  rcases h.1 with ((h' | h') | h') | h'
  · exact .inl h'
  · exact .inr (.inl h')
  · exact .inr (.inr (.inl h'))
  · exact .inr (.inr (.inr h'))

private theorem split28_and {a b : ℕ} (ha : a < 256) (hb : b < 256)
    (hsum : cost8 a + cost8 b ≤ 5) (heq : a &&& b = 28) :
    (a = 221 ∧ b = 62) ∨ (a = 62 ∧ b = 221) ∨ (a = 190 ∧ b = 93) ∨ (a = 93 ∧ b = 190) := by
  have h1 := ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp splits_ok).1).1
  have hpa := cost8_pos a
  have hpb := cost8_pos b
  have h := List.all_eq_true.mp (List.all_eq_true.mp h1 a (c8_mem_14 a ha (by omega))) b (c8_mem_14 b hb (by omega))
  simp only [hsum, ite_true, heq, bne_self_eq_false, Bool.false_or, Bool.and_eq_true,
    Bool.or_eq_true, beq_iff_eq] at h
  rcases h.2 with ((h' | h') | h') | h'
  · exact .inl h'
  · exact .inr (.inl h')
  · exact .inr (.inr (.inl h'))
  · exact .inr (.inr (.inr h'))

private theorem split20 {a b : ℕ} (ha : a < 256) (hb : b < 256)
    (hsum : cost8 a + cost8 b ≤ 3) (g : Bool) (heq : (if g then a ||| b else a &&& b) = 20) :
    g = false ∧ ((a = 54 ∧ b = 221) ∨ (a = 221 ∧ b = 54)) := by
  have h2 := ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp splits_ok).1).2
  have hpa := cost8_pos a
  have hpb := cost8_pos b
  have h := List.all_eq_true.mp (List.all_eq_true.mp h2 a (c8_mem_12 a ha (by omega))) b (c8_mem_12 b hb (by omega))
  simp only [hsum, ite_true, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, beq_iff_eq] at h
  cases g
  · simp only [Bool.false_eq_true, ite_false] at heq
    rcases h.1.1.2 with (hne | h') | h'
    · exact (hne heq).elim
    · exact ⟨rfl, .inl h'⟩
    · exact ⟨rfl, .inr h'⟩
  · simp only [ite_true] at heq
    exact (h.1.1.1 heq).elim

private theorem split62 {a b : ℕ} (ha : a < 256) (hb : b < 256)
    (hsum : cost8 a + cost8 b ≤ 3) (g : Bool) (heq : (if g then a ||| b else a &&& b) = 62) :
    g = true ∧ ((a = 54 ∧ b = 8) ∨ (a = 8 ∧ b = 54) ∨ (a = 54 ∧ b = 40) ∨ (a = 40 ∧ b = 54)) := by
  have h2 := ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp splits_ok).1).2
  have hpa := cost8_pos a
  have hpb := cost8_pos b
  have h := List.all_eq_true.mp (List.all_eq_true.mp h2 a (c8_mem_12 a ha (by omega))) b (c8_mem_12 b hb (by omega))
  simp only [hsum, ite_true, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, beq_iff_eq] at h
  cases g
  · simp only [Bool.false_eq_true, ite_false] at heq
    exact (h.1.2 heq).elim
  · simp only [ite_true] at heq
    rcases h.2 with (((hne | h') | h') | h') | h'
    · exact (hne heq).elim
    · exact ⟨rfl, .inl h'⟩
    · exact ⟨rfl, .inr (.inl h')⟩
    · exact ⟨rfl, .inr (.inr (.inl h'))⟩
    · exact ⟨rfl, .inr (.inr (.inr h'))⟩

private theorem split8 {a b : ℕ} (ha : a < 256) (hb : b < 256)
    (hsum : cost8 a + cost8 b ≤ 2) (g : Bool) (heq : (if g then a ||| b else a &&& b) = 8) :
    g = false ∧ ((a = 77 ∧ b = 168) ∨ (a = 168 ∧ b = 77)) := by
  have h3 := ((Bool.and_eq_true _ _).mp splits_ok).2
  have hpa := cost8_pos a
  have hpb := cost8_pos b
  have ha1 : cost8 a = 1 := by omega
  have hb1 : cost8 b = 1 := by omega
  have hma : a ∈ c8exact 1 := ha1 ▸ c8_mem_exact a ha (by omega)
  have hmb : b ∈ c8exact 1 := hb1 ▸ c8_mem_exact b hb (by omega)
  have h := List.all_eq_true.mp (List.all_eq_true.mp h3 a hma) b hmb
  simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, beq_iff_eq] at h
  cases g
  · simp only [Bool.false_eq_true, ite_false] at heq
    rcases h.1.1.1.1.2 with (hne | h') | h'
    · exact (hne heq).elim
    · exact ⟨rfl, .inl h'⟩
    · exact ⟨rfl, .inr h'⟩
  · simp only [ite_true] at heq
    exact (h.1.1.1.1.1 heq).elim

private theorem split221 {a b : ℕ} (ha : a < 256) (hb : b < 256)
    (hsum : cost8 a + cost8 b ≤ 2) (g : Bool) (heq : (if g then a ||| b else a &&& b) = 221) :
    g = true ∧ ((a = 77 ∧ b = 208) ∨ (a = 208 ∧ b = 77)) := by
  have h3 := ((Bool.and_eq_true _ _).mp splits_ok).2
  have hpa := cost8_pos a
  have hpb := cost8_pos b
  have ha1 : cost8 a = 1 := by omega
  have hb1 : cost8 b = 1 := by omega
  have hma : a ∈ c8exact 1 := ha1 ▸ c8_mem_exact a ha (by omega)
  have hmb : b ∈ c8exact 1 := hb1 ▸ c8_mem_exact b hb (by omega)
  have h := List.all_eq_true.mp (List.all_eq_true.mp h3 a hma) b hmb
  simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, beq_iff_eq] at h
  cases g
  · simp only [Bool.false_eq_true, ite_false] at heq
    exact (h.1.1.1.2 heq).elim
  · simp only [ite_true] at heq
    rcases h.1.1.2 with (hne | h') | h'
    · exact (hne heq).elim
    · exact ⟨rfl, .inl h'⟩
    · exact ⟨rfl, .inr h'⟩

private theorem split40 {a b : ℕ} (ha : a < 256) (hb : b < 256)
    (hsum : cost8 a + cost8 b ≤ 2) (g : Bool) (heq : (if g then a ||| b else a &&& b) = 40) :
    g = false ∧ ((a = 168 ∧ b = 47) ∨ (a = 47 ∧ b = 168)) := by
  have h3 := ((Bool.and_eq_true _ _).mp splits_ok).2
  have hpa := cost8_pos a
  have hpb := cost8_pos b
  have ha1 : cost8 a = 1 := by omega
  have hb1 : cost8 b = 1 := by omega
  have hma : a ∈ c8exact 1 := ha1 ▸ c8_mem_exact a ha (by omega)
  have hmb : b ∈ c8exact 1 := hb1 ▸ c8_mem_exact b hb (by omega)
  have h := List.all_eq_true.mp (List.all_eq_true.mp h3 a hma) b hmb
  simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, beq_iff_eq] at h
  cases g
  · simp only [Bool.false_eq_true, ite_false] at heq
    rcases h.2 with (hne | h') | h'
    · exact (hne heq).elim
    · exact ⟨rfl, .inl h'⟩
    · exact ⟨rfl, .inr h'⟩
  · simp only [ite_true] at heq
    exact (h.1.2 heq).elim


private def vals4 (m : ℕ) : Input 4 := fun v => m.testBit v.val

private def rows8 : Fin 8 → ℕ := ![1, 2, 3, 5, 10, 6, 9, 12]
private def rows7 : Fin 7 → ℕ := ![0, 12, 1, 2, 3, 5, 10]

private def table8 : DMFormula 4 → ℕ
  | .lit v b => if b then (![77, 54, 168, 208] : Fin 4 → ℕ) v else
      (![178, 201, 87, 47] : Fin 4 → ℕ) v
  | .and a b => table8 a &&& table8 b
  | .or a b => table8 a ||| table8 b

private theorem table8_join (g : Bool) (a b : DMFormula 4) :
    table8 (join g a b) = if g then table8 a ||| table8 b else table8 a &&& table8 b := by
  cases g <;> rfl

private theorem table8_lt (φ : DMFormula 4) : table8 φ < 256 := by
  induction φ with
  | lit v b => fin_cases v <;> cases b <;> decide
  | and a b ha _ => exact Nat.lt_of_le_of_lt Nat.and_le_left ha
  | or a b ha hb => exact Nat.or_lt_two_pow (n := 8) ha hb

private theorem table8_eval (φ : DMFormula 4) (i : Fin 8) :
    (table8 φ).testBit i.val = φ.eval (vals4 (rows8 i)) := by
  induction φ with
  | lit v b =>
    have h : ∀ (v : Fin 4) (b : Bool) (i : Fin 8),
        (table8 (.lit v b)).testBit i.val = (DMFormula.lit v b).eval (vals4 (rows8 i)) := by decide
    exact h v b i
  | and a b ha hb => simp [table8, DMFormula.eval, ha, hb]
  | or a b ha hb => simp [table8, DMFormula.eval, ha, hb]

private theorem cost8_le_leaves (φ : DMFormula 4) : cost8 (table8 φ) ≤ φ.leaves := by
  induction φ using join_induct with
  | lit v b =>
    have h : ∀ (v : Fin 4) (b : Bool), cost8 (table8 (.lit v b)) ≤ 1 := by decide +kernel
    exact h v b
  | bin g a b ha hb =>
    rw [table8_join, join_leaves]
    have hg := cost8_gates (table8 a) (table8 b) (table8_lt a) (table8_lt b)
    cases g <;> simp only [Bool.false_eq_true, ite_true, ite_false] <;> omega

private def table7 : DMFormula 4 → ℕ
  | .lit v b => if b then (![52, 88, 34, 66] : Fin 4 → ℕ) v else
      (![75, 39, 93, 61] : Fin 4 → ℕ) v
  | .and a b => table7 a &&& table7 b
  | .or a b => table7 a ||| table7 b

private theorem table7_lt (φ : DMFormula 4) : table7 φ < 128 := by
  induction φ with
  | lit v b => fin_cases v <;> cases b <;> decide
  | and a b ha _ => exact Nat.lt_of_le_of_lt Nat.and_le_left ha
  | or a b ha hb => exact Nat.or_lt_two_pow (n := 7) ha hb

private theorem table7_eval (φ : DMFormula 4) (i : Fin 7) :
    (table7 φ).testBit i.val = φ.eval (vals4 (rows7 i)) := by
  induction φ with
  | lit v b =>
    have h : ∀ (v : Fin 4) (b : Bool) (i : Fin 7),
        (table7 (.lit v b)).testBit i.val = (DMFormula.lit v b).eval (vals4 (rows7 i)) := by decide
    exact h v b i
  | and a b ha hb => simp [table7, DMFormula.eval, ha, hb]
  | or a b ha hb => simp [table7, DMFormula.eval, ha, hb]

private theorem pcost7_le_leaves (φ : DMFormula 4) : pcost7 (table7 φ) ≤ φ.leaves := by
  induction φ using join_induct with
  | lit v b =>
    have h : ∀ (v : Fin 4) (b : Bool), pcost7 (table7 (.lit v b)) ≤ 1 := by decide +kernel
    exact h v b
  | bin g a b ha hb =>
    rw [join_leaves]
    have hg := pcost7_gates (table7 a) (table7 b) (table7_lt a) (table7_lt b)
    cases g <;> simp only [join, Bool.false_eq_true, ite_true, ite_false, table7] <;> omega

private def d4SwapFin : Fin 4 → Fin 4 := ![1, 0, 3, 2]

private def swap8 (t : ℕ) : ℕ :=
  (if t.testBit 1 then 1 else 0) ||| (if t.testBit 0 then 2 else 0) |||
  (if t.testBit 2 then 4 else 0) ||| (if t.testBit 4 then 8 else 0) |||
  (if t.testBit 3 then 16 else 0) ||| (if t.testBit 6 then 32 else 0) |||
  (if t.testBit 5 then 64 else 0) ||| (if t.testBit 7 then 128 else 0)

private theorem swap8_lt (x : ℕ) : swap8 x < 2 ^ 8 := by
  unfold swap8
  refine Nat.or_lt_two_pow (n := 8) ?_ (by split_ifs <;> decide)
  refine Nat.or_lt_two_pow (n := 8) ?_ (by split_ifs <;> decide)
  refine Nat.or_lt_two_pow (n := 8) ?_ (by split_ifs <;> decide)
  refine Nat.or_lt_two_pow (n := 8) ?_ (by split_ifs <;> decide)
  refine Nat.or_lt_two_pow (n := 8) ?_ (by split_ifs <;> decide)
  refine Nat.or_lt_two_pow (n := 8) ?_ (by split_ifs <;> decide)
  exact Nat.or_lt_two_pow (n := 8) (by split_ifs <;> decide) (by split_ifs <;> decide)

private theorem swap8_bit (x : ℕ) (j : Fin 8) :
    (swap8 x).testBit j.val = x.testBit ((![1, 0, 2, 4, 3, 6, 5, 7] : Fin 8 → ℕ) j) := by
  have ht (c : Bool) (m k : ℕ) : (if c then m else 0).testBit k = (c && m.testBit k) := by
    cases c <;> simp
  have hb : ∀ k : Fin 8,
      (1 : ℕ).testBit k.val = decide (k = 0) ∧ (2 : ℕ).testBit k.val = decide (k = 1) ∧
      (4 : ℕ).testBit k.val = decide (k = 2) ∧ (8 : ℕ).testBit k.val = decide (k = 3) ∧
      (16 : ℕ).testBit k.val = decide (k = 4) ∧ (32 : ℕ).testBit k.val = decide (k = 5) ∧
      (64 : ℕ).testBit k.val = decide (k = 6) ∧ (128 : ℕ).testBit k.val = decide (k = 7) := by decide
  obtain ⟨h1, h2, h4, h8, h16, h32, h64, h128⟩ := hb j
  simp only [swap8, Nat.testBit_or, ht, h1, h2, h4, h8, h16, h32, h64, h128]
  fin_cases j <;> simp

private theorem swap8_and (a b : ℕ) : swap8 (a &&& b) = swap8 a &&& swap8 b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 8
  · let j : Fin 8 := ⟨i, hi⟩
    change (swap8 (a &&& b)).testBit j.val = (swap8 a &&& swap8 b).testBit j.val
    rw [Nat.testBit_and, swap8_bit, swap8_bit, swap8_bit, Nat.testBit_and]
  · rw [Nat.testBit_and,
      Nat.testBit_eq_false_of_lt ((swap8_lt _).trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))),
      Nat.testBit_eq_false_of_lt ((swap8_lt _).trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))),
      Nat.testBit_eq_false_of_lt ((swap8_lt _).trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)))]
    rfl

private theorem swap8_or (a b : ℕ) : swap8 (a ||| b) = swap8 a ||| swap8 b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 8
  · let j : Fin 8 := ⟨i, hi⟩
    change (swap8 (a ||| b)).testBit j.val = (swap8 a ||| swap8 b).testBit j.val
    rw [Nat.testBit_or, swap8_bit, swap8_bit, swap8_bit, Nat.testBit_or]
  · rw [Nat.testBit_or,
      Nat.testBit_eq_false_of_lt ((swap8_lt _).trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))),
      Nat.testBit_eq_false_of_lt ((swap8_lt _).trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))),
      Nat.testBit_eq_false_of_lt ((swap8_lt _).trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)))]
    rfl

private theorem table8_swap (φ : DMFormula 4) :
    table8 (rename d4SwapFin φ) = swap8 (table8 φ) := by
  induction φ with
  | lit v b => fin_cases v <;> cases b <;> decide
  | and a b ha hb => simp [rename, table8, ha, hb, swap8_and]
  | or a b ha hb => simp [rename, table8, ha, hb, swap8_or]

private theorem form4_one_lit (φ : DMFormula 4) (h1 : φ.leaves = 1) :
    ∃ v b, φ = .lit v b := by
  cases φ with
  | lit v b => exact ⟨v, b, rfl⟩
  | and a b => have := leaves_pos a; have := leaves_pos b; simp [DMFormula.leaves] at h1; omega
  | or a b => have := leaves_pos a; have := leaves_pos b; simp [DMFormula.leaves] at h1; omega

private theorem form4_eq_77 {φ : DMFormula 4} (h1 : φ.leaves = 1) (ht : table8 φ = 77) :
    φ = .lit 0 true := by
  obtain ⟨v, b, rfl⟩ := form4_one_lit φ h1
  fin_cases v <;> cases b <;> simp [table8] at ht ⊢

private theorem form4_eq_54 {φ : DMFormula 4} (h1 : φ.leaves = 1) (ht : table8 φ = 54) :
    φ = .lit 1 true := by
  obtain ⟨v, b, rfl⟩ := form4_one_lit φ h1
  fin_cases v <;> cases b <;> simp [table8] at ht ⊢

private theorem form4_eq_168 {φ : DMFormula 4} (h1 : φ.leaves = 1) (ht : table8 φ = 168) :
    φ = .lit 2 true := by
  obtain ⟨v, b, rfl⟩ := form4_one_lit φ h1
  fin_cases v <;> cases b <;> simp [table8] at ht ⊢

private theorem form4_eq_208 {φ : DMFormula 4} (h1 : φ.leaves = 1) (ht : table8 φ = 208) :
    φ = .lit 3 true := by
  obtain ⟨v, b, rfl⟩ := form4_one_lit φ h1
  fin_cases v <;> cases b <;> simp [table8] at ht ⊢

private theorem form4_eq_47 {φ : DMFormula 4} (h1 : φ.leaves = 1) (ht : table8 φ = 47) :
    φ = .lit 3 false := by
  obtain ⟨v, b, rfl⟩ := form4_one_lit φ h1
  fin_cases v <;> cases b <;> simp [table8] at ht ⊢

private theorem form4_split_two (φ : DMFormula 4) (h2 : φ.leaves = 2) :
    ∃ g a b, φ = join g a b ∧ a.leaves = 1 ∧ b.leaves = 1 := by
  cases φ with
  | lit _ _ => simp [DMFormula.leaves] at h2
  | and a b =>
    have := leaves_pos a; have := leaves_pos b; simp [DMFormula.leaves] at h2
    exact ⟨false, a, b, rfl, by omega, by omega⟩
  | or a b =>
    have := leaves_pos a; have := leaves_pos b; simp [DMFormula.leaves] at h2
    exact ⟨true, a, b, rfl, by omega, by omega⟩

private theorem form4_two_8 {φ : DMFormula 4} (h2 : φ.leaves = 2) (ht : table8 φ = 8) :
    (∀ x, φ.eval x = (x 0 && x 2)) ∧
    count {0} φ = 1 ∧ count {1} φ = 0 ∧ count {2} φ = 1 ∧ count {3} φ = 0 := by
  obtain ⟨g, a, b, rfl, ha1, hb1⟩ := form4_split_two φ h2
  rw [table8_join] at ht
  have hca := cost8_le_leaves a
  have hcb := cost8_le_leaves b
  obtain ⟨rfl, ⟨ha, hb⟩ | ⟨ha, hb⟩⟩ := split8 (table8_lt a) (table8_lt b) (by omega) g ht
  · rw [form4_eq_77 ha1 ha, form4_eq_168 hb1 hb]
    exact ⟨fun _ => rfl, by decide, by decide, by decide, by decide⟩
  · rw [form4_eq_168 ha1 ha, form4_eq_77 hb1 hb]
    exact ⟨fun x => Bool.and_comm _ _, by decide, by decide, by decide, by decide⟩

private theorem form4_two_221 {φ : DMFormula 4} (h2 : φ.leaves = 2) (ht : table8 φ = 221) :
    (∀ x, φ.eval x = (x 0 || x 3)) ∧
    count {0} φ = 1 ∧ count {1} φ = 0 ∧ count {2} φ = 0 ∧ count {3} φ = 1 := by
  obtain ⟨g, a, b, rfl, ha1, hb1⟩ := form4_split_two φ h2
  rw [table8_join] at ht
  have hca := cost8_le_leaves a
  have hcb := cost8_le_leaves b
  obtain ⟨rfl, ⟨ha, hb⟩ | ⟨ha, hb⟩⟩ := split221 (table8_lt a) (table8_lt b) (by omega) g ht
  · rw [form4_eq_77 ha1 ha, form4_eq_208 hb1 hb]
    exact ⟨fun _ => rfl, by decide, by decide, by decide, by decide⟩
  · rw [form4_eq_208 ha1 ha, form4_eq_77 hb1 hb]
    exact ⟨fun x => Bool.or_comm _ _, by decide, by decide, by decide, by decide⟩

private theorem form4_two_40 {φ : DMFormula 4} (h2 : φ.leaves = 2) (ht : table8 φ = 40) :
    ∀ x, φ.eval x = (x 2 && !(x 3)) := by
  obtain ⟨g, a, b, rfl, ha1, hb1⟩ := form4_split_two φ h2
  rw [table8_join] at ht
  have hca := cost8_le_leaves a
  have hcb := cost8_le_leaves b
  obtain ⟨rfl, ⟨ha, hb⟩ | ⟨ha, hb⟩⟩ := split40 (table8_lt a) (table8_lt b) (by omega) g ht
  · rw [form4_eq_168 ha1 ha, form4_eq_47 hb1 hb]; intro _; rfl
  · rw [form4_eq_47 ha1 ha, form4_eq_168 hb1 hb]; intro x; exact Bool.and_comm _ _

private theorem form4_three_20 {φ : DMFormula 4} (h3 : φ.leaves = 3) (ht : table8 φ = 20) :
    count {0} φ = 1 ∧ count {1} φ = 1 ∧ count {2} φ = 0 ∧ count {3} φ = 1 := by
  cases φ with
  | lit _ _ => simp [DMFormula.leaves] at h3
  | and a b =>
    have hca := cost8_le_leaves a; have hcb := cost8_le_leaves b
    simp only [DMFormula.leaves] at h3
    obtain ⟨_, ⟨ha, hb⟩ | ⟨ha, hb⟩⟩ := split20 (table8_lt a) (table8_lt b) (by omega) false ht
    · have hca' : cost8 (table8 a) = 1 := by rw [ha]; decide
      have hcb' : cost8 (table8 b) = 2 := by rw [hb]; decide
      have ha1 : a.leaves = 1 := by omega
      have hb2 : b.leaves = 2 := by omega
      obtain ⟨_, h0, h1, h2, h3'⟩ := form4_two_221 hb2 hb
      rw [form4_eq_54 ha1 ha]
      simp [count, h0, h1, h2, h3']
    · have hca' : cost8 (table8 a) = 2 := by rw [ha]; decide
      have hcb' : cost8 (table8 b) = 1 := by rw [hb]; decide
      have ha2 : a.leaves = 2 := by omega
      have hb1 : b.leaves = 1 := by omega
      obtain ⟨_, h0, h1, h2, h3'⟩ := form4_two_221 ha2 ha
      rw [form4_eq_54 hb1 hb]
      simp [count, h0, h1, h2, h3']
  | or a b =>
    have hca := cost8_le_leaves a; have hcb := cost8_le_leaves b
    simp only [DMFormula.leaves] at h3
    obtain ⟨habs, _⟩ := split20 (table8_lt a) (table8_lt b) (by omega) true ht
    contradiction

private def d4Index {n : ℕ} (b c ub : Fin n) (v : Fin n) : Fin 4 :=
  if v = b then 0 else if v = c then 1 else if v = ub then 2 else 3

private def d4Row {n : ℕ} (b c ub uc : Fin n) (m : ℕ) : Input n :=
  fun v =>
    if v = b then m.testBit 0
    else if v = c then m.testBit 1
    else if v = ub then m.testBit 2
    else if v = uc then m.testBit 3
    else false

private theorem d4Row_rename {n : ℕ} {b c ub uc : Fin n}
    (hbc : b ≠ c) (hbub : b ≠ ub) (hbuc : b ≠ uc)
    (hcub : c ≠ ub) (hcuc : c ≠ uc) (hubuc : ub ≠ uc)
    (φ : DMFormula n) (hp : outside {b, c, ub, uc} φ = 0) (m : ℕ) :
    (rename (d4Index b c ub) φ).eval (vals4 m) = φ.eval (d4Row b c ub uc m) := by
  rw [rename_eval]
  apply eval_agree {b, c, ub, uc} _ _ _ _ hp
  intro v hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl <;>
    simp [vals4, d4Index, d4Row, hbc, hbc.symm, hbub, hbub.symm, hbuc, hbuc.symm,
      hcub, hcub.symm, hcuc, hcuc.symm, hubuc, hubuc.symm]

private theorem rename_count_d4 {n : ℕ} {b c ub uc : Fin n}
    (hbc : b ≠ c) (hbub : b ≠ ub) (hbuc : b ≠ uc)
    (hcub : c ≠ ub) (hcuc : c ≠ uc) (hubuc : ub ≠ uc)
    (φ : DMFormula n) (hp : outside {b, c, ub, uc} φ = 0)
    (v : Fin n) (hv : v ∈ ({b, c, ub, uc} : Finset (Fin n))) :
    count {d4Index b c ub v} (rename (d4Index b c ub) φ) = count {v} φ := by
  induction φ using join_induct with
  | lit w pol =>
    have hw : w ∈ ({b, c, ub, uc} : Finset (Fin n)) := by
      by_contra hw
      have hw' : w ∈ ({b, c, ub, uc} : Finset (Fin n))ᶜ := by simpa using hw
      change (if w ∈ ({b, c, ub, uc} : Finset (Fin n))ᶜ then 1 else 0) = 0 at hp
      rw [if_pos hw'] at hp; omega
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv hw
    rcases hv with rfl | rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl | rfl <;>
      simp [rename, count, d4Index, hbc, hbc.symm, hbub, hbub.symm, hbuc, hbuc.symm,
        hcub, hcub.symm, hcuc, hcuc.symm, hubuc, hubuc.symm]
  | bin g x y hx hy =>
    rw [outside_join] at hp
    cases g <;> simp only [join, ite_true, ite_false, Bool.false_eq_true, rename, count,
      hx (by omega), hy (by omega)]

private theorem rename_d4_swap {n : ℕ} {b c ub uc : Fin n}
    (hbc : b ≠ c) (hbub : b ≠ ub) (hbuc : b ≠ uc)
    (hcub : c ≠ ub) (hcuc : c ≠ uc) (hubuc : ub ≠ uc)
    (φ : DMFormula n) (hp : outside {b, c, ub, uc} φ = 0) :
    rename (d4Index c b uc) φ = rename d4SwapFin (rename (d4Index b c ub) φ) := by
  induction φ using join_induct with
  | lit w pol =>
    have hw : w ∈ ({b, c, ub, uc} : Finset (Fin n)) := by
      by_contra hw
      have hw' : w ∈ ({b, c, ub, uc} : Finset (Fin n))ᶜ := by simpa using hw
      change (if w ∈ ({b, c, ub, uc} : Finset (Fin n))ᶜ then 1 else 0) = 0 at hp
      rw [if_pos hw'] at hp; omega
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl <;>
      simp [rename, d4Index, d4SwapFin, hbc, hbc.symm, hbub, hbub.symm, hbuc, hbuc.symm,
        hcub, hcub.symm, hcuc, hcuc.symm, hubuc, hubuc.symm]
  | bin g x y hx hy =>
    rw [outside_join] at hp
    cases g <;> simp only [join, ite_true, ite_false, Bool.false_eq_true, rename,
      hx (by omega), hy (by omega)]

private theorem d4_eval_from_form4 {n : ℕ} {b c ub uc : Fin n}
    (hbc : b ≠ c) (hbub : b ≠ ub) (hbuc : b ≠ uc)
    (hcub : c ≠ ub) (hcuc : c ≠ uc) (hubuc : ub ≠ uc)
    (A0 : DMFormula n) (hAo : outside {b, c, ub, uc} A0 = 0)
    (f : Input 4 → Bool) (hf : ∀ z, (rename (d4Index b c ub) A0).eval z = f z)
    (x : Input n) : A0.eval x = f ![x b, x c, x ub, x uc] := by
  have := hf ![x b, x c, x ub, x uc]
  rw [rename_eval] at this
  rw [← this]
  apply eval_agree {b, c, ub, uc} A0 _ _ _ hAo
  intro v hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl <;>
    simp [Function.comp_def, d4Index, hbc, hbc.symm, hbub, hbub.symm, hbuc, hbuc.symm,
      hcub, hcub.symm, hcuc, hcuc.symm, hubuc, hubuc.symm]

private theorem d4Row_eq_empty {n : ℕ} (b c ub uc : Fin n) :
    bits (∅ : Finset (Fin n)) = d4Row b c ub uc 0 := by
  funext v; simp [bits, d4Row]

private theorem d4Row_eq_ub {n : ℕ} {b c ub uc : Fin n}
    (hbub : b ≠ ub) (hcub : c ≠ ub) (hubuc : ub ≠ uc) :
    bits ({ub} : Finset (Fin n)) = d4Row b c ub uc 4 := by
  funext v
  by_cases hv : v = ub
  · subst v; simp [bits, d4Row, hbub.symm, hcub.symm]; decide
  · simp only [bits, d4Row, Finset.mem_singleton, hv, decide_false, ite_false]; split_ifs <;> decide

private theorem d4Row_eq_uc {n : ℕ} {b c ub uc : Fin n}
    (hbuc : b ≠ uc) (hcuc : c ≠ uc) (hubuc : ub ≠ uc) :
    bits ({uc} : Finset (Fin n)) = d4Row b c ub uc 8 := by
  funext v
  by_cases hv : v = uc
  · subst v; simp [bits, d4Row, hbuc.symm, hcuc.symm, hubuc.symm]; decide
  · simp only [bits, d4Row, Finset.mem_singleton, hv, decide_false, ite_false]; split_ifs <;> decide

private def killed {n : ℕ} (D : Finset (Fin n)) (x : Input n) (φ : DMFormula n) : ℕ :=
  outside D φ - weight (reduce D x φ)

private theorem killed_join {n : ℕ} (D : Finset (Fin n)) (x : Input n)
    (g : Bool) (a b : DMFormula n) :
    killed D x a + killed D x b ≤ killed D x (join g a b) := by
  unfold killed
  rw [outside_join, reduce_join]
  have ha := reduce_le D a x
  have hb := reduce_le D b x
  have hc := combine_le g (reduce D x a) (reduce D x b)
  omega

private theorem killed_indep_of_zero {n : ℕ} (D : Finset (Fin n)) (φ : DMFormula n)
    (x y : Input n) (h : ∀ v, 0 < count {v} φ → x v = y v) :
    reduce D x φ = reduce D y φ := by
  induction φ using join_induct with
  | lit v pol =>
    have hv : x v = y v := h v (by simp [count])
    by_cases hmem : v ∈ D <;> simp [reduce, DMFormula.eval, hmem, hv]
  | bin g a b ha hb =>
    simp only [count_join] at h
    rw [reduce_join, reduce_join, ha (fun v hv => h v (by omega)), hb (fun v hv => h v (by omega))]

private theorem cofactor_kills {n : ℕ} (D : Finset (Fin n)) (φ : DMFormula n)
    (x1 x2 : Input n) (ho : 0 < outside D φ) (hne : cofactorNe D φ x1 x2) :
    1 ≤ killed D x1 φ ∨ 1 ≤ killed D x2 φ := by
  by_contra! h
  have h1 : outside D φ ≤ weight (reduce D x1 φ) := by unfold killed at h; omega
  have h2 : outside D φ ≤ weight (reduce D x2 φ) := by unfold killed at h; omega
  obtain ⟨y, hy⟩ := hne
  apply hy
  apply chunks_agree D φ _ _ (by simp +contextual [splice])
  intro ψ hψ
  have hp := chunks_pure D φ ψ hψ
  have he1 : ψ.eval (splice D x1 y) = ψ.eval x1 :=
    eval_agree D ψ _ _ (fun v hv => by simp [splice, hv]) hp
  have he2 : ψ.eval (splice D x2 y) = ψ.eval x2 :=
    eval_agree D ψ _ _ (fun v hv => by simp [splice, hv]) hp
  exact he1.trans ((chunks_fixed D φ x1 x2 ho h1 h2 ψ hψ).trans he2.symm)

private def rcount {n : ℕ} (S : Finset (Fin n)) : Reduced n → ℕ
  | .inl _ => 0
  | .inr ψ => count S ψ

private theorem rcount_combine {n : ℕ} (S : Finset (Fin n)) (g : Bool) (a b : Reduced n) :
    rcount S (combine g a b) ≤ rcount S a + rcount S b := by
  cases a with
  | inl c => cases c <;> cases g <;> cases b <;> simp [combine, rcount]
  | inr a =>
    cases b with
    | inl c => cases c <;> cases g <;> simp [combine, rcount]
    | inr b => simp [combine, rcount, count_join]

private theorem rcount_reduce_le {n : ℕ} (D S : Finset (Fin n)) (x : Input n) (φ : DMFormula n) :
    rcount S (reduce D x φ) ≤ count S φ := by
  induction φ using join_induct with
  | lit v b =>
    by_cases hD : v ∈ D <;> by_cases hS : v ∈ S <;> simp [reduce, rcount, count, hD, hS]
  | bin g a b ha hb =>
    rw [reduce_join, count_join]
    exact (rcount_combine S g _ _).trans (Nat.add_le_add ha hb)

private def Survive {n : ℕ} (D : Finset (Fin n)) (φ : DMFormula n) : Prop :=
  weight (reduce Dᶜ (bits ∅) φ) = count D φ

private theorem reduce_compl_le {n : ℕ} (D : Finset (Fin n)) (φ : DMFormula n) :
    weight (reduce Dᶜ (bits ∅) φ) ≤ count D φ := by
  have h := reduce_le Dᶜ φ (bits ∅)
  change weight (reduce Dᶜ (bits ∅) φ) ≤ count Dᶜᶜ φ at h
  rwa [compl_compl] at h

private theorem survive_join {n : ℕ} (D : Finset (Fin n)) (g : Bool) (a b : DMFormula n)
    (h : Survive D (join g a b)) : Survive D a ∧ Survive D b := by
  unfold Survive at h ⊢
  rw [reduce_join, count_join] at h
  have hc := combine_le g (reduce Dᶜ (bits ∅) a) (reduce Dᶜ (bits ∅) b)
  have ha := reduce_compl_le D a
  have hb := reduce_compl_le D b
  omega

private theorem survive_inr {n : ℕ} (D : Finset (Fin n)) (φ : DMFormula n)
    (hs : Survive D φ) (hpos : 0 < count D φ) :
    ∃ ψ, reduce Dᶜ (bits ∅) φ = .inr ψ ∧ ψ.leaves = count D φ ∧ outside D ψ = 0 ∧
      (∀ x, ψ.eval x = φ.eval (splice D x (bits ∅))) ∧
      (∀ v ∈ D, count {v} ψ = count {v} φ) := by
  cases hr : reduce Dᶜ (bits ∅) φ with
  | inl c =>
    unfold Survive at hs
    rw [hr] at hs
    simp [weight] at hs
    omega
  | inr ψ =>
    have hleaves : ψ.leaves = count D φ := by
      unfold Survive at hs; rw [hr] at hs; exact hs
    have hout : outside D ψ = 0 := reduce_scope Dᶜ (bits ∅) φ ψ hr
    have hev (x : Input n) : ψ.eval x = φ.eval (splice D x (bits ∅)) := by
      have := reduce_eval Dᶜ φ (bits ∅) x
      rw [hr] at this
      change ψ.eval x = φ.eval (splice Dᶜ (bits ∅) x) at this
      rw [this]
      congr 1
      funext v
      by_cases hv : v ∈ D <;> simp [splice, hv]
    have hcnt (v : Fin n) (hv : v ∈ D) : count {v} ψ = count {v} φ := by
      have hle (w : Fin n) : count {w} ψ ≤ count {w} φ := by
        have := rcount_reduce_le Dᶜ {w} (bits ∅) φ
        rwa [hr] at this
      have hsum : ∑ w ∈ D, count {w} ψ = ∑ w ∈ D, count {w} φ := by
        rw [← count_sum, ← count_sum]
        have := count_add_outside D ψ
        omega
      by_contra hne
      have hlt : count {v} ψ < count {v} φ := lt_of_le_of_ne (hle v) hne
      have hlt_sum := Finset.sum_lt_sum (fun w _ => hle w) ⟨v, hv, hlt⟩
      omega
    exact ⟨ψ, rfl, hleaves, hout, hev, hcnt⟩

private theorem strip_core {n : ℕ} (D : Finset (Fin n)) (ya : Input n) (φ : DMFormula n)
    (hpos : 0 < count D φ) (hs : Survive D φ)
    (hnc : ∃ x1 x2, φ.eval (splice D x1 ya) ≠ φ.eval (splice D x2 ya)) :
    ∃ ψ, (∀ v ∈ D, count {v} ψ = count {v} φ) ∧ count D ψ = count D φ ∧ Survive D ψ ∧
      (∀ x, ψ.eval (splice D x (bits ∅)) = φ.eval (splice D x (bits ∅))) ∧
      (∀ x, ψ.eval (splice D x ya) = φ.eval (splice D x ya)) ∧
      (∀ x, killed D x ψ ≤ killed D x φ) ∧
      (count D ψ = 1 ∨ ∃ g a b, ψ = join g a b ∧ 0 < count D a ∧ 0 < count D b) := by
  induction φ using join_induct with
  | lit v pol =>
    have hv : v ∈ D := by by_contra hv; simp [count, hv] at hpos
    exact ⟨.lit v pol, fun _ _ => rfl, rfl, hs, fun _ => rfl, fun _ => rfl, fun _ => le_rfl,
      .inl (by simp [count, hv])⟩
  | bin g a b ha hb =>
    obtain ⟨hsa, hsb⟩ := survive_join D g a b hs
    rw [count_join] at hpos
    by_cases ha0 : count D a = 0
    · have hpa : outside Dᶜ a = 0 := by change count Dᶜᶜ a = 0; rwa [compl_compl]
      have ha_const (y x : Input n) : a.eval (splice D x y) = a.eval y :=
        eval_agree Dᶜ a _ _ (fun v hv => by simp [splice, Finset.mem_compl.mp hv]) hpa
      have ha_y0 : a.eval (bits ∅) ≠ g := by
        intro heq
        unfold Survive at hs
        rw [reduce_join, count_join, reduce_pure Dᶜ a (bits ∅) hpa, heq] at hs
        simp [combine, weight] at hs
        omega
      have ha_ya : a.eval ya ≠ g := by
        intro heq
        obtain ⟨x1, x2, hne⟩ := hnc
        apply hne
        rw [join_eval, join_eval, ha_const ya x1, ha_const ya x2, heq]
        cases g <;> simp [gate]
      have hev0 (x : Input n) : (join g a b).eval (splice D x (bits ∅)) = b.eval (splice D x (bits ∅)) := by
        rw [join_eval, ha_const (bits ∅) x]
        cases g <;> cases h : a.eval (bits ∅) <;> simp_all [gate]
      have heva (x : Input n) : (join g a b).eval (splice D x ya) = b.eval (splice D x ya) := by
        rw [join_eval, ha_const ya x]
        cases g <;> cases h : a.eval ya <;> simp_all [gate]
      have hncb : ∃ x1 x2, b.eval (splice D x1 ya) ≠ b.eval (splice D x2 ya) := by
        obtain ⟨x1, x2, hne⟩ := hnc
        exact ⟨x1, x2, by rwa [← heva x1, ← heva x2]⟩
      obtain ⟨ψ, hvc, hc, hsp, h0, h1, hk, hstr⟩ := hb (by omega) hsb hncb
      refine ⟨ψ, fun v hv => ?_, ?_, hsp, fun x => (h0 x).trans (hev0 x).symm,
        fun x => (h1 x).trans (heva x).symm,
        fun x => (hk x).trans (Nat.le_trans (Nat.le_add_left _ _) (killed_join D x g a b)), hstr⟩
      · rw [hvc v hv, count_join]
        have hav : count {v} a = 0 := by
          rw [count_sum] at ha0
          have := Finset.single_le_sum (f := fun w => count {w} a) (fun _ _ => Nat.zero_le _) hv
          omega
        omega
      · rw [hc, count_join]; omega
    · by_cases hb0 : count D b = 0
      · have hpb : outside Dᶜ b = 0 := by change count Dᶜᶜ b = 0; rwa [compl_compl]
        have hb_const (y x : Input n) : b.eval (splice D x y) = b.eval y :=
          eval_agree Dᶜ b _ _ (fun v hv => by simp [splice, Finset.mem_compl.mp hv]) hpb
        have hb_y0 : b.eval (bits ∅) ≠ g := by
          intro heq
          unfold Survive at hs
          rw [reduce_join, count_join, reduce_pure Dᶜ b (bits ∅) hpb, heq] at hs
          cases hr : reduce Dᶜ (bits ∅) a <;> cases g <;> simp [combine, weight, hr] at hs <;> omega
        have hb_ya : b.eval ya ≠ g := by
          intro heq
          obtain ⟨x1, x2, hne⟩ := hnc
          apply hne
          rw [join_eval, join_eval, hb_const ya x1, hb_const ya x2, heq]
          cases g <;> simp [gate]
        have hev0 (x : Input n) : (join g a b).eval (splice D x (bits ∅)) = a.eval (splice D x (bits ∅)) := by
          rw [join_eval, hb_const (bits ∅) x]
          cases g <;> cases h : b.eval (bits ∅) <;> simp_all [gate]
        have heva (x : Input n) : (join g a b).eval (splice D x ya) = a.eval (splice D x ya) := by
          rw [join_eval, hb_const ya x]
          cases g <;> cases h : b.eval ya <;> simp_all [gate]
        have hnca : ∃ x1 x2, a.eval (splice D x1 ya) ≠ a.eval (splice D x2 ya) := by
          obtain ⟨x1, x2, hne⟩ := hnc
          exact ⟨x1, x2, by rwa [← heva x1, ← heva x2]⟩
        obtain ⟨ψ, hvc, hc, hsp, h0, h1, hk, hstr⟩ := ha (by omega) hsa hnca
        refine ⟨ψ, fun v hv => ?_, ?_, hsp, fun x => (h0 x).trans (hev0 x).symm,
          fun x => (h1 x).trans (heva x).symm,
          fun x => (hk x).trans (Nat.le_trans (Nat.le_add_right _ _) (killed_join D x g a b)), hstr⟩
        · rw [hvc v hv, count_join]
          have hbv : count {v} b = 0 := by
            rw [count_sum] at hb0
            have := Finset.single_le_sum (f := fun w => count {w} b) (fun _ _ => Nat.zero_le _) hv
            omega
          omega
        · rw [hc, count_join]; omega
      · exact ⟨join g a b, fun _ _ => rfl, rfl, hs, fun _ => rfl, fun _ => rfl,
          fun _ => le_rfl, .inr ⟨g, a, b, rfl, by omega, by omega⟩⟩

private theorem two_leaf_and_kills {n : ℕ} {b c ub uc : Fin n}
    (hbc : b ≠ c) (hbub : b ≠ ub) (hbuc : b ≠ uc)
    (hcub : c ≠ ub) (hcuc : c ≠ uc) (hubuc : ub ≠ uc)
    (ya : Input n) (φ : DMFormula n)
    (hc : count ({b, c, ub, uc} : Finset (Fin n)) φ = 2)
    (hs : Survive {b, c, ub, uc} φ)
    (hev0 : ∀ x, φ.eval (splice {b, c, ub, uc} x (bits ∅)) = (x b && x ub))
    (ha0 : φ.eval (splice {b, c, ub, uc} (bits ∅) ya) = false)
    (hab : φ.eval (splice {b, c, ub, uc} (bits {b}) ya) = true) :
    1 ≤ killed {b, c, ub, uc} (bits ∅) φ ∨ 1 ≤ killed {b, c, ub, uc} (bits {ub}) φ := by
  let D : Finset (Fin n) := {b, c, ub, uc}
  change count D φ = 2 at hc
  have hnc : ∃ x1 x2, φ.eval (splice D x1 ya) ≠ φ.eval (splice D x2 ya) :=
    ⟨bits ∅, bits {b}, by rw [ha0, hab]; decide⟩
  obtain ⟨ψ, _, hψc, hψs, hψ0, hψa, hψk, hstr⟩ := strip_core D ya φ (by omega) hs hnc
  rcases hstr with h1 | ⟨g, A, B, rfl, hAp, hBp⟩
  · omega
  obtain ⟨hAs, hBs⟩ := survive_join D g A B hψs
  rw [count_join] at hψc
  have hAc : count D A = 1 := by omega
  have hBc : count D B = 1 := by omega
  obtain ⟨A0, _, hAl, hAo, hAe, hAcnt⟩ := survive_inr D A hAs hAp
  obtain ⟨B0, _, hBl, hBo, hBe, hBcnt⟩ := survive_inr D B hBs hBp
  let rA := rename (d4Index b c ub) A0
  let rB := rename (d4Index b c ub) B0
  have ht : (if g then table8 rA ||| table8 rB else table8 rA &&& table8 rB) = 8 := by
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < 8
    · have haux : ∀ idx : Fin 8,
          (if g then table8 rA ||| table8 rB else table8 rA &&& table8 rB).testBit idx.val =
            (8 : ℕ).testBit idx.val := by
        intro idx
        have he1 : (table8 rA).testBit idx.val = A.eval (splice D (d4Row b c ub uc (rows8 idx)) (bits ∅)) := by
          rw [table8_eval rA idx, d4Row_rename hbc hbub hbuc hcub hcuc hubuc A0 hAo, hAe]
        have he2 : (table8 rB).testBit idx.val = B.eval (splice D (d4Row b c ub uc (rows8 idx)) (bits ∅)) := by
          rw [table8_eval rB idx, d4Row_rename hbc hbub hbuc hcub hcuc hubuc B0 hBo, hBe]
        have htot : (join g A B).eval (splice D (d4Row b c ub uc (rows8 idx)) (bits ∅)) = (8 : ℕ).testBit idx.val := by
          rw [hψ0, hev0]
          fin_cases idx <;> simp [rows8, d4Row, hbc, hbc.symm, hbub, hbub.symm, hbuc, hbuc.symm,
            hcub, hcub.symm, hcuc, hcuc.symm, hubuc, hubuc.symm] <;> decide
        cases g
        · simp only [Bool.false_eq_true, ite_false, Nat.testBit_and, he1, he2]
          simpa [join_eval, gate] using htot
        · simp only [ite_true, Nat.testBit_or, he1, he2]
          simpa [join_eval, gate] using htot
      exact haux ⟨i, hi⟩
    · have hlt : (if g then table8 rA ||| table8 rB else table8 rA &&& table8 rB) < 2 ^ 8 := by
        cases g
        · exact Nat.lt_of_le_of_lt Nat.and_le_left (table8_lt rA)
        · exact Nat.or_lt_two_pow (n := 8) (table8_lt rA) (table8_lt rB)
      rw [Nat.testBit_eq_false_of_lt (hlt.trans_le (Nat.pow_le_pow_right (i := 8) (by decide : 0 < 2) (by omega))),
        Nat.testBit_eq_false_of_lt ((show 8 < 2 ^ 8 by decide).trans_le (Nat.pow_le_pow_right (i := 8) (by decide : 0 < 2) (by omega)))]
  have hcA : cost8 (table8 rA) ≤ 1 := (cost8_le_leaves rA).trans (by rw [rename_leaves, hAl, hAc])
  have hcB : cost8 (table8 rB) ≤ 1 := (cost8_le_leaves rB).trans (by rw [rename_leaves, hBl, hBc])
  obtain ⟨rfl, ⟨hA77, hB168⟩ | ⟨hA168, hB77⟩⟩ := split8 (table8_lt rA) (table8_lt rB) (by omega) g ht
  · have hrB : rB = .lit 2 true := form4_eq_168 (by rw [rename_leaves, hBl, hBc]) hB168
    have hBb0 : count {b} B = 0 := by
      rw [← hBcnt b (by simp [D]), ← rename_count_d4 hbc hbub hbuc hcub hcuc hubuc B0 hBo b (by simp [D])]
      change count {d4Index b c ub b} rB = 0
      rw [hrB]; simp [d4Index, count]
    have hBa_b : B.eval (splice D (bits {b}) ya) = true := by
      have := (hψa (bits {b})).trans hab
      simp [join_eval, gate] at this
      exact this.2
    have hBa_0 : B.eval (splice D (bits ∅) ya) = true := by
      rw [← hBa_b]
      apply eval_occ_agree B _ _
      intro v hv
      have hvb : v ≠ b := by rintro rfl; omega
      by_cases hvD : v ∈ D <;> simp [splice, bits, hvD, hvb]
    have hB0_ev (m : ℕ) : B.eval (splice D (d4Row b c ub uc m) (bits ∅)) = m.testBit 2 := by
      rw [← hBe, ← d4Row_rename hbc hbub hbuc hcub hcuc hubuc B0 hBo m]
      change rB.eval (vals4 m) = m.testBit 2
      rw [hrB]; rfl
    have hB0_0 : B.eval (splice D (bits ∅) (bits ∅)) = false := by
      have hsp : splice D (bits ∅) (bits ∅) = splice D (d4Row b c ub uc 0) (bits ∅) := by
        rw [← d4Row_eq_empty]
      rw [hsp, hB0_ev]; decide
    have hB0_ub : B.eval (splice D (bits {ub}) (bits ∅)) = true := by
      rw [d4Row_eq_ub hbub hcub hubuc, hB0_ev]; decide
    have hBo_pos : 0 < outside D B := by
      by_contra! hz
      have := eval_agree D B (splice D (bits ∅) (bits ∅)) (splice D (bits ∅) ya)
        (fun v hv => by simp [splice, hv]) (by omega)
      rw [hB0_0, hBa_0] at this; contradiction
    have hne : cofactorNe D B (bits ∅) (bits {ub}) := ⟨bits ∅, by rw [hB0_0, hB0_ub]; decide⟩
    rcases cofactor_kills D B (bits ∅) (bits {ub}) hBo_pos hne with h | h
    · exact .inl (h.trans ((Nat.le_add_left _ _).trans ((killed_join D _ false A B).trans (hψk _))))
    · exact .inr (h.trans ((Nat.le_add_left _ _).trans ((killed_join D _ false A B).trans (hψk _))))
  · have hrA : rA = .lit 2 true := form4_eq_168 (by rw [rename_leaves, hAl, hAc]) hA168
    have hAb0 : count {b} A = 0 := by
      rw [← hAcnt b (by simp [D]), ← rename_count_d4 hbc hbub hbuc hcub hcuc hubuc A0 hAo b (by simp [D])]
      change count {d4Index b c ub b} rA = 0
      rw [hrA]; simp [d4Index, count]
    have hAa_b : A.eval (splice D (bits {b}) ya) = true := by
      have := (hψa (bits {b})).trans hab
      simp [join_eval, gate] at this
      exact this.1
    have hAa_0 : A.eval (splice D (bits ∅) ya) = true := by
      rw [← hAa_b]
      apply eval_occ_agree A _ _
      intro v hv
      have hvb : v ≠ b := by rintro rfl; omega
      by_cases hvD : v ∈ D <;> simp [splice, bits, hvD, hvb]
    have hA0_ev (m : ℕ) : A.eval (splice D (d4Row b c ub uc m) (bits ∅)) = m.testBit 2 := by
      rw [← hAe, ← d4Row_rename hbc hbub hbuc hcub hcuc hubuc A0 hAo m]
      change rA.eval (vals4 m) = m.testBit 2
      rw [hrA]; rfl
    have hA0_0 : A.eval (splice D (bits ∅) (bits ∅)) = false := by
      have hsp : splice D (bits ∅) (bits ∅) = splice D (d4Row b c ub uc 0) (bits ∅) := by
        rw [← d4Row_eq_empty]
      rw [hsp, hA0_ev]; decide
    have hA0_ub : A.eval (splice D (bits {ub}) (bits ∅)) = true := by
      rw [d4Row_eq_ub hbub hcub hubuc, hA0_ev]; decide
    have hAo_pos : 0 < outside D A := by
      by_contra! hz
      have := eval_agree D A (splice D (bits ∅) (bits ∅)) (splice D (bits ∅) ya)
        (fun v hv => by simp [splice, hv]) (by omega)
      rw [hA0_0, hAa_0] at this; contradiction
    have hne : cofactorNe D A (bits ∅) (bits {ub}) := ⟨bits ∅, by rw [hA0_0, hA0_ub]; decide⟩
    rcases cofactor_kills D A (bits ∅) (bits {ub}) hAo_pos hne with h | h
    · exact .inl (h.trans ((Nat.le_add_right _ _).trans ((killed_join D _ false A B).trans (hψk _))))
    · exact .inr (h.trans ((Nat.le_add_right _ _).trans ((killed_join D _ false A B).trans (hψk _))))

private def d4Assign {n : ℕ} (ub uc : Fin n) (u1 u2 : Bool) : Input n :=
  fun v => if v = ub then u1 else if v = uc then u2 else false

private theorem d4_combine_kills {n : ℕ} {b c ub uc : Fin n}
    (hbub : b ≠ ub) (hbuc : b ≠ uc) (hcub : c ≠ ub) (hcuc : c ≠ uc) (hubuc : ub ≠ uc)
    (g : Bool) (A B : DMFormula n)
    (hAuc : count {uc} A = 0) (hBub : count {ub} B = 0)
    (hA : 1 ≤ killed {b, c, ub, uc} (bits ∅) A ∨ 1 ≤ killed {b, c, ub, uc} (bits {ub}) A)
    (hB : 1 ≤ killed {b, c, ub, uc} (bits ∅) B ∨ 1 ≤ killed {b, c, ub, uc} (bits {uc}) B) :
    ∃ u1 u2 : Bool, 2 ≤ killed {b, c, ub, uc} (d4Assign ub uc u1 u2) (join g A B) := by
  let D : Finset (Fin n) := {b, c, ub, uc}
  obtain ⟨u1, hu1⟩ : ∃ u1 : Bool, 1 ≤ killed D (d4Assign ub uc u1 false) A := by
    rcases hA with h | h
    · refine ⟨false, ?_⟩
      convert h using 2
      funext v; simp [d4Assign, bits]
    · refine ⟨true, ?_⟩
      convert h using 2
      funext v; by_cases hv : v = ub <;> simp [d4Assign, bits, hv]
  obtain ⟨u2, hu2⟩ : ∃ u2 : Bool, 1 ≤ killed D (d4Assign ub uc false u2) B := by
    rcases hB with h | h
    · refine ⟨false, ?_⟩
      convert h using 2
      funext v; simp [d4Assign, bits]
    · refine ⟨true, ?_⟩
      convert h using 2
      funext v; by_cases hv : v = uc <;> simp [d4Assign, bits, hv, hubuc.symm]
  refine ⟨u1, u2, ?_⟩
  have hEqA : killed D (d4Assign ub uc u1 u2) A = killed D (d4Assign ub uc u1 false) A := by
    unfold killed
    rw [killed_indep_of_zero D A (d4Assign ub uc u1 u2) (d4Assign ub uc u1 false)]
    intro v hv
    have hne : v ≠ uc := by rintro rfl; omega
    simp [d4Assign, hne]
  have hEqB : killed D (d4Assign ub uc u1 u2) B = killed D (d4Assign ub uc false u2) B := by
    unfold killed
    rw [killed_indep_of_zero D B (d4Assign ub uc u1 u2) (d4Assign ub uc false u2)]
    intro v hv
    have hne : v ≠ ub := by rintro rfl; omega
    simp [d4Assign, hne]
  have hj := killed_join D (d4Assign ub uc u1 u2) g A B
  change 2 ≤ killed D (d4Assign ub uc u1 u2) (join g A B)
  omega

private theorem handle_typeI {n : ℕ} {b c ub uc : Fin n}
    (hbc : b ≠ c) (hbub : b ≠ ub) (hbuc : b ≠ uc)
    (hcub : c ≠ ub) (hcuc : c ≠ uc) (hubuc : ub ≠ uc)
    (ya : Input n) (A B : DMFormula n)
    (hAs : Survive {b, c, ub, uc} A) (hBs : Survive {b, c, ub, uc} B)
    (hAc : count {b, c, ub, uc} A = 2) (hBc : count {b, c, ub, uc} B = 3)
    (hA0 : ∀ A0, reduce ({b, c, ub, uc} : Finset (Fin n))ᶜ (bits ∅) A = .inr A0 →
      table8 (rename (d4Index b c ub) A0) = 8)
    (hB0 : ∀ B0, reduce ({b, c, ub, uc} : Finset (Fin n))ᶜ (bits ∅) B = .inr B0 →
      table8 (rename (d4Index b c ub) B0) = 20)
    (heva : ∀ x, (join true A B).eval (splice {b, c, ub, uc} x ya) = (x b || x c)) :
    ∃ u1 u2 : Bool, 2 ≤ killed {b, c, ub, uc} (d4Assign ub uc u1 u2) (join true A B) := by
  let D : Finset (Fin n) := {b, c, ub, uc}
  change count D A = 2 at hAc
  change count D B = 3 at hBc
  change ∀ x, (join true A B).eval (splice D x ya) = (x b || x c) at heva
  obtain ⟨A0, hAr, hAl, hAo, hAe, hAcnt⟩ := survive_inr D A hAs (by omega)
  obtain ⟨B0, hBr, hBl, hBo, hBe, hBcnt⟩ := survive_inr D B hBs (by omega)
  have htA := hA0 A0 hAr
  have htB := hB0 B0 hBr
  obtain ⟨hAeval, _, hAc0, _, hAuc0⟩ := form4_two_8 (by rw [rename_leaves, hAl, hAc]) htA
  obtain ⟨_, _, hBub0, _⟩ := form4_three_20 (by rw [rename_leaves, hBl, hBc]) htB
  have hAc_zero : count {c} A = 0 := by
    rw [← hAcnt c (by simp [D]), ← rename_count_d4 hbc hbub hbuc hcub hcuc hubuc A0 hAo c (by simp [D])]
    simpa [d4Index, hbc.symm] using hAc0
  have hAuc_zero : count {uc} A = 0 := by
    rw [← hAcnt uc (by simp [D]), ← rename_count_d4 hbc hbub hbuc hcub hcuc hubuc A0 hAo uc (by simp [D])]
    simpa [d4Index, hbuc.symm, hcuc.symm, hubuc.symm] using hAuc0
  have hBub_zero : count {ub} B = 0 := by
    rw [← hBcnt ub (by simp [D]), ← rename_count_d4 hbc hbub hbuc hcub hcuc hubuc B0 hBo ub (by simp [D])]
    simpa [d4Index, hbub.symm, hcub.symm] using hBub0
  have h0_ab := heva (bits ∅)
  simp only [join_eval, gate, ite_true, bits, Finset.notMem_empty, decide_false, Bool.or_self,
    Bool.or_eq_false_iff] at h0_ab
  have hAa0 : A.eval (splice D (bits ∅) ya) = false := h0_ab.1
  have hBa0 : B.eval (splice D (bits ∅) ya) = false := h0_ab.2
  have hAac : A.eval (splice D (bits {c}) ya) = false := by
    rw [← hAa0]
    apply eval_occ_agree A _ _
    intro v hv
    have hvc : v ≠ c := by rintro rfl; omega
    by_cases hvD : v ∈ D <;> simp [splice, bits, hvD, hvc]
  have hBac : B.eval (splice D (bits {c}) ya) = true := by
    have hc_ab := heva (bits {c})
    simp only [join_eval, gate, ite_true, bits, Finset.mem_singleton, decide_true,
      Bool.or_true, hAac, Bool.false_or] at hc_ab
    exact hc_ab
  -- Strip B to coreB = B1 ∧ B2
  have hncB : ∃ x1 x2, B.eval (splice D x1 ya) ≠ B.eval (splice D x2 ya) :=
    ⟨bits ∅, bits {c}, by rw [hBa0, hBac]; decide⟩
  obtain ⟨cB, _, hcBc, hcBs, hcB0, hcBa, hcBk, hstrB⟩ := strip_core D ya B (by omega) hBs hncB
  rcases hstrB with h1 | ⟨gB, B1, B2, rfl, hB1p, hB2p⟩
  · omega
  obtain ⟨hB1s, hB2s⟩ := survive_join D gB B1 B2 hcBs
  rw [count_join] at hcBc
  obtain ⟨B10, hB1r, hB1l, hB1o, hB1e, hB1cnt⟩ := survive_inr D B1 hB1s hB1p
  obtain ⟨B20, hB2r, hB2l, hB2o, hB2e, hB2cnt⟩ := survive_inr D B2 hB2s hB2p
  let rB1 := rename (d4Index b c ub) B10
  let rB2 := rename (d4Index b c ub) B20
  have htB_eq : (if gB then table8 rB1 ||| table8 rB2 else table8 rB1 &&& table8 rB2) = 20 := by
    rw [← htB]
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < 8
    · let idx : Fin 8 := ⟨i, hi⟩
      have hL1 : (table8 rB1).testBit i = B1.eval (splice D (d4Row b c ub uc (rows8 idx)) (bits ∅)) := by
        rw [table8_eval rB1 idx, d4Row_rename hbc hbub hbuc hcub hcuc hubuc B10 hB1o, hB1e]
      have hL2 : (table8 rB2).testBit i = B2.eval (splice D (d4Row b c ub uc (rows8 idx)) (bits ∅)) := by
        rw [table8_eval rB2 idx, d4Row_rename hbc hbub hbuc hcub hcuc hubuc B20 hB2o, hB2e]
      have hR : (table8 (rename (d4Index b c ub) B0)).testBit i =
          B.eval (splice D (d4Row b c ub uc (rows8 idx)) (bits ∅)) := by
        rw [table8_eval _ idx, d4Row_rename hbc hbub hbuc hcub hcuc hubuc B0 hBo, hBe]
      have htot := hcB0 (d4Row b c ub uc (rows8 idx))
      cases gB
      · simp only [Bool.false_eq_true, ite_false, Nat.testBit_and, hL1, hL2, hR]
        simpa [join_eval, gate] using htot
      · simp only [ite_true, Nat.testBit_or, hL1, hL2, hR]
        simpa [join_eval, gate] using htot
    · have hltL : (if gB then table8 rB1 ||| table8 rB2 else table8 rB1 &&& table8 rB2) < 2 ^ 8 := by
        cases gB
        · exact Nat.lt_of_le_of_lt Nat.and_le_left (table8_lt rB1)
        · exact Nat.or_lt_two_pow (n := 8) (table8_lt rB1) (table8_lt rB2)
      rw [Nat.testBit_eq_false_of_lt (hltL.trans_le (Nat.pow_le_pow_right (i := 8) (by decide : 0 < 2) (by omega))),
        Nat.testBit_eq_false_of_lt ((table8_lt _).trans_le (Nat.pow_le_pow_right (i := 8) (by decide : 0 < 2) (by omega)))]
  have hcB1 : cost8 (table8 rB1) ≤ count D B1 := (cost8_le_leaves rB1).trans (by rw [rename_leaves, hB1l])
  have hcB2 : cost8 (table8 rB2) ≤ count D B2 := (cost8_le_leaves rB2).trans (by rw [rename_leaves, hB2l])
  obtain ⟨rfl, hsp⟩ := split20 (table8_lt rB1) (table8_lt rB2) (by omega) gB htB_eq
  -- Helper given ordered (C1 = c, C2 = b|uc)
  have hpart : ∀ (C1 C2 : DMFormula n) (hC1s : Survive D C1) (hC2s : Survive D C2)
      (hC1c : count D C1 = 1) (hC2c : count D C2 = 2)
      (hC1t : ∀ X, reduce Dᶜ (bits ∅) C1 = .inr X → table8 (rename (d4Index b c ub) X) = 54)
      (hC2t : ∀ X, reduce Dᶜ (bits ∅) C2 = .inr X → table8 (rename (d4Index b c ub) X) = 221)
      (h0_eq : (join false C1 C2).eval (splice D (bits ∅) ya) = false)
      (hc_eq : (join false C1 C2).eval (splice D (bits {c}) ya) = true)
      (hb_eq : (join false C1 C2).eval (splice D (bits {b}) ya) = B.eval (splice D (bits {b}) ya))
      (hk_le : ∀ x, killed D x C2 ≤ killed D x B),
      B.eval (splice D (bits {b}) ya) = false ∧
      (1 ≤ killed D (bits ∅) B ∨ 1 ≤ killed D (bits {uc}) B) := by
    intro C1 C2 hC1s hC2s hC1c hC2c hC1t hC2t h0_eq hc_eq hb_eq hk_le
    obtain ⟨X1, hX1r, hX1l, hX1o, _, hX1cnt⟩ := survive_inr D C1 hC1s (by omega)
    obtain ⟨X2, hX2r, hX2l, hX2o, hX2e, hX2cnt⟩ := survive_inr D C2 hC2s (by omega)
    have hX1 := form4_eq_54 (by rw [rename_leaves, hX1l, hC1c]) (hC1t X1 hX1r)
    obtain ⟨hX2ev, _, hX2c0, _, _⟩ := form4_two_221 (by rw [rename_leaves, hX2l, hC2c]) (hC2t X2 hX2r)
    have hC1b0 : count {b} C1 = 0 := by
      rw [← hX1cnt b (by simp [D]), ← rename_count_d4 hbc hbub hbuc hcub hcuc hubuc X1 hX1o b (by simp [D]), hX1]
      simp [d4Index, count]
    have hC2c0 : count {c} C2 = 0 := by
      rw [← hX2cnt c (by simp [D]), ← rename_count_d4 hbc hbub hbuc hcub hcuc hubuc X2 hX2o c (by simp [D])]
      simpa [d4Index, hbc.symm] using hX2c0
    simp only [join_eval, gate, Bool.false_eq_true, ite_false, Bool.and_eq_true] at hc_eq
    have hC2a0 : C2.eval (splice D (bits ∅) ya) = true := by
      rw [← hc_eq.2]
      apply eval_occ_agree C2 _ _
      intro v hv
      have hvc : v ≠ c := by rintro rfl; omega
      by_cases hvD : v ∈ D <;> simp [splice, bits, hvD, hvc]
    have hC1a0 : C1.eval (splice D (bits ∅) ya) = false := by
      simp only [join_eval, gate, Bool.false_eq_true, ite_false, hC2a0, Bool.and_true] at h0_eq
      exact h0_eq
    have hC1ab : C1.eval (splice D (bits {b}) ya) = false := by
      rw [← hC1a0]
      apply eval_occ_agree C1 _ _
      intro v hv
      have hvb : v ≠ b := by rintro rfl; omega
      by_cases hvD : v ∈ D <;> simp [splice, bits, hvD, hvb]
    have hBab : B.eval (splice D (bits {b}) ya) = false := by
      rw [← hb_eq, join_eval, hC1ab]; rfl
    have hC20_ev (m : ℕ) : C2.eval (splice D (d4Row b c ub uc m) (bits ∅)) = (m.testBit 0 || m.testBit 3) := by
      rw [← hX2e, ← d4Row_rename hbc hbub hbuc hcub hcuc hubuc X2 hX2o m, hX2ev]
      rfl
    have hC20_0 : C2.eval (splice D (bits ∅) (bits ∅)) = false := by
      have hsp : splice D (bits ∅) (bits ∅) = splice D (d4Row b c ub uc 0) (bits ∅) := by
        rw [← d4Row_eq_empty]
      rw [hsp, hC20_ev]; decide
    have hC20_uc : C2.eval (splice D (bits {uc}) (bits ∅)) = true := by
      rw [d4Row_eq_uc hbuc hcuc hubuc, hC20_ev]; decide
    have hC2o_pos : 0 < outside D C2 := by
      by_contra! hz
      have := eval_agree D C2 (splice D (bits ∅) (bits ∅)) (splice D (bits ∅) ya)
        (fun v hv => by simp [splice, hv]) (by omega)
      rw [hC20_0, hC2a0] at this; contradiction
    have hne : cofactorNe D C2 (bits ∅) (bits {uc}) := ⟨bits ∅, by rw [hC20_0, hC20_uc]; decide⟩
    exact ⟨hBab, (cofactor_kills D C2 (bits ∅) (bits {uc}) hC2o_pos hne).imp
      (fun h => h.trans (hk_le _)) (fun h => h.trans (hk_le _))⟩
  have ⟨hBab, hBk⟩ : B.eval (splice D (bits {b}) ya) = false ∧
      (1 ≤ killed D (bits ∅) B ∨ 1 ≤ killed D (bits {uc}) B) := by
    rcases hsp with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hc1' : cost8 (table8 rB1) = 1 := by rw [h1]; decide
      have hc2' : cost8 (table8 rB2) = 2 := by rw [h2]; decide
      exact hpart B1 B2 hB1s hB2s (by omega) (by omega)
        (fun X hX => by rw [hB1r] at hX; cases hX; exact h1)
        (fun X hX => by rw [hB2r] at hX; cases hX; exact h2)
        ((hcBa _).trans hBa0) ((hcBa _).trans hBac) (hcBa _)
        (fun x => (Nat.le_add_left _ _).trans ((killed_join D x false B1 B2).trans (hcBk x)))
    · have hc1' : cost8 (table8 rB1) = 2 := by rw [h1]; decide
      have hc2' : cost8 (table8 rB2) = 1 := by rw [h2]; decide
      exact hpart B2 B1 hB2s hB1s (by omega) (by omega)
        (fun X hX => by rw [hB2r] at hX; cases hX; exact h2)
        (fun X hX => by rw [hB1r] at hX; cases hX; exact h1)
        (by rw [join_eval]; simp only [gate, Bool.false_eq_true, ite_false]; rw [Bool.and_comm]; exact (hcBa _).trans hBa0)
        (by rw [join_eval]; simp only [gate, Bool.false_eq_true, ite_false]; rw [Bool.and_comm]; exact (hcBa _).trans hBac)
        (by rw [join_eval]; simp only [gate, Bool.false_eq_true, ite_false]; rw [Bool.and_comm]; exact hcBa _)
        (fun x => (Nat.le_add_right _ _).trans ((killed_join D x false B1 B2).trans (hcBk x)))
  have hAab : A.eval (splice D (bits {b}) ya) = true := by
    have hb_ab := heva (bits {b})
    simp only [join_eval, gate, ite_true, bits, Finset.mem_singleton, decide_true,
      Bool.true_or, hBab, Bool.or_false] at hb_ab
    exact hb_ab
  have hAe_all (x : Input n) : A.eval (splice D x (bits ∅)) = (x b && x ub) := by
    rw [← hAe]
    exact d4_eval_from_form4 hbc hbub hbuc hcub hcuc hubuc A0 hAo (fun z => z 0 && z 2) hAeval x
  have hAk := two_leaf_and_kills hbc hbub hbuc hcub hcuc hubuc ya A hAc hAs hAe_all hAa0 hAab
  exact d4_combine_kills hbub hbuc hcub hcuc hubuc true A B hAuc_zero hBub_zero hAk hBk


private theorem handle_typeII {n : ℕ} {b c ub uc : Fin n}
    (hbc : b ≠ c) (hbub : b ≠ ub) (hbuc : b ≠ uc)
    (hcub : c ≠ ub) (hcuc : c ≠ uc) (hubuc : ub ≠ uc)
    (ya : Input n) (A B : DMFormula n)
    (hAs : Survive {b, c, ub, uc} A) (hBs : Survive {b, c, ub, uc} B)
    (hAc : count {b, c, ub, uc} A = 2) (hBc : count {b, c, ub, uc} B = 3)
    (hA0 : ∀ A0, reduce ({b, c, ub, uc} : Finset (Fin n))ᶜ (bits ∅) A = .inr A0 →
      table8 (rename (d4Index b c ub) A0) = 221)
    (hB0 : ∀ B0, reduce ({b, c, ub, uc} : Finset (Fin n))ᶜ (bits ∅) B = .inr B0 →
      table8 (rename (d4Index b c ub) B0) = 62)
    (h13 : (join false A B).eval (splice {b, c, ub, uc} (d4Row b c ub uc 13) (bits ∅)) = true)
    (heva : ∀ x, (join false A B).eval (splice {b, c, ub, uc} x ya) = (x b || x c)) :
    ∃ u1 u2 : Bool, 2 ≤ killed {b, c, ub, uc} (d4Assign ub uc u1 u2) (join false A B) := by
  let D : Finset (Fin n) := {b, c, ub, uc}
  change count D A = 2 at hAc
  change count D B = 3 at hBc
  change ∀ x, (join false A B).eval (splice D x ya) = (x b || x c) at heva
  obtain ⟨A0, hAr, hAl, hAo, hAe, hAcnt⟩ := survive_inr D A hAs (by omega)
  obtain ⟨B0, hBr, hBl, hBo, hBe, hBcnt⟩ := survive_inr D B hBs (by omega)
  have htA := hA0 A0 hAr
  have htB := hB0 B0 hBr
  obtain ⟨hAeval, _, hAc0, hAub0, _⟩ := form4_two_221 (by rw [rename_leaves, hAl, hAc]) htA
  have hAc_zero : count {c} A = 0 := by
    rw [← hAcnt c (by simp [D]), ← rename_count_d4 hbc hbub hbuc hcub hcuc hubuc A0 hAo c (by simp [D])]
    simpa [d4Index, hbc.symm] using hAc0
  have hAub_zero : count {ub} A = 0 := by
    rw [← hAcnt ub (by simp [D]), ← rename_count_d4 hbc hbub hbuc hcub hcuc hubuc A0 hAo ub (by simp [D])]
    simpa [d4Index, hbub.symm, hcub.symm] using hAub0
  have hBab_pair : A.eval (splice D (bits {b}) ya) = true ∧ B.eval (splice D (bits {b}) ya) = true := by
    have := heva (bits {b})
    simp only [join_eval, gate, Bool.false_eq_true, ite_false, bits, Finset.mem_singleton, decide_true, Bool.true_or,
      Bool.and_eq_true] at this
    exact this
  have hBac_pair : A.eval (splice D (bits {c}) ya) = true ∧ B.eval (splice D (bits {c}) ya) = true := by
    have := heva (bits {c})
    simp only [join_eval, gate, Bool.false_eq_true, ite_false, bits, Finset.mem_singleton, decide_true, Bool.or_true,
      Bool.and_eq_true] at this
    exact this
  have hAa0 : A.eval (splice D (bits ∅) ya) = true := by
    rw [← hBac_pair.1]
    apply eval_occ_agree A _ _
    intro v hv
    have hvc : v ≠ c := by rintro rfl; omega
    by_cases hvD : v ∈ D <;> simp [splice, bits, hvD, hvc]
  have hBa0 : B.eval (splice D (bits ∅) ya) = false := by
    have := heva (bits ∅)
    simp only [join_eval, gate, Bool.false_eq_true, ite_false, bits, Finset.notMem_empty, decide_false, Bool.or_self,
      hAa0, Bool.true_and] at this
    exact this
  have hA0_ev (m : ℕ) : A.eval (splice D (d4Row b c ub uc m) (bits ∅)) = (m.testBit 0 || m.testBit 3) := by
    rw [← hAe, ← d4Row_rename hbc hbub hbuc hcub hcuc hubuc A0 hAo m, hAeval]
    rfl
  have hA0_0 : A.eval (splice D (bits ∅) (bits ∅)) = false := by
    have hsp : splice D (bits ∅) (bits ∅) = splice D (d4Row b c ub uc 0) (bits ∅) := by
      rw [← d4Row_eq_empty]
    rw [hsp, hA0_ev]; decide
  have hA0_uc : A.eval (splice D (bits {uc}) (bits ∅)) = true := by
    rw [d4Row_eq_uc hbuc hcuc hubuc, hA0_ev]; decide
  have hAo_pos : 0 < outside D A := by
    by_contra! hz
    have := eval_agree D A (splice D (bits ∅) (bits ∅)) (splice D (bits ∅) ya)
      (fun v hv => by simp [splice, hv]) (by omega)
    rw [hA0_0, hAa0] at this; contradiction
  have hAk : 1 ≤ killed D (bits ∅) A ∨ 1 ≤ killed D (bits {uc}) A :=
    cofactor_kills D A (bits ∅) (bits {uc}) hAo_pos ⟨bits ∅, by rw [hA0_0, hA0_uc]; decide⟩
  -- Strip B to coreB = B1 ∨ B2
  have hncB : ∃ x1 x2, B.eval (splice D x1 ya) ≠ B.eval (splice D x2 ya) :=
    ⟨bits ∅, bits {b}, by rw [hBa0, hBab_pair.2]; decide⟩
  obtain ⟨cB, hcBvc, hcBc, hcBs, hcB0, hcBa, hcBk, hstrB⟩ := strip_core D ya B (by omega) hBs hncB
  rcases hstrB with h1 | ⟨gB, B1, B2, rfl, hB1p, hB2p⟩
  · omega
  obtain ⟨hB1s, hB2s⟩ := survive_join D gB B1 B2 hcBs
  rw [count_join] at hcBc
  obtain ⟨B10, hB1r, hB1l, hB1o, hB1e, hB1cnt⟩ := survive_inr D B1 hB1s hB1p
  obtain ⟨B20, hB2r, hB2l, hB2o, hB2e, hB2cnt⟩ := survive_inr D B2 hB2s hB2p
  let rB1 := rename (d4Index b c ub) B10
  let rB2 := rename (d4Index b c ub) B20
  have htB_eq : (if gB then table8 rB1 ||| table8 rB2 else table8 rB1 &&& table8 rB2) = 62 := by
    rw [← htB]
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < 8
    · let idx : Fin 8 := ⟨i, hi⟩
      have hL1 : (table8 rB1).testBit i = B1.eval (splice D (d4Row b c ub uc (rows8 idx)) (bits ∅)) := by
        rw [table8_eval rB1 idx, d4Row_rename hbc hbub hbuc hcub hcuc hubuc B10 hB1o, hB1e]
      have hL2 : (table8 rB2).testBit i = B2.eval (splice D (d4Row b c ub uc (rows8 idx)) (bits ∅)) := by
        rw [table8_eval rB2 idx, d4Row_rename hbc hbub hbuc hcub hcuc hubuc B20 hB2o, hB2e]
      have hR : (table8 (rename (d4Index b c ub) B0)).testBit i =
          B.eval (splice D (d4Row b c ub uc (rows8 idx)) (bits ∅)) := by
        rw [table8_eval _ idx, d4Row_rename hbc hbub hbuc hcub hcuc hubuc B0 hBo, hBe]
      have htot := hcB0 (d4Row b c ub uc (rows8 idx))
      cases gB
      · simp only [Bool.false_eq_true, ite_false, Nat.testBit_and, hL1, hL2, hR]
        simpa [join_eval, gate] using htot
      · simp only [ite_true, Nat.testBit_or, hL1, hL2, hR]
        simpa [join_eval, gate] using htot
    · have hltL : (if gB then table8 rB1 ||| table8 rB2 else table8 rB1 &&& table8 rB2) < 2 ^ 8 := by
        cases gB
        · exact Nat.lt_of_le_of_lt Nat.and_le_left (table8_lt rB1)
        · exact Nat.or_lt_two_pow (n := 8) (table8_lt rB1) (table8_lt rB2)
      rw [Nat.testBit_eq_false_of_lt (hltL.trans_le (Nat.pow_le_pow_right (i := 8) (by decide : 0 < 2) (by omega))),
        Nat.testBit_eq_false_of_lt ((table8_lt _).trans_le (Nat.pow_le_pow_right (i := 8) (by decide : 0 < 2) (by omega)))]
  have hcB1 : cost8 (table8 rB1) ≤ count D B1 := (cost8_le_leaves rB1).trans (by rw [rename_leaves, hB1l])
  have hcB2 : cost8 (table8 rB2) ≤ count D B2 := (cost8_le_leaves rB2).trans (by rw [rename_leaves, hB2l])
  obtain ⟨rfl, hsp⟩ := split62 (table8_lt rB1) (table8_lt rB2) (by omega) gB htB_eq
  have hB13 : (join true B1 B2).eval (splice D (d4Row b c ub uc 13) (bits ∅)) = true := by
    rw [hcB0]
    simp only [join_eval, gate, Bool.false_eq_true, ite_false, Bool.and_eq_true] at h13
    exact h13.2
  have hno40 : ∀ (C1 C2 : DMFormula n) (hC1s : Survive D C1) (hC2s : Survive D C2)
      (hC1c : count D C1 = 1) (hC2c : count D C2 = 2)
      (hC1t : ∀ X, reduce Dᶜ (bits ∅) C1 = .inr X → table8 (rename (d4Index b c ub) X) = 54)
      (hC2t : ∀ X, reduce Dᶜ (bits ∅) C2 = .inr X → table8 (rename (d4Index b c ub) X) = 40)
      (h13c : (join true C1 C2).eval (splice D (d4Row b c ub uc 13) (bits ∅)) = true), False := by
    intro C1 C2 hC1s hC2s hC1c hC2c hC1t hC2t h13c
    obtain ⟨X1, hX1r, hX1l, hX1o, hX1e, _⟩ := survive_inr D C1 hC1s (by omega)
    obtain ⟨X2, hX2r, hX2l, hX2o, hX2e, _⟩ := survive_inr D C2 hC2s (by omega)
    have hX1 := form4_eq_54 (by rw [rename_leaves, hX1l, hC1c]) (hC1t X1 hX1r)
    have hX2 := form4_two_40 (by rw [rename_leaves, hX2l, hC2c]) (hC2t X2 hX2r)
    have h1 : C1.eval (splice D (d4Row b c ub uc 13) (bits ∅)) = false := by
      rw [← hX1e, ← d4Row_rename hbc hbub hbuc hcub hcuc hubuc X1 hX1o 13, hX1]
      decide
    have h2 : C2.eval (splice D (d4Row b c ub uc 13) (bits ∅)) = false := by
      rw [← hX2e, ← d4Row_rename hbc hbub hbuc hcub hcuc hubuc X2 hX2o 13, hX2]
      decide
    simp [join_eval, gate, h1, h2] at h13c
  have hpart : ∀ (C1 C2 : DMFormula n) (hC1s : Survive D C1) (hC2s : Survive D C2)
      (hC1c : count D C1 = 1) (hC2c : count D C2 = 2)
      (hC1t : ∀ X, reduce Dᶜ (bits ∅) C1 = .inr X → table8 (rename (d4Index b c ub) X) = 54)
      (hC2t : ∀ X, reduce Dᶜ (bits ∅) C2 = .inr X → table8 (rename (d4Index b c ub) X) = 8)
      (h0_eq : (join true C1 C2).eval (splice D (bits ∅) ya) = false)
      (hb_eq : (join true C1 C2).eval (splice D (bits {b}) ya) = true)
      (huc_eq : count {uc} C1 + count {uc} C2 = count {uc} B)
      (hk_le : ∀ x, killed D x C2 ≤ killed D x B),
      count {uc} B = 0 ∧ (1 ≤ killed D (bits ∅) B ∨ 1 ≤ killed D (bits {ub}) B) := by
    intro C1 C2 hC1s hC2s hC1c hC2c hC1t hC2t h0_eq hb_eq huc_eq hk_le
    obtain ⟨X1, hX1r, hX1l, hX1o, _, hX1cnt⟩ := survive_inr D C1 hC1s (by omega)
    obtain ⟨X2, hX2r, hX2l, hX2o, hX2e, hX2cnt⟩ := survive_inr D C2 hC2s (by omega)
    have hX1 := form4_eq_54 (by rw [rename_leaves, hX1l, hC1c]) (hC1t X1 hX1r)
    obtain ⟨hX2ev, _, _, _, hX2uc0⟩ := form4_two_8 (by rw [rename_leaves, hX2l, hC2c]) (hC2t X2 hX2r)
    have hC1b0 : count {b} C1 = 0 := by
      rw [← hX1cnt b (by simp [D]), ← rename_count_d4 hbc hbub hbuc hcub hcuc hubuc X1 hX1o b (by simp [D]), hX1]
      simp [d4Index, count]
    have hC1uc0 : count {uc} C1 = 0 := by
      rw [← hX1cnt uc (by simp [D]), ← rename_count_d4 hbc hbub hbuc hcub hcuc hubuc X1 hX1o uc (by simp [D]), hX1]
      simp [d4Index, count, hbuc.symm, hcuc.symm, hubuc.symm]
    have hC2uc0 : count {uc} C2 = 0 := by
      rw [← hX2cnt uc (by simp [D]), ← rename_count_d4 hbc hbub hbuc hcub hcuc hubuc X2 hX2o uc (by simp [D])]
      simpa [d4Index, hbuc.symm, hcuc.symm, hubuc.symm] using hX2uc0
    simp only [join_eval, gate, ite_true, Bool.or_eq_false_iff] at h0_eq
    have hC1ab : C1.eval (splice D (bits {b}) ya) = false := by
      rw [← h0_eq.1]
      apply eval_occ_agree C1 _ _
      intro v hv
      have hvb : v ≠ b := by rintro rfl; omega
      by_cases hvD : v ∈ D <;> simp [splice, bits, hvD, hvb]
    have hC2ab : C2.eval (splice D (bits {b}) ya) = true := by
      simp only [join_eval, gate, ite_true, hC1ab, Bool.false_or] at hb_eq
      exact hb_eq
    have hC2e_all (x : Input n) : C2.eval (splice D x (bits ∅)) = (x b && x ub) := by
      rw [← hX2e]
      exact d4_eval_from_form4 hbc hbub hbuc hcub hcuc hubuc X2 hX2o (fun z => z 0 && z 2) hX2ev x
    have hC2k := two_leaf_and_kills hbc hbub hbuc hcub hcuc hubuc ya C2 hC2c hC2s hC2e_all h0_eq.2 hC2ab
    exact ⟨by omega, hC2k.imp (fun h => h.trans (hk_le _)) (fun h => h.trans (hk_le _))⟩
  have ⟨hBuc_zero, hBk⟩ : count {uc} B = 0 ∧ (1 ≤ killed D (bits ∅) B ∨ 1 ≤ killed D (bits {ub}) B) := by
    have huc_tot : count {uc} B1 + count {uc} B2 = count {uc} B := by
      rw [← count_join {uc} true B1 B2]; exact hcBvc uc (by simp [D])
    rcases hsp with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hc1' : cost8 (table8 rB1) = 1 := by rw [h1]; decide
      have hc2' : cost8 (table8 rB2) = 2 := by rw [h2]; decide
      exact hpart B1 B2 hB1s hB2s (by omega) (by omega)
        (fun X hX => by rw [hB1r] at hX; cases hX; exact h1)
        (fun X hX => by rw [hB2r] at hX; cases hX; exact h2)
        ((hcBa _).trans hBa0) ((hcBa _).trans hBab_pair.2) huc_tot
        (fun x => (Nat.le_add_left _ _).trans ((killed_join D x true B1 B2).trans (hcBk x)))
    · have hc1' : cost8 (table8 rB1) = 2 := by rw [h1]; decide
      have hc2' : cost8 (table8 rB2) = 1 := by rw [h2]; decide
      exact hpart B2 B1 hB2s hB1s (by omega) (by omega)
        (fun X hX => by rw [hB2r] at hX; cases hX; exact h2)
        (fun X hX => by rw [hB1r] at hX; cases hX; exact h1)
        (by rw [join_eval]; simp only [gate, ite_true]; rw [Bool.or_comm]; exact (hcBa _).trans hBa0)
        (by rw [join_eval]; simp only [gate, ite_true]; rw [Bool.or_comm]; exact (hcBa _).trans hBab_pair.2)
        (by omega)
        (fun x => (Nat.le_add_right _ _).trans ((killed_join D x true B1 B2).trans (hcBk x)))
    · have hc1' : cost8 (table8 rB1) = 1 := by rw [h1]; decide
      have hc2' : cost8 (table8 rB2) = 2 := by rw [h2]; decide
      exact (hno40 B1 B2 hB1s hB2s (by omega) (by omega)
        (fun X hX => by rw [hB1r] at hX; cases hX; exact h1)
        (fun X hX => by rw [hB2r] at hX; cases hX; exact h2) hB13).elim
    · have hc1' : cost8 (table8 rB1) = 2 := by rw [h1]; decide
      have hc2' : cost8 (table8 rB2) = 1 := by rw [h2]; decide
      exact (hno40 B2 B1 hB2s hB1s (by omega) (by omega)
        (fun X hX => by rw [hB2r] at hX; cases hX; exact h2)
        (fun X hX => by rw [hB1r] at hX; cases hX; exact h1)
        (by rw [join_eval]; simp only [gate, ite_true]; rw [Bool.or_comm]; exact hB13)).elim
  -- Swap A and B when calling d4_combine_kills!
  have hcomb := d4_combine_kills hbub hbuc hcub hcuc hubuc false B A hBuc_zero hAub_zero hBk hAk
  obtain ⟨u1, u2, hk⟩ := hcomb
  refine ⟨u1, u2, ?_⟩
  have hcomm : ∀ x, killed D x (join false B A) = killed D x (join false A B) := by
    intro x
    unfold killed
    rw [outside_join, outside_join, Nat.add_comm (outside D B), reduce_join, reduce_join]
    have hcb : ∀ (r1 r2 : Reduced n), weight (combine false r1 r2) = weight (combine false r2 r1) := by
      intro r1 r2
      cases r1 with
      | inl c1 =>
        cases r2 with
        | inl c2 => cases c1 <;> cases c2 <;> rfl
        | inr f2 => cases c1 <;> rfl
      | inr f1 =>
        cases r2 with
        | inl c2 => cases c2 <;> rfl
        | inr f2 => simp [combine, weight, join_leaves, Nat.add_comm]
    rw [hcb]
  rwa [← hcomm]

private theorem d4_eval_y0 {n : ℕ} (G : Graph n) [DecidableRel G.Adj]
    {a b c ub uc : Fin n} (ht : Tri G a b c)
    (hbub : G.Adj b ub) (hcuc : G.Adj c uc)
    (hubl : ∀ w, G.Adj ub w → w = b) (hucl : ∀ w, G.Adj uc w → w = c)
    (x : Input n) :
    funOf G (splice {b, c, ub, uc} x (bits ∅)) = ((x b && x c) || (x b && x ub) || (x c && x uc)) := by
  let D : Finset (Fin n) := {b, c, ub, uc}
  apply Bool.eq_iff_iff.mpr
  rw [funOf_true]
  simp only [Bool.or_eq_true, Bool.and_eq_true]
  have hmem (v : Fin n) : splice D x (bits ∅) v = true ↔ v ∈ D ∧ x v = true := by
    by_cases hv : v ∈ D <;> simp [splice, bits, hv]
  constructor
  · rintro ⟨u, v, huv, hu, hv⟩
    obtain ⟨huD, hux⟩ := (hmem u).1 hu
    obtain ⟨hvD, hvx⟩ := (hmem v).1 hv
    simp only [D, Finset.mem_insert, Finset.mem_singleton] at huD hvD
    rcases huD with hu_eq | hu_eq | hu_eq | hu_eq <;> rcases hvD with hv_eq | hv_eq | hv_eq | hv_eq
    all_goals rw [hu_eq] at huv hux; rw [hv_eq] at huv hvx
    all_goals try exact (huv.ne rfl).elim
    · exact .inl (.inl ⟨hux, hvx⟩)
    · exact .inl (.inr ⟨hux, hvx⟩)
    · exact (ht.2.1.ne (hucl b huv.symm)).elim
    · exact .inl (.inl ⟨hvx, hux⟩)
    · exact (ht.2.1.ne.symm (hubl c huv.symm)).elim
    · exact .inr ⟨hux, hvx⟩
    · exact .inl (.inr ⟨hvx, hux⟩)
    · exact (ht.2.1.ne.symm (hubl c huv)).elim
    · exact (ht.2.2.ne.symm (hucl a ((hubl uc huv) ▸ ht.1.symm))).elim
    · exact (ht.2.1.ne (hucl b huv)).elim
    · exact .inr ⟨hvx, hux⟩
    · exact (ht.2.2.ne.symm (hucl a ((hubl uc huv.symm) ▸ ht.1.symm))).elim
  · rintro ((⟨hb, hc⟩ | ⟨hb, hub⟩) | ⟨hc, huc⟩)
    · exact ⟨b, c, ht.2.1, (hmem b).2 ⟨by simp [D], hb⟩, (hmem c).2 ⟨by simp [D], hc⟩⟩
    · exact ⟨b, ub, hbub, (hmem b).2 ⟨by simp [D], hb⟩, (hmem ub).2 ⟨by simp [D], hub⟩⟩
    · exact ⟨c, uc, hcuc, (hmem c).2 ⟨by simp [D], hc⟩, (hmem uc).2 ⟨by simp [D], huc⟩⟩

private theorem d4_eval_ya {n : ℕ} (G : Graph n) [DecidableRel G.Adj]
    {a b c ub uc : Fin n} (ht : Tri G a b c)
    (hbub : G.Adj b ub) (hcuc : G.Adj c uc)
    (hubl : ∀ w, G.Adj ub w → w = b) (hucl : ∀ w, G.Adj uc w → w = c)
    (x : Input n) :
    funOf G (splice {b, c, ub, uc} x (bits {a})) = (x b || x c) := by
  let D : Finset (Fin n) := {b, c, ub, uc}
  have haD : a ∉ D := by
    simp only [D, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨ht.1.ne, ht.2.2.ne.symm, fun h => ht.2.1.ne.symm (hubl c (h ▸ ht.2.2.symm)),
      fun h => ht.2.1.ne (hucl b (h ▸ ht.1))⟩
  apply Bool.eq_iff_iff.mpr
  rw [funOf_true, Bool.or_eq_true]
  have hmem (v : Fin n) : splice D x (bits {a}) v = true ↔ (v ∈ D ∧ x v = true) ∨ v = a := by
    by_cases hv : v ∈ D
    · have hva : v ≠ a := fun h => haD (h ▸ hv)
      simp [splice, bits, hv, hva]
    · simp [splice, bits, hv]
  constructor
  · rintro ⟨u, v, huv, hu, hv⟩
    rcases (hmem u).1 hu with ⟨huD, hux⟩ | hu_eq
    · rcases (hmem v).1 hv with ⟨hvD, hvx⟩ | hv_eq
      · simp only [D, Finset.mem_insert, Finset.mem_singleton] at huD hvD
        rcases huD with hu_eq | hu_eq | hu_eq | hu_eq <;> rcases hvD with hv_eq | hv_eq | hv_eq | hv_eq
        all_goals rw [hu_eq] at huv hux; rw [hv_eq] at huv hvx
        all_goals try exact (huv.ne rfl).elim
        · exact .inl hux
        · exact .inl hux
        · exact .inl hux
        · exact .inr hux
        · exact .inr hux
        · exact .inr hux
        · exact .inl hvx
        · exact .inr hvx
        · exact (ht.2.2.ne.symm (hucl a ((hubl uc huv) ▸ ht.1.symm))).elim
        · exact .inl hvx
        · exact .inr hvx
        · exact (ht.2.2.ne.symm (hucl a ((hubl uc huv.symm) ▸ ht.1.symm))).elim
      · rw [hv_eq] at huv
        simp only [D, Finset.mem_insert, Finset.mem_singleton] at huD
        rcases huD with hu_eq | hu_eq | hu_eq | hu_eq
        all_goals rw [hu_eq] at huv hux
        · exact .inl hux
        · exact .inr hux
        · exact (ht.1.ne (hubl a huv)).elim
        · exact (ht.2.2.ne.symm (hucl a huv)).elim
    · rw [hu_eq] at huv
      rcases (hmem v).1 hv with ⟨hvD, hvx⟩ | hv_eq
      · simp only [D, Finset.mem_insert, Finset.mem_singleton] at hvD
        rcases hvD with hv_eq | hv_eq | hv_eq | hv_eq
        all_goals rw [hv_eq] at huv hvx
        · exact .inl hvx
        · exact .inr hvx
        · exact (ht.1.ne (hubl a huv.symm)).elim
        · exact (ht.2.2.ne.symm (hucl a huv.symm)).elim
      · rw [hv_eq] at huv; exact (huv.ne rfl).elim
  · rintro (hb | hc)
    · exact ⟨a, b, ht.1, (hmem a).2 (.inr rfl), (hmem b).2 (.inl ⟨by simp [D], hb⟩)⟩
    · exact ⟨a, c, ht.2.2.symm, (hmem a).2 (.inr rfl), (hmem c).2 (.inl ⟨by simp [D], hc⟩)⟩

private def mval9 {n : ℕ} (b c ub uc : Fin n) (ya : Input n) (φ : DMFormula n) : ℕ :=
  let D : Finset (Fin n) := {b, c, ub, uc}
  let y0 := bits ∅
  (if φ.eval (splice D (d4Row b c ub uc 0) y0) then 1 else 0) |||
  (if φ.eval (splice D (d4Row b c ub uc 1) y0) then 2 else 0) |||
  (if φ.eval (splice D (d4Row b c ub uc 2) y0) then 4 else 0) |||
  (if φ.eval (splice D (d4Row b c ub uc 3) y0) then 8 else 0) |||
  (if φ.eval (splice D (d4Row b c ub uc 5) y0) then 16 else 0) |||
  (if φ.eval (splice D (d4Row b c ub uc 10) y0) then 32 else 0) |||
  (if φ.eval (splice D (d4Row b c ub uc 0) ya) then 64 else 0) |||
  (if φ.eval (splice D (d4Row b c ub uc 1) ya) then 128 else 0) |||
  (if φ.eval (splice D (d4Row b c ub uc 2) ya) then 256 else 0)

private theorem mval9_lt {n : ℕ} (b c ub uc : Fin n) (ya : Input n) (φ : DMFormula n) :
    mval9 b c ub uc ya φ < 512 := by
  unfold mval9
  refine Nat.or_lt_two_pow (n := 9) ?_ (by split_ifs <;> decide)
  refine Nat.or_lt_two_pow (n := 9) ?_ (by split_ifs <;> decide)
  refine Nat.or_lt_two_pow (n := 9) ?_ (by split_ifs <;> decide)
  refine Nat.or_lt_two_pow (n := 9) ?_ (by split_ifs <;> decide)
  refine Nat.or_lt_two_pow (n := 9) ?_ (by split_ifs <;> decide)
  refine Nat.or_lt_two_pow (n := 9) ?_ (by split_ifs <;> decide)
  refine Nat.or_lt_two_pow (n := 9) ?_ (by split_ifs <;> decide)
  exact Nat.or_lt_two_pow (n := 9) (by split_ifs <;> decide) (by split_ifs <;> decide)

private theorem mval9_bit {n : ℕ} (b c ub uc : Fin n) (ya : Input n) (φ : DMFormula n) (j : Fin 9) :
    (mval9 b c ub uc ya φ).testBit j.val =
      match j.val with
      | 0 => φ.eval (splice {b, c, ub, uc} (d4Row b c ub uc 0) (bits ∅))
      | 1 => φ.eval (splice {b, c, ub, uc} (d4Row b c ub uc 1) (bits ∅))
      | 2 => φ.eval (splice {b, c, ub, uc} (d4Row b c ub uc 2) (bits ∅))
      | 3 => φ.eval (splice {b, c, ub, uc} (d4Row b c ub uc 3) (bits ∅))
      | 4 => φ.eval (splice {b, c, ub, uc} (d4Row b c ub uc 5) (bits ∅))
      | 5 => φ.eval (splice {b, c, ub, uc} (d4Row b c ub uc 10) (bits ∅))
      | 6 => φ.eval (splice {b, c, ub, uc} (d4Row b c ub uc 0) ya)
      | 7 => φ.eval (splice {b, c, ub, uc} (d4Row b c ub uc 1) ya)
      | _ => φ.eval (splice {b, c, ub, uc} (d4Row b c ub uc 2) ya) := by
  have ht (c : Bool) (m k : ℕ) : (if c then m else 0).testBit k = (c && m.testBit k) := by
    cases c <;> simp
  have hb : ∀ k : Fin 9,
      (1 : ℕ).testBit k.val = decide (k = 0) ∧ (2 : ℕ).testBit k.val = decide (k = 1) ∧
      (4 : ℕ).testBit k.val = decide (k = 2) ∧ (8 : ℕ).testBit k.val = decide (k = 3) ∧
      (16 : ℕ).testBit k.val = decide (k = 4) ∧ (32 : ℕ).testBit k.val = decide (k = 5) ∧
      (64 : ℕ).testBit k.val = decide (k = 6) ∧ (128 : ℕ).testBit k.val = decide (k = 7) ∧
      (256 : ℕ).testBit k.val = decide (k = 8) := by decide
  obtain ⟨h1, h2, h4, h8, h16, h32, h64, h128, h256⟩ := hb j
  simp only [mval9, Nat.testBit_or, ht, h1, h2, h4, h8, h16, h32, h64, h128, h256]
  fin_cases j <;> simp

private theorem mval9_join {n : ℕ} (b c ub uc : Fin n) (ya : Input n) (g : Bool) (A B : DMFormula n) :
    mval9 b c ub uc ya (join g A B) =
      if g then mval9 b c ub uc ya A ||| mval9 b c ub uc ya B
      else mval9 b c ub uc ya A &&& mval9 b c ub uc ya B := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 9
  · have haux : ∀ j : Fin 9,
        (mval9 b c ub uc ya (join g A B)).testBit j.val =
          (if g then mval9 b c ub uc ya A ||| mval9 b c ub uc ya B
           else mval9 b c ub uc ya A &&& mval9 b c ub uc ya B).testBit j.val := by
      intro j
      cases g
      · simp only [Bool.false_eq_true, ite_false, Nat.testBit_and]
        rw [mval9_bit, mval9_bit, mval9_bit]
        fin_cases j <;> rfl
      · simp only [ite_true, Nat.testBit_or]
        rw [mval9_bit, mval9_bit, mval9_bit]
        fin_cases j <;> rfl
    exact haux ⟨i, hi⟩
  · have hltR : (if g then mval9 b c ub uc ya A ||| mval9 b c ub uc ya B
        else mval9 b c ub uc ya A &&& mval9 b c ub uc ya B) < 2 ^ 9 := by
      cases g
      · exact Nat.lt_of_le_of_lt Nat.and_le_left (mval9_lt b c ub uc ya A)
      · exact Nat.or_lt_two_pow (n := 9) (mval9_lt b c ub uc ya A) (mval9_lt b c ub uc ya B)
    rw [Nat.testBit_eq_false_of_lt ((mval9_lt b c ub uc ya _).trans_le (Nat.pow_le_pow_right (i := 9) (by decide : 0 < 2) (by omega))),
      Nat.testBit_eq_false_of_lt (hltR.trans_le (Nat.pow_le_pow_right (i := 9) (by decide : 0 < 2) (by omega)))]

private theorem mval9_pure {n : ℕ} {b c ub uc : Fin n}
    (hbc : b ≠ c) (hbub : b ≠ ub) (hbuc : b ≠ uc)
    (hcub : c ≠ ub) (hcuc : c ≠ uc) (hubuc : ub ≠ uc)
    (ya : Input n) (φ : DMFormula n) (hp : outside {b, c, ub, uc} φ = 0) :
    mval9 b c ub uc ya φ = pack7 (table7 (rename (d4Index b c ub) φ)) := by
  let D : Finset (Fin n) := {b, c, ub, uc}
  let p := table7 (rename (d4Index b c ub) φ)
  have hbit (m : ℕ) (y : Input n) :
      φ.eval (splice D (d4Row b c ub uc m) y) = (rename (d4Index b c ub) φ).eval (vals4 m) := by
    rw [d4Row_rename hbc hbub hbuc hcub hcuc hubuc φ hp m]
    exact eval_agree D φ _ _ (fun v hv => by simp [splice, hv]) hp
  have hp_lt : p < 128 := table7_lt _
  have hpk_lt : pack7 p < 512 := by
    unfold pack7
    have hf0 : ((p &&& 1) ||| ((p >>> 1) &&& 62)) < 64 := by
      refine Nat.or_lt_two_pow (n := 6) ?_ ?_
      · exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
      · exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
    have hf1 : ((p &&& 1) ||| ((p >>> 1) &&& 6)) < 8 := by
      refine Nat.or_lt_two_pow (n := 3) ?_ ?_
      · exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
      · exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
    refine Nat.or_lt_two_pow (n := 9) (hf0.trans (by decide)) ?_
    rw [Nat.shiftLeft_eq]
    omega
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 9
  · have haux : ∀ j : Fin 9, (mval9 b c ub uc ya φ).testBit j.val = (pack7 p).testBit j.val := by
      intro j
      rw [mval9_bit]
      have hpk : ∀ (x : Fin 128) (k : Fin 9),
          (pack7 x.val).testBit k.val =
          match k.val with
          | 0 => x.val.testBit 0
          | 1 => x.val.testBit 2
          | 2 => x.val.testBit 3
          | 3 => x.val.testBit 4
          | 4 => x.val.testBit 5
          | 5 => x.val.testBit 6
          | 6 => x.val.testBit 0
          | 7 => x.val.testBit 2
          | _ => x.val.testBit 3 := by decide +kernel
      rw [hpk ⟨p, hp_lt⟩ j]
      have ht7 (k : Fin 7) : p.testBit k.val = (rename (d4Index b c ub) φ).eval (vals4 (rows7 k)) :=
        table7_eval _ k
      fin_cases j
      · exact (hbit 0 (bits ∅)).trans (ht7 0).symm
      · exact (hbit 1 (bits ∅)).trans (ht7 2).symm
      · exact (hbit 2 (bits ∅)).trans (ht7 3).symm
      · exact (hbit 3 (bits ∅)).trans (ht7 4).symm
      · exact (hbit 5 (bits ∅)).trans (ht7 5).symm
      · exact (hbit 10 (bits ∅)).trans (ht7 6).symm
      · exact (hbit 0 ya).trans (ht7 0).symm
      · exact (hbit 1 ya).trans (ht7 2).symm
      · exact (hbit 2 ya).trans (ht7 3).symm
    exact haux ⟨i, hi⟩
  · rw [Nat.testBit_eq_false_of_lt ((mval9_lt b c ub uc ya φ).trans_le (Nat.pow_le_pow_right (i := 9) (by decide : 0 < 2) (by omega))),
      Nat.testBit_eq_false_of_lt (hpk_lt.trans_le (Nat.pow_le_pow_right (i := 9) (by decide : 0 < 2) (by omega)))]

private theorem mcost9_le {n : ℕ} {b c ub uc : Fin n}
    (hbc : b ≠ c) (hbub : b ≠ ub) (hbuc : b ≠ uc)
    (hcub : c ≠ ub) (hcuc : c ≠ uc) (hubuc : ub ≠ uc)
    (ya : Input n) (φ : DMFormula n)
    (ho : 0 < outside {b, c, ub, uc} φ)
    (hk0 : killed {b, c, ub, uc} (d4Row b c ub uc 0) φ = 0)
    (hk12 : killed {b, c, ub, uc} (d4Row b c ub uc 12) φ = 0) :
    mcost9 (mval9 b c ub uc ya φ) ≤ count {b, c, ub, uc} φ := by
  let D : Finset (Fin n) := {b, c, ub, uc}
  change 0 < outside D φ at ho
  change killed D (d4Row b c ub uc 0) φ = 0 at hk0
  change killed D (d4Row b c ub uc 12) φ = 0 at hk12
  change mcost9 (mval9 b c ub uc ya φ) ≤ count D φ
  induction φ using join_induct with
  | lit v pol =>
    have hv : v ∉ D := by
      intro hv
      have hv' : v ∉ Dᶜ := by simp [hv]
      change 0 < count Dᶜ (.lit v pol) at ho
      simp [count, hv'] at ho
    have h0 : mval9 b c ub uc ya (.lit v pol) = 0 ∨ mval9 b c ub uc ya (.lit v pol) = 63 ∨
        mval9 b c ub uc ya (.lit v pol) = 448 ∨ mval9 b c ub uc ya (.lit v pol) = 511 := by
      unfold mval9
      change _ ∨ _ ∨ _ ∨ _
      have hvD : v ∉ ({b, c, ub, uc} : Finset (Fin n)) := hv
      simp only [DMFormula.eval, splice, hvD, ite_false]
      cases pol <;> cases bits ∅ v <;> cases ya v <;> simp
    have hmc0 : mcost9 0 = 0 := by decide
    have hmc63 : mcost9 63 = 0 := by decide
    have hmc448 : mcost9 448 = 0 := by decide
    have hmc511 : mcost9 511 = 0 := by decide
    rcases h0 with h | h | h | h <;> rw [h]
    · rw [hmc0]; exact Nat.zero_le _
    · rw [hmc63]; exact Nat.zero_le _
    · rw [hmc448]; exact Nat.zero_le _
    · rw [hmc511]; exact Nat.zero_le _
  | bin g A B ha hb =>
    rw [outside_join] at ho
    rw [count_join, mval9_join]
    have hj0 := killed_join D (d4Row b c ub uc 0) g A B
    have hj12 := killed_join D (d4Row b c ub uc 12) g A B
    have hA0 : killed D (d4Row b c ub uc 0) A = 0 := by omega
    have hB0 : killed D (d4Row b c ub uc 0) B = 0 := by omega
    have hA12 : killed D (d4Row b c ub uc 12) A = 0 := by omega
    have hB12 : killed D (d4Row b c ub uc 12) B = 0 := by omega
    have pure_neq (P Q : DMFormula n) (z : Input n) (hp : outside D P = 0) (hq : 0 < outside D Q)
        (hk : killed D z (join g P Q) = 0) : P.eval z ≠ g := by
      unfold killed at hk
      rw [outside_join, reduce_join, reduce_pure D P z hp] at hk
      intro heq
      simp [combine, heq, weight] at hk
      omega
    have pure_neq_r (P Q : DMFormula n) (z : Input n) (hq : outside D Q = 0) (hp : 0 < outside D P)
        (hk : killed D z (join g P Q) = 0) : Q.eval z ≠ g := by
      unfold killed at hk
      rw [outside_join, reduce_join, reduce_pure D Q z hq] at hk
      intro heq
      rw [heq] at hk
      cases he : reduce D z P <;> cases g <;> simp [combine, weight, he] at hk <;> omega
    have pure_bits (P : DMFormula n) (hp : outside D P = 0)
        (h0 : P.eval (d4Row b c ub uc 0) ≠ g) (h12 : P.eval (d4Row b c ub uc 12) ≠ g) :
        let p := table7 (rename (d4Index b c ub) P)
        (g = true → p &&& 3 = 0) ∧ (g = false → p &&& 3 = 3) := by
      intro p
      have hb0 : p.testBit 0 = P.eval (d4Row b c ub uc 0) := by
        simpa [p, rows7] using (table7_eval (rename (d4Index b c ub) P) 0).trans
          (d4Row_rename hbc hbub hbuc hcub hcuc hubuc P hp 0)
      have hb1 : p.testBit 1 = P.eval (d4Row b c ub uc 12) := by
        simpa [p, rows7] using (table7_eval (rename (d4Index b c ub) P) 1).trans
          (d4Row_rename hbc hbub hbuc hcub hcuc hubuc P hp 12)
      have hand3 : ∀ (k : ℕ), k &&& 3 = (if k.testBit 0 then 1 else 0) + (if k.testBit 1 then 2 else 0) := by
        intro k
        apply Nat.eq_of_testBit_eq
        intro j
        by_cases hj : j < 2
        · cases h0' : k.testBit 0 <;> cases h1' : k.testBit 1 <;> interval_cases j <;>
            rw [Nat.testBit_and] <;> simp only [h0', h1'] <;> decide
        · rw [Nat.testBit_and,
            Nat.testBit_eq_false_of_lt ((show 3 < 2 ^ 2 by decide).trans_le (Nat.pow_le_pow_right (i := 2) (by decide : 0 < 2) (by omega))),
            Bool.and_false]
          have hlt : (if k.testBit 0 then 1 else 0) + (if k.testBit 1 then 2 else 0) < 2 ^ 2 := by
            split_ifs <;> decide
          exact (Nat.testBit_eq_false_of_lt (hlt.trans_le (Nat.pow_le_pow_right (i := 2) (by decide : 0 < 2) (by omega)))).symm
      rw [hand3 p, hb0, hb1]
      constructor
      · intro rfl; cases h' : P.eval (d4Row b c ub uc 0) <;> cases h'' : P.eval (d4Row b c ub uc 12) <;> simp_all
      · intro rfl; cases h' : P.eval (d4Row b c ub uc 0) <;> cases h'' : P.eval (d4Row b c ub uc 12) <;> simp_all
    by_cases hAo : outside D A = 0
    · have hBo : 0 < outside D B := by omega
      have hBih := hb hBo hB0 hB12
      have hne0 := pure_neq A B (d4Row b c ub uc 0) hAo hBo hk0
      have hne12 := pure_neq A B (d4Row b c ub uc 12) hAo hBo hk12
      have hpb := pure_bits A hAo hne0 hne12
      have hpc : pcost7 (table7 (rename (d4Index b c ub) A)) ≤ count D A := by
        have := pcost7_le_leaves (rename (d4Index b c ub) A)
        rw [rename_leaves] at this
        have htot := count_add_outside D A
        omega
      rw [mval9_pure hbc hbub hbuc hcub hcuc hubuc ya A hAo]
      have hpm := mcost9_pure (table7 (rename (d4Index b c ub) A)) (mval9 b c ub uc ya B)
        (table7_lt _) (mval9_lt b c ub uc ya B)
      cases g
      · exact (hpm.2 (hpb.2 rfl)).trans (Nat.add_le_add hpc hBih)
      · exact (hpm.1 (hpb.1 rfl)).trans (Nat.add_le_add hpc hBih)
    · by_cases hBo : outside D B = 0
      · have hAo' : 0 < outside D A := by omega
        have hAih := ha hAo' hA0 hA12
        have hne0 := pure_neq_r A B (d4Row b c ub uc 0) hBo hAo' hk0
        have hne12 := pure_neq_r A B (d4Row b c ub uc 12) hBo hAo' hk12
        have hpb := pure_bits B hBo hne0 hne12
        have hpc : pcost7 (table7 (rename (d4Index b c ub) B)) ≤ count D B := by
          have := pcost7_le_leaves (rename (d4Index b c ub) B)
          rw [rename_leaves] at this
          have htot := count_add_outside D B
          omega
        rw [mval9_pure hbc hbub hbuc hcub hcuc hubuc ya B hBo]
        have hpm := mcost9_pure (table7 (rename (d4Index b c ub) B)) (mval9 b c ub uc ya A)
          (table7_lt _) (mval9_lt b c ub uc ya A)
        cases g
        · rw [Nat.and_comm]
          exact (hpm.2 (hpb.2 rfl)).trans (by omega)
        · rw [Nat.or_comm]
          exact (hpm.1 (hpb.1 rfl)).trans (by omega)
      · have hAih := ha (by omega) hA0 hA12
        have hBih := hb (by omega) hB0 hB12
        have hmg := mcost9_gates (mval9 b c ub uc ya A) (mval9 b c ub uc ya B)
          (mval9_lt b c ub uc ya A) (mval9_lt b c ub uc ya B)
        cases g
        · exact hmg.1.trans (Nat.add_le_add hAih hBih)
        · exact hmg.2.trans (Nat.add_le_add hAih hBih)

private theorem peel_D4_saving {n : ℕ} (G : Graph n) [DecidableRel G.Adj]
    {a b c ub uc : Fin n} (ht : Tri G a b c)
    (hbub : G.Adj b ub) (hcuc : G.Adj c uc)
    (hubl : ∀ w, G.Adj ub w → w = b) (hucl : ∀ w, G.Adj uc w → w = c)
    (φ : DMFormula n) (hφ : ∀ x, φ.eval x = funOf G x) :
    ∃ u1 u2 : Bool, weight (reduce {b, c, ub, uc} (d4Assign ub uc u1 u2) φ) + 7 ≤ φ.leaves := by
  let D : Finset (Fin n) := {b, c, ub, uc}
  have hbc : b ≠ c := ht.2.1.ne
  have hbub_ne : b ≠ ub := hbub.ne
  have hbuc_ne : b ≠ uc := fun h => ht.2.2.ne.symm (hucl a (h ▸ ht.1.symm))
  have hcub_ne : c ≠ ub := fun h => ht.1.ne (hubl a (h ▸ ht.2.2))
  have hcuc_ne : c ≠ uc := hcuc.ne
  have hubuc_ne : ub ≠ uc := fun h => hbc.symm (hubl c (h ▸ hcuc.symm))
  have haD : a ∉ D := by
    simp only [D, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨ht.1.ne, ht.2.2.ne.symm, fun h => ht.2.1.ne.symm (hubl c (h ▸ ht.2.2.symm)),
      fun h => ht.2.1.ne (hucl b (h ▸ ht.1))⟩
  have hev0 (x : Input n) : φ.eval (splice D x (bits ∅)) =
      ((x b && x c) || (x b && x ub) || (x c && x uc)) := by
    rw [hφ]; exact d4_eval_y0 G ht hbub hcuc hubl hucl x
  have heva (x : Input n) : φ.eval (splice D x (bits {a})) = (x b || x c) := by
    rw [hφ]; exact d4_eval_ya G ht hbub hcuc hubl hucl x
  have htot := count_add_outside D φ
  have hbound : ∀ u1 u2 : Bool,
      7 ≤ count D φ + killed D (d4Assign ub uc u1 u2) φ →
      weight (reduce D (d4Assign ub uc u1 u2) φ) + 7 ≤ φ.leaves := by
    intro u1 u2 hk
    unfold killed at hk
    have hr := reduce_le D φ (d4Assign ub uc u1 u2)
    omega
  -- First show 5 ≤ count D φ via reduce Dᶜ (bits ∅) φ and cost8 28 = 5
  have h5 : 5 ≤ count D φ ∧ (count D φ = 5 → Survive D φ) := by
    cases hr : reduce Dᶜ (bits ∅) φ with
    | inl q =>
      have h0 : φ.eval (splice D (bits ∅) (bits ∅)) = q := by
        have := reduce_eval Dᶜ φ (bits ∅) (bits ∅)
        rw [hr] at this
        simpa [value, splice_bits] using this.symm
      have h3 : φ.eval (splice D (bits {b, c}) (bits ∅)) = q := by
        have := reduce_eval Dᶜ φ (bits ∅) (bits {b, c})
        rw [hr] at this
        have hsp : splice Dᶜ (bits ∅) (bits {b, c}) = splice D (bits {b, c}) (bits ∅) := by
          funext v; by_cases hv : v ∈ D <;> simp [splice, hv]
        rw [hsp] at this
        exact this.symm
      rw [hev0] at h0 h3
      simp [bits] at h0 h3
      exact (Bool.false_ne_true (h0.symm.trans h3)).elim
    | inr ψ0 =>
      have hψ0_out : outside D ψ0 = 0 := reduce_scope Dᶜ (bits ∅) φ ψ0 hr
      have hψ0_le : ψ0.leaves ≤ count D φ := by
        have := reduce_compl_le D φ
        rwa [hr] at this
      have hψ0_ev (x : Input n) : ψ0.eval x = φ.eval (splice D x (bits ∅)) := by
        have := reduce_eval Dᶜ φ (bits ∅) x
        rw [hr] at this
        have hsp : splice Dᶜ (bits ∅) x = splice D x (bits ∅) := by
          funext v; by_cases hv : v ∈ D <;> simp [splice, hv]
        rw [hsp] at this
        exact this
      have ht28 : table8 (rename (d4Index b c ub) ψ0) = 28 := by
        apply Nat.eq_of_testBit_eq
        intro i
        by_cases hi : i < 8
        · have haux : ∀ idx : Fin 8, (table8 (rename (d4Index b c ub) ψ0)).testBit idx.val = (28 : ℕ).testBit idx.val := by
            intro idx
            rw [table8_eval _ idx, d4Row_rename hbc hbub_ne hbuc_ne hcub_ne hcuc_ne hubuc_ne ψ0 hψ0_out,
              hψ0_ev, hev0]
            fin_cases idx <;> simp [rows8, d4Row, hbc, hbc.symm, hbub_ne, hbub_ne.symm, hbuc_ne, hbuc_ne.symm,
              hcub_ne, hcub_ne.symm, hcuc_ne, hcuc_ne.symm, hubuc_ne, hubuc_ne.symm] <;> decide
          exact haux ⟨i, hi⟩
        · rw [Nat.testBit_eq_false_of_lt ((table8_lt _).trans_le (Nat.pow_le_pow_right (i := 8) (by decide : 0 < 2) (by omega))),
            Nat.testBit_eq_false_of_lt ((show 28 < 2 ^ 8 by decide).trans_le (Nat.pow_le_pow_right (i := 8) (by decide : 0 < 2) (by omega)))]
      have hc5 : 5 ≤ ψ0.leaves := by
        have := cost8_le_leaves (rename (d4Index b c ub) ψ0)
        rw [ht28, rename_leaves] at this
        have h28 : cost8 28 = 5 := by decide
        omega
      refine ⟨hc5.trans hψ0_le, fun h5eq => ?_⟩
      unfold Survive; rw [hr]; change ψ0.leaves = count D φ; omega
  by_cases h7 : 7 ≤ count D φ
  · exact ⟨false, false, hbound false false (by omega)⟩
  by_cases h6 : count D φ = 6
  · by_cases hk0 : 1 ≤ killed D (d4Assign ub uc false false) φ
    · exact ⟨false, false, hbound false false (by omega)⟩
    by_cases hk12 : 1 ≤ killed D (d4Assign ub uc true true) φ
    · exact ⟨true, true, hbound true true (by omega)⟩
    have ho : 0 < outside D φ := by
      apply (graph_essential G φ hφ ht.1).trans_le
      change count {a} φ ≤ count Dᶜ φ
      rw [count_sum Dᶜ]
      exact Finset.single_le_sum (f := fun w => count {w} φ) (fun _ _ => Nat.zero_le _) (by simpa using haD)
    have hrow0 : d4Row b c ub uc 0 = d4Assign ub uc false false := by
      funext v; simp [d4Row, d4Assign]
    have hrow12 : d4Row b c ub uc 12 = d4Assign ub uc true true := by
      funext v
      by_cases h1 : v = ub
      · subst v; simp [d4Row, d4Assign, hbub_ne.symm, hcub_ne.symm]; decide
      · by_cases h2 : v = uc
        · subst v; simp [d4Row, d4Assign, hbuc_ne.symm, hcuc_ne.symm, hubuc_ne.symm]; decide
        · simp only [d4Row, d4Assign, h1, h2, ite_false]; split_ifs <;> decide
    have hmle := mcost9_le hbc hbub_ne hbuc_ne hcub_ne hcuc_ne hubuc_ne (bits {a}) φ ho
      (by change killed D (d4Row b c ub uc 0) φ = 0; rw [hrow0]; omega)
      (by change killed D (d4Row b c ub uc 12) φ = 0; rw [hrow12]; omega)
    have hm440 : mval9 b c ub uc (bits {a}) φ = 440 := by
      apply Nat.eq_of_testBit_eq
      intro i
      by_cases hi : i < 9
      · have haux : ∀ j : Fin 9, (mval9 b c ub uc (bits {a}) φ).testBit j.val = (440 : ℕ).testBit j.val := by
          intro j
          rw [mval9_bit]
          have hev0' : ∀ x, φ.eval (splice {b, c, ub, uc} x (bits ∅)) = ((x b && x c) || (x b && x ub) || (x c && x uc)) := hev0
          have heva' : ∀ x, φ.eval (splice {b, c, ub, uc} x (bits {a})) = (x b || x c) := heva
          fin_cases j <;>
            simp [hev0', heva', d4Row, hbc, hbc.symm, hbub_ne, hbub_ne.symm, hbuc_ne, hbuc_ne.symm,
              hcub_ne, hcub_ne.symm, hcuc_ne, hcuc_ne.symm, hubuc_ne, hubuc_ne.symm] <;> decide
        exact haux ⟨i, hi⟩
      · rw [Nat.testBit_eq_false_of_lt ((mval9_lt b c ub uc (bits {a}) φ).trans_le (Nat.pow_le_pow_right (i := 9) (by decide : 0 < 2) (by omega))),
          Nat.testBit_eq_false_of_lt ((show 440 < 2 ^ 9 by decide).trans_le (Nat.pow_le_pow_right (i := 9) (by decide : 0 < 2) (by omega)))]
    rw [hm440] at hmle
    have h440 : mcost9 440 = 7 := by decide
    change count {b, c, ub, uc} φ = 6 at h6
    omega
  -- Remaining case: count D φ = 5!
  have hc5 : count D φ = 5 := by omega
  have hsurv : Survive D φ := h5.2 hc5
  have hnc : ∃ x1 x2, φ.eval (splice D x1 (bits {a})) ≠ φ.eval (splice D x2 (bits {a})) :=
    ⟨bits ∅, bits {b}, by rw [heva, heva]; simp [bits]⟩
  obtain ⟨core, _, hcore_c, hcore_s, hcore_0, hcore_a, hcore_k, hstr⟩ :=
    strip_core D (bits {a}) φ (by omega) hsurv hnc
  rcases hstr with h1 | ⟨g, A, B, rfl, hAp, hBp⟩
  · omega
  obtain ⟨hAs, hBs⟩ := survive_join D g A B hcore_s
  rw [count_join] at hcore_c
  obtain ⟨A0, hAr, hAl, hAo, hAe, _⟩ := survive_inr D A hAs hAp
  obtain ⟨B0, hBr, hBl, hBo, hBe, _⟩ := survive_inr D B hBs hBp
  let rA := rename (d4Index b c ub) A0
  let rB := rename (d4Index b c ub) B0
  have ht28 : (if g then table8 rA ||| table8 rB else table8 rA &&& table8 rB) = 28 := by
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < 8
    · have haux : ∀ idx : Fin 8,
          (if g then table8 rA ||| table8 rB else table8 rA &&& table8 rB).testBit idx.val =
            (28 : ℕ).testBit idx.val := by
        intro idx
        have hL1 : (table8 rA).testBit idx.val = A.eval (splice D (d4Row b c ub uc (rows8 idx)) (bits ∅)) := by
          rw [table8_eval rA idx, d4Row_rename hbc hbub_ne hbuc_ne hcub_ne hcuc_ne hubuc_ne A0 hAo, hAe]
        have hL2 : (table8 rB).testBit idx.val = B.eval (splice D (d4Row b c ub uc (rows8 idx)) (bits ∅)) := by
          rw [table8_eval rB idx, d4Row_rename hbc hbub_ne hbuc_ne hcub_ne hcuc_ne hubuc_ne B0 hBo, hBe]
        have htot : (join g A B).eval (splice D (d4Row b c ub uc (rows8 idx)) (bits ∅)) = (28 : ℕ).testBit idx.val := by
          rw [hcore_0, hev0]
          fin_cases idx <;> simp [rows8, d4Row, hbc, hbc.symm, hbub_ne, hbub_ne.symm, hbuc_ne, hbuc_ne.symm,
            hcub_ne, hcub_ne.symm, hcuc_ne, hcuc_ne.symm, hubuc_ne, hubuc_ne.symm] <;> decide
        cases g
        · simp only [Bool.false_eq_true, ite_false, Nat.testBit_and, hL1, hL2]; simpa [join_eval, gate] using htot
        · simp only [ite_true, Nat.testBit_or, hL1, hL2]; simpa [join_eval, gate] using htot
      exact haux ⟨i, hi⟩
    · have hlt : (if g then table8 rA ||| table8 rB else table8 rA &&& table8 rB) < 2 ^ 8 := by
        cases g
        · exact Nat.lt_of_le_of_lt Nat.and_le_left (table8_lt rA)
        · exact Nat.or_lt_two_pow (n := 8) (table8_lt rA) (table8_lt rB)
      rw [Nat.testBit_eq_false_of_lt (hlt.trans_le (Nat.pow_le_pow_right (i := 8) (by decide : 0 < 2) (by omega))),
        Nat.testBit_eq_false_of_lt ((show 28 < 2 ^ 8 by decide).trans_le (Nat.pow_le_pow_right (i := 8) (by decide : 0 < 2) (by omega)))]
  have hcA : cost8 (table8 rA) ≤ count {b, c, ub, uc} A := (cost8_le_leaves rA).trans (by rw [rename_leaves, hAl])
  have hcB : cost8 (table8 rB) ≤ count {b, c, ub, uc} B := (cost8_le_leaves rB).trans (by rw [rename_leaves, hBl])
  dsimp only [D] at hbound hcore_c hc5 hcore_0 hcore_a hcore_k hev0 heva hAs hBs hAr hBr hAl hBl hAo hBo
  have hDswap : ({c, b, uc, ub} : Finset (Fin n)) = {b, c, ub, uc} := by
    ext v; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  have hassign_swap (u1 u2 : Bool) : d4Assign uc ub u1 u2 = d4Assign ub uc u2 u1 := by
    funext v
    by_cases h1 : v = ub
    · subst v; simp [d4Assign, hubuc_ne]
    · by_cases h2 : v = uc
      · subst v; simp [d4Assign, hubuc_ne.symm]
      · simp [d4Assign, h1, h2]
  have hjoin_comm (g0 : Bool) (X Y : DMFormula n) (x : Input n) :
      killed {b, c, ub, uc} x (join g0 Y X) = killed {b, c, ub, uc} x (join g0 X Y) := by
    unfold killed
    rw [outside_join, outside_join, Nat.add_comm (outside {b, c, ub, uc} Y), reduce_join, reduce_join]
    have hcb : ∀ (r1 r2 : Reduced n), weight (combine g0 r1 r2) = weight (combine g0 r2 r1) := by
      intro r1 r2
      cases r1 with
      | inl c1 => cases r2 with | inl c2 => cases g0 <;> cases c1 <;> cases c2 <;> rfl | inr _ => cases g0 <;> cases c1 <;> rfl
      | inr _ => cases r2 with | inl c2 => cases g0 <;> cases c2 <;> rfl | inr _ => simp [combine, weight, join_leaves, Nat.add_comm]
    rw [hcb]
  cases g
  · -- g = false (AND): Type II!
    simp only [Bool.false_eq_true, ite_false] at ht28
    have h13_bc : (join false A B).eval (splice {b, c, ub, uc} (d4Row b c ub uc 13) (bits ∅)) = true := by
      rw [hcore_0, hev0]
      simp [d4Row, hbc, hbc.symm, hbub_ne, hbub_ne.symm, hbuc_ne, hbuc_ne.symm,
        hcub_ne, hcub_ne.symm, hcuc_ne, hcuc_ne.symm, hubuc_ne, hubuc_ne.symm]
      decide
    have h13_cb : (join false A B).eval (splice {b, c, ub, uc} (d4Row c b uc ub 13) (bits ∅)) = true := by
      rw [hcore_0, hev0]
      simp [d4Row, hbc, hbc.symm, hbub_ne, hbub_ne.symm, hbuc_ne, hbuc_ne.symm,
        hcub_ne, hcub_ne.symm, hcuc_ne, hcuc_ne.symm, hubuc_ne, hubuc_ne.symm]
      decide
    rcases split28_and (table8_lt rA) (table8_lt rB) (by omega) ht28 with
        ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩
    · have hcA' : cost8 (table8 rA) = 2 := by rw [hA]; decide
      have hcB' : cost8 (table8 rB) = 3 := by rw [hB]; decide
      obtain ⟨u1, u2, hk⟩ := handle_typeII hbc hbub_ne hbuc_ne hcub_ne hcuc_ne hubuc_ne (bits {a}) A B
        hAs hBs (by omega) (by omega)
        (fun X hX => by rw [hAr] at hX; cases hX; exact hA)
        (fun X hX => by rw [hBr] at hX; cases hX; exact hB)
        h13_bc (fun x => (hcore_a x).trans (heva x))
      exact ⟨u1, u2, hbound u1 u2 (by have := hcore_k (d4Assign ub uc u1 u2); omega)⟩
    · have hcA' : cost8 (table8 rA) = 3 := by rw [hA]; decide
      have hcB' : cost8 (table8 rB) = 2 := by rw [hB]; decide
      obtain ⟨u1, u2, hk⟩ := handle_typeII hbc hbub_ne hbuc_ne hcub_ne hcuc_ne hubuc_ne (bits {a}) B A
        hBs hAs (by omega) (by omega)
        (fun X hX => by rw [hBr] at hX; cases hX; exact hB)
        (fun X hX => by rw [hAr] at hX; cases hX; exact hA)
        (by rw [join_eval]; simp only [gate, Bool.false_eq_true, ite_false]; rw [Bool.and_comm]; exact h13_bc)
        (fun x => by rw [join_eval]; simp only [gate, Bool.false_eq_true, ite_false]; rw [Bool.and_comm]; exact (hcore_a x).trans (heva x))
      exact ⟨u1, u2, hbound u1 u2 (by
        have := hcore_k (d4Assign ub uc u1 u2); rw [hjoin_comm false A B] at hk; omega)⟩
    · have hcA' : cost8 (table8 rA) = 2 := by rw [hA]; decide
      have hcB' : cost8 (table8 rB) = 3 := by rw [hB]; decide
      obtain ⟨u1, u2, hk⟩ := handle_typeII hbc.symm hcuc_ne hcub_ne hbuc_ne hbub_ne hubuc_ne.symm
        (bits {a}) A B (hDswap.symm ▸ hAs) (hDswap.symm ▸ hBs) (by rw [hDswap]; omega) (by rw [hDswap]; omega)
        (fun X hX => by
          rw [hDswap, hAr] at hX; cases hX
          rw [rename_d4_swap hbc hbub_ne hbuc_ne hcub_ne hcuc_ne hubuc_ne A0 hAo, table8_swap, hA]; decide)
        (fun X hX => by
          rw [hDswap, hBr] at hX; cases hX
          rw [rename_d4_swap hbc hbub_ne hbuc_ne hcub_ne hcuc_ne hubuc_ne B0 hBo, table8_swap, hB]; decide)
        (by rw [hDswap]; exact h13_cb)
        (fun x => by rw [hDswap, hcore_a, heva, Bool.or_comm])
      rw [hDswap, hassign_swap] at hk
      exact ⟨u2, u1, hbound u2 u1 (by have := hcore_k (d4Assign ub uc u2 u1); omega)⟩
    · have hcA' : cost8 (table8 rA) = 3 := by rw [hA]; decide
      have hcB' : cost8 (table8 rB) = 2 := by rw [hB]; decide
      obtain ⟨u1, u2, hk⟩ := handle_typeII hbc.symm hcuc_ne hcub_ne hbuc_ne hbub_ne hubuc_ne.symm
        (bits {a}) B A (hDswap.symm ▸ hBs) (hDswap.symm ▸ hAs) (by rw [hDswap]; omega) (by rw [hDswap]; omega)
        (fun X hX => by
          rw [hDswap, hBr] at hX; cases hX
          rw [rename_d4_swap hbc hbub_ne hbuc_ne hcub_ne hcuc_ne hubuc_ne B0 hBo, table8_swap, hB]; decide)
        (fun X hX => by
          rw [hDswap, hAr] at hX; cases hX
          rw [rename_d4_swap hbc hbub_ne hbuc_ne hcub_ne hcuc_ne hubuc_ne A0 hAo, table8_swap, hA]; decide)
        (by rw [hDswap, join_eval]; simp only [gate, Bool.false_eq_true, ite_false]; rw [Bool.and_comm]; exact h13_cb)
        (fun x => by rw [hDswap, join_eval]; simp only [gate, Bool.false_eq_true, ite_false]; rw [Bool.and_comm]; exact (hcore_a x).trans ((heva x).trans (Bool.or_comm _ _)))
      rw [hDswap, hassign_swap, hjoin_comm false A B] at hk
      exact ⟨u2, u1, hbound u2 u1 (by have := hcore_k (d4Assign ub uc u2 u1); omega)⟩
  · -- g = true (OR): Type I!
    simp only [ite_true] at ht28
    rcases split28_or (table8_lt rA) (table8_lt rB) (by omega) ht28 with
        ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩
    · have hcA' : cost8 (table8 rA) = 2 := by rw [hA]; decide
      have hcB' : cost8 (table8 rB) = 3 := by rw [hB]; decide
      obtain ⟨u1, u2, hk⟩ := handle_typeI hbc hbub_ne hbuc_ne hcub_ne hcuc_ne hubuc_ne (bits {a}) A B
        hAs hBs (by omega) (by omega)
        (fun X hX => by rw [hAr] at hX; cases hX; exact hA)
        (fun X hX => by rw [hBr] at hX; cases hX; exact hB)
        (fun x => (hcore_a x).trans (heva x))
      exact ⟨u1, u2, hbound u1 u2 (by have := hcore_k (d4Assign ub uc u1 u2); omega)⟩
    · have hcA' : cost8 (table8 rA) = 3 := by rw [hA]; decide
      have hcB' : cost8 (table8 rB) = 2 := by rw [hB]; decide
      obtain ⟨u1, u2, hk⟩ := handle_typeI hbc hbub_ne hbuc_ne hcub_ne hcuc_ne hubuc_ne (bits {a}) B A
        hBs hAs (by omega) (by omega)
        (fun X hX => by rw [hBr] at hX; cases hX; exact hB)
        (fun X hX => by rw [hAr] at hX; cases hX; exact hA)
        (fun x => by rw [join_eval]; simp only [gate, ite_true]; rw [Bool.or_comm]; exact (hcore_a x).trans (heva x))
      exact ⟨u1, u2, hbound u1 u2 (by
        have := hcore_k (d4Assign ub uc u1 u2); rw [hjoin_comm true A B] at hk; omega)⟩
    · have hcA' : cost8 (table8 rA) = 2 := by rw [hA]; decide
      have hcB' : cost8 (table8 rB) = 3 := by rw [hB]; decide
      obtain ⟨u1, u2, hk⟩ := handle_typeI hbc.symm hcuc_ne hcub_ne hbuc_ne hbub_ne hubuc_ne.symm
        (bits {a}) A B (hDswap.symm ▸ hAs) (hDswap.symm ▸ hBs) (by rw [hDswap]; omega) (by rw [hDswap]; omega)
        (fun X hX => by
          rw [hDswap, hAr] at hX; cases hX
          rw [rename_d4_swap hbc hbub_ne hbuc_ne hcub_ne hcuc_ne hubuc_ne A0 hAo, table8_swap, hA]; decide)
        (fun X hX => by
          rw [hDswap, hBr] at hX; cases hX
          rw [rename_d4_swap hbc hbub_ne hbuc_ne hcub_ne hcuc_ne hubuc_ne B0 hBo, table8_swap, hB]; decide)
        (fun x => by rw [hDswap, hcore_a, heva, Bool.or_comm])
      rw [hDswap, hassign_swap] at hk
      exact ⟨u2, u1, hbound u2 u1 (by have := hcore_k (d4Assign ub uc u2 u1); omega)⟩
    · have hcA' : cost8 (table8 rA) = 3 := by rw [hA]; decide
      have hcB' : cost8 (table8 rB) = 2 := by rw [hB]; decide
      obtain ⟨u1, u2, hk⟩ := handle_typeI hbc.symm hcuc_ne hcub_ne hbuc_ne hbub_ne hubuc_ne.symm
        (bits {a}) B A (hDswap.symm ▸ hBs) (hDswap.symm ▸ hAs) (by rw [hDswap]; omega) (by rw [hDswap]; omega)
        (fun X hX => by
          rw [hDswap, hBr] at hX; cases hX
          rw [rename_d4_swap hbc hbub_ne hbuc_ne hcub_ne hcuc_ne hubuc_ne B0 hBo, table8_swap, hB]; decide)
        (fun X hX => by
          rw [hDswap, hAr] at hX; cases hX
          rw [rename_d4_swap hbc hbub_ne hbuc_ne hcub_ne hcuc_ne hubuc_ne A0 hAo, table8_swap, hA]; decide)
        (fun x => by rw [hDswap, join_eval]; simp only [gate, ite_true]; rw [Bool.or_comm]; exact (hcore_a x).trans ((heva x).trans (Bool.or_comm _ _)))
      rw [hDswap, hassign_swap, hjoin_comm true A B] at hk
      exact ⟨u2, u1, hbound u2 u1 (by have := hcore_k (d4Assign ub uc u2 u1); omega)⟩

private abbrev Budget {n : ℕ} (G : Graph n) [DecidableRel G.Adj] (k : ℕ) : Prop :=
  ∃ S : Finset (Fin n), CoverPromise.IsVertexCover G S ∧ G.edgeFinset.card + S.card ≤ k

private abbrev Smaller {n : ℕ} (G : Graph n) [DecidableRel G.Adj] : Prop :=
  ∀ (H : Graph n) [DecidableRel H.Adj], H.edgeFinset.card < G.edgeFinset.card →
    Good H → ∀ r : Reduced n, (∀ y, value y r = funOf H y) → Budget H (weight r)

-- Charge the removed edges and the cover extension against leaves saved by a restriction.
private theorem use_cut {n : ℕ} (G : Graph n) [DecidableRel G.Adj] (hg : Good G) (ih : Smaller G)
    (D : Finset (Fin n)) [DecidableRel (cut G D).Adj] (φ : DMFormula n)
    (hφ : ∀ x, φ.eval x = funOf G x) (x : Input n)
    (hx : ∀ u v, G.Adj u v → u ∈ D → x u = true → v ∈ D ∧ x v = false)
    (he : ∃ u ∈ D, ∃ v, G.Adj u v) (e k : ℕ)
    (hm : (G.edgeFinset \ (cut G D).edgeFinset).card ≤ e)
    (hs : ∀ S, CoverPromise.IsVertexCover (cut G D) S → ∃ T, CoverPromise.IsVertexCover G T ∧ T.card ≤ S.card + k)
    (hb : weight (reduce D x φ) + e + k ≤ φ.leaves) : Budget G φ.leaves := by
  obtain ⟨u, hu, v, huv⟩ := he
  obtain ⟨S, hS, hcard⟩ := ih (cut G D) (cut_lt G D huv hu) (good_cut G D hg) (reduce D x φ)
    (fun y => by rw [reduce_eval, hφ, cut_eval G D x hx y])
  obtain ⟨T, hT, hcard'⟩ := hs S hS
  refine ⟨T, hT, ?_⟩
  have := card_cut G D
  omega

private theorem removed_sub {n : ℕ} (G : Graph n) [DecidableRel G.Adj] (D : Finset (Fin n))
    [DecidableRel (cut G D).Adj] (E : Finset (Sym2 (Fin n)))
    (he : ∀ u v, G.Adj u v → u ∈ D → s(u, v) ∈ E) :
    (G.edgeFinset \ (cut G D).edgeFinset).card ≤ E.card := by
  apply Finset.card_le_card
  intro e
  induction e using Sym2.ind with
  | h u v =>
    rw [removed_iff]
    rintro ⟨h, hu | hv⟩
    · exact he u v h hu
    · rw [Sym2.eq_swap]
      exact he v u h.symm hv

private theorem peel_triangle_pendant {n : ℕ} (G : Graph n) [DecidableRel G.Adj]
    (hg : Good G) (ih : Smaller G) (φ : DMFormula n) (hφ : ∀ x, φ.eval x = funOf G x)
    {u v b c : Fin n} (huv : G.Adj u v) (hu : ∀ w, G.Adj u w → w = v)
    (ht : Tri G v b c) (hc : G.degree c = 2) : Budget G φ.leaves := by
  let D : Finset (Fin n) := {u}
  letI : DecidableRel (cut G D).Adj := cutDec G D
  have hub : u ≠ b := by
    rintro rfl
    exact ht.2.2.ne (hu c ht.2.1)
  have huc : u ≠ c := by
    rintro rfl
    exact ht.1.ne.symm (hu b ht.2.1.symm)
  refine use_cut G hg ih D φ hφ (fun _ => false) (by simp) ⟨u, by simp [D], v, huv⟩ 1 0 ?_ ?_ ?_
  · refine (removed_sub G D {s(u, v)} (fun a w haw ha => ?_)).trans (by simp)
    have ha' : a = u := by simpa [D] using ha
    subst a
    rw [hu w haw]
    simp
  · intro S hS
    by_cases hv : v ∈ S
    · refine ⟨S, ?_, by simp⟩
      intro a w haw
      by_cases ha : a = u
      · subst a; exact .inr (hu w haw ▸ hv)
      by_cases hw : w = u
      · subst w; exact .inl (hu a haw.symm ▸ hv)
      exact hS a w ⟨haw, by simpa [D], by simpa [D]⟩
    have hcv : (cut G D).Adj c v := ⟨ht.2.2, by simpa [D] using huc.symm,
      by simpa [D] using huv.ne.symm⟩
    have hbc : (cut G D).Adj v b := ⟨ht.1, by simpa [D] using huv.ne.symm,
      by simpa [D] using hub.symm⟩
    have hc' : c ∈ S := (hS c v hcv).resolve_right hv
    have hb : b ∈ S := (hS v b hbc).resolve_left hv
    refine ⟨insert v (S.erase c), ?_, ?_⟩
    · intro a w haw
      have hhit (a w : Fin n) (haw : G.Adj a w) (ha : a = u ∨ a = c) :
          w ∈ insert v (S.erase c) := by
        rcases ha with rfl | rfl
        · simp [hu w haw]
        · rcases (degree_two_neighbors (tri_rotate (tri_rotate ht)) hc w).1 haw with rfl | rfl
          · simp
          · simp [hb, ht.2.1.ne]
      by_cases ha : a = u ∨ a = c
      · exact .inr (hhit a w haw ha)
      by_cases hw : w = u ∨ w = c
      · exact .inl (hhit w a haw.symm hw)
      have ha' : a ≠ u ∧ a ≠ c := not_or.mp ha
      have hw' : w ≠ u ∧ w ≠ c := not_or.mp hw
      rcases hS a w ⟨haw, by simpa [D] using ha'.1, by simpa [D] using hw'.1⟩ with h | h
      · exact .inl (by simp [h, ha'.2])
      · exact .inr (by simp [h, hw'.2])
    · have hne : v ∉ S.erase c := fun h => hv (Finset.mem_of_mem_erase h)
      rw [Finset.card_insert_of_notMem hne, Finset.card_erase_of_mem hc']
      have := Finset.card_pos.mpr ⟨c, hc'⟩
      omega
  · have he := graph_essential G φ hφ huv
    have hr := reduce_le D φ (fun _ => false)
    have ht := count_add_outside D φ
    change 0 < count D φ at he
    omega

private theorem empty_splice {n : ℕ} (D X : Finset (Fin n)) (hX : X ⊆ D) :
    splice D (bits X) (bits ∅) = bits X := by
  rw [splice_bits]
  simp [Finset.inter_eq_left.mpr hX]

private theorem peel_star {n : ℕ} (G : Graph n) [DecidableRel G.Adj]
    (hg : Good G) (ih : Smaller G) (φ : DMFormula n) (hφ : ∀ x, φ.eval x = funOf G x)
    {u v p : Fin n} (huv : G.Adj u v) (hu : ∀ w, G.Adj u w → w = v)
    (hv : ∀ w, G.Adj v w → (∀ z, G.Adj w z → z = v) ∨ w = p) : Budget G φ.leaves := by
  classical
  let L := (G.neighborFinset v).filter fun w => ∀ z, G.Adj w z → z = v
  let D := insert v L
  letI : DecidableRel (cut G D).Adj := cutDec G D
  have hL (w : Fin n) : w ∈ L ↔ G.Adj v w ∧ ∀ z, G.Adj w z → z = v := by simp [L]
  have hvL : v ∉ L := fun h => ((hL v).1 h).1.ne rfl
  have hvD : v ∈ D := by simp [D]
  have huD : u ∈ D := Finset.mem_insert_of_mem ((hL u).2 ⟨huv.symm, hu⟩)
  have hcard : D.card = L.card + 1 := Finset.card_insert_of_notMem hvL
  have hD (w : Fin n) : w ∈ D ↔ w = v ∨ w ∈ L := by simp [D]
  have he (w : Fin n) (hw : w ∈ D) : 0 < count {w} φ := by
    rcases (hD w).1 hw with rfl | hw
    · exact graph_essential G φ hφ huv.symm
    · exact graph_essential G φ hφ ((hL w).1 hw).1.symm
  have hcut (x : Input n) (hx : x v = false) (a b : Fin n) (hab : G.Adj a b)
      (ha : a ∈ D) (hax : x a = true) : b ∈ D ∧ x b = false := by
    rcases (hD a).1 ha with rfl | ha
    · rw [hx] at hax; contradiction
    · rw [((hL a).1 ha).2 b hab]
      exact ⟨hvD, hx⟩
  have hcover (S : Finset (Fin n)) (hS : CoverPromise.IsVertexCover (cut G D) S) :
      ∃ T, CoverPromise.IsVertexCover G T ∧ T.card ≤ S.card + 1 := by
    refine ⟨insert v S, ?_, Finset.card_insert_le _ _⟩
    intro a b hab
    have hcent (a b : Fin n) (ha : a ∈ D) (hab : G.Adj a b) : a = v ∨ b = v := by
      exact ((hD a).1 ha).imp_right (fun ha => ((hL a).1 ha).2 b hab)
    by_cases ha : a ∈ D
    · rcases hcent a b ha hab with rfl | rfl <;> simp
    by_cases hb : b ∈ D
    · rcases hcent b a hb hab.symm with rfl | rfl <;> simp
    exact (hS a b ⟨hab, ha, hb⟩).imp Finset.mem_insert_of_mem Finset.mem_insert_of_mem
  let E := L.image fun w => s(v, w)
  have hE (a b : Fin n) (hab : G.Adj a b) (ha : a ∈ D)
      (hh : ∀ w, G.Adj v w → w ∈ L ∨ s(v, w) ∈ ({s(v, p)} : Finset _)) :
      s(a, b) ∈ insert s(v, p) E := by
    rcases (hD a).1 ha with rfl | ha
    · rcases hh b hab with hl | hp
      · exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hl)
      · rw [Finset.mem_singleton.mp hp]
        exact Finset.mem_insert_self _ _
    · rw [((hL a).1 ha).2 b hab, Sym2.eq_swap (a := a) (b := v)]
      exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ ha)
  by_cases hp : G.Adj v p ∧ p ∉ D
  · have hthree : ∃ x y z, cofactorNe D φ x y ∧ cofactorNe D φ x z ∧ cofactorNe D φ y z := by
      refine ⟨bits ∅, bits {v}, bits {u, v}, ?_, ?_, ?_⟩
      · refine ⟨bits {p}, ?_⟩
        have h0 : splice D (bits ∅) (bits {p}) = bits {p} := by
          rw [splice_bits]
          congr 1
          ext w
          simp +contextual [hp.2]
        have h1 : splice D (bits {v}) (bits {p}) = bits {v, p} := by
          rw [splice_bits]
          congr 1
          ext w
          simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff,
            Finset.mem_insert, Finset.mem_singleton]
          grind [hp.2]
        rw [h0, h1, hφ, hφ, (funOf_false _ _).2 (inactive_singleton G p),
          (funOf_true _ _).2 ((active_pair _ _ _).2 hp.1)]
        decide
      · refine ⟨bits ∅, ?_⟩
        rw [empty_splice D ∅ (by simp), empty_splice D {u, v} (Finset.insert_subset_iff.mpr ⟨huD, Finset.singleton_subset_iff.mpr hvD⟩), hφ, hφ,
          (funOf_false _ _).2 (inactive_empty G), (funOf_true _ _).2 ((active_pair _ _ _).2 huv)]
        decide
      · refine ⟨bits ∅, ?_⟩
        rw [empty_splice D {v} (Finset.singleton_subset_iff.mpr hvD), empty_splice D {u, v} (Finset.insert_subset_iff.mpr ⟨huD, Finset.singleton_subset_iff.mpr hvD⟩), hφ, hφ,
          (funOf_false _ _).2 (inactive_singleton G v), (funOf_true _ _).2 ((active_pair _ _ _).2 huv)]
        decide
    have ho : 0 < outside D φ := by
      apply (graph_essential G φ hφ hp.1.symm).trans_le
      change count {p} φ ≤ count Dᶜ φ
      rw [count_sum Dᶜ]
      exact Finset.single_le_sum (f := fun w => count {w} φ) (fun _ _ => Nat.zero_le _) (by simpa using hp.2)
    obtain ⟨x, hx, hb⟩ := star_saving D φ v hvD he ho hthree
    refine use_cut G hg ih D φ hφ x (hcut x hx) ⟨u, huD, v, huv⟩
      (L.card + 1) 1 ?_ hcover (by omega)
    refine (removed_sub G D (insert s(v, p) E) (fun a b hab ha => hE a b hab ha ?_)).trans ?_
    · intro w hw
      rcases hv w hw with hl | rfl
      · exact .inl ((hL w).2 ⟨hw, hl⟩)
      · exact .inr (by simp)
    · exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right Finset.card_image_le _)
  · refine use_cut G hg ih D φ hφ (fun _ => false) (hcut _ rfl) ⟨u, huD, v, huv⟩
      L.card 1 ?_ hcover ?_
    · refine (removed_sub G D E (fun a b hab ha => ?_)).trans Finset.card_image_le
      rcases (hD a).1 ha with rfl | ha
      · apply Finset.mem_image_of_mem
        rcases hv b hab with hl | rfl
        · exact (hL b).2 ⟨hab, hl⟩
        · exact ((hD b).1 (by by_contra hn; exact hp ⟨hab, hn⟩)).resolve_left hab.ne.symm
      · rw [((hL a).1 ha).2 b hab, Sym2.eq_swap (a := a) (b := v)]
        exact Finset.mem_image_of_mem _ ha
    · have hr := reduce_le D φ (fun _ => false)
      have hc := count_essential D φ he
      have ht := count_add_outside D φ
      omega

private theorem peel_triangle {n : ℕ} (G : Graph n) [DecidableRel G.Adj]
    (hg : Good G) (ih : Smaller G) (φ : DMFormula n) (hφ : ∀ x, φ.eval x = funOf G x)
    {a b c : Fin n} (ht : Tri G a b c) (hb : G.degree b = 2) (hc : G.degree c = 2) (ha3 : G.degree a ≤ 3) :
    Budget G φ.leaves := by
  let D : Finset (Fin n) := {a, b, c}
  letI : DecidableRel (cut G D).Adj := cutDec G D
  have haD : a ∈ D := by simp [D]
  have hbD : b ∈ D := by simp [D]
  have hcD : c ∈ D := by simp [D]
  have hbn := degree_two_neighbors (tri_rotate ht) hb
  have hcn := degree_two_neighbors (tri_rotate (tri_rotate ht)) hc
  have hab := ht.1.ne
  have hbc := ht.2.1.ne
  have hca := ht.2.2.ne
  have hcover (S : Finset (Fin n)) (hS : CoverPromise.IsVertexCover (cut G D) S) :
      ∃ T, CoverPromise.IsVertexCover G T ∧ T.card ≤ S.card + 2 := by
    refine ⟨insert a (insert b S), ?_, ?_⟩
    · have hhit (u v : Fin n) (hu : u ∈ D) (h : G.Adj u v) :
          u ∈ insert a (insert b S) ∨ v ∈ insert a (insert b S) := by
        simp only [D, Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl | rfl
        · simp
        · simp
        · rcases (hcn v).1 h with rfl | rfl <;> simp
      intro u v huv
      by_cases hu : u ∈ D
      · exact hhit u v hu huv
      by_cases hv : v ∈ D
      · exact (hhit v u hv huv.symm).symm
      exact (hS u v ⟨huv, hu, hv⟩).imp (fun h => by simp [h]) (fun h => by simp [h])
    · have h₁ := Finset.card_insert_le a (insert b S)
      have h₂ := Finset.card_insert_le b S
      omega
  have hcut (i : Fin 8) (hi : i = 0 ∨ i = 2 ∨ i = 4) (u v : Fin n) (huv : G.Adj u v)
      (_ : u ∈ D) (hu : triRow a b c i.val u = true) :
      v ∈ D ∧ triRow a b c i.val v = false := by
    rcases hi with rfl | rfl | rfl
    · change bits ∅ u = true at hu
      simp [bits] at hu
    · change bits {b} u = true at hu
      have hub : u = b := by simpa [bits] using hu
      subst u
      change v ∈ D ∧ bits {b} v = false
      rcases (hbn v).1 huv with rfl | rfl <;> simp [bits, D, hbc.symm, hab]
    · change bits {c} u = true at hu
      have huc : u = c := by simpa [bits] using hu
      subst u
      change v ∈ D ∧ bits {c} v = false
      rcases (hcn v).1 huv with rfl | rfl <;> simp [bits, D, hbc, hca.symm]
  let E : Finset (Sym2 (Fin n)) := {s(a, b), s(b, c), s(c, a)}
  have hE : E.card ≤ 3 := by
    have h₁ := Finset.card_insert_le s(a,b) ({s(b,c), s(c,a)} : Finset _)
    have h₂ := Finset.card_insert_le s(b,c) ({s(c,a)} : Finset _)
    simp only [Finset.card_singleton] at h₂
    change E.card ≤ 3
    unfold E
    omega
  have hin (u v : Fin n) (huv : G.Adj u v) (hu : u ∈ D) (hv : v ∈ D) :
      s(u, v) ∈ E := by
    simp only [D, Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
    all_goals first | exact (huv.ne rfl).elim | simp [E] | rw [Sym2.eq_swap]; simp [E]
  by_cases hp : ∃ p, G.Adj a p ∧ p ∉ D
  · obtain ⟨p, hp, hpD⟩ := hp
    obtain ⟨i, hi, hr⟩ := attached_triangle_saving G ht hp hpD φ hφ
    have hp' : p ≠ b ∧ p ≠ c := ⟨fun e => hpD (e ▸ hbD), fun e => hpD (e ▸ hcD)⟩
    have han := degree_three_neighbors ht ha3 hp hp'.1 hp'.2
    refine use_cut G hg ih D φ hφ (triRow a b c i.val) (hcut i hi)
      ⟨a, haD, b, ht.1⟩ 4 2 ?_ hcover (by omega)
    refine (removed_sub G D (insert s(a, p) E) (fun u v huv hu => ?_)).trans ?_
    · by_cases hv : v ∈ D
      · exact Finset.mem_insert_of_mem (hin u v huv hu hv)
      simp only [D, Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl
      · rcases (han v).1 huv with rfl | rfl | rfl
        · exact (hv hbD).elim
        · exact (hv hcD).elim
        · simp
      · rcases (hbn v).1 huv with rfl | rfl
        · exact (hv hcD).elim
        · exact (hv haD).elim
      · rcases (hcn v).1 huv with rfl | rfl
        · exact (hv haD).elim
        · exact (hv hbD).elim
    · exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right hE 1)
  · refine use_cut G hg ih D φ hφ (triRow a b c 0) (hcut 0 (.inl rfl))
      ⟨a, haD, b, ht.1⟩ 3 2 ?_ hcover ?_
    · refine (removed_sub G D E (fun u v huv hu => hin u v huv hu ?_)).trans hE
      simp only [D, Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl
      · by_contra hn
        exact hp ⟨v, huv, hn⟩
      · rcases (hbn v).1 huv with rfl | rfl
        · exact hcD
        · exact haD
      · rcases (hcn v).1 huv with rfl | rfl
        · exact haD
        · exact hbD
    · have hr := reduce_le D φ (triRow a b c 0)
      have ht' := count_add_outside D φ
      have hc' : 5 ≤ count D φ := restrict_triangle G ht φ hφ
      omega

private theorem no_edges_budget {n : ℕ} (G : Graph n) [DecidableRel G.Adj]
    (h : ¬ ∃ u v, G.Adj u v) (k : ℕ) : Budget G k := by
  have he : G.edgeFinset = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e
    induction e using Sym2.ind with
    | h u v =>
      simp only [mem_edgeFinset, mem_edgeSet]
      exact fun huv => h ⟨u, v, huv⟩
  exact ⟨∅, fun u v huv => (h ⟨u, v, huv⟩).elim, by simp [he]⟩


private theorem peel_twin_leaf {n : ℕ} (G : Graph n) [DecidableRel G.Adj]
    (hg : Good G) (ih : Smaller G) (φ : DMFormula n) (hφ : ∀ x, φ.eval x = funOf G x)
    {u1 u2 v : Fin n} (h1 : G.Adj u1 v) (h2 : G.Adj u2 v) (hne : u1 ≠ u2)
    (hl1 : ∀ w, G.Adj u1 w → w = v) (hl2 : ∀ w, G.Adj u2 w → w = v) :
    Budget G φ.leaves := by
  let D : Finset (Fin n) := {u1}
  letI : DecidableRel (cut G D).Adj := cutDec G D
  refine use_cut G hg ih D φ hφ (fun _ => false) (by simp) ⟨u1, by simp [D], v, h1⟩ 1 0 ?_ ?_ ?_
  · refine (removed_sub G D {s(u1, v)} (fun a w haw ha => ?_)).trans (by simp)
    have ha' : a = u1 := by simpa [D] using ha
    subst a
    rw [hl1 w haw]; simp
  · intro S hS
    by_cases hv : v ∈ S
    · refine ⟨S, ?_, by simp⟩
      intro a w haw
      by_cases ha : a = u1
      · subst a; exact .inr (hl1 w haw ▸ hv)
      by_cases hw : w = u1
      · subst w; exact .inl (hl1 a haw.symm ▸ hv)
      exact hS a w ⟨haw, by simpa [D], by simpa [D]⟩
    have hu2v : (cut G D).Adj u2 v := ⟨h2, by simpa [D] using hne.symm, by simpa [D] using h1.ne.symm⟩
    have hu2S : u2 ∈ S := (hS u2 v hu2v).resolve_right hv
    refine ⟨insert v (S.erase u2), ?_, ?_⟩
    · intro a w haw
      by_cases ha : a = u1 ∨ a = u2
      · rcases ha with rfl | rfl
        · exact .inr (by simp [hl1 w haw])
        · exact .inr (by simp [hl2 w haw])
      by_cases hw : w = u1 ∨ w = u2
      · rcases hw with rfl | rfl
        · exact .inl (by simp [hl1 a haw.symm])
        · exact .inl (by simp [hl2 a haw.symm])
      have ha' := not_or.mp ha
      have hw' := not_or.mp hw
      rcases hS a w ⟨haw, by simpa [D] using ha'.1, by simpa [D] using hw'.1⟩ with h | h
      · exact .inl (by simp [h, ha'.2])
      · exact .inr (by simp [h, hw'.2])
    · have hnv : v ∉ S.erase u2 := fun h => hv (Finset.mem_of_mem_erase h)
      rw [Finset.card_insert_of_notMem hnv, Finset.card_erase_of_mem hu2S]
      have := Finset.card_pos.mpr ⟨u2, hu2S⟩
      omega
  · have he := graph_essential G φ hφ h1
    have hr := reduce_le D φ (fun _ => false)
    have ht := count_add_outside D φ
    change 0 < count D φ at he
    omega

private theorem peel_D4 {n : ℕ} (G : Graph n) [DecidableRel G.Adj]
    (hg : Good G) (ih : Smaller G) (φ : DMFormula n) (hφ : ∀ x, φ.eval x = funOf G x)
    {a b c ub uc : Fin n} (ht : Tri G a b c)
    (hbub : G.Adj b ub) (hcuc : G.Adj c uc)
    (hubl : ∀ w, G.Adj ub w → w = b) (hucl : ∀ w, G.Adj uc w → w = c)
    (hdb : G.degree b = 3) (hdc : G.degree c = 3) :
    Budget G φ.leaves := by
  let D : Finset (Fin n) := {b, c, ub, uc}
  letI : DecidableRel (cut G D).Adj := cutDec G D
  have hbc : b ≠ c := ht.2.1.ne
  have hbub_ne : b ≠ ub := hbub.ne
  have hbuc_ne : b ≠ uc := fun h => ht.2.2.ne.symm (hucl a (h ▸ ht.1.symm))
  have hcub_ne : c ≠ ub := fun h => ht.1.ne (hubl a (h ▸ ht.2.2))
  have hcuc_ne : c ≠ uc := hcuc.ne
  have hubuc_ne : ub ≠ uc := fun h => hbc.symm (hubl c (h ▸ hcuc.symm))
  have huba : ub ≠ a := fun h => ht.2.1.ne.symm (hubl c (h ▸ ht.2.2.symm))
  have huca : uc ≠ a := fun h => ht.2.1.ne (hucl b (h ▸ ht.1))
  have hbn := degree_three_neighbors (tri_rotate ht) (by omega) hbub hcub_ne.symm huba
  have hcn := degree_three_neighbors (tri_rotate (tri_rotate ht)) (by omega) hcuc huca hbuc_ne.symm
  obtain ⟨u1, u2, hsave⟩ := peel_D4_saving G ht hbub hcuc hubl hucl φ hφ
  refine use_cut G hg ih D φ hφ (d4Assign ub uc u1 u2) ?_ ⟨b, by simp [D], c, ht.2.1⟩ 5 2 ?_ ?_ (by omega)
  · intro u v huv _ hu
    by_cases h1 : u = ub
    · subst u
      rw [hubl v huv]
      exact ⟨by simp [D], by simp [d4Assign, hbub_ne, hbuc_ne]⟩
    by_cases h2 : u = uc
    · subst u
      rw [hucl v huv]
      exact ⟨by simp [D], by simp [d4Assign, hcub_ne, hcuc_ne]⟩
    simp [d4Assign, h1, h2] at hu
  · let E : Finset (Sym2 (Fin n)) := {s(a, b), s(a, c), s(b, c), s(b, ub), s(c, uc)}
    have hEcard : E.card ≤ 5 := by
      have h1 := Finset.card_insert_le s(a, b) ({s(a, c), s(b, c), s(b, ub), s(c, uc)} : Finset _)
      have h2 := Finset.card_insert_le s(a, c) ({s(b, c), s(b, ub), s(c, uc)} : Finset _)
      have h3 := Finset.card_insert_le s(b, c) ({s(b, ub), s(c, uc)} : Finset _)
      have h4 := Finset.card_insert_le s(b, ub) ({s(c, uc)} : Finset _)
      simp only [Finset.card_singleton] at h4
      change E.card ≤ 5; unfold E; omega
    refine (removed_sub G D E (fun u v huv hu => ?_)).trans hEcard
    simp only [D, Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · rcases (hbn v).1 huv with rfl | rfl | rfl
      · simp [E]
      · rw [Sym2.eq_swap]; simp [E]
      · simp [E]
    · rcases (hcn v).1 huv with rfl | rfl | rfl
      · rw [Sym2.eq_swap]; simp [E]
      · rw [Sym2.eq_swap]; simp [E]
      · simp [E]
    · rw [hubl v huv, Sym2.eq_swap]; simp [E]
    · rw [hucl v huv, Sym2.eq_swap]; simp [E]
  · intro S hS
    refine ⟨insert b (insert c S), ?_, ?_⟩
    · have hhit (u v : Fin n) (hu : u ∈ D) (huv : G.Adj u v) :
          u ∈ insert b (insert c S) ∨ v ∈ insert b (insert c S) := by
        simp only [D, Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl | rfl | rfl
        · exact .inl (by simp)
        · exact .inl (by simp)
        · rw [hubl v huv]; exact .inr (by simp)
        · rw [hucl v huv]; exact .inr (by simp)
      intro u v huv
      by_cases hu : u ∈ D
      · exact hhit u v hu huv
      by_cases hv : v ∈ D
      · exact (hhit v u hv huv.symm).symm
      exact (hS u v ⟨huv, hu, hv⟩).imp (fun h => by simp [h]) (fun h => by simp [h])
    · have h1 := Finset.card_insert_le b (insert c S)
      have h2 := Finset.card_insert_le c S
      omega

private theorem lower_bound {n : ℕ} (G : Graph n) [DecidableRel G.Adj] (hg : Good G)
    (r : Reduced n) (hr : ∀ y, value y r = funOf G y) : Budget G (weight r) := by
  generalize hk : G.edgeFinset.card = k
  induction k using Nat.strong_induction_on generalizing G r with
  | ind k ih =>
    by_cases he : ∃ u v, G.Adj u v
    · cases r with
      | inl d =>
        obtain ⟨u, v, huv⟩ := he
        have h₀ := (hr (bits ∅)).trans ((funOf_false _ _).2 (inactive_empty G))
        have h₁ := (hr (bits {u, v})).trans ((funOf_true _ _).2 ((active_pair _ _ _).2 huv))
        exact (Bool.false_ne_true (h₀.symm.trans h₁)).elim
      | inr φ =>
        have hi : Smaller G := by
          intro H _ hlt hh p hp
          exact ih H.edgeFinset.card (hk ▸ hlt) H hh p hp rfl
        rcases structural222 G hg he with
            ⟨u1, u2, v, h1, h2, hne, hl1, hl2⟩ |
            ⟨u, v, b, c, huv, hu, ht, hc⟩ |
            ⟨a, b, c, ht, hb, hc, ha3⟩ |
            ⟨u, v, p, huv, hu, hv⟩ |
            ⟨a, b, c, ub, uc, ht, hbub, hcuc, hubl, hucl, hdb, hdc⟩
        · exact peel_twin_leaf G hg hi φ hr h1 h2 hne hl1 hl2
        · exact peel_triangle_pendant G hg hi φ hr huv hu ht hc
        · exact peel_triangle G hg hi φ hr ht hb hc ha3
        · exact peel_star G hg hi φ hr huv hu hv
        · exact peel_D4 G hg hi φ hr ht hbub hcuc hubl hucl hdb hdc
    · exact no_edges_budget G he _

private theorem or_vars {n : ℕ} (S : Finset (Fin n)) :
    ∃ r : Reduced n, weight r ≤ S.card ∧
      ∀ x, value x r = true ↔ ∃ v ∈ S, x v = true := by
  induction S using Finset.induction_on with
  | empty => exact ⟨.inl false, by simp [weight, value]⟩
  | @insert v S hv ih =>
    obtain ⟨r, hr, he⟩ := ih
    refine ⟨combine true (.inr (.lit v true)) r, ?_, ?_⟩
    · have h := combine_le true (.inr (.lit v true)) r
      rw [Finset.card_insert_of_notMem hv]
      change weight (combine true (.inr (.lit v true)) r) ≤ 1 + weight r at h
      omega
    · intro x
      rw [combine_eval]
      change (x v || value x r) = true ↔ ∃ w ∈ insert v S, x w = true
      rw [Bool.or_eq_true, he x]
      simp only [Finset.mem_insert]
      constructor
      · rintro (hx | ⟨w, hw, hx⟩)
        · exact ⟨v, .inl rfl, hx⟩
        · exact ⟨w, .inr hw, hx⟩
      · rintro ⟨w, rfl | hw, hx⟩
        · exact .inl hx
        · exact .inr ⟨w, hw, hx⟩

private theorem upper_bound {n : ℕ} (S : Finset (Fin n))
    (G : Graph n) [DecidableRel G.Adj] (hS : CoverPromise.IsVertexCover G S) :
    ∃ r : Reduced n, weight r ≤ G.edgeFinset.card + S.card ∧ ∀ x, value x r = funOf G x := by
  induction S using Finset.induction_on generalizing G with
  | empty =>
    have h : ∀ u v, ¬G.Adj u v := by
      intro u v hu
      simpa using hS u v hu
    exact ⟨.inl false, Nat.zero_le _, fun x => ((funOf_false _ _).2
      (fun ⟨u, v, huv, _⟩ => h u v huv)).symm⟩
  | @insert v S hv ih =>
    let H := G.deleteIncidenceSet v
    have hH : CoverPromise.IsVertexCover H S := by
      intro a b hab
      obtain ⟨hab, ha, hb⟩ := deleteIncidenceSet_adj.mp hab
      simpa [Finset.mem_insert, ha, hb] using hS a b hab
    obtain ⟨r, hr, he⟩ := ih H hH
    obtain ⟨o, ho, hoe⟩ := or_vars (G.neighborFinset v)
    let a := combine false (.inr (.lit v true)) o
    refine ⟨combine true a r, ?_, ?_⟩
    · have h₁ := combine_le true a r
      have h₂ := combine_le false (.inr (.lit v true)) o
      change weight a ≤ 1 + weight o at h₂
      have h₃ := card_edgeFinset_deleteIncidenceSet G v
      have h₄ : G.degree v ≤ G.edgeFinset.card := by
        rw [← card_incidenceFinset_eq_degree]
        exact Finset.card_le_card (G.incidenceFinset_subset _)
      change H.edgeFinset.card = _ at h₃
      change weight o ≤ G.degree v at ho
      rw [Finset.card_insert_of_notMem hv]
      omega
    · intro x
      have ha : value x a = (x v && value x o) := by
        unfold a
        rw [combine_eval]
        rfl
      have hl : value x (combine true a r) = ((x v && value x o) || funOf H x) := by
        rw [combine_eval, ha, he]
        rfl
      rw [hl]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.or_eq_true, Bool.and_eq_true, hoe x, mem_neighborFinset, funOf_true]
      constructor
      · rintro (⟨hv, w, hw, hx⟩ | ⟨u, w, huw, hu, hw⟩)
        · exact ⟨v, w, hw, hv, hx⟩
        · exact ⟨u, w, (deleteIncidenceSet_adj.mp huw).1, hu, hw⟩
      · rintro ⟨u, w, huw, hu, hw⟩
        by_cases heq : u = v
        · subst u
          exact .inl ⟨hu, w, huw, hw⟩
        by_cases hweq : w = v
        · subst w
          exact .inl ⟨hw, u, huw.symm, hu⟩
        exact .inr ⟨u, w, deleteIncidenceSet_adj.mpr ⟨huw, heq, hweq⟩, hu, hw⟩

private theorem main {n : ℕ} (G : Graph n) [DecidableRel G.Adj] (t s : ℕ)
    (he : ∃ u v, G.Adj u v) (hg : Good G)
    (ht : ∃ S, CoverPromise.IsVertexCover G S ∧ S.card = t)
    (hmin : ∀ S, CoverPromise.IsVertexCover G S → t ≤ S.card) :
    HasLeafSize n (funOf G) s ↔ G.edgeFinset.card + t ≤ s := by
  constructor
  · rintro ⟨φ, hs, hp⟩
    obtain ⟨S, hS, hb⟩ := lower_bound G hg (.inr φ) hp
    exact (Nat.add_le_add_left (hmin S hS) _).trans (hb.trans hs)
  · intro hs
    obtain ⟨S, hS, rfl⟩ := ht
    obtain ⟨r, hb, hr⟩ := upper_bound S G hS
    cases r with
    | inr φ => exact ⟨φ, hb.trans hs, hr⟩
    | inl d =>
      obtain ⟨u, v, huv⟩ := he
      have h₀ := (hr (bits ∅)).trans ((funOf_false _ _).2 (inactive_empty G))
      have h₁ := (hr (bits {u, v})).trans ((funOf_true _ _).2 ((active_pair _ _ _).2 huv))
      exact (Bool.false_ne_true (h₀.symm.trans h₁)).elim


end PEqualNP.Outside.L_meta_222

theorem PEqualNP.Outside.L_meta_222 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (t s : ℕ), (∃ u v : Fin n, G.Adj u v) → (∀ (u : Fin n) (p : G.Walk u u), p.IsCycle → p.length = 3) → (∀ a b c d e : Fin n, G.Adj a b → G.Adj b c → G.Adj c a → G.Adj a d → G.Adj d e → G.Adj e a → ((b = d ∧ c = e) ∨ (b = e ∧ c = d))) → (∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧ S.card = t) → (∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → t ≤ S.card) → (PEqualNP.MetaComplexity.HasLeafSize n (fun x : Fin n → Bool => decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) s ↔ G.edgeFinset.card + t ≤ s) := by
  intro n G _ t s he hcyc hdisj ht hmin
  apply PEqualNP.Outside.L_meta_222.main G t s he ?_ ht hmin
  refine ⟨hcyc, ?_⟩
  intro a b c d e h1 h2
  exact hdisj a b c d e h1.1 h1.2.1 h1.2.2 h2.1 h2.2.1 h2.2.2
