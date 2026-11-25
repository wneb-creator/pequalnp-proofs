import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583_aux.Structural

lemma point_degree (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hpair : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (p : Fin N) : (Finset.univ.filter (fun l => I p l)).card = q + 1 := by
  classical
  let L : Finset (Fin N) := Finset.univ.filter (fun l => I p l)
  let F (l : Fin N) : Finset (Fin N) := (Finset.univ.filter (fun r => I r l)).erase p
  have hc : ∀ l ∈ L, (F l).card = q := by
    intro l hl
    have hp : p ∈ Finset.univ.filter (fun r => I r l) := by
      simpa [L] using hl
    simp only [F, Finset.card_erase_of_mem hp, hline]
    omega
  have hd : (L : Set (Fin N)).PairwiseDisjoint F := by
    intro l hl l' hl' hne
    apply Finset.disjoint_left.mpr
    intro r hr hr'
    have hrl : r ≠ p ∧ I r l := by simpa [F] using hr
    have hrl' : r ≠ p ∧ I r l' := by simpa [F] using hr'
    have hpl : I p l := by simpa [L] using hl
    have hpl' : I p l' := by simpa [L] using hl'
    obtain ⟨a, ha, hu⟩ := hpair p r (Ne.symm hrl.1)
    exact hne ((hu l ⟨hpl, hrl.2⟩).trans (hu l' ⟨hpl', hrl'.2⟩).symm)
  have hu : L.biUnion F = Finset.univ.erase p := by
    ext r
    simp only [Finset.mem_biUnion, L, F, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_erase]
    constructor
    · rintro ⟨l, hpl, hrp, hrl⟩
      exact ⟨hrp, trivial⟩
    · rintro ⟨hrp, _⟩
      obtain ⟨l, ⟨hpl, hrl⟩, _⟩ := hpair p r (Ne.symm hrp)
      exact ⟨l, hpl, hrp, hrl⟩
  have hsum : (L.biUnion F).card = L.card * q := by
    rw [Finset.card_biUnion hd]
    exact Finset.sum_const_nat hc
  have hcount : (Finset.univ.erase p).card + 1 = N := by
    simpa using Finset.card_erase_add_one (Finset.mem_univ p)
  rw [← hu, hsum] at hcount
  change L.card = q + 1
  have hmul : q * L.card = q * (q + 1) := by nlinarith
  exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < q) hmul

lemma pencil_cover_card {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hpair : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (p : Fin N) (X : Finset (Fin N)) (hp : p ∉ X)
    (hc : ∀ l : Fin N, I p l → ∃ a ∈ X, I a l) :
    (Finset.univ.filter (fun l => I p l)).card ≤ X.card := by
  classical
  let L := Finset.univ.filter (fun l => I p l)
  let J := fun a : Fin N => Finset.univ.filter (fun l => I p l ∧ I a l)
  have hJ : ∀ a ∈ X, (J a).card ≤ 1 := by
    intro a ha
    apply Finset.card_le_one.mpr
    intro l hl r hr
    have hpa : p ≠ a := by rintro rfl; exact hp ha
    obtain ⟨k, _, hk⟩ := hpair p a hpa
    exact (hk l (Finset.mem_filter.mp hl).2).trans
      (hk r (Finset.mem_filter.mp hr).2).symm
  have hsub : L ⊆ X.biUnion J := by
    intro l hl
    obtain ⟨a, ha, hal⟩ := hc l (Finset.mem_filter.mp hl).2
    exact Finset.mem_biUnion.mpr ⟨a, ha, by simp [J, (Finset.mem_filter.mp hl).2, hal]⟩
  calc
    L.card ≤ (X.biUnion J).card := Finset.card_le_card hsub
    _ ≤ ∑ a ∈ X, (J a).card := Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ X, 1 := Finset.sum_le_sum hJ
    _ = X.card := by simp

lemma independent_pencil_replacement {q N : ℕ} (I : Fin N → Fin N → Prop)
    [DecidableRel I] (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hpair : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (p : Fin N) (X Y : Finset (Fin N)) (hp : p ∉ X)
    (hind : ∀ a ∈ X, ∀ b ∈ Y, ¬ I a b)
    (hreplace : ∀ l : Fin N, I p l → ∃ a ∈ X, ∃ b ∈ insert l Y, I a b) :
    q + 1 ≤ X.card := by
  rw [← point_degree q N I hq hN hline hpair p]
  apply pencil_cover_card I hpair p X hp
  intro l hpl
  obtain ⟨a, ha, b, hb, hab⟩ := hreplace l hpl
  rcases Finset.mem_insert.mp hb with rfl | hb
  · exact ⟨a, ha, hab⟩
  · exact (hind a ha b hb hab).elim

end PEqualNP.Outside.L_meta_2583_aux.Structural


namespace PEqualNP.Outside.L_meta_2583_aux.OrSplice

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma getD_snoc (W : List Bool) (v : Bool) (w : ℕ) :
    (W ++ [v]).getD w false = if w = W.length then v else W.getD w false := by
  rcases lt_trichotomy w W.length with h | h | h
  · rw [List.getD_append _ _ _ _ h, if_neg (Nat.ne_of_lt h)]
  · subst h
    rw [List.getD_append_right _ _ _ _ (le_refl _), if_pos rfl]
    simp
  · rw [List.getD_append_right _ _ _ _ (le_of_lt h), if_neg (Nat.ne_of_gt h)]
    have h1 : 1 ≤ w - W.length := by omega
    rw [List.getD_eq_default _ _ (by simpa using h1),
      List.getD_eq_default _ _ (le_of_lt h)]

lemma gate_mono (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (a b : ℕ → Bool) (h : ∀ i ∈ g.inputs, a i = true → b i = true) :
    g.op.eval (g.inputs.map a) = true → g.op.eval (g.inputs.map b) = true := by
  rcases hop with h1 | h1
  · rw [h1]
    simp only [GateOp.eval]
    intro hall
    rw [List.all_eq_true] at hall ⊢
    intro y hy
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy
    exact h i hi (hall _ (List.mem_map.mpr ⟨i, hi, rfl⟩))
  · rw [h1]
    simp only [GateOp.eval]
    intro hany
    rw [List.any_eq_true] at hany ⊢
    obtain ⟨y, hy, hyt⟩ := hany
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy
    exact ⟨b i, List.mem_map.mpr ⟨i, hi, rfl⟩, h i hi hyt⟩

lemma fold_mono_except (G : List Gate) (v : ℕ)
    (basis : ∀ g ∈ G, g.op = GateOp.and ∨ g.op = GateOp.or)
    (ignore : ∀ g ∈ G, v ∉ g.inputs)
    (a b : List Bool) (same : a.length = b.length) (early : v < a.length)
    (ordered : ∀ i, i ≠ v → a.getD i false = true → b.getD i false = true) :
    ∀ i, i ≠ v → (G.foldl step a).getD i false = true →
      (G.foldl step b).getD i false = true := by
  induction G generalizing a b with
  | nil => simpa using ordered
  | cons g G ih =>
    rw [List.foldl_cons, List.foldl_cons]
    apply ih
    · exact fun h hm => basis h (List.mem_cons_of_mem g hm)
    · exact fun h hm => ignore h (List.mem_cons_of_mem g hm)
    · simp only [step, List.length_append, List.length_singleton, same]
    · simp only [step, List.length_append, List.length_singleton]
      omega
    · intro i hiv
      simp only [step, getD_snoc, same]
      by_cases hi : i = b.length
      · simp only [hi, if_pos]
        apply gate_mono g (basis g (List.mem_cons_self ..))
        intro j hj
        apply ordered j
        intro he
        exact ignore g (List.mem_cons_self ..) (he ▸ hj)
      · simp only [hi, if_false]
        exact ordered i hiv

lemma eval_mono_except (C : Circuit) (mono : Monotone2 C) (v : ℕ)
    (ignore : ∀ g ∈ C.gates, v ∉ g.inputs) (out : C.output ≠ v)
    (a b : List Bool) (same : a.length = b.length) (early : v < a.length)
    (ordered : ∀ i, i ≠ v → a.getD i false = true → b.getD i false = true) :
    C.eval a = true → C.eval b = true := by
  apply fold_mono_except C.gates v ?_ ignore a b same early ordered C.output out
  intro g hg
  simpa using (mono g hg).1

lemma fold_length (G : List Gate) (x : List Bool) :
    (G.foldl step x).length = x.length + G.length := by
  induction G generalizing x with
  | nil => simp
  | cons g G ih =>
    rw [List.foldl_cons, ih]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma sole_or_transfer (pre post : List Gate) (v a out : ℕ)
    (basis : ∀ g ∈ pre ++ post, g.op = GateOp.and ∨ g.op = GateOp.or)
    (ignore : ∀ g ∈ pre ++ post, v ∉ g.inputs)
    (hout : out ≠ v) (x y : List Bool) (same : x.length = y.length)
    (early : v < x.length)
    (ordered : ∀ i, i ≠ v → x.getD i false = true → y.getD i false = true)
    (other : (pre.foldl step y).getD a false = true) :
    (Circuit.mk (pre ++ ⟨GateOp.or, [v, a]⟩ :: post) out).eval x = true →
      (Circuit.mk (pre ++ ⟨GateOp.or, [v, a]⟩ :: post) out).eval y = true := by
  have preBasis : ∀ g ∈ pre, g.op = GateOp.and ∨ g.op = GateOp.or :=
    fun g hg => basis g (List.mem_append_left _ hg)
  have postBasis : ∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or :=
    fun g hg => basis g (List.mem_append_right _ hg)
  have preIgnore : ∀ g ∈ pre, v ∉ g.inputs :=
    fun g hg => ignore g (List.mem_append_left _ hg)
  have postIgnore : ∀ g ∈ post, v ∉ g.inputs :=
    fun g hg => ignore g (List.mem_append_right _ hg)
  have before := fold_mono_except pre v preBasis preIgnore x y same early ordered
  have len : (pre.foldl step x).length = (pre.foldl step y).length := by
    simp only [fold_length, same]
  have trueGate : GateOp.or.eval ([v, a].map fun i =>
      (pre.foldl step y).getD i false) = true := by
    change ((pre.foldl step y).getD v false ||
      ((pre.foldl step y).getD a false || false)) = true
    rw [other]
    simp
  have after : ∀ i, i ≠ v →
      (step (pre.foldl step x) ⟨GateOp.or, [v, a]⟩).getD i false = true →
      (step (pre.foldl step y) ⟨GateOp.or, [v, a]⟩).getD i false = true := by
    intro i hi
    simp only [step, getD_snoc, len, trueGate]
    by_cases he : i = (pre.foldl step y).length
    · simp [he]
    · simp only [he, if_false]
      exact before i hi
  change ((pre ++ ⟨GateOp.or, [v, a]⟩ :: post).foldl step x).getD out false = true →
    ((pre ++ ⟨GateOp.or, [v, a]⟩ :: post).foldl step y).getD out false = true
  rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons]
  apply fold_mono_except post v postBasis postIgnore _ _ ?_ ?_ after out hout
  · simp only [step, List.length_append, List.length_singleton, len]
  · simp only [step, List.length_append, List.length_singleton, fold_length]
    omega

end PEqualNP.Outside.L_meta_2583_aux.OrSplice

namespace PEqualNP.Outside.L_meta_2583_aux.SoleOr

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Structural OrSplice

def incidenceInput {N : ℕ} (X Y : Finset (Fin N)) : Fin (N + N) → Bool :=
  Fin.append (fun p => decide (p ∈ X)) (fun l => decide (l ∈ Y))

lemma ofFn_ordered_except {n : ℕ} (x y : Fin n → Bool) (v : ℕ)
    (h : ∀ i, i.val ≠ v → x i = true → y i = true) :
    ∀ j, j ≠ v → (List.ofFn x).getD j false = true →
      (List.ofFn y).getD j false = true := by
  intro j hj ht
  by_cases hb : j < n
  · simp only [List.getD, List.getElem?_ofFn, dif_pos hb, Option.getD_some] at ht ⊢
    exact h ⟨j, hb⟩ hj ht
  · simp [List.getD, hb] at ht

lemma input_insert_ordered {N : ℕ} (X Y : Finset (Fin N)) (l : Fin N) :
    ∀ i, incidenceInput X Y i = true → incidenceInput X (insert l Y) i = true := by
  intro i
  refine Fin.addCases (fun p => ?_) (fun r => ?_) i
  · simp [incidenceInput]
  · simp only [incidenceInput, Fin.append_right, decide_eq_true_eq]
    exact Finset.mem_insert_of_mem

lemma pair_ordered_except {N : ℕ} (p l : Fin N) (X Y : Finset (Fin N)) :
    ∀ i : Fin (N + N), i.val ≠ p.val →
      incidenceInput {p} {l} i = true → incidenceInput X (insert l Y) i = true := by
  intro i
  refine Fin.addCases (fun r => ?_) (fun s => ?_) i
  · intro hr ht
    have he : r = p := by simpa [incidenceInput] using ht
    exact (hr (congrArg Fin.val he)).elim
  · intro _ ht
    have he : s = l := by
      simpa only [incidenceInput, Fin.append_right, decide_eq_true_eq, Finset.mem_singleton] using ht
    subst s
    simp only [incidenceInput, Fin.append_right, Finset.mem_insert_self, decide_true]

lemma sole_or_pencil_replacement {N : ℕ} (I : Fin N → Fin N → Prop)
    [DecidableRel I] (pre post : List Gate) (p : Fin N) (a out : ℕ)
    (basis : ∀ g ∈ pre ++ post, g.op = GateOp.and ∨ g.op = GateOp.or)
    (ignore : ∀ g ∈ pre ++ post, p.val ∉ g.inputs)
    (hout : out ≠ p.val) (ha : a ≠ p.val)
    (computes : ∀ z : Fin (N + N) → Bool,
      circuitFun (N + N) (Circuit.mk (pre ++ ⟨GateOp.or, [p.val, a]⟩ :: post) out) z =
        decide (∃ r s : Fin N, I r s ∧ z (Fin.castAdd N r) = true ∧
          z (Fin.natAdd N s) = true))
    (X Y : Finset (Fin N))
    (other : (pre.foldl step (List.ofFn (incidenceInput X Y))).getD a false = true) :
    ∀ l : Fin N, I p l → ∃ r ∈ X, ∃ s ∈ insert l Y, I r s := by
  intro l hpl
  let x := incidenceInput {p} {l}
  let y := incidenceInput X (insert l Y)
  let z := incidenceInput X Y
  have preBasis : ∀ g ∈ pre, g.op = GateOp.and ∨ g.op = GateOp.or :=
    fun g hg => basis g (List.mem_append_left _ hg)
  have preIgnore : ∀ g ∈ pre, p.val ∉ g.inputs :=
    fun g hg => ignore g (List.mem_append_left _ hg)
  have early : p.val < (List.ofFn x).length := by simp [x]; omega
  have otherY : (pre.foldl step (List.ofFn y)).getD a false = true := by
    apply fold_mono_except pre p.val preBasis preIgnore
      (List.ofFn z) (List.ofFn y) (by simp) (by simpa [z] using early) ?_ a ha other
    apply ofFn_ordered_except
    intro i _ ht
    exact input_insert_ordered X Y l i ht
  have source : circuitFun (N + N)
      (Circuit.mk (pre ++ ⟨GateOp.or, [p.val, a]⟩ :: post) out) x = true := by
    rw [computes]
    apply decide_eq_true
    exact ⟨p, l, hpl, by simp only [x, incidenceInput, Fin.append_left, Finset.mem_singleton, decide_true],
      by simp only [x, incidenceInput, Fin.append_right, Finset.mem_singleton, decide_true]⟩
  have target := sole_or_transfer pre post p.val a out basis ignore hout
    (List.ofFn x) (List.ofFn y) (by simp) early
    (ofFn_ordered_except x y p.val (pair_ordered_except p l X Y)) otherY source
  change circuitFun (N + N)
      (Circuit.mk (pre ++ ⟨GateOp.or, [p.val, a]⟩ :: post) out) y = true at target
  rw [computes] at target
  obtain ⟨r, s, hrs, hr, hs⟩ := of_decide_eq_true target
  exact ⟨r, by simpa [y, incidenceInput] using hr, s,
    by simpa only [y, incidenceInput, Fin.append_right, decide_eq_true_eq] using hs, hrs⟩

lemma sole_or_independent_witness_large {q N : ℕ} (I : Fin N → Fin N → Prop)
    [DecidableRel I] (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hpair : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (pre post : List Gate) (p : Fin N) (a out : ℕ)
    (basis : ∀ g ∈ pre ++ post, g.op = GateOp.and ∨ g.op = GateOp.or)
    (ignore : ∀ g ∈ pre ++ post, p.val ∉ g.inputs)
    (hout : out ≠ p.val) (ha : a ≠ p.val)
    (computes : ∀ z : Fin (N + N) → Bool,
      circuitFun (N + N) (Circuit.mk (pre ++ ⟨GateOp.or, [p.val, a]⟩ :: post) out) z =
        decide (∃ r s : Fin N, I r s ∧ z (Fin.castAdd N r) = true ∧
          z (Fin.natAdd N s) = true))
    (X Y : Finset (Fin N)) (hp : p ∉ X)
    (hind : ∀ r ∈ X, ∀ s ∈ Y, ¬ I r s)
    (other : (pre.foldl step (List.ofFn (incidenceInput X Y))).getD a false = true) :
    q + 1 ≤ X.card := by
  apply independent_pencil_replacement I hq hN hline hpair p X Y hp hind
  exact sole_or_pencil_replacement I pre post p a out basis ignore hout ha computes X Y other

end PEqualNP.Outside.L_meta_2583_aux.SoleOr
