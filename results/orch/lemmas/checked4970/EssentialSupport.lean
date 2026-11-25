import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4970.EssentialSupport

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wiresLength (gs : List Gate) (x : List Bool) :
    (gs.foldl step x).length = x.length+gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih => simp [List.foldl_append,step,ih,Nat.add_assoc]

theorem wireSnoc (w : List Bool) (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false = if i = w.length then b else w.getD i false := by
  rcases lt_trichotomy i w.length with h|rfl|h
  · simp [List.getD_eq_getElem?_getD,List.getElem?_append_left h,h.ne]
  · simp [List.getD_eq_getElem?_getD]
  · have h1 : w.length ≤ i := by omega
    have h2 : (w ++ [b]).length ≤ i := by simp; omega
    simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none h1,List.getElem?_eq_none h2,h.ne']

theorem smallSupport (n : ℕ) (gs : List Gate)
    (arity : ∀ g ∈ gs, g.inputs.length ≤ 2) (S : Finset ℕ) :
    ∃ T : Finset ℕ, T.card ≤ S.card + gs.length ∧
      ∀ x y : List Bool, x.length = n → y.length = n →
      (∀ i ∈ T, x.getD i false = y.getD i false) →
      ∀ i ∈ S, (gs.foldl step x).getD i false = (gs.foldl step y).getD i false := by
  induction gs using List.reverseRecOn generalizing S with
  | nil => exact ⟨S,by simp,fun _ _ _ _ same => same⟩
  | append_singleton gs g ih =>
    have prior : ∀ a ∈ gs, a.inputs.length ≤ 2 :=
      fun a ha => arity a (List.mem_append_left _ ha)
    have fan : g.inputs.length ≤ 2 := arity g (List.mem_append_right _ (List.mem_singleton_self _))
    let w := n+gs.length
    let U := if w ∈ S then S.erase w ∪ g.inputs.toFinset else S
    have small : U.card ≤ S.card+1 := by
      dsimp only [U]
      split_ifs with used
      · have h1 := Finset.card_union_le (S.erase w) g.inputs.toFinset
        have h2 := Finset.card_erase_add_one used
        have h3 := List.toFinset_card_le (l := g.inputs)
        omega
      · omega
    obtain ⟨T,bound,works⟩ := ih prior U
    refine ⟨T,by simp only [List.length_append,List.length_singleton]; omega,?_⟩
    intro x y hx hy equal i iq
    have X := (wiresLength gs x).trans (by rw [hx])
    have Y := (wiresLength gs y).trans (by rw [hy])
    change (gs.foldl step x).length = w at X
    change (gs.foldl step y).length = w at Y
    have old := works x y hx hy equal
    simp only [List.foldl_append,List.foldl_cons,List.foldl_nil,step,wireSnoc,X,Y]
    by_cases atNew : i = w
    · have used : w ∈ S := atNew ▸ iq
      rw [ite_eq_left atNew,ite_eq_left atNew]
      congr 1
      apply List.map_congr_left
      intro j jRead
      apply old
      dsimp only [U]
      rw [ite_eq_left used]
      exact Finset.mem_union_right _ (List.mem_toFinset.mpr jRead)
    · rw [ite_eq_right atNew,ite_eq_right atNew]
      apply old
      dsimp only [U]
      split_ifs
      · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨atNew,iq⟩)
      · exact iq


lemma essential_bound (n : ℕ) (C : Circuit) (hfan : FanInTwo C)
    (S : Finset (Fin n))
    (hess : ∀ i ∈ S, ∃ x y : Fin n → Bool,
      (∀ k, k ≠ i → x k = y k) ∧ circuitFun n C x ≠ circuitFun n C y) :
    S.card ≤ C.size + 1 := by
  classical
  obtain ⟨T, hT, hworks⟩ := smallSupport n C.gates (fun g hg => (hfan g hg).2) {C.output}
  have hsub : S.image Fin.val ⊆ T := by
    intro j hj
    obtain ⟨i, his, rfl⟩ := Finset.mem_image.mp hj
    by_contra hn
    obtain ⟨x, y, hxy, hne⟩ := hess i his
    apply hne
    have heq := hworks (List.ofFn x) (List.ofFn y) (by simp) (by simp) ?_ C.output (by simp)
    · exact heq
    · intro k hk
      by_cases hkn : k < n
      · have hki : (⟨k, hkn⟩ : Fin n) ≠ i := by
          intro h
          apply hn
          simpa only [← h] using hk
        simpa only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hkn,
          dite_true, Option.getD_some] using hxy ⟨k, hkn⟩ hki
      · rw [List.getD_eq_default _ _ (by simp; omega),
          List.getD_eq_default _ _ (by simp; omega)]
  have hc := Finset.card_le_card hsub
  have himage : (S.image Fin.val).card = S.card :=
    Finset.card_image_of_injective S Fin.val_injective
  rw [himage] at hc
  simp only [Finset.card_singleton] at hT
  change S.card ≤ C.gates.length + 1
  omega

lemma left_ne_right {p l : ℕ} (a : Fin p) (b : Fin l) :
    Fin.castAdd l a ≠ Fin.natAdd p b := by
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at this
  omega

lemma edge_input_essential (p l : ℕ) (E : Finset (Fin p × Fin l))
    (C : Circuit)
    (hcomp : ∀ x : Fin (p + l) → Bool, circuitFun (p + l) C x =
      decide (∃ a b, (a, b) ∈ E ∧ x (Fin.castAdd l a) = true ∧
        x (Fin.natAdd p b) = true))
    (a : Fin p) (b : Fin l) (hab : (a, b) ∈ E) :
    (∃ x y : Fin (p + l) → Bool,
      (∀ k, k ≠ Fin.castAdd l a → x k = y k) ∧
      circuitFun (p + l) C x ≠ circuitFun (p + l) C y) ∧
    (∃ x y : Fin (p + l) → Bool,
      (∀ k, k ≠ Fin.natAdd p b → x k = y k) ∧
      circuitFun (p + l) C x ≠ circuitFun (p + l) C y) := by
  classical
  let x : Fin (p + l) → Bool := fun k => decide (k = Fin.castAdd l a ∨ k = Fin.natAdd p b)
  have hx : circuitFun (p + l) C x = true := by
    rw [hcomp]
    exact decide_eq_true ⟨a, b, hab, by simp [x], by simp [x]⟩
  constructor
  · let y : Fin (p + l) → Bool := fun k => decide (k = Fin.natAdd p b)
    refine ⟨x, y, ?_, ?_⟩
    · intro k hk
      simp [x, y, hk]
    · have hy : circuitFun (p + l) C y = false := by
        rw [hcomp]
        apply decide_eq_false
        rintro ⟨a', b', he, ha, hb⟩
        exact left_ne_right a' b (of_decide_eq_true ha)
      rw [hx, hy]
      decide
  · let y : Fin (p + l) → Bool := fun k => decide (k = Fin.castAdd l a)
    refine ⟨x, y, ?_, ?_⟩
    · intro k hk
      simp [x, y, hk]
    · have hy : circuitFun (p + l) C y = false := by
        rw [hcomp]
        apply decide_eq_false
        rintro ⟨a', b', he, ha, hb⟩
        exact left_ne_right a b' (of_decide_eq_true hb).symm
      rw [hx, hy]
      decide

def active (p l : ℕ) (E : Finset (Fin p × Fin l)) : Finset (Fin (p + l)) :=
  E.image (fun e => Fin.castAdd l e.1) ∪ E.image (fun e => Fin.natAdd p e.2)

lemma active_bound (p l : ℕ) (E : Finset (Fin p × Fin l))
    (C : Circuit) (hfan : FanInTwo C)
    (hcomp : ∀ x : Fin (p + l) → Bool, circuitFun (p + l) C x =
      decide (∃ a b, (a, b) ∈ E ∧ x (Fin.castAdd l a) = true ∧
        x (Fin.natAdd p b) = true)) :
    (active p l E).card ≤ C.size + 1 := by
  apply essential_bound (p + l) C hfan
  intro i hi
  rcases Finset.mem_union.mp hi with hi | hi
  · obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hi
    exact (edge_input_essential p l E C hcomp a b hab).1
  · obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hi
    exact (edge_input_essential p l E C hcomp a b hab).2

end PEqualNP.Outside.L_meta_4970.EssentialSupport
