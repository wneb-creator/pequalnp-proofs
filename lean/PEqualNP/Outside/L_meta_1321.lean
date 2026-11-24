import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_1321
open PEqualNP PEqualNP.MetaComplexity
namespace LineDegTest
open PEqualNP.CircuitLowerBounds
def W (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x
def Dg (gs : List Gate) (n : ℕ) (marked : Finset ℕ) : List ℕ :=
  gs.foldl (fun d g => d ++ [g.lineDegree d])
    ((List.range n).map fun i => if i ∈ marked then 1 else 0)
theorem W_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    W (gs ++ [g]) x = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
  simp [W, List.foldl_append]
theorem Dg_snoc (gs : List Gate) (g : Gate) (n : ℕ) (marked : Finset ℕ) :
    Dg (gs ++ [g]) n marked = Dg gs n marked ++ [g.lineDegree (Dg gs n marked)] := by
  simp [Dg, List.foldl_append]
theorem W_length (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih => rw [W_snoc]; simp [ih]; omega
theorem Dg_length (gs : List Gate) (n : ℕ) (marked : Finset ℕ) :
    (Dg gs n marked).length = n + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Dg]
  | append_singleton gs g ih => rw [Dg_snoc]; simp [ih]; omega
theorem getD_snoc {α : Type} (l : List α) (a d : α) (t : ℕ) :
    (l ++ [a]).getD t d =
      if t < l.length then l.getD t d else if t = l.length then a else d := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h1 : t < l.length
  · rw [if_pos h1, List.getElem?_append_left h1]
  · rw [if_neg h1, List.getElem?_append_right (by omega)]
    by_cases h2 : t = l.length
    · subst h2; simp
    · rw [if_neg h2]
      have : t - l.length ≠ 0 := by omega
      simp [List.getElem?_cons, this]
theorem getD_false_lt {l : List Bool} {t : ℕ} (h : l.getD t false = true) : t < l.length := by
  by_contra h'
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at h
  simp at h
def Le (x y : List Bool) : Prop := ∀ i, x.getD i false = true → y.getD i false = true
theorem eval_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (w w' : List Bool)
    (h : ∀ i ∈ g.inputs, w.getD i false = true → w'.getD i false = true)
    (he : g.op.eval (g.inputs.map fun i => w.getD i false) = true) :
    g.op.eval (g.inputs.map fun i => w'.getD i false) = true := by
  rcases hg with hg | hg <;> rw [hg] at he ⊢ <;> simp [GateOp.eval] at he ⊢
  · intro i hi; exact h i hi (he i hi)
  · obtain ⟨i, hi, hv⟩ := he; exact ⟨i, hi, h i hi hv⟩
theorem W_mono (gs : List Gate) (hm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : List Bool) (hl : x.length = y.length) (hxy : Le x y) : Le (W gs x) (W gs y) := by
  induction gs using List.reverseRecOn with
  | nil => simpa [W] using hxy
  | append_singleton gs g ih =>
    have ih := ih (fun g' hg' => hm g' (by simp [hg']))
    intro t ht
    have hlen : (W gs x).length = (W gs y).length := by simp [W_length, hl]
    rw [W_snoc, getD_snoc] at ht ⊢
    rw [← hlen]
    by_cases h1 : t < (W gs x).length
    · rw [if_pos h1] at ht ⊢; exact ih t ht
    · rw [if_neg h1] at ht ⊢
      by_cases h2 : t = (W gs x).length
      · rw [if_pos h2] at ht ⊢
        exact eval_mono g (hm g (by simp)) _ _ (fun i _ => ih i) ht
      · rw [if_neg h2] at ht; simp at ht
def rst (marked T : Finset ℕ) (x : List Bool) : List Bool :=
  x.mapIdx fun i b => b && (decide (i ∉ marked) || decide (i ∈ T))
theorem rst_length (marked T : Finset ℕ) (x : List Bool) : (rst marked T x).length = x.length := by
  simp [rst]
theorem rst_getD (marked T : Finset ℕ) (x : List Bool) (i : ℕ) :
    (rst marked T x).getD i false =
      (x.getD i false && (decide (i ∉ marked) || decide (i ∈ T))) := by
  simp only [rst, List.getD_eq_getElem?_getD, List.getElem?_mapIdx]
  cases x[i]? <;> simp
theorem rst_mono (marked : Finset ℕ) {T U : Finset ℕ} (hTU : T ⊆ U) (x : List Bool) :
    Le (rst marked T x) (rst marked U x) := by
  intro i h
  rw [rst_getD] at h ⊢
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h ⊢
  exact ⟨h.1, h.2.imp id (fun hi => hTU hi)⟩
def lines (marked : Finset ℕ) (x : List Bool) : Finset ℕ :=
  (Finset.range x.length).filter fun i => i ∈ marked ∧ x.getD i false = true
theorem le_foldr_max {l : List ℕ} {a : ℕ} (h : a ∈ l) : a ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 h with h | h
    · subst h; exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)
theorem inv (marked : Finset ℕ) (gs : List Gate)
    (hm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) (n : ℕ) (x : List Bool)
    (hx : x.length = n) : ∀ t, (W gs x).getD t false = true →
      ∃ T ⊆ lines marked x, T.card ≤ (Dg gs n marked).getD t 0 ∧
        (W gs (rst marked T x)).getD t false = true := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro t ht
    simp only [W, List.foldl_nil] at ht ⊢
    have htl := getD_false_lt ht
    have hdeg : (Dg [] n marked).getD t 0 = if t ∈ marked then 1 else 0 := by
      simp [Dg, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range, ← hx, htl]
    rw [hdeg]
    by_cases hmk : t ∈ marked
    · refine ⟨{t}, ?_, by simp [hmk], ?_⟩
      · intro i hi; rw [Finset.mem_singleton] at hi; subst hi
        simp only [lines, Finset.mem_filter, Finset.mem_range]; exact ⟨htl, hmk, ht⟩
      · rw [rst_getD, ht]; simp
    · refine ⟨∅, Finset.empty_subset _, by simp, ?_⟩
      rw [rst_getD, ht]; simp [hmk]
  | append_singleton gs g ih =>
    have hm' : ∀ g' ∈ gs, g'.op = GateOp.and ∨ g'.op = GateOp.or :=
      fun g' hg' => hm g' (by simp [hg'])
    have ih := ih hm'
    have hlenW : ∀ T, (W gs (rst marked T x)).length = (W gs x).length := by
      intro T; simp [W_length, rst_length]
    have hlenD : (Dg gs n marked).length = (W gs x).length := by
      simp [W_length, Dg_length, hx]
    intro t ht
    rw [W_snoc, getD_snoc] at ht
    by_cases h1 : t < (W gs x).length
    · rw [if_pos h1] at ht
      obtain ⟨T, hTL, hTc, hTv⟩ := ih t ht
      refine ⟨T, hTL, ?_, ?_⟩
      · rw [Dg_snoc, getD_snoc, if_pos (by rw [hlenD]; exact h1)]; exact hTc
      · rw [W_snoc, getD_snoc, if_pos (by rw [hlenW]; exact h1)]; exact hTv
    rw [if_neg h1] at ht
    by_cases h2 : t = (W gs x).length
    swap
    · rw [if_neg h2] at ht; simp at ht
    rw [if_pos h2] at ht
    have hdg : (Dg (gs ++ [g]) n marked).getD t 0 = g.lineDegree (Dg gs n marked) := by
      rw [Dg_snoc, getD_snoc, if_neg (by omega), if_pos (by omega)]
    have hwg : ∀ T, (W (gs ++ [g]) (rst marked T x)).getD t false =
        g.op.eval (g.inputs.map fun i => (W gs (rst marked T x)).getD i false) := by
      intro T
      rw [W_snoc, getD_snoc, hlenW, if_neg h1, if_pos h2]
    simp only [hdg, hwg]
    have hmonoT : ∀ T U, T ⊆ U → ∀ i, (W gs (rst marked T x)).getD i false = true →
        (W gs (rst marked U x)).getD i false = true := by
      intro T U hTU i hi
      exact W_mono gs hm' _ _ (by simp [rst_length]) (rst_mono marked hTU x) i hi
    rcases hm g (by simp) with hg | hg
    ·
      rw [hg] at ht ⊢
      simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id] at ht
      have key : ∀ l : List ℕ, (∀ i ∈ l, (W gs x).getD i false = true) →
          ∃ U ⊆ lines marked x, U.card ≤ (l.map fun i => (Dg gs n marked).getD i 0).sum ∧
            ∀ i ∈ l, (W gs (rst marked U x)).getD i false = true := by
        intro l
        induction l with
        | nil => intro _; exact ⟨∅, Finset.empty_subset _, by simp, by simp⟩
        | cons a l ihl =>
          intro hl
          obtain ⟨T, hTL, hTc, hTv⟩ := ih a (hl a (by simp))
          obtain ⟨U, hUL, hUc, hUv⟩ := ihl (fun i hi => hl i (by simp [hi]))
          refine ⟨T ∪ U, Finset.union_subset hTL hUL, ?_, ?_⟩
          · simp only [List.map_cons, List.sum_cons]
            exact le_trans (Finset.card_union_le _ _) (by omega)
          · intro i hi
            rcases List.mem_cons.1 hi with hi | hi
            · subst hi; exact hmonoT T _ Finset.subset_union_left _ hTv
            · exact hmonoT U _ Finset.subset_union_right _ (hUv i hi)
      obtain ⟨U, hUL, hUc, hUv⟩ := key g.inputs ht
      refine ⟨U, hUL, ?_, ?_⟩
      · simp only [Gate.lineDegree, hg, if_true]; exact hUc
      · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id]
        exact hUv
    ·
      rw [hg] at ht ⊢
      simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id] at ht
      obtain ⟨i, hi, hv⟩ := ht
      obtain ⟨T, hTL, hTc, hTv⟩ := ih i hv
      refine ⟨T, hTL, ?_, ?_⟩
      · simp only [Gate.lineDegree, hg, reduceCtorEq, if_false]
        exact le_trans hTc (le_foldr_max (List.mem_map.2 ⟨i, hi, rfl⟩))
      · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
        exact ⟨i, hi, hTv⟩
theorem ofFn_getD {n : ℕ} (f : Fin n → Bool) (k : ℕ) :
    (List.ofFn f).getD k false = if h : k < n then f ⟨k, h⟩ else false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  by_cases h : k < n <;> simp [h]
theorem main : ∀ (n D : ℕ) (marked : Finset ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : PEqualNP.CircuitLowerBounds.Circuit),
    (∀ i j : Fin n, G.Adj i j → (i.val ∈ marked ↔ j.val ∉ marked)) →
    PEqualNP.CircuitLowerBounds.IsMonotoneCircuit C →
    PEqualNP.CircuitLowerBounds.HasLineDegree n marked C D →
    (∀ i j : Fin n, G.Adj i j → C.eval (List.ofFn fun k => decide (k = i ∨ k = j)) = true) →
    (∀ S : Finset (Fin n), (∀ j ∈ S, j.val ∈ marked) → S.card ≤ D →
      C.eval (List.ofFn fun k => decide (k ∈ S ∨ (k.val ∉ marked ∧ ∀ j ∈ S, ¬ G.Adj k j)))
        = false) →
    ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
      ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true := by
  intro n D marked G _ C _ hmono hdeg hedge htest x
  have hW : ∀ y, C.eval y = (W C.gates y).getD C.output false := fun y => rfl
  have hD : C.lineDeg n marked = (Dg C.gates n marked).getD C.output 0 := rfl
  have hmono' : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := hmono
  constructor
  · intro hx
    by_contra hne
    push_neg at hne
    rw [hW] at hx
    obtain ⟨T, hTL, hTc, hTv⟩ := inv marked C.gates hmono' n (List.ofFn x) (by simp) C.output hx
    have hTD : T.card ≤ D := le_trans hTc (by rw [← hD]; exact hdeg)
    have hTmem : ∀ i ∈ T, i < n ∧ i ∈ marked ∧ (List.ofFn x).getD i false = true := by
      intro i hi
      have := hTL hi
      simp only [lines, Finset.mem_filter, Finset.mem_range, List.length_ofFn] at this
      exact this
    let S : Finset (Fin n) := Finset.univ.filter fun k => k.val ∈ T
    have hS1 : ∀ j ∈ S, j.val ∈ marked := by
      intro j hj
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      exact (hTmem _ hj).2.1
    have hScard : S.card ≤ D := by
      refine le_trans ?_ hTD
      refine Finset.card_le_card_of_injOn (fun k => k.val) ?_ ?_
      · intro k hk
        simp only [S, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hk
        exact hk
      · intro a _ b _ hab; exact Fin.ext hab
    have hfalse := htest S hS1 hScard
    rw [hW] at hfalse
    have hle : Le (rst marked T (List.ofFn x))
        (List.ofFn fun k => decide (k ∈ S ∨ (k.val ∉ marked ∧ ∀ j ∈ S, ¬ G.Adj k j))) := by
      intro k hk
      rw [rst_getD] at hk
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hk
      obtain ⟨hxk, hk2⟩ := hk
      rw [ofFn_getD] at hxk ⊢
      by_cases hkn : k < n
      swap
      · rw [dif_neg hkn] at hxk; exact absurd hxk (by simp)
      rw [dif_pos hkn] at hxk ⊢
      simp only [decide_eq_true_eq]
      by_cases hkT : k ∈ T
      · left; simp [S, hkT]
      · right
        have hkm : k ∉ marked := by
          rcases hk2 with h | h
          · exact h
          · exact absurd h hkT
        refine ⟨hkm, ?_⟩
        intro j hj hadj
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hj
        have hxj := (hTmem _ hj).2.2
        rw [ofFn_getD, dif_pos j.isLt] at hxj
        exact hne ⟨k, hkn⟩ j hadj hxk hxj
    have := W_mono C.gates hmono' _ _ (by simp [rst_length]) hle C.output hTv
    rw [hfalse] at this
    exact absurd this (by simp)
  · rintro ⟨i, j, hij, hi, hj⟩
    have h := hedge i j hij
    rw [hW] at h ⊢
    refine W_mono C.gates hmono' _ _ (by simp) ?_ C.output h
    intro k hk
    rw [ofFn_getD] at hk ⊢
    by_cases hkn : k < n
    · rw [dif_pos hkn] at hk ⊢
      simp only [decide_eq_true_eq] at hk
      rcases hk with hk | hk
      · rw [hk]; exact hi
      · rw [hk]; exact hj
    · rw [dif_neg hkn] at hk; exact absurd hk (by simp)
end LineDegTest
namespace HonestFactor
open Classical
theorem castAdd_ne_natAdd' {N : ℕ} (i j : Fin N) : Fin.castAdd N i ≠ Fin.natAdd N j := by
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at this
  omega
theorem pi_le_of_imp {α : Type*} {x y : α → Bool} (h : ∀ k, x k = true → y k = true) :
    x ≤ y := by
  intro k
  cases hx : x k
  · exact Bool.false_le _
  · rw [h k hx]
theorem eq_true_of_true_le' {b : Bool} (h : true ≤ b) : b = true := by
  revert h; cases b <;> decide
theorem castAdd_inj' {N : ℕ} (i j : Fin N) : Fin.castAdd N i = Fin.castAdd N j ↔ i = j := by
  constructor
  · intro h
    exact Fin.ext (by simpa using congrArg Fin.val h)
  · rintro rfl; rfl
theorem natAdd_inj' {N : ℕ} (i j : Fin N) : Fin.natAdd N i = Fin.natAdd N j ↔ i = j := by
  constructor
  · intro h
    have := congrArg Fin.val h
    simp only [Fin.val_natAdd] at this
    exact Fin.ext (by omega)
  · rintro rfl; rfl
theorem main (N : ℕ) (I : Fin N → Fin N → Prop) (Λ : (Fin (N + N) → Bool) → Bool)
    (r : List ((Fin (N + N) → Bool) → Bool)) (p w : Fin N) (_hΛ : Monotone Λ)
    (hpts : ∀ z z' : Fin (N + N) → Bool,
      (∀ i : Fin N, z (Fin.castAdd N i) = z' (Fin.castAdd N i)) → Λ z = Λ z')
    (hr : ∀ f ∈ r, Monotone f)
    (honly : ∀ z : Fin (N + N) → Bool, (Λ z && r.all (fun f => f z)) = true →
      ∃ a b : Fin N, I a b ∧ z (Fin.castAdd N a) = true ∧ z (Fin.natAdd N b) = true)
    (hedge : (Λ (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N w)) &&
      r.all (fun f => f (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N w)))) = true) :
    r ≠ [] ∧ ∃ f ∈ r, f (fun k => decide (k = Fin.castAdd N p)) = false ∧
      ∀ u : Fin N, f (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N u)) = true →
        I p u := by
  rw [Bool.and_eq_true] at hedge
  have hΛe := hedge.1
  have hΛz : ∀ z : Fin (N + N) → Bool,
      (∀ i : Fin N, z (Fin.castAdd N i) = decide (i = p)) → Λ z = true := by
    intro z hz
    rw [← hΛe]
    apply hpts
    intro i
    rw [hz i]
    apply decide_eq_decide.mpr
    constructor
    · rintro rfl; exact Or.inl rfl
    · rintro (h | h)
      · exact (castAdd_inj' _ _).mp h
      · exact absurd h (castAdd_ne_natAdd' _ _)
  constructor
  · rintro rfl
    obtain ⟨a, b, -, -, hb⟩ := honly (fun k => decide (k = Fin.castAdd N p)) (by
      simp only [List.all_nil, Bool.and_true]
      apply hΛz
      intro i
      simp)
    exact castAdd_ne_natAdd' p b (of_decide_eq_true hb).symm
  · by_contra hno
    push Not at hno
    let z : Fin (N + N) → Bool :=
      fun k => decide (k = Fin.castAdd N p ∨ ∃ u, k = Fin.natAdd N u ∧ ¬ I p u)
    have hzf : ∀ f ∈ r, f z = true := by
      intro f hf
      by_cases h0 : f (fun k => decide (k = Fin.castAdd N p)) = false
      · obtain ⟨u, hu, hnI⟩ := hno f hf h0
        have hle : (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N u)) ≤ z := by
          apply pi_le_of_imp
          intro k hk
          simp only [z, decide_eq_true_eq] at hk ⊢
          rcases hk with hk | hk
          · exact Or.inl hk
          · exact Or.inr ⟨u, hk, hnI⟩
        have := hr f hf hle
        rw [hu] at this
        exact eq_true_of_true_le' this
      · have h1 : f (fun k => decide (k = Fin.castAdd N p)) = true := by
          simpa using h0
        have hle : (fun k => decide (k = Fin.castAdd N p)) ≤ z := by
          apply pi_le_of_imp
          intro k hk
          simp only [z, decide_eq_true_eq] at hk ⊢
          exact Or.inl hk
        have := hr f hf hle
        rw [h1] at this
        exact eq_true_of_true_le' this
    have hzΛ : Λ z = true := by
      apply hΛz
      intro i
      simp only [z, castAdd_inj', decide_eq_decide]
      constructor
      · rintro (h | ⟨u, hu, -⟩)
        · exact h
        · exact absurd hu (castAdd_ne_natAdd' _ _)
      · intro h; exact Or.inl h
    obtain ⟨a, b, hab, ha, hb⟩ := honly z (by
      rw [Bool.and_eq_true, List.all_eq_true]
      exact ⟨hzΛ, fun f hf => hzf f hf⟩)
    simp only [z, decide_eq_true_eq] at ha hb
    rcases hb with hb | ⟨u, hu, hnI⟩
    · exact absurd hb.symm (castAdd_ne_natAdd' _ _)
    · rw [natAdd_inj'] at hu
      subst hu
      rcases ha with ha | ⟨v, hv, -⟩
      · rw [castAdd_inj'] at ha
        subst ha
        exact hnI hab
      · exact absurd hv (castAdd_ne_natAdd' _ _)
end HonestFactor
namespace Deg2
open PEqualNP.CircuitLowerBounds
inductive G where
  | and (a b : ℕ)
  | or (a b : ℕ)
  | cst (v : Bool)
  deriving DecidableEq, Repr
def G.kids : G → List ℕ
  | .and a b => [a, b]
  | .or a b => [a, b]
  | .cst _ => []
structure Dag (N : ℕ) where
  gates : List G
  out : ℕ
namespace Dag
variable {N : ℕ}
def size (D : Dag N) : ℕ := D.gates.length
def gateAt (D : Dag N) (i : ℕ) : Option G :=
  if N + N ≤ i then D.gates[i - (N + N)]? else none
def val (D : Dag N) (x : Fin (N + N) → Bool) (i : ℕ) : Bool :=
  if h : i < N + N then x ⟨i, h⟩ else
  match D.gates[i - (N + N)]? with
  | some (.and a b) =>
      (if _ : a < i then D.val x a else false) && (if _ : b < i then D.val x b else false)
  | some (.or a b) =>
      (if _ : a < i then D.val x a else false) || (if _ : b < i then D.val x b else false)
  | some (.cst v) => v
  | none => false
termination_by i
def deg (D : Dag N) (i : ℕ) : ℕ :=
  if i < N + N then (if N ≤ i then 1 else 0) else
  match D.gates[i - (N + N)]? with
  | some (.and a b) =>
      (if _ : a < i then D.deg a else 0) + (if _ : b < i then D.deg b else 0)
  | some (.or a b) =>
      max (if _ : a < i then D.deg a else 0) (if _ : b < i then D.deg b else 0)
  | some (.cst _) => 0
  | none => 0
termination_by i
def fn (D : Dag N) (x : Fin (N + N) → Bool) : Bool := D.val x D.out
def Kid (D : Dag N) (i c : ℕ) : Prop := ∃ g, D.gateAt i = some g ∧ c ∈ g.kids ∧ c < i
def WF (D : Dag N) : Prop := ∀ i g, D.gateAt i = some g → ∀ c ∈ g.kids, c < i
def Reach (D : Dag N) : ℕ → ℕ → Prop := Relation.ReflTransGen D.Kid
def IsAnd (D : Dag N) (i : ℕ) : Prop := ∃ a b, D.gateAt i = some (.and a b)
def IsOr (D : Dag N) (i : ℕ) : Prop := ∃ a b, D.gateAt i = some (.or a b)
open Classical in
noncomputable def coneOf (D : Dag N) (S : Finset ℕ) : Finset ℕ :=
  (Finset.range (N + N + D.size)).filter (fun i => N + N ≤ i ∧ ∃ r ∈ S, D.Reach r i)
noncomputable def cone (D : Dag N) : Finset ℕ := D.coneOf {D.out}
noncomputable def X (D : Dag N) : Finset ℕ := D.cone.filter (fun i => D.deg i = 0)
noncomputable def M (D : Dag N) : Finset ℕ := D.cone.filter (fun i => D.deg i = 1)
noncomputable def T (D : Dag N) : Finset ℕ := D.cone.filter (fun i => D.deg i = 2)
open Classical in
noncomputable def AndM (D : Dag N) : Finset ℕ := D.M.filter D.IsAnd
open Classical in
noncomputable def OrM (D : Dag N) : Finset ℕ := D.M.filter D.IsOr
open Classical in
noncomputable def Tor (D : Dag N) : Finset ℕ := D.T.filter D.IsOr
open Classical in
noncomputable def Tandf (D : Dag N) : Finset ℕ :=
  D.T.filter (fun i => ∃ a b, D.gateAt i = some (.and a b) ∧ (D.deg a = 0 ∨ D.deg b = 0))
open Classical in
noncomputable def Tmix (D : Dag N) : Finset ℕ :=
  D.T.filter (fun i => ∃ a b, D.gateAt i = some (.and a b) ∧ D.deg a = 1 ∧ D.deg b = 1)
end Dag
def trGate (i : ℕ) (g : Gate) : G :=
  match g.op, g.inputs with
  | .and, [] => .cst true
  | .or, [] => .cst false
  | .and, [a] => if a < i then .or a a else .cst false
  | .or, [a] => if a < i then .or a a else .cst false
  | .and, [a, b] => if a < i ∧ b < i then .and a b else .cst false
  | .or, [a, b] =>
      if a < i ∧ b < i then .or a b else if a < i then .or a a
      else if b < i then .or b b else .cst false
  | _, _ => .cst false
def ofCircuit (N : ℕ) (C : Circuit) : Dag N :=
  { gates := C.gates.mapIdx (fun j g => trGate (N + N + j) g), out := C.output }
def G.toGate : G → Gate
  | .and a b => ⟨.and, [a, b]⟩
  | .or a b => ⟨.or, [a, b]⟩
  | .cst v => if v then ⟨.and, []⟩ else ⟨.or, []⟩
def Dag.toCircuit {N : ℕ} (D : Dag N) : Circuit := ⟨D.gates.map G.toGate, D.out⟩
def NoRect {N : ℕ} (I : Fin N → Fin N → Prop) : Prop :=
  ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')
def lineMarks (N : ℕ) : Finset ℕ := Finset.Ico N (N + N)
def edgeFun (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] :
    (Fin (N + N) → Bool) → Bool :=
  fun z => decide (∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
def edges (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] : Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)
def Computes {N : ℕ} (I : Fin N → Fin N → Prop) (f : (Fin (N + N) → Bool) → Bool) : Prop :=
  ∀ z, f z = true ↔ ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true
def inp {N : ℕ} (P S : Finset (Fin N)) : Fin (N + N) → Bool :=
  Fin.addCases (motive := fun _ => Bool) (fun p => decide (p ∈ P)) (fun l => decide (l ∈ S))
def pt {N : ℕ} (p : Fin N) : Fin (N + N) → Bool := inp {p} ∅
def ep {N : ℕ} (p w : Fin N) : Fin (N + N) → Bool := inp {p} {w}
open Classical in
noncomputable def testInput {N : ℕ} (I : Fin N → Fin N → Prop) (S : Finset (Fin N)) :
    Fin (N + N) → Bool :=
  inp (Finset.univ.filter (fun p => ∀ l ∈ S, ¬ I p l)) S
open Classical in
noncomputable def ptsOn {N : ℕ} (I : Fin N → Fin N → Prop) (l : Fin N) : Finset (Fin N) :=
  Finset.univ.filter (fun p => I p l)
open Classical in
noncomputable def pencil {N : ℕ} (I : Fin N → Fin N → Prop) (p : Fin N) : Finset (Fin N) :=
  Finset.univ.filter (fun l => I p l)
def IsHonest {N : ℕ} (I : Fin N → Fin N → Prop) (r : (Fin (N + N) → Bool) → Bool)
    (p : Fin N) : Prop :=
  r (pt p) = false ∧ ∀ u, r (ep p u) = true → I p u
namespace Dag
variable {N : ℕ}
def alive (D : Dag N) (f : ℕ) : Finset (Fin N) :=
  Finset.univ.filter (fun p => D.val (pt p) f = true)
open Classical in
noncomputable def deadSets (I : Fin N → Fin N → Prop) (D : Dag N) (d : ℕ) (f : ℕ) :
    Finset (Finset (Fin N)) :=
  (Finset.univ : Finset (Finset (Fin N))).filter
    (fun S => S.card ≤ d ∧ D.val (testInput I S) f = false)
inductive VReach (D : Dag N) : ℕ → Fin N → Prop
  | leaf (u : Fin N) : VReach D (N + u.val) u
  | step {v c : ℕ} {u : Fin N} : D.IsOr v → D.deg v = 1 → D.Kid v c → VReach D c u →
      VReach D v u
open Classical in
noncomputable def Vstar (D : Dag N) (v : ℕ) : Finset (Fin N) :=
  Finset.univ.filter (fun u => D.VReach v u)
def PinnedTo (I : Fin N → Fin N → Prop) (D : Dag N) (v : ℕ) (p : Fin N) : Prop :=
  D.IsOr v ∧ D.deg v = 1 ∧ 2 ≤ (D.Vstar v).card ∧ D.Vstar v ⊆ pencil I p
open Classical in
noncomputable def pinned (I : Fin N → Fin N → Prop) (D : Dag N) : Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun e => ∃ v ∈ D.OrM, PinnedTo I D v e.1 ∧ e.2 ∈ D.Vstar v)
def IsMarker (D : Dag N) (r : ℕ) (w : Fin N) : Prop := D.deg r = 1 ∧ D.Vstar r = {w}
def LabAnd (D : Dag N) (e f v : ℕ) : Prop :=
  (D.gateAt e = some (.and f v) ∨ D.gateAt e = some (.and v f)) ∧ D.deg f = 0 ∧ D.deg v = 1
open Classical in
noncomputable def served (I : Fin N → Fin N → Prop) (D : Dag N) : Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun e => ∃ g ∈ D.AndM, ∃ f v, D.LabAnd g f v ∧ D.Vstar v = {e.2} ∧
    e.1 ∈ D.alive f ∧ I e.1 e.2 ∧ (D.alive f ∩ ptsOn I e.2).card ≤ 2)
open Classical in
noncomputable def fSet (I : Fin N → Fin N → Prop) (D : Dag N) (Gs : Finset ℕ) (d : ℕ) :
    Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun e => I e.1 e.2 ∧ ∃ f ∈ Gs, D.deg f = 0 ∧ D.deadSets I d f ≠ ∅ ∧
    e.1 ∈ D.alive f ∧ d + 1 ≤ (D.alive f ∩ ptsOn I e.2).card)
def Cleaned (I : Fin N → Fin N → Prop) (D : Dag N) (Gs : Finset ℕ) : Prop :=
  ∀ e ∈ Gs, ∀ f v, D.LabAnd e f v → D.deadSets I 2 f ≠ ∅
def IsPath (D : Dag N) (π : List ℕ) (a b : ℕ) : Prop :=
  π.head? = some a ∧ π.getLast? = some b ∧
    ∀ k, k + 1 < π.length → D.Kid (π.getD k 0) (π.getD (k + 1) 0)
def LabelsAlive (D : Dag N) (π : List ℕ) (x : Fin (N + N) → Bool) : Prop :=
  ∀ k f, k + 1 < π.length → D.LabAnd (π.getD k 0) f (π.getD (k + 1) 0) → D.val x f = true
inductive Top (D : Dag N) (ok : ℕ → Prop) : ℕ → Prop
  | root : Top D ok D.out
  | orStep {h c : ℕ} : Top D ok h → h ∈ D.Tor → D.Kid h c → 1 ≤ D.deg c → Top D ok c
  | andStep {h f c : ℕ} : Top D ok h → h ∈ D.Tandf →
      (D.gateAt h = some (.and f c) ∨ D.gateAt h = some (.and c f)) →
      D.deg f = 0 → D.deg c = 2 → f < h → c < h → ok f → Top D ok c
def IsItem (D : Dag N) (b : ℕ) : Prop :=
  D.Top (fun _ => True) b ∧ (D.deg b ≤ 1 ∨ b ∈ D.Tmix)
open Classical in
noncomputable def ctx (D : Dag N) (b : ℕ) : (Fin (N + N) → Bool) → Bool :=
  fun x => decide (D.Top (fun f => D.val x f = true) b)
def IsFactor (D : Dag N) (b r : ℕ) : Prop :=
  (D.deg b ≤ 1 ∧ r = b) ∨ (b ∈ D.Tmix ∧ D.Kid b r)
open Classical in
noncomputable def markerEdges (I : Fin N → Fin N → Prop) (D : Dag N) :
    Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun e => I e.1 e.2 ∧ ∃ b, D.IsItem b ∧ D.ctx b (pt e.1) = true ∧
    (∀ r, D.IsFactor b r → D.val (ep e.1 e.2) r = true) ∧ ∃ r, D.IsFactor b r ∧ D.IsMarker r e.2)
noncomputable def rootCone (D : Dag N) (W : Finset (Fin N)) (R : Fin N → ℕ) : Finset ℕ :=
  D.coneOf (W.image R)
def SoundPartialForm (I : Fin N → Fin N → Prop) (D : Dag N) (W : Finset (Fin N))
    (R : Fin N → ℕ) : Prop :=
  D.WF ∧ (∀ w ∈ W, D.deg (R w) ≤ 1) ∧
    ∀ z, (∃ w ∈ W, z (Fin.natAdd N w) = true ∧ D.val z (R w) = true) →
      ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true
open Classical in
noncomputable def countedEdges (D : Dag N) (W : Finset (Fin N)) (R : Fin N → ℕ) :
    Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun e => e.2 ∈ W ∧ D.val (ep e.1 e.2) (R e.2) = true)
open Classical in
noncomputable def e0Set (D : Dag N) (W : Finset (Fin N)) (R : Fin N → ℕ) :
    Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun e => e.2 ∈ W ∧ D.val (pt e.1) (R e.2) = true)
def LeSum (I : Fin N → Fin N → Prop) (D : Dag N) (f : ℕ) (w : Fin N) : Prop :=
  ∀ z, D.val z f = true → ∃ p, I p w ∧ z (Fin.castAdd N p) = true
open Classical in
noncomputable def e1Set (I : Fin N → Fin N → Prop) (D : Dag N) (W : Finset (Fin N))
    (R : Fin N → ℕ) : Finset (Fin N × Fin N) :=
  (D.countedEdges W R).filter (fun e => ∃ f ∈ D.rootCone W R, D.deg f = 0 ∧
    D.LeSum I f e.2 ∧ e.1 ∈ D.alive f ∧ 2 ≤ (D.alive f).card)
def EdgePath (D : Dag N) (R : Fin N → ℕ) (p w : Fin N) (π : List ℕ) : Prop :=
  D.IsPath π (R w) (N + w.val) ∧ ∀ v ∈ π, D.val (ep p w) v = true ∧ D.val (pt p) v = false
def PGateAt (D : Dag N) (p : Fin N) (π : List ℕ) (k : ℕ) : Prop :=
  k + 1 < π.length ∧ ∃ f, D.LabAnd (π.getD k 0) f (π.getD (k + 1) 0) ∧ D.alive f = {p}
def IsBeta (I : Fin N → Fin N → Prop) (D : Dag N) (W : Finset (Fin N)) (R : Fin N → ℕ)
    (p : Fin N) (g' : ℕ) : Prop :=
  ∃ u ∈ W, ¬ I p u ∧ ∃ π, D.IsPath π (R u) g' ∧ D.LabelsAlive π (pt p)
open Classical in
noncomputable def alphaEdges (I : Fin N → Fin N → Prop) (D : Dag N) (W : Finset (Fin N))
    (R : Fin N → ℕ) : Finset (Fin N × Fin N) :=
  (D.countedEdges W R).filter (fun e => ∃ π, D.EdgePath R e.1 e.2 π ∧ ∃ k,
    D.PGateAt e.1 π k ∧ (∀ k' < k, ¬ D.PGateAt e.1 π k') ∧
    ¬ D.IsBeta I W R e.1 (π.getD (k + 1) 0))
open Classical in
noncomputable def betaEdges (I : Fin N → Fin N → Prop) (D : Dag N) (W : Finset (Fin N))
    (R : Fin N → ℕ) : Finset (Fin N × Fin N) :=
  (D.countedEdges W R).filter (fun e => ∃ π, D.EdgePath R e.1 e.2 π ∧ ∃ k,
    D.PGateAt e.1 π k ∧ (∀ k', k < k' → ¬ D.PGateAt e.1 π k') ∧
    D.IsBeta I W R e.1 (π.getD (k + 1) 0))
end Dag
end Deg2
namespace Deg2.Api
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Deg2
variable {N : ℕ}
theorem gateAt_some {D : Dag N} {i : ℕ} {g : G} (h : D.gateAt i = some g) :
    N + N ≤ i ∧ D.gates[i - (N + N)]? = some g := by
  unfold Dag.gateAt at h
  split_ifs at h with hi
  exact ⟨hi, h⟩
theorem deg_kid {D : Dag N} {i c : ℕ} (h : D.Kid i c) : D.deg c ≤ D.deg i := by
  obtain ⟨g, hg, hc, hci⟩ := h
  obtain ⟨hi, hg⟩ := gateAt_some hg
  conv_rhs => rw [Dag.deg]
  rw [if_neg (by omega), hg]
  cases g with
  | and a b =>
    simp only [G.kids, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · dsimp only; rw [dif_pos hci]; omega
    · dsimp only; rw [dif_pos hci]; omega
  | or a b =>
    simp only [G.kids, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · dsimp only; rw [dif_pos hci]; exact le_max_left _ _
    · dsimp only; rw [dif_pos hci]; exact le_max_right _ _
  | cst v => simp [G.kids] at hc
theorem api_reach_deg (D : Dag N) {i j : ℕ} (h : D.Reach i j) : D.deg j ≤ D.deg i := by
  induction h with
  | refl => exact le_rfl
  | tail _ hk ih => exact le_trans (deg_kid hk) ih
theorem api_coneOf_down (D : Dag N) (S : Finset ℕ) :
    ∀ i ∈ D.coneOf S, ∀ c, D.Kid i c → N + N ≤ c → c ∈ D.coneOf S := by
  intro i hi c hk hc
  classical
  unfold Dag.coneOf at hi ⊢
  simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
  obtain ⟨hlt, -, r, hr, hreach⟩ := hi
  obtain ⟨_, _, _, hci⟩ := id hk
  refine ⟨by omega, hc, r, hr, ?_⟩
  exact Relation.ReflTransGen.tail hreach hk
theorem coneOf_sub (D : Dag N) (S : Finset ℕ) :
    D.coneOf S ⊆ Finset.Ico (N + N) (N + N + D.size) := by
  intro i hi
  classical
  unfold Dag.coneOf at hi
  simp only [Finset.mem_filter, Finset.mem_range] at hi
  simp only [Finset.mem_Ico]
  omega
theorem coneOf_card (D : Dag N) (S : Finset ℕ) : (D.coneOf S).card ≤ D.size := by
  have := Finset.card_le_card (coneOf_sub D S)
  simpa using this
theorem card_filter_disj {s : Finset ℕ} {p q : ℕ → Prop} [DecidablePred p] [DecidablePred q]
    (h : ∀ i, p i → ¬ q i) :
    (s.filter p).card + (s.filter q).card ≤ (s.filter (fun i => p i ∨ q i)).card := by
  have hu := Finset.card_union_add_card_inter (s.filter p) (s.filter q)
  have hi : s.filter p ∩ s.filter q = ∅ := by
    ext i
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.notMem_empty, iff_false]
    rintro ⟨⟨_, hp⟩, ⟨_, hq⟩⟩
    exact h i hp hq
  have hsub : s.filter p ∪ s.filter q ⊆ s.filter (fun i => p i ∨ q i) := by
    intro i
    simp only [Finset.mem_union, Finset.mem_filter]
    rintro (⟨hs, hp⟩ | ⟨hs, hq⟩)
    · exact ⟨hs, Or.inl hp⟩
    · exact ⟨hs, Or.inr hq⟩
  rw [hi, Finset.card_empty] at hu
  have := Finset.card_le_card hsub
  omega
theorem api_classes_card (D : Dag N) : D.X.card + D.M.card + D.T.card ≤ D.size := by
  have h1 := card_filter_disj (s := D.cone) (p := fun i => D.deg i = 0)
    (q := fun i => D.deg i = 1) (by intro i h1 h2; omega)
  have h2 := card_filter_disj (s := D.cone) (p := fun i => D.deg i = 0 ∨ D.deg i = 1)
    (q := fun i => D.deg i = 2) (by intro i h1 h2; omega)
  have h3 := Finset.card_filter_le D.cone (fun i => (D.deg i = 0 ∨ D.deg i = 1) ∨ D.deg i = 2)
  have h4 := coneOf_card D {D.out}
  unfold Dag.X Dag.M Dag.T
  unfold Dag.cone at *
  omega
theorem api_andor_card (D : Dag N) : D.AndM.card + D.OrM.card ≤ D.M.card := by
  classical
  have h := card_filter_disj (s := D.M) (p := D.IsAnd) (q := D.IsOr) (by
    rintro i ⟨a, b, ha⟩ ⟨a', b', hb⟩
    rw [ha] at hb
    cases hb)
  have h' := Finset.card_filter_le D.M (fun i => D.IsAnd i ∨ D.IsOr i)
  unfold Dag.AndM Dag.OrM
  convert le_trans h h' using 2
theorem band_mono : ∀ a b c d : Bool, a ≤ c → b ≤ d → (a && b) ≤ (c && d) := by decide
theorem bor_mono : ∀ a b c d : Bool, a ≤ c → b ≤ d → (a || b) ≤ (c || d) := by decide
theorem api_val_mono (D : Dag N) (i : ℕ) {x y : Fin (N + N) → Bool} (h : x ≤ y) :
    D.val x i ≤ D.val y i := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    have hd : ∀ a, (if _ : a < i then D.val x a else false) ≤
        (if _ : a < i then D.val y a else false) := by
      intro a
      split_ifs with ha
      · exact ih a ha
      · exact le_rfl
    conv_lhs => rw [Dag.val]
    conv_rhs => rw [Dag.val]
    split_ifs with hi
    · exact h _
    · cases hg : D.gates[i - (N + N)]? with
      | none => exact le_rfl
      | some g =>
        cases g with
        | and a b => exact band_mono _ _ _ _ (hd a) (hd b)
        | or a b => exact bor_mono _ _ _ _ (hd a) (hd b)
        | cst v => exact le_rfl
theorem api_val_xonly (D : Dag N) {i : ℕ} (hd : D.deg i = 0) {x y : Fin (N + N) → Bool}
    (h : ∀ p : Fin N, x (Fin.castAdd N p) = y (Fin.castAdd N p)) : D.val x i = D.val y i := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    have he : ∀ a, (if _ : a < i then D.deg a else 0) = 0 →
        (if _ : a < i then D.val x a else false) = (if _ : a < i then D.val y a else false) := by
      intro a ha
      split_ifs at ha ⊢ with hai
      · exact ih a hai ha
      · rfl
    rw [Dag.deg] at hd
    conv_lhs => rw [Dag.val]
    conv_rhs => rw [Dag.val]
    by_cases hi : i < N + N
    · rw [dif_pos hi, dif_pos hi]
      rw [if_pos hi] at hd
      have hN : ¬ N ≤ i := by intro hN; rw [if_pos hN] at hd; exact absurd hd one_ne_zero
      have := h ⟨i, by omega⟩
      simpa [Fin.castAdd] using this
    · rw [dif_neg hi, dif_neg hi]
      rw [if_neg hi] at hd
      cases hg : D.gates[i - (N + N)]? with
      | none => rfl
        | some g =>
          rw [hg] at hd
          cases g with
          | and a b =>
            dsimp only at hd ⊢
            rw [he a (by omega), he b (by omega)]
          | or a b =>
            dsimp only at hd ⊢
            rw [he a (by omega), he b (by omega)]
          | cst v => rfl
theorem card03a_size (C : Circuit) : (ofCircuit N C).size = C.size := by
  simp [Dag.size, ofCircuit, Circuit.size]
theorem trGate_kids (i : ℕ) (g : Gate) : ∀ c ∈ (trGate i g).kids, c < i := by
  intro c hc
  unfold trGate at hc
  split at hc <;> (try split_ifs at hc) <;> simp_all [G.kids] <;> omega
theorem card03b_wf (C : Circuit) : (ofCircuit N C).WF := by
  intro i g hg c hc
  obtain ⟨hi, hg⟩ := gateAt_some hg
  simp only [ofCircuit, List.getElem?_mapIdx] at hg
  cases h : C.gates[i - (N + N)]? with
  | none => rw [h] at hg; cases hg
  | some g0 =>
    rw [h] at hg
    simp only [Option.map_some, Option.some.injEq] at hg
    subst hg
    have := trGate_kids _ g0 c hc
    omega
theorem card03r_mono (D : Dag N) : Monotone2 D.toCircuit := by
  intro g hg
  simp only [Dag.toCircuit, List.mem_map] at hg
  obtain ⟨g0, -, rfl⟩ := hg
  cases g0 with
  | and a b => simp [G.toGate]
  | or a b => simp [G.toGate]
  | cst v => cases v <;> simp [G.toGate]
theorem labAnd_unique {D : Dag N} {g f v f' v' : ℕ} (h : D.LabAnd g f v) (h' : D.LabAnd g f' v') :
    f = f' ∧ v = v' := by
  obtain ⟨hg, hf, hv⟩ := h
  obtain ⟨hg', hf', hv'⟩ := h'
  rcases hg with hg | hg <;> rcases hg' with hg' | hg' <;> rw [hg] at hg' <;>
    simp only [Option.some.injEq, G.and.injEq] at hg' <;> obtain ⟨rfl, rfl⟩ := hg'
  · exact ⟨rfl, rfl⟩
  · omega
  · omega
  · exact ⟨rfl, rfl⟩
theorem card17s_served (I : Fin N → Fin N → Prop) (D : Dag N) :
    (D.served I).card ≤ 2 * D.AndM.card := by
  classical
  let T : ℕ → Finset (Fin N × Fin N) := fun g => Finset.univ.filter (fun e => ∃ f v,
    D.LabAnd g f v ∧ D.Vstar v = {e.2} ∧ e.1 ∈ D.alive f ∧ I e.1 e.2 ∧
      (D.alive f ∩ ptsOn I e.2).card ≤ 2)
  have hsub : D.served I ⊆ D.AndM.biUnion T := by
    intro e he
    unfold Dag.served at he
    rw [Finset.mem_filter] at he
    obtain ⟨-, g, hg, f, v, h1, h2, h3, h4, h5⟩ := he
    rw [Finset.mem_biUnion]
    exact ⟨g, hg, Finset.mem_filter.2 ⟨Finset.mem_univ _, f, v, h1, h2, h3, h4, h5⟩⟩
  have hT : ∀ g ∈ D.AndM, (T g).card ≤ 2 := by
    intro g _
    by_cases hne : (T g).Nonempty
    · obtain ⟨e0, he0⟩ := hne
      obtain ⟨-, f0, v0, h1, h2, -, -, h5⟩ := Finset.mem_filter.1 he0
      have hsub' : T g ⊆ (D.alive f0 ∩ ptsOn I e0.2).image (fun p => (p, e0.2)) := by
        intro e he
        obtain ⟨-, f, v, k1, k2, k3, k4, -⟩ := Finset.mem_filter.1 he
        obtain ⟨rfl, rfl⟩ := labAnd_unique k1 h1
        have hw : e.2 = e0.2 := by
          rw [h2] at k2
          exact (Finset.singleton_inj.1 k2).symm
        rw [Finset.mem_image]
        refine ⟨e.1, Finset.mem_inter.2 ⟨k3, ?_⟩, ?_⟩
        · unfold ptsOn
          rw [Finset.mem_filter, ← hw]
          exact ⟨Finset.mem_univ _, k4⟩
        · ext <;> simp [hw]
      exact le_trans (Finset.card_le_card hsub') (le_trans Finset.card_image_le h5)
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne]; simp
  calc (D.served I).card ≤ (D.AndM.biUnion T).card := Finset.card_le_card hsub
    _ ≤ ∑ g ∈ D.AndM, (T g).card := Finset.card_biUnion_le
    _ ≤ ∑ _g ∈ D.AndM, 2 := Finset.sum_le_sum hT
    _ = 2 * D.AndM.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
end Deg2.Api
namespace Deg2.Path
open Deg2
variable {N : ℕ}
theorem isPath_single (D : Dag N) (a : ℕ) : D.IsPath [a] a a := by
  refine ⟨rfl, rfl, ?_⟩
  intro k hk
  simp at hk
theorem isPath_cons (D : Dag N) {f c b : ℕ} {π : List ℕ} (hk : D.Kid f c)
    (hp : D.IsPath π c b) : D.IsPath (f :: π) f b := by
  obtain ⟨hh, hl, hc⟩ := hp
  cases π with
  | nil => simp at hh
  | cons c' π' =>
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    refine ⟨rfl, ?_, ?_⟩
    · rw [List.getLast?_cons_cons]; exact hl
    · intro k hk'
      cases k with
      | zero => simpa using hk
      | succ k =>
        have := hc k (by simp at hk' ⊢; omega)
        simpa using this
theorem pt_val {p : Fin N} {i : ℕ} (hi : i < N + N) (h : pt p ⟨i, hi⟩ = true) : i = p.val := by
  unfold pt inp at h
  by_cases hN : i < N
  · have : (⟨i, hi⟩ : Fin (N + N)) = Fin.castAdd N ⟨i, hN⟩ := rfl
    rw [this, Fin.addCases_left] at h
    simp only [Finset.mem_singleton, decide_eq_true_eq] at h
    rw [← h]
  · have : (⟨i, hi⟩ : Fin (N + N)) = Fin.natAdd N ⟨i - N, by omega⟩ := by
      ext; simp; omega
    rw [this, Fin.addCases_right] at h
    simp at h
theorem card05_path (I : Fin N → Fin N → Prop) (D : Dag N) (f : ℕ) (p : Fin N)
    (S : Finset (Fin N)) (h1 : D.val (pt p) f = true) (h0 : D.val (testInput I S) f = false) :
    ∃ π, D.IsPath π f p.val ∧
      ∀ v ∈ π, D.val (pt p) v = true ∧ D.val (testInput I S) v = false := by
  induction f using Nat.strong_induction_on with
  | _ f ih =>
    have step : ∀ c, D.Kid f c → D.val (pt p) c = true → D.val (testInput I S) c = false →
        ∃ π, D.IsPath π f p.val ∧
          ∀ v ∈ π, D.val (pt p) v = true ∧ D.val (testInput I S) v = false := by
      intro c hk hc1 hc0
      obtain ⟨_, _, _, hcf⟩ := id hk
      obtain ⟨π, hπ, hv⟩ := ih c hcf hc1 hc0
      refine ⟨f :: π, isPath_cons D hk hπ, ?_⟩
      intro v hv'
      rcases List.mem_cons.1 hv' with rfl | hv'
      · exact ⟨h1, h0⟩
      · exact hv v hv'
    by_cases hi : f < N + N
    · rw [Dag.val, dif_pos hi] at h1
      have := pt_val hi h1
      subst this
      refine ⟨[p.val], isPath_single D _, ?_⟩
      intro v hv
      simp only [List.mem_singleton] at hv
      subst hv
      exact ⟨by rw [Dag.val, dif_pos hi]; exact h1, h0⟩
    · have hga : ∀ g, D.gates[f - (N + N)]? = some g → D.gateAt f = some g := by
        intro g hg; unfold Dag.gateAt; rw [if_pos (by omega)]; exact hg
      rw [Dag.val, dif_neg hi] at h1 h0
      cases hg : D.gates[f - (N + N)]? with
      | none => rw [hg] at h1; simp at h1
      | some g =>
        rw [hg] at h1 h0
        cases g with
        | and a b =>
          dsimp only at h1 h0
          rw [Bool.and_eq_true] at h1
          obtain ⟨ha, hb⟩ := h1
          split_ifs at ha with hax
          split_ifs at hb with hbx
          have hka : D.Kid f a := ⟨_, hga _ hg, by simp [G.kids], hax⟩
          have hkb : D.Kid f b := ⟨_, hga _ hg, by simp [G.kids], hbx⟩
          rw [dif_pos hax, dif_pos hbx, Bool.and_eq_false_iff] at h0
          rcases h0 with h0 | h0
          · exact step a hka ha h0
          · exact step b hkb hb h0
        | or a b =>
          dsimp only at h1 h0
          rw [Bool.or_eq_false_iff] at h0
          obtain ⟨h0a, h0b⟩ := h0
          rw [Bool.or_eq_true] at h1
          rcases h1 with ha | hb
          · split_ifs at ha with hax
            have hka : D.Kid f a := ⟨_, hga _ hg, by simp [G.kids], hax⟩
            rw [dif_pos hax] at h0a
            exact step a hka ha h0a
          · split_ifs at hb with hbx
            have hkb : D.Kid f b := ⟨_, hga _ hg, by simp [G.kids], hbx⟩
            rw [dif_pos hbx] at h0b
            exact step b hkb hb h0b
        | cst v =>
          dsimp only at h1 h0
          rw [h1] at h0
          cases h0
end Deg2.Path
namespace Deg2
open Deg2.Api Deg2.Path
variable {N : ℕ}
theorem circ_val_input (D : Dag N) (x : Fin (N + N) → Bool) {i : ℕ} (hi : i < N + N) :
    D.val x i = x ⟨i, hi⟩ := by
  rw [Dag.val, dif_pos hi]
theorem circ_deg_input (D : Dag N) {i : ℕ} (hi : i < N + N) :
    D.deg i = if N ≤ i then 1 else 0 := by
  rw [Dag.deg, if_pos hi]
theorem circ_val_and_eq (D : Dag N) {i a b : ℕ} (h : D.gateAt i = some (.and a b)) (ha : a < i)
    (hb : b < i) (x : Fin (N + N) → Bool) : D.val x i = (D.val x a && D.val x b) := by
  obtain ⟨hi, hg⟩ := gateAt_some h
  rw [Dag.val, dif_neg (by omega), hg]
  dsimp only
  rw [dif_pos ha, dif_pos hb]
theorem circ_val_and (D : Dag N) {i a b : ℕ} (h : D.gateAt i = some (.and a b))
    {x : Fin (N + N) → Bool} (hv : D.val x i = true) :
    a < i ∧ b < i ∧ D.val x a = true ∧ D.val x b = true := by
  obtain ⟨hi, hg⟩ := gateAt_some h
  rw [Dag.val, dif_neg (by omega), hg] at hv
  dsimp only at hv
  rw [Bool.and_eq_true] at hv
  obtain ⟨ha, hb⟩ := hv
  split_ifs at ha with hax
  split_ifs at hb with hbx
  exact ⟨hax, hbx, ha, hb⟩
theorem circ_val_or_true (D : Dag N) {i a b : ℕ} (h : D.gateAt i = some (.or a b))
    {x : Fin (N + N) → Bool} (hv : D.val x i = true) :
    (a < i ∧ D.val x a = true) ∨ (b < i ∧ D.val x b = true) := by
  obtain ⟨hi, hg⟩ := gateAt_some h
  rw [Dag.val, dif_neg (by omega), hg] at hv
  dsimp only at hv
  rw [Bool.or_eq_true] at hv
  rcases hv with ha | hb
  · split_ifs at ha with hax
    exact Or.inl ⟨hax, ha⟩
  · split_ifs at hb with hbx
    exact Or.inr ⟨hbx, hb⟩
theorem circ_val_or_false (D : Dag N) {i a b : ℕ} (h : D.gateAt i = some (.or a b))
    {x : Fin (N + N) → Bool} (hv : D.val x i = false) :
    (a < i → D.val x a = false) ∧ (b < i → D.val x b = false) := by
  obtain ⟨hi, hg⟩ := gateAt_some h
  rw [Dag.val, dif_neg (by omega), hg] at hv
  dsimp only at hv
  rw [Bool.or_eq_false_iff] at hv
  obtain ⟨ha, hb⟩ := hv
  refine ⟨fun hax => ?_, fun hbx => ?_⟩
  · rwa [dif_pos hax] at ha
  · rwa [dif_pos hbx] at hb
theorem circ_val_or_kid (D : Dag N) {i a b c : ℕ} (h : D.gateAt i = some (.or a b))
    (hk : D.Kid i c) {x : Fin (N + N) → Bool} (hc : D.val x c = true) : D.val x i = true := by
  obtain ⟨g, hg, hcg, hci⟩ := hk
  rw [h, Option.some.injEq] at hg
  subst hg
  obtain ⟨hi, hg⟩ := gateAt_some h
  rw [Dag.val, dif_neg (by omega), hg]
  dsimp only
  simp only [G.kids, List.mem_cons, List.not_mem_nil, or_false] at hcg
  rw [Bool.or_eq_true]
  rcases hcg with rfl | rfl
  · left; rw [dif_pos hci]; exact hc
  · right; rw [dif_pos hci]; exact hc
theorem circ_deg_and (D : Dag N) {i a b : ℕ} (h : D.gateAt i = some (.and a b)) (ha : a < i)
    (hb : b < i) : D.deg i = D.deg a + D.deg b := by
  obtain ⟨hi, hg⟩ := gateAt_some h
  rw [Dag.deg, if_neg (by omega), hg]
  dsimp only
  rw [dif_pos ha, dif_pos hb]
theorem circ_kid_lt {D : Dag N} {i c : ℕ} (h : D.Kid i c) : c < i := by
  obtain ⟨_, _, _, h⟩ := h
  exact h
theorem circ_kid_gate {D : Dag N} {i c : ℕ} (h : D.Kid i c) : N + N ≤ i := by
  obtain ⟨_, hg, _, _⟩ := h
  exact (gateAt_some hg).1
theorem circ_kid_of {D : Dag N} {i c : ℕ} {g : G} (h : D.gateAt i = some g) (hc : c ∈ g.kids)
    (hci : c < i) : D.Kid i c := ⟨g, h, hc, hci⟩
theorem circ_ep_pts (p u : Fin N) (q : Fin N) : ep p u (Fin.castAdd N q) = pt p (Fin.castAdd N q) := by
  simp [ep, pt, inp]
theorem circ_ep_line {p w : Fin N} {i : ℕ} (hi : i < N + N) (hN : N ≤ i)
    (h : ep p w ⟨i, hi⟩ = true) : i = N + w.val := by
  unfold ep inp at h
  have : (⟨i, hi⟩ : Fin (N + N)) = Fin.natAdd N ⟨i - N, by omega⟩ := by
    ext; simp; omega
  rw [this, Fin.addCases_right] at h
  simp only [Finset.mem_singleton, decide_eq_true_eq] at h
  have := congrArg Fin.val h
  simp at this
  omega
theorem circ_getD_mem {π : List ℕ} {k : ℕ} (hk : k < π.length) : π.getD k 0 ∈ π := by
  rw [List.getD_eq_getElem _ _ hk]
  exact List.getElem_mem hk
theorem circ_path_first {D : Dag N} {π : List ℕ} {a b : ℕ} (hp : D.IsPath π a b) (hab : a ≠ b) :
    ∃ c, D.Kid a c ∧ c ∈ π := by
  obtain ⟨hh, hl, hc⟩ := hp
  cases π with
  | nil => simp at hh
  | cons a' rest =>
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    cases rest with
    | nil => simp at hl; exact absurd hl hab
    | cons c rest' =>
      refine ⟨c, ?_, by simp⟩
      have := hc 0 (by simp)
      simpa using this
theorem circ_vreach_val (D : Dag N) {v : ℕ} {u : Fin N} (h : D.VReach v u)
    {x : Fin (N + N) → Bool} (hx : x (Fin.natAdd N u) = true) : D.val x v = true := by
  induction h with
  | leaf u =>
    rw [circ_val_input D x (by omega)]
    exact hx
  | step hor _ hk _ ih =>
    obtain ⟨a, b, hg⟩ := hor
    exact circ_val_or_kid D hg hk (ih hx)
theorem circ_honest_core (I : Fin N → Fin N → Prop) (D : Dag N) (p w : Fin N) :
    ∀ g, D.deg g = 1 → D.val (ep p w) g = true → D.val (pt p) g = false →
      (∀ u, D.val (ep p u) g = true → I p u) →
      ∃ π, D.IsPath π g (N + w.val) ∧ ∀ v ∈ π, D.deg v = 1 ∧ D.val (ep p w) v = true ∧
          ∀ u, D.val (ep p u) v = true → I p u := by
  intro g
  induction g using Nat.strong_induction_on with
  | _ g ih =>
    intro hd h1 h0 hh
    have extend : ∀ c, D.Kid g c → D.deg c = 1 → D.val (ep p w) c = true →
        D.val (pt p) c = false → (∀ u, D.val (ep p u) c = true → I p u) →
        ∃ π, D.IsPath π g (N + w.val) ∧ ∀ v ∈ π, D.deg v = 1 ∧ D.val (ep p w) v = true ∧
          ∀ u, D.val (ep p u) v = true → I p u := by
      intro c hk hcd hc1 hc0 hch
      obtain ⟨π, hπ, hv⟩ := ih c (circ_kid_lt hk) hcd hc1 hc0 hch
      refine ⟨g :: π, isPath_cons D hk hπ, ?_⟩
      intro v hv'
      rcases List.mem_cons.1 hv' with rfl | hv'
      · exact ⟨hd, h1, hh⟩
      · exact hv v hv'
    by_cases hi : g < N + N
    · rw [circ_deg_input D hi] at hd
      have hN : N ≤ g := by
        by_contra hN; rw [if_neg hN] at hd; exact absurd hd zero_ne_one
      rw [circ_val_input D _ hi] at h1
      have hgw := circ_ep_line hi hN h1
      refine ⟨[g], ?_, ?_⟩
      · rw [hgw]; exact isPath_single D _
      · intro v hv
        simp only [List.mem_singleton] at hv
        subst hv
        refine ⟨by rw [circ_deg_input D hi, if_pos hN], ?_⟩
        refine ⟨?_, ?_⟩
        · rw [circ_val_input D _ hi]; exact h1
        · exact hh
    · have hga : ∀ gg, D.gates[g - (N + N)]? = some gg → D.gateAt g = some gg := by
        intro gg hg; unfold Dag.gateAt; rw [if_pos (by omega)]; exact hg
      cases hg : D.gates[g - (N + N)]? with
      | none =>
        rw [Dag.deg, if_neg hi, hg] at hd
        exact absurd hd zero_ne_one
      | some gg =>
        have hgA := hga gg hg
        cases gg with
        | cst v =>
          rw [Dag.deg, if_neg hi, hg] at hd
          exact absurd hd zero_ne_one
        | or a b =>
          have hstep : ∀ c, c < g → (c = a ∨ c = b) → D.val (ep p w) c = true →
              D.val (pt p) c = false →
              ∃ π, D.IsPath π g (N + w.val) ∧
                ∀ v ∈ π, D.deg v = 1 ∧ D.val (ep p w) v = true ∧
          ∀ u, D.val (ep p u) v = true → I p u := by
            intro c hcg hcab hc1 hc0
            have hk : D.Kid g c := circ_kid_of hgA (by rcases hcab with rfl | rfl <;> simp [G.kids]) hcg
            have hle : D.deg c ≤ 1 := hd ▸ deg_kid hk
            have hcd : D.deg c = 1 := by
              by_contra hne
              have h0' : D.deg c = 0 := by omega
              have := api_val_xonly D h0' (x := ep p w) (y := pt p) (circ_ep_pts p w)
              rw [hc1, hc0] at this
              cases this
            refine extend c hk hcd hc1 hc0 ?_
            intro u hu
            exact hh u (circ_val_or_kid D hgA hk hu)
          have h0' := circ_val_or_false D hgA h0
          rcases circ_val_or_true D hgA h1 with ⟨ha, ha1⟩ | ⟨hb, hb1⟩
          · exact hstep a ha (Or.inl rfl) ha1 (h0'.1 ha)
          · exact hstep b hb (Or.inr rfl) hb1 (h0'.2 hb)
        | and a b =>
          obtain ⟨ha, hb, ha1, hb1⟩ := circ_val_and D hgA h1
          have hdeg := circ_deg_and D hgA ha hb
          have hstep : ∀ f v, v < g → (v = a ∨ v = b) → D.deg f = 0 → D.deg v = 1 →
              D.val (ep p w) f = true → D.val (ep p w) v = true →
              (∀ x, D.val x g = (D.val x f && D.val x v)) →
              ∃ π, D.IsPath π g (N + w.val) ∧
                ∀ v ∈ π, D.deg v = 1 ∧ D.val (ep p w) v = true ∧
          ∀ u, D.val (ep p u) v = true → I p u := by
            intro f v hvg hvab hf hv hf1 hv1 heq
            have hk : D.Kid g v := circ_kid_of hgA (by rcases hvab with rfl | rfl <;> simp [G.kids]) hvg
            have hfp : ∀ u, D.val (ep p u) f = true := by
              intro u
              rw [api_val_xonly D hf (x := ep p u) (y := ep p w)
                (fun q => by rw [circ_ep_pts, circ_ep_pts])]
              exact hf1
            have hfpt : D.val (pt p) f = true := by
              rw [api_val_xonly D hf (x := pt p) (y := ep p w)
                (fun q => by rw [circ_ep_pts])]
              exact hf1
            have hv0 : D.val (pt p) v = false := by
              rw [heq, hfpt, Bool.true_and] at h0; exact h0
            refine extend v hk hv hv1 hv0 ?_
            intro u hu
            apply hh u
            rw [heq, hfp u, hu]; rfl
          by_cases hda : D.deg a = 0
          · exact hstep a b hb (Or.inr rfl) hda (by omega) ha1 hb1
              (circ_val_and_eq D hgA ha hb)
          · exact hstep b a ha (Or.inl rfl) (by omega) (by omega) hb1 ha1
              (fun x => by rw [circ_val_and_eq D hgA ha hb x, Bool.and_comm])
theorem card06_honest_path (I : Fin N → Fin N → Prop) (D : Dag N) (r : ℕ) (p w : Fin N)
    (hr : D.deg r = 1) (hh : IsHonest I (fun x => D.val x r) p)
    (h1 : D.val (ep p w) r = true) :
    ∃ π, D.IsPath π r (N + w.val) ∧ (∀ v ∈ π, D.deg v = 1 ∧ D.val (ep p w) v = true) ∧
      D.LabelsAlive π (pt p) ∧ ∀ v ∈ π, D.Vstar v ⊆ pencil I p := by
  obtain ⟨π, hπ, hv⟩ := circ_honest_core I D p w r hr h1 hh.1
    (fun u hu => hh.2 u hu)
  refine ⟨π, hπ, fun v hv' => ⟨(hv v hv').1, (hv v hv').2.1⟩, ?_, ?_⟩
  · intro k f hk hlab
    have hg1 := (hv _ (circ_getD_mem (by omega : k < π.length))).2.1
    obtain ⟨hgate, hf, -⟩ := hlab
    have hf1 : D.val (ep p w) f = true := by
      rcases hgate with hgate | hgate
      · exact (circ_val_and D hgate hg1).2.2.1
      · exact (circ_val_and D hgate hg1).2.2.2
    rw [api_val_xonly D hf (x := pt p) (y := ep p w) (fun q => by rw [circ_ep_pts])]
    exact hf1
  · intro v hv' u hu
    classical
    unfold Dag.Vstar at hu
    rw [Finset.mem_filter] at hu
    have hval := circ_vreach_val D hu.2 (x := ep p u) (by unfold ep inp; rw [Fin.addCases_right]; simp)
    unfold pencil
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (hv v hv').2.2 u hval⟩
def circKids (D : Dag N) (g : ℕ) : Finset ℕ := (((D.gateAt g).map G.kids).getD []).toFinset
theorem circKids_card (D : Dag N) (g : ℕ) : (circKids D g).card ≤ 2 := by
  unfold circKids
  refine le_trans (List.toFinset_card_le _) ?_
  cases D.gateAt g with
  | none => simp
  | some gg => cases gg <;> simp [G.kids]
theorem circKids_mem {D : Dag N} {g c : ℕ} (h : D.Kid g c) : c ∈ circKids D g := by
  obtain ⟨gg, hg, hc, -⟩ := h
  unfold circKids
  rw [hg]
  simpa using hc
theorem circ_alive_input (D : Dag N) {i : ℕ} (hi : i < N + N) : (D.alive i).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  unfold Dag.alive at ha hb
  rw [Finset.mem_filter, circ_val_input D _ hi] at ha hb
  have h1 := pt_val hi ha.2
  have h2 := pt_val hi hb.2
  exact Fin.ext (by omega)
theorem circ_pt_le_test (I : Fin N → Fin N → Prop) (S : Finset (Fin N)) {q : Fin N}
    (hq : ∀ l ∈ S, ¬ I q l) : pt q ≤ testInput I S := by
  classical
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · unfold pt testInput inp
    rw [Fin.addCases_left, Fin.addCases_left]
    by_cases hj : j = q
    · subst hj
      have : j ∈ Finset.univ.filter (fun p => ∀ l ∈ S, ¬ I p l) := by
        rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hq⟩
      simp only [Finset.mem_singleton, decide_true]
      rw [decide_eq_true this]
    · simp [hj]
  · unfold pt testInput inp
    rw [Fin.addCases_right, Fin.addCases_right]
    simp
theorem circ_alive_on (I : Fin N → Fin N → Prop) (D : Dag N) {f : ℕ} {S : Finset (Fin N)}
    (h0 : D.val (testInput I S) f = false) {q : Fin N} (hq : q ∈ D.alive f) :
    ∃ s ∈ S, I q s := by
  by_contra hne
  push_neg at hne
  have hle := api_val_mono D f (circ_pt_le_test I S hne)
  unfold Dag.alive at hq
  rw [Finset.mem_filter] at hq
  rw [hq.2, h0] at hle
  exact absurd hle (by decide)
theorem circ_lines_le_two (I : Fin N → Fin N → Prop) (hI : NoRect I) (D : Dag N) {f : ℕ}
    {S : Finset (Fin N)} (hS : S.card ≤ 2) (h0 : D.val (testInput I S) f = false) :
    (Finset.univ.filter (fun l => 3 ≤ (D.alive f ∩ ptsOn I l).card)).card ≤ 2 := by
  classical
  refine le_trans (Finset.card_le_card (t := S) ?_) hS
  intro l hl
  rw [Finset.mem_filter] at hl
  by_contra hlS
  have hsub : D.alive f ∩ ptsOn I l ⊆ S.biUnion (fun s => ptsOn I s ∩ ptsOn I l) := by
    intro q hq
    rw [Finset.mem_inter] at hq
    obtain ⟨s, hs, hqs⟩ := circ_alive_on I D h0 hq.1
    rw [Finset.mem_biUnion]
    refine ⟨s, hs, Finset.mem_inter.2 ⟨?_, hq.2⟩⟩
    unfold ptsOn; rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hqs⟩
  have hb := Finset.card_biUnion_le_card_mul S (fun s => ptsOn I s ∩ ptsOn I l) 1 (by
    intro s hs
    rw [Finset.card_le_one]
    intro a ha b hb
    by_contra hab
    have hsl : s ≠ l := by rintro rfl; exact hlS hs
    unfold ptsOn at ha hb
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    exact hI a b s l hab hsl ⟨ha.1, ha.2, hb.1, hb.2⟩)
  have := Finset.card_le_card hsub
  omega
theorem circ_charge (I : Fin N → Fin N → Prop) (D : Dag N) (Gs : Finset ℕ)
    (hdown : ∀ i ∈ Gs, ∀ c, D.Kid i c → N + N ≤ c → c ∈ Gs) (p l : Fin N)
    (S : Finset (Fin N)) :
    ∀ f, f ∈ Gs → D.deg f = 0 → D.val (pt p) f = true → D.val (testInput I S) f = false →
      3 ≤ (D.alive f ∩ ptsOn I l).card →
      ∃ g ∈ Gs, D.deg g = 0 ∧ D.val (testInput I S) g = false ∧
        3 ≤ (D.alive g ∩ ptsOn I l).card ∧
        ∃ c, D.Kid g c ∧ p ∈ D.alive c ∧ (D.alive c ∩ ptsOn I l).card ≤ 2 := by
  intro f
  induction f using Nat.strong_induction_on with
  | _ f ih =>
    intro hf hd h1 h0 h3
    by_cases hi : f < N + N
    · have := le_trans (Finset.card_le_card (Finset.inter_subset_left (s₁ := D.alive f)
        (s₂ := ptsOn I l))) (circ_alive_input D hi)
      omega
    · obtain ⟨π, hπ, hv⟩ := card05_path I D f p S h1 h0
      have hne : f ≠ p.val := by have := p.isLt; omega
      obtain ⟨c, hk, hcπ⟩ := circ_path_first hπ hne
      obtain ⟨hc1, hc0⟩ := hv c hcπ
      have hcd : D.deg c = 0 := by have := deg_kid hk; omega
      by_cases hc3 : 3 ≤ (D.alive c ∩ ptsOn I l).card
      · have hcg : N + N ≤ c := by
          by_contra hcn
          have := le_trans (Finset.card_le_card (Finset.inter_subset_left (s₁ := D.alive c)
            (s₂ := ptsOn I l))) (circ_alive_input D (by omega : c < N + N))
          omega
        exact ih c (circ_kid_lt hk) (hdown f hf c hk hcg) hcd hc1 hc0 hc3
      · refine ⟨f, hf, hd, h0, h3, c, hk, ?_, by omega⟩
        unfold Dag.alive; rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hc1⟩
theorem card07_two_line (I : Fin N → Fin N → Prop) (hI : NoRect I) (D : Dag N)
    (Gs : Finset ℕ) (hdown : ∀ i ∈ Gs, ∀ c, D.Kid i c → N + N ≤ c → c ∈ Gs) :
    (D.fSet I Gs 2).card ≤ 8 * (Gs.filter (fun f => D.deg f = 0)).card := by
  classical
  let Lg : ℕ → Finset (Fin N) := fun g => Finset.univ.filter (fun l =>
    3 ≤ (D.alive g ∩ ptsOn I l).card ∧
      ∃ S : Finset (Fin N), S.card ≤ 2 ∧ D.val (testInput I S) g = false)
  let Tc : Fin N → ℕ → Finset (Fin N × Fin N) := fun l c =>
    if (D.alive c ∩ ptsOn I l).card ≤ 2 then (D.alive c ∩ ptsOn I l).image (fun q => (q, l))
    else ∅
  have hLg : ∀ g, (Lg g).card ≤ 2 := by
    intro g
    by_cases hS : ∃ S : Finset (Fin N), S.card ≤ 2 ∧ D.val (testInput I S) g = false
    · obtain ⟨S, hS2, hS0⟩ := hS
      refine le_trans (Finset.card_le_card ?_) (circ_lines_le_two I hI D hS2 hS0)
      intro l hl
      simp only [Lg, Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
      exact hl.1
    · have : Lg g = ∅ := by
        ext l
        simp only [Lg, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
          iff_false, not_and]
        intro _ h; exact hS h
      rw [this]; simp
  have hTc : ∀ l c, (Tc l c).card ≤ 2 := by
    intro l c
    simp only [Tc]
    split_ifs with h
    · exact le_trans Finset.card_image_le h
    · simp
  have hsub : D.fSet I Gs 2 ⊆ (Gs.filter (fun f => D.deg f = 0)).biUnion
      (fun g => (Lg g).biUnion (fun l => (circKids D g).biUnion (fun c => Tc l c))) := by
    intro e he
    unfold Dag.fSet at he
    rw [Finset.mem_filter] at he
    obtain ⟨-, hIe, f, hf, hfd, hdead, hp, h3⟩ := he
    obtain ⟨S, hS⟩ := Finset.nonempty_iff_ne_empty.2 hdead
    unfold Dag.deadSets at hS
    rw [Finset.mem_filter] at hS
    obtain ⟨-, hS2, hS0⟩ := hS
    unfold Dag.alive at hp
    rw [Finset.mem_filter] at hp
    obtain ⟨g, hg, hgd, hg0, hg3, c, hk, hpc, hc2⟩ :=
      circ_charge I D Gs hdown e.1 e.2 S f hf hfd hp.2 hS0 h3
    simp only [Finset.mem_biUnion]
    refine ⟨g, Finset.mem_filter.2 ⟨hg, hgd⟩, e.2, ?_, c, circKids_mem hk, ?_⟩
    · simp only [Lg, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hg3, S, hS2, hg0⟩
    · simp only [Tc]
      rw [if_pos hc2, Finset.mem_image]
      refine ⟨e.1, Finset.mem_inter.2 ⟨hpc, ?_⟩, rfl⟩
      unfold ptsOn; rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hIe⟩
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans (Finset.card_biUnion_le_card_mul _ _ 8 ?_) (by rw [mul_comm])
  intro g _
  refine le_trans (Finset.card_biUnion_le_card_mul _ _ 4 ?_) ?_
  · intro l _
    refine le_trans (Finset.card_biUnion_le_card_mul _ _ 2 (fun c _ => hTc l c)) ?_
    have := circKids_card D g
    omega
  · have := hLg g
    omega
theorem circ_vreach_input (D : Dag N) {i : ℕ} {u : Fin N} (h : D.VReach i u) (hi : i < N + N) :
    i = N + u.val := by
  cases h with
  | leaf => rfl
  | step hor _ _ _ =>
    obtain ⟨a, b, hg⟩ := hor
    have := (gateAt_some hg).1
    omega
theorem circ_vstar_sub (D : Dag N) {v c : ℕ} (hor : D.IsOr v) (hd : D.deg v = 1)
    (hk : D.Kid v c) : D.Vstar c ⊆ D.Vstar v := by
  classical
  intro u hu
  unfold Dag.Vstar at hu ⊢
  rw [Finset.mem_filter] at hu ⊢
  exact ⟨Finset.mem_univ _, Dag.VReach.step hor hd hk hu.2⟩
theorem circ_pin_charge (D : Dag N) {v : ℕ} {u : Fin N} (h : D.VReach v u) :
    2 ≤ (D.Vstar v).card →
    ∃ o c, D.Reach v o ∧ D.IsOr o ∧ D.deg o = 1 ∧ 2 ≤ (D.Vstar o).card ∧
      D.Vstar o ⊆ D.Vstar v ∧ D.Kid o c ∧ D.Vstar c = {u} := by
  classical
  induction h with
  | leaf u =>
    intro h2
    exfalso
    have : (D.Vstar (N + u.val)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      unfold Dag.Vstar at ha hb
      rw [Finset.mem_filter] at ha hb
      have h1 := circ_vreach_input D ha.2 (by omega)
      have h2 := circ_vreach_input D hb.2 (by omega)
      exact Fin.ext (by omega)
    omega
  | @step v c u hor hd hk hc ih =>
    intro h2
    by_cases h2c : 2 ≤ (D.Vstar c).card
    · obtain ⟨o, c', hr, ho, hod, ho2, hos, hk', hc'⟩ := ih h2c
      exact ⟨o, c', Relation.ReflTransGen.head hk hr, ho, hod, ho2,
        hos.trans (circ_vstar_sub D hor hd hk), hk', hc'⟩
    · refine ⟨v, c, Relation.ReflTransGen.refl, hor, hd, h2, subset_refl _, hk, ?_⟩
      have hu : u ∈ D.Vstar c := by
        unfold Dag.Vstar; rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hc⟩
      rw [Finset.eq_singleton_iff_unique_mem]
      refine ⟨hu, fun x hx => ?_⟩
      exact Finset.card_le_one.1 (by omega) x hx u hu
theorem circ_pinned_unique (I : Fin N → Fin N → Prop) (hI : NoRect I) (D : Dag N) {o : ℕ}
    {p p' : Fin N} (h : Dag.PinnedTo I D o p) (h' : Dag.PinnedTo I D o p') : p = p' := by
  classical
  obtain ⟨-, -, h2, hs⟩ := h
  obtain ⟨-, -, -, hs'⟩ := h'
  obtain ⟨u, hu, u', hu', huu⟩ := Finset.one_lt_card.1 (by omega : 1 < (D.Vstar o).card)
  by_contra hpp
  have m := fun {q l} (h : l ∈ pencil I q) => (Finset.mem_filter.1 h).2
  exact hI p p' u u' hpp huu ⟨m (hs hu), m (hs hu'), m (hs' hu), m (hs' hu')⟩
theorem circ_orM_reach (D : Dag N) {v o : ℕ} (hv : v ∈ D.OrM) (hr : D.Reach v o)
    (ho : D.IsOr o) (hod : D.deg o = 1) : o ∈ D.OrM := by
  classical
  unfold Dag.OrM Dag.M Dag.cone Dag.coneOf at hv ⊢
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton,
    exists_eq_left] at hv ⊢
  obtain ⟨a, b, hg⟩ := ho
  obtain ⟨hi, hgs⟩ := gateAt_some hg
  have hlt : o - (N + N) < D.gates.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hgs
    cases hgs
  refine ⟨⟨⟨by unfold Dag.size; omega, hi, hv.1.1.2.2.trans hr⟩, hod⟩, a, b, hg⟩
theorem card08_pinned (I : Fin N → Fin N → Prop) (hI : NoRect I) (D : Dag N) :
    (D.pinned I).card ≤ 2 * D.OrM.card := by
  classical
  let T : ℕ → ℕ → Finset (Fin N × Fin N) := fun o c =>
    Finset.univ.filter (fun e => Dag.PinnedTo I D o e.1 ∧ D.Vstar c = {e.2})
  have hT : ∀ o c, (T o c).card ≤ 1 := by
    intro o c
    rw [Finset.card_le_one]
    intro e he e' he'
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at he he'
    have h1 := circ_pinned_unique I hI D he.1 he'.1
    have h2 : e.2 = e'.2 := by
      have := he.2.symm.trans he'.2
      exact Finset.singleton_inj.1 this
    exact Prod.ext h1 h2
  have hsub : D.pinned I ⊆ D.OrM.biUnion (fun o => (circKids D o).biUnion (fun c => T o c)) := by
    intro e he
    unfold Dag.pinned at he
    rw [Finset.mem_filter] at he
    obtain ⟨-, v, hv, hpin, hu⟩ := he
    have hvr : D.VReach v e.2 := by
      unfold Dag.Vstar at hu; exact (Finset.mem_filter.1 hu).2
    obtain ⟨o, c, hr, ho, hod, ho2, hos, hk, hc⟩ := circ_pin_charge D hvr hpin.2.2.1
    simp only [Finset.mem_biUnion]
    refine ⟨o, circ_orM_reach D hv hr ho hod, c, circKids_mem hk, ?_⟩
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨⟨ho, hod, ho2, hos.trans hpin.2.2.2⟩, hc⟩
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans (Finset.card_biUnion_le_card_mul _ _ 2 ?_) (by rw [mul_comm])
  intro o _
  refine le_trans (Finset.card_biUnion_le_card_mul _ _ 1 (fun c _ => hT o c)) ?_
  have := circKids_card D o
  omega
end Deg2
namespace Deg2.Forms
open Deg2
variable {N : ℕ}
theorem inp_castAdd (P S : Finset (Fin N)) (p : Fin N) :
    inp P S (Fin.castAdd N p) = decide (p ∈ P) := by
  unfold inp
  exact Fin.addCases_left _
theorem inp_natAdd (P S : Finset (Fin N)) (l : Fin N) :
    inp P S (Fin.natAdd N l) = decide (l ∈ S) := by
  unfold inp
  exact Fin.addCases_right _
theorem inp_le {P S : Finset (Fin N)} {x : Fin (N + N) → Bool}
    (hP : ∀ p ∈ P, x (Fin.castAdd N p) = true) (hS : ∀ l ∈ S, x (Fin.natAdd N l) = true) :
    inp P S ≤ x := by
  intro j
  refine Fin.addCases (fun p => ?_) (fun l => ?_) j
  · rw [inp_castAdd]
    by_cases h : p ∈ P
    · rw [hP p h]; exact Bool.le_true _
    · simp [h]
  · rw [inp_natAdd]
    by_cases h : l ∈ S
    · rw [hS l h]; exact Bool.le_true _
    · simp [h]
theorem testInput_castAdd (I : Fin N → Fin N → Prop) (S : Finset (Fin N)) (p : Fin N) :
    testInput I S (Fin.castAdd N p) = true ↔ ∀ l ∈ S, ¬ I p l := by
  classical
  unfold testInput
  rw [inp_castAdd]
  simp
theorem testInput_natAdd (I : Fin N → Fin N → Prop) (S : Finset (Fin N)) (l : Fin N) :
    testInput I S (Fin.natAdd N l) = true ↔ l ∈ S := by
  classical
  unfold testInput
  rw [inp_natAdd]
  simp
theorem val_point (D : Dag N) (x : Fin (N + N) → Bool) (p : Fin N) :
    D.val x p.val = x (Fin.castAdd N p) := by
  rw [Dag.val, dif_pos (by omega)]
  rfl
theorem val_line (D : Dag N) (x : Fin (N + N) → Bool) (l : Fin N) :
    D.val x (N + l.val) = x (Fin.natAdd N l) := by
  rw [Dag.val, dif_pos (by omega)]
  rfl
theorem deg_line (D : Dag N) (l : Fin N) : D.deg (N + l.val) = 1 := by
  rw [Dag.deg, if_pos (by omega), if_pos (by omega)]
theorem pt_ep_points (p w : Fin N) (q : Fin N) :
    pt p (Fin.castAdd N q) = ep p w (Fin.castAdd N q) := by
  unfold pt ep
  rw [inp_castAdd, inp_castAdd]
theorem gateAt_of_get {D : Dag N} {i : ℕ} {g : G} (hi : N + N ≤ i)
    (hg : D.gates[i - (N + N)]? = some g) : D.gateAt i = some g := by
  unfold Dag.gateAt
  rw [if_pos hi]
  exact hg
theorem kid_gate {D : Dag N} {i c : ℕ} (h : D.Kid i c) :
    N + N ≤ i ∧ i < N + N + D.size := by
  obtain ⟨g, hg, -, -⟩ := h
  obtain ⟨hi, hg⟩ := Api.gateAt_some hg
  have := (List.getElem?_eq_some_iff.1 hg).1
  unfold Dag.size
  omega
theorem val_and {D : Dag N} {i a b : ℕ} (hg : D.gateAt i = some (.and a b)) (ha : a < i)
    (hb : b < i) (x : Fin (N + N) → Bool) : D.val x i = (D.val x a && D.val x b) := by
  obtain ⟨hi, hg⟩ := Api.gateAt_some hg
  rw [Dag.val, dif_neg (by omega), hg]
  simp only [dif_pos ha, dif_pos hb]
theorem val_or {D : Dag N} {i a b : ℕ} (hg : D.gateAt i = some (.or a b)) (ha : a < i)
    (hb : b < i) (x : Fin (N + N) → Bool) : D.val x i = (D.val x a || D.val x b) := by
  obtain ⟨hi, hg⟩ := Api.gateAt_some hg
  rw [Dag.val, dif_neg (by omega), hg]
  simp only [dif_pos ha, dif_pos hb]
theorem deg_and {D : Dag N} {i a b : ℕ} (hg : D.gateAt i = some (.and a b)) (ha : a < i)
    (hb : b < i) : D.deg i = D.deg a + D.deg b := by
  obtain ⟨hi, hg⟩ := Api.gateAt_some hg
  rw [Dag.deg, if_neg (by omega), hg]
  simp only [dif_pos ha, dif_pos hb]
theorem deg_or {D : Dag N} {i a b : ℕ} (hg : D.gateAt i = some (.or a b)) (ha : a < i)
    (hb : b < i) : D.deg i = max (D.deg a) (D.deg b) := by
  obtain ⟨hi, hg⟩ := Api.gateAt_some hg
  rw [Dag.deg, if_neg (by omega), hg]
  simp only [dif_pos ha, dif_pos hb]
theorem exists_kid (D : Dag N) {f : ℕ} (hf : N + N ≤ f) {x y : Fin (N + N) → Bool}
    (h1 : D.val y f = true) (h0 : D.val x f = false) :
    ∃ c, D.Kid f c ∧ D.val y c = true ∧ D.val x c = false := by
  rw [Dag.val, dif_neg (by omega)] at h1 h0
  cases hg : D.gates[f - (N + N)]? with
  | none => rw [hg] at h1; simp at h1
  | some g =>
    have hga := gateAt_of_get hf hg
    rw [hg] at h1 h0
    cases g with
    | and a b =>
      dsimp only at h1 h0
      rw [Bool.and_eq_true] at h1
      obtain ⟨ha, hb⟩ := h1
      split_ifs at ha with hax
      split_ifs at hb with hbx
      have hka : D.Kid f a := ⟨_, hga, by simp [G.kids], hax⟩
      have hkb : D.Kid f b := ⟨_, hga, by simp [G.kids], hbx⟩
      rw [dif_pos hax, dif_pos hbx, Bool.and_eq_false_iff] at h0
      rcases h0 with h0 | h0
      · exact ⟨a, hka, ha, h0⟩
      · exact ⟨b, hkb, hb, h0⟩
    | or a b =>
      dsimp only at h1 h0
      rw [Bool.or_eq_false_iff] at h0
      obtain ⟨h0a, h0b⟩ := h0
      rw [Bool.or_eq_true] at h1
      rcases h1 with ha | hb
      · split_ifs at ha with hax
        have hka : D.Kid f a := ⟨_, hga, by simp [G.kids], hax⟩
        rw [dif_pos hax] at h0a
        exact ⟨a, hka, ha, h0a⟩
      · split_ifs at hb with hbx
        have hkb : D.Kid f b := ⟨_, hga, by simp [G.kids], hbx⟩
        rw [dif_pos hbx] at h0b
        exact ⟨b, hkb, hb, h0b⟩
    | cst v =>
      dsimp only at h1 h0
      rw [h1] at h0
      cases h0
theorem alive_input_card (D : Dag N) {i : ℕ} (hi : i < N + N) : (D.alive i).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  unfold Dag.alive at ha hb
  rw [Finset.mem_filter, Dag.val, dif_pos hi] at ha hb
  have h1 := Path.pt_val hi ha.2
  have h2 := Path.pt_val hi hb.2
  exact Fin.ext (by omega)
theorem two_le_alive_gate (D : Dag N) {i : ℕ} (h : 2 ≤ (D.alive i).card) : N + N ≤ i := by
  by_contra hi
  have := alive_input_card D (i := i) (by omega)
  omega
theorem alive_eq_single (D : Dag N) {c : ℕ} {p : Fin N} (hp : p ∈ D.alive c)
    (h : ¬ 2 ≤ (D.alive c).card) : D.alive c = {p} := by
  rw [Finset.eq_singleton_iff_unique_mem]
  refine ⟨hp, fun q hq => ?_⟩
  exact Finset.card_le_one.1 (by omega) q hq p hp
theorem mem_alive {D : Dag N} {f : ℕ} {p : Fin N} : p ∈ D.alive f ↔ D.val (pt p) f = true := by
  unfold Dag.alive
  simp
theorem alive_on_line (I : Fin N → Fin N → Prop) (D : Dag N) {g : ℕ} {w : Fin N}
    (h : D.val (testInput I {w}) g = false) {q : Fin N} (hq : q ∈ D.alive g) : I q w := by
  by_contra hqw
  have hle : pt q ≤ testInput I {w} := by
    unfold pt
    apply inp_le
    · intro p hp
      rw [Finset.mem_singleton] at hp
      subst hp
      rw [testInput_castAdd]
      intro l hl
      rw [Finset.mem_singleton] at hl
      subst hl
      exact hqw
    · intro l hl
      simp at hl
  have := Api.api_val_mono D g hle
  rw [mem_alive.1 hq, h] at this
  exact absurd this (by decide)
theorem line_unique (I : Fin N → Fin N → Prop) (hI : NoRect I) (D : Dag N) {g : ℕ}
    (h2 : 2 ≤ (D.alive g).card) {w w' : Fin N} (h : D.val (testInput I {w}) g = false)
    (h' : D.val (testInput I {w'}) g = false) : w = w' := by
  by_contra hne
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by omega : 1 < (D.alive g).card)
  exact hI a b w w' hab hne ⟨alive_on_line I D h ha, alive_on_line I D h' ha,
    alive_on_line I D h hb, alive_on_line I D h' hb⟩
theorem leSum_of (I : Fin N → Fin N → Prop) (D : Dag N) {f : ℕ} {w : Fin N}
    (hd : D.deg f = 0) (h : D.val (testInput I {w}) f = false) : D.LeSum I f w := by
  classical
  intro z hz
  by_contra hno
  push_neg at hno
  let z' : Fin (N + N) → Bool := inp (Finset.univ.filter (fun q => z (Fin.castAdd N q) = true)) ∅
  have heq : D.val z f = D.val z' f := by
    apply Api.api_val_xonly D hd
    intro q
    simp only [z', inp_castAdd, Finset.mem_filter, Finset.mem_univ, true_and]
    cases z (Fin.castAdd N q) <;> rfl
  have hle : z' ≤ testInput I {w} := by
    apply inp_le
    · intro q hq
      rw [Finset.mem_filter] at hq
      rw [testInput_castAdd]
      intro l hl
      rw [Finset.mem_singleton] at hl
      subst hl
      intro hql
      exact absurd hq.2 (by simp [hno q hql])
    · intro l hl
      simp at hl
  have := Api.api_val_mono D f hle
  rw [← heq, hz, h] at this
  exact absurd this (by decide)
theorem false_of_leSum (I : Fin N → Fin N → Prop) (D : Dag N) {f : ℕ} {w : Fin N}
    (h : D.LeSum I f w) : D.val (testInput I {w}) f = false := by
  by_contra hf
  rw [Bool.not_eq_false] at hf
  obtain ⟨q, hq, hz⟩ := h _ hf
  rw [testInput_castAdd] at hz
  exact hz w (Finset.mem_singleton_self w) hq
theorem mem_coneOf_reach {D : Dag N} {S : Finset ℕ} {i j : ℕ} (hi : i ∈ D.coneOf S)
    (hr : D.Reach i j) (hj : N + N ≤ j) (hj' : j < N + N + D.size) : j ∈ D.coneOf S := by
  classical
  unfold Dag.coneOf at hi ⊢
  simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
  obtain ⟨-, -, r, hr', hreach⟩ := hi
  exact ⟨hj', hj, r, hr', Relation.ReflTransGen.trans hreach hr⟩
theorem mem_rootCone {D : Dag N} {W : Finset (Fin N)} {R : Fin N → ℕ} {w : Fin N} (hw : w ∈ W)
    {j : ℕ} (hr : D.Reach (R w) j) (hj : N + N ≤ j) (hj' : j < N + N + D.size) :
    j ∈ D.rootCone W R := by
  classical
  unfold Dag.rootCone Dag.coneOf
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
  exact ⟨hj', hj, R w, ⟨w, hw, rfl⟩, hr⟩
theorem walk_two (D : Dag N) (p : Fin N) (x : Fin (N + N) → Bool) :
    ∀ f, D.val (pt p) f = true → D.val x f = false → 2 ≤ (D.alive f).card →
      ∃ g c, D.Reach f g ∧ D.Kid g c ∧ 2 ≤ (D.alive g).card ∧ D.alive c = {p} ∧
        D.val x g = false := by
  intro f
  induction f using Nat.strong_induction_on with
  | _ f ih =>
    intro h1 h0 h2
    obtain ⟨c, hk, hc1, hc0⟩ := exists_kid D (two_le_alive_gate D h2) h1 h0
    obtain ⟨_, _, _, hcf⟩ := id hk
    by_cases hc2 : 2 ≤ (D.alive c).card
    · obtain ⟨g, c', hr, hk', hg2, hc', hg0⟩ := ih c hcf hc1 hc0 hc2
      exact ⟨g, c', Relation.ReflTransGen.head hk hr, hk', hg2, hc', hg0⟩
    · exact ⟨f, c, Relation.ReflTransGen.refl, hk, h2, alive_eq_single D (mem_alive.2 hc1) hc2,
        h0⟩
open Classical in
theorem kid_points_card (D : Dag N) (g : ℕ) :
    (Finset.univ.filter (fun q : Fin N => ∃ c, D.Kid g c ∧ D.alive c = {q})).card ≤ 2 := by
  classical
  cases hg : D.gateAt g with
  | none =>
    have : Finset.univ.filter (fun q : Fin N => ∃ c, D.Kid g c ∧ D.alive c = {q}) = ∅ := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        iff_false, not_exists, not_and]
      intro c hk
      obtain ⟨g', hg', -⟩ := hk
      rw [hg] at hg'
      cases hg'
    rw [this]
    simp
  | some gg =>
    have hsub : Finset.univ.filter (fun q : Fin N => ∃ c, D.Kid g c ∧ D.alive c = {q}) ⊆
        gg.kids.toFinset.biUnion (fun c => if (D.alive c).card ≤ 1 then D.alive c else ∅) := by
      intro q hq
      rw [Finset.mem_filter] at hq
      obtain ⟨c, hk, hc⟩ := hq.2
      obtain ⟨g', hg', hcm, -⟩ := hk
      rw [hg] at hg'
      cases hg'
      rw [Finset.mem_biUnion]
      refine ⟨c, List.mem_toFinset.2 hcm, ?_⟩
      rw [hc]
      simp
    have hb := Finset.card_biUnion_le (s := gg.kids.toFinset)
      (t := fun c => if (D.alive c).card ≤ 1 then D.alive c else ∅)
    have hs : ∑ c ∈ gg.kids.toFinset,
        (if (D.alive c).card ≤ 1 then D.alive c else ∅).card ≤ ∑ _c ∈ gg.kids.toFinset, 1 := by
      apply Finset.sum_le_sum
      intro c _
      split_ifs with h
      · exact h
      · simp
    have hk : gg.kids.toFinset.card ≤ 2 := by
      refine le_trans (List.toFinset_card_le _) ?_
      cases gg <;> simp [G.kids]
    have := Finset.card_le_card hsub
    simp only [Finset.sum_const, smul_eq_mul, mul_one] at hs
    omega
theorem card10_e1 (I : Fin N → Fin N → Prop) (hI : NoRect I) (D : Dag N) (W : Finset (Fin N))
    (R : Fin N → ℕ) (hs : Dag.SoundPartialForm I D W R) :
    (D.e1Set I W R).card ≤ 2 * ((D.rootCone W R).filter (fun f => D.deg f = 0)).card := by
  classical
  let T : ℕ → Finset (Fin N × Fin N) := fun g =>
    (Finset.univ.filter (fun q : Fin N => ∃ c, D.Kid g c ∧ D.alive c = {q})) ×ˢ
      (Finset.univ.filter (fun w : Fin N =>
        D.val (testInput I {w}) g = false ∧ 2 ≤ (D.alive g).card))
  have hT : ∀ g, (T g).card ≤ 2 := by
    intro g
    rw [Finset.card_product]
    have h1 := kid_points_card D g
    have h2 : (Finset.univ.filter (fun w : Fin N =>
        D.val (testInput I {w}) g = false ∧ 2 ≤ (D.alive g).card)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      rw [Finset.mem_filter] at ha hb
      exact line_unique I hI D ha.2.2 ha.2.1 hb.2.1
    calc _ ≤ 2 * 1 := Nat.mul_le_mul h1 h2
      _ = 2 := rfl
  have hsub : D.e1Set I W R ⊆ ((D.rootCone W R).filter (fun f => D.deg f = 0)).biUnion T := by
    intro e he
    unfold Dag.e1Set at he
    rw [Finset.mem_filter] at he
    obtain ⟨hce, f, hf, hfd, hle, hp, h2⟩ := he
    have hf0 := false_of_leSum I D hle
    obtain ⟨g, c, hr, hk, hg2, hc, hg0⟩ := walk_two D e.1 _ f (mem_alive.1 hp) hf0 h2
    have hgd : D.deg g = 0 := by
      have := Api.api_reach_deg D hr
      omega
    obtain ⟨hgN, hgs⟩ := kid_gate hk
    rw [Finset.mem_biUnion]
    refine ⟨g, Finset.mem_filter.2 ⟨mem_coneOf_reach hf hr hgN hgs, hgd⟩, ?_⟩
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter]
    exact ⟨⟨Finset.mem_univ _, c, hk, hc⟩, Finset.mem_univ _, hg0, hg2⟩
  calc (D.e1Set I W R).card ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ g ∈ (D.rootCone W R).filter (fun f => D.deg f = 0), (T g).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _g ∈ (D.rootCone W R).filter (fun f => D.deg f = 0), 2 :=
        Finset.sum_le_sum (fun g _ => hT g)
    _ = 2 * ((D.rootCone W R).filter (fun f => D.deg f = 0)).card := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]
theorem path_len_pos {D : Dag N} {π : List ℕ} {a b : ℕ} (h : D.IsPath π a b) : 0 < π.length := by
  obtain ⟨hh, -, -⟩ := h
  cases π with
  | nil => simp at hh
  | cons _ _ => simp
theorem path_getD_mem {π : List ℕ} {k : ℕ} (hk : k < π.length) : π.getD k 0 ∈ π := by
  rw [List.getD_eq_getElem _ _ hk]
  exact List.getElem_mem hk
theorem path_head {D : Dag N} {π : List ℕ} {a b : ℕ} (h : D.IsPath π a b) : π.getD 0 0 = a := by
  obtain ⟨hh, -, -⟩ := h
  rw [List.getD_eq_getElem?_getD, ← List.head?_eq_getElem?, hh]
  rfl
theorem path_last {D : Dag N} {π : List ℕ} {a b : ℕ} (h : D.IsPath π a b) :
    π.getD (π.length - 1) 0 = b := by
  obtain ⟨-, hl, -⟩ := h
  rw [List.getD_eq_getElem?_getD, ← List.getLast?_eq_getElem?, hl]
  rfl
theorem getD_snoc_lt {π : List ℕ} {c k : ℕ} (hk : k < π.length) :
    (π ++ [c]).getD k 0 = π.getD k 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hk]
theorem getD_snoc_eq {π : List ℕ} {c : ℕ} : (π ++ [c]).getD π.length 0 = c := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]
  simp
theorem isPath_snoc {D : Dag N} {π : List ℕ} {a b c : ℕ} (hp : D.IsPath π a b)
    (hk : D.Kid b c) : D.IsPath (π ++ [c]) a c := by
  have hlen := path_len_pos hp
  have hlast := path_last hp
  obtain ⟨hh, -, hs⟩ := hp
  refine ⟨?_, by simp, ?_⟩
  · rw [List.head?_append, hh]
    rfl
  · intro k hk'
    simp only [List.length_append, List.length_singleton] at hk'
    by_cases h : k + 1 < π.length
    · rw [getD_snoc_lt (by omega), getD_snoc_lt h]
      exact hs k h
    · have hk1 : k + 1 = π.length := by omega
      rw [getD_snoc_lt (by omega), hk1, getD_snoc_eq]
      rw [show k = π.length - 1 by omega, hlast]
      exact hk
theorem labelsAlive_snoc {D : Dag N} {π : List ℕ} {a b c : ℕ} {x : Fin (N + N) → Bool}
    (hp : D.IsPath π a b) (hl : D.LabelsAlive π x)
    (hc : ∀ f, D.LabAnd b f c → D.val x f = true) : D.LabelsAlive (π ++ [c]) x := by
  have hlen := path_len_pos hp
  have hlast := path_last hp
  intro k f hk' hlab
  simp only [List.length_append, List.length_singleton] at hk'
  by_cases h : k + 1 < π.length
  · rw [getD_snoc_lt (by omega), getD_snoc_lt h] at hlab
    exact hl k f h hlab
  · have hk1 : k + 1 = π.length := by omega
    rw [getD_snoc_lt (by omega), hk1, getD_snoc_eq, show k = π.length - 1 by omega,
      hlast] at hlab
    exact hc f hlab
theorem ep_input {p w : Fin N} {i : ℕ} (hi : i < N + N) (h1 : ep p w ⟨i, hi⟩ = true)
    (h0 : pt p ⟨i, hi⟩ = false) : i = N + w.val := by
  by_cases hN : i < N
  · have : (⟨i, hi⟩ : Fin (N + N)) = Fin.castAdd N ⟨i, hN⟩ := rfl
    rw [this, ← pt_ep_points p w] at h1
    rw [this, h1] at h0
    cases h0
  · have : (⟨i, hi⟩ : Fin (N + N)) = Fin.natAdd N ⟨i - N, by omega⟩ := by
      ext
      simp only [Fin.natAdd_mk]
      omega
    rw [this] at h1
    unfold ep at h1
    rw [inp_natAdd, decide_eq_true_eq, Finset.mem_singleton] at h1
    have := congrArg Fin.val h1
    simp only at this
    omega
theorem edge_walk (D : Dag N) (p w : Fin N) : ∀ f, D.val (ep p w) f = true →
    D.val (pt p) f = false →
    ∃ π, D.IsPath π f (N + w.val) ∧ ∀ v ∈ π, D.val (ep p w) v = true ∧
      D.val (pt p) v = false ∧ D.Reach f v ∧ D.Reach v (N + w.val) := by
  intro f
  induction f using Nat.strong_induction_on with
  | _ f ih =>
    intro h1 h0
    by_cases hi : f < N + N
    · have h1' := h1
      have h0' := h0
      rw [Dag.val, dif_pos hi] at h1' h0'
      have hf := ep_input hi h1' h0'
      subst hf
      refine ⟨[N + w.val], Path.isPath_single D _, ?_⟩
      intro v hv
      rw [List.mem_singleton] at hv
      subst hv
      exact ⟨h1, h0, .refl, .refl⟩
    · obtain ⟨c, hk, hc1, hc0⟩ := exists_kid D (by omega) h1 h0
      obtain ⟨_, _, _, hcf⟩ := id hk
      obtain ⟨π, hπ, hv⟩ := ih c hcf hc1 hc0
      refine ⟨f :: π, Path.isPath_cons D hk hπ, ?_⟩
      intro v hv'
      rcases List.mem_cons.1 hv' with rfl | hv'
      · have hcm : c ∈ π := by
          obtain ⟨hh, -, -⟩ := hπ
          exact List.mem_of_mem_head? hh
        exact ⟨h1, h0, .refl, Relation.ReflTransGen.head hk (hv c hcm).2.2.2⟩
      · obtain ⟨a1, a2, a3, a4⟩ := hv v hv'
        exact ⟨a1, a2, Relation.ReflTransGen.head hk a3, a4⟩
theorem labAnd_val {D : Dag N} (hwf : D.WF) {e f v : ℕ} (h : D.LabAnd e f v)
    (x : Fin (N + N) → Bool) : D.val x e = (D.val x f && D.val x v) := by
  rcases h.1 with hg | hg
  · exact val_and hg (hwf _ _ hg f (by simp [G.kids])) (hwf _ _ hg v (by simp [G.kids])) x
  · rw [val_and hg (hwf _ _ hg v (by simp [G.kids])) (hwf _ _ hg f (by simp [G.kids])) x,
      Bool.and_comm]
theorem labAnd_kid {D : Dag N} (hwf : D.WF) {e f v : ℕ} (h : D.LabAnd e f v) : D.Kid e f := by
  rcases h.1 with hg | hg
  · exact ⟨_, hg, by simp [G.kids], hwf _ _ hg f (by simp [G.kids])⟩
  · exact ⟨_, hg, by simp [G.kids], hwf _ _ hg f (by simp [G.kids])⟩
theorem step_cases {D : Dag N} (hwf : D.WF) {v c : ℕ} (hk : D.Kid v c) (hv : D.deg v = 1)
    (hc : D.deg c = 1) :
    (∀ x, D.val x c = true → D.val x v = true) ∨ ∃ f, D.LabAnd v f c := by
  obtain ⟨g, hg, hcm, -⟩ := hk
  cases g with
  | and a b =>
    have ha := hwf _ _ hg a (by simp [G.kids])
    have hb := hwf _ _ hg b (by simp [G.kids])
    rw [deg_and hg ha hb] at hv
    simp only [G.kids, List.mem_cons, List.not_mem_nil, or_false] at hcm
    right
    rcases hcm with rfl | rfl
    · exact ⟨b, Or.inr hg, by omega, hc⟩
    · exact ⟨a, Or.inl hg, by omega, hc⟩
  | or a b =>
    have ha := hwf _ _ hg a (by simp [G.kids])
    have hb := hwf _ _ hg b (by simp [G.kids])
    left
    intro x hx
    rw [val_or hg ha hb x]
    simp only [G.kids, List.mem_cons, List.not_mem_nil, or_false] at hcm
    rcases hcm with rfl | rfl <;> simp [hx]
  | cst _ => simp [G.kids] at hcm
theorem card11_cover (I : Fin N → Fin N → Prop) (D : Dag N) (W : Finset (Fin N))
    (R : Fin N → ℕ) (hs : Dag.SoundPartialForm I D W R) :
    D.countedEdges W R ⊆
      D.e0Set W R ∪ D.e1Set I W R ∪ D.alphaEdges I W R ∪ D.betaEdges I W R := by
  classical
  obtain ⟨hwf, hdeg, hsound⟩ := hs
  intro e he
  have he' := he
  unfold Dag.countedEdges at he'
  rw [Finset.mem_filter] at he'
  obtain ⟨-, hw, hep⟩ := he'
  obtain ⟨p, w⟩ := e
  dsimp only at hw hep
  simp only [Finset.mem_union]
  by_cases h0 : D.val (pt p) (R w) = true
  · left; left; left
    unfold Dag.e0Set
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hw, h0⟩
  rw [Bool.not_eq_true] at h0
  obtain ⟨π, hπ, hv⟩ := edge_walk D p w (R w) hep h0
  have hdeg1 : ∀ v ∈ π, D.deg v = 1 := by
    intro v hv'
    obtain ⟨-, -, r1, r2⟩ := hv v hv'
    have a1 := Api.api_reach_deg D r1
    have a2 := Api.api_reach_deg D r2
    have a3 := hdeg w hw
    rw [deg_line] at a2
    omega
  have hlen := path_len_pos hπ
  by_cases hlab : ∃ k f, k + 1 < π.length ∧ D.LabAnd (π.getD k 0) f (π.getD (k + 1) 0) ∧
      D.val (testInput I {w}) f = false
  swap
  · exfalso
    push_neg at hlab
    have hall : ∀ m k, k + m + 1 = π.length →
        D.val (testInput I {w}) (π.getD k 0) = true := by
      intro m
      induction m with
      | zero =>
        intro k hk
        rw [show k = π.length - 1 by omega, path_last hπ, val_line, testInput_natAdd]
        exact Finset.mem_singleton_self w
      | succ m ih =>
        intro k hk
        have h1 := ih (k + 1) (by omega)
        have hk' : k + 1 < π.length := by omega
        have hkid := hπ.2.2 k hk'
        rcases step_cases hwf hkid (hdeg1 _ (path_getD_mem (by omega)))
            (hdeg1 _ (path_getD_mem hk')) with h | ⟨f, hf⟩
        · exact h _ h1
        · rw [labAnd_val hwf hf, h1, Bool.and_true]
          have := hlab k f hk' hf
          simpa using this
    have hR := hall (π.length - 1) 0 (by omega)
    rw [path_head hπ] at hR
    have hy : testInput I {w} (Fin.natAdd N w) = true := by
      rw [testInput_natAdd]
      exact Finset.mem_singleton_self w
    obtain ⟨q, l, hql, hq, hl⟩ := hsound (testInput I {w}) ⟨w, hw, hy, hR⟩
    rw [testInput_natAdd] at hl
    rw [testInput_castAdd] at hq
    exact hq l hl hql
  obtain ⟨k, f, hk, hlabk, hf0⟩ := hlab
  have hfd : D.deg f = 0 := hlabk.2.1
  have hvk := hv _ (path_getD_mem (by omega : k < π.length))
  have hfep : D.val (ep p w) f = true := by
    have := hvk.1
    rw [labAnd_val hwf hlabk, Bool.and_eq_true] at this
    exact this.1
  have hfpt : D.val (pt p) f = true := by
    rw [Api.api_val_xonly D hfd (pt_ep_points p w)]
    exact hfep
  by_cases h2 : 2 ≤ (D.alive f).card
  · left; left; right
    have hkf := labAnd_kid hwf hlabk
    have hr : D.Reach (R w) f := Relation.ReflTransGen.tail hvk.2.2.1 hkf
    obtain ⟨-, hes⟩ := kid_gate hkf
    obtain ⟨_, _, _, hfe⟩ := id hkf
    unfold Dag.e1Set
    rw [Finset.mem_filter]
    exact ⟨he, f, mem_rootCone hw hr (two_le_alive_gate D h2) (by omega), hfd,
      leSum_of I D hfd hf0, mem_alive.2 hfpt, h2⟩
  have hpg : D.PGateAt p π k := ⟨hk, f, hlabk, alive_eq_single D (mem_alive.2 hfpt) h2⟩
  have hex : ∃ k, D.PGateAt p π k := ⟨k, hpg⟩
  have hk0 : D.PGateAt p π (Nat.find hex) := Nat.find_spec hex
  have hmin : ∀ k' < Nat.find hex, ¬ D.PGateAt p π k' := fun k' h => Nat.find_min hex h
  have hEP : D.EdgePath R p w π := ⟨hπ, fun v hv' => ⟨(hv v hv').1, (hv v hv').2.1⟩⟩
  by_cases hb : D.IsBeta I W R p (π.getD (Nat.find hex + 1) 0)
  · right
    have hk1 : D.PGateAt p π (Nat.findGreatest (fun k => D.PGateAt p π k) π.length) :=
      Nat.findGreatest_spec (m := Nat.find hex) (by have := hk0.1; omega) hk0
    have hmax : ∀ k', Nat.findGreatest (fun k => D.PGateAt p π k) π.length < k' →
        ¬ D.PGateAt p π k' := by
      intro k' hlt hk'
      have := hk'.1
      exact Nat.findGreatest_is_greatest hlt (by omega) hk'
    have hle : Nat.find hex ≤ Nat.findGreatest (fun k => D.PGateAt p π k) π.length :=
      Nat.find_min' hex hk1
    have hprop : ∀ j, Nat.find hex + 1 ≤ j → j < π.length →
        D.IsBeta I W R p (π.getD j 0) := by
      intro j hj
      induction j, hj using Nat.le_induction with
      | base => intro _; exact hb
      | succ j hj ih =>
        intro hjl
        obtain ⟨u, hu, hoff, π', hπ', hla⟩ := ih (by omega)
        have hkid := hπ.2.2 j hjl
        refine ⟨u, hu, hoff, π' ++ [π.getD (j + 1) 0], isPath_snoc hπ' hkid,
          labelsAlive_snoc hπ' hla ?_⟩
        intro f' hf'
        have h1 := (hv _ (path_getD_mem (by omega : j < π.length))).1
        rw [labAnd_val hwf hf', Bool.and_eq_true] at h1
        rw [Api.api_val_xonly D hf'.2.1 (pt_ep_points p w)]
        exact h1.1
    unfold Dag.betaEdges
    rw [Finset.mem_filter]
    exact ⟨he, π, hEP, _, hk1, hmax, hprop _ (by omega) hk1.1⟩
  · left; right
    unfold Dag.alphaEdges
    rw [Finset.mem_filter]
    exact ⟨he, π, hEP, Nat.find hex, hk0, hmin, hb⟩
theorem inp_mono {P S S' : Finset (Fin N)} (h : S ⊆ S') : inp P S ≤ inp P S' := by
  apply inp_le
  · intro p hp
    rw [inp_castAdd]
    simpa using hp
  · intro l hl
    rw [inp_natAdd]
    simpa using h hl
theorem bool_true_le {b : Bool} (h : true ≤ b) : b = true := by
  revert h
  cases b <;> decide
theorem exists_few_lines (D : Dag N) (x : Fin (N + N) → Bool) : ∀ i, D.val x i = true →
    ∃ S : Finset (Fin N), S.card ≤ D.deg i ∧ (∀ l ∈ S, x (Fin.natAdd N l) = true) ∧
      D.val (inp (Finset.univ.filter (fun q => x (Fin.castAdd N q) = true)) S) i = true := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro h
    by_cases hi : i < N + N
    · by_cases hN : i < N
      · obtain ⟨p, rfl⟩ : ∃ p : Fin N, p.val = i := ⟨⟨i, hN⟩, rfl⟩
        rw [val_point] at h
        refine ⟨∅, by simp, by simp, ?_⟩
        rw [val_point, inp_castAdd]
        simpa using h
      · obtain ⟨l, rfl⟩ : ∃ l : Fin N, N + l.val = i := ⟨⟨i - N, by omega⟩, by simp; omega⟩
        rw [val_line] at h
        refine ⟨{l}, by rw [deg_line]; simp, ?_, ?_⟩
        · intro l' hl'
          rw [Finset.mem_singleton] at hl'
          subst hl'
          exact h
        · rw [val_line, inp_natAdd]
          simp
    · rw [Dag.val, dif_neg hi] at h
      cases hg : D.gates[i - (N + N)]? with
      | none => rw [hg] at h; simp at h
      | some g =>
        have hga := gateAt_of_get (by omega) hg
        rw [hg] at h
        cases g with
        | and a b =>
          dsimp only at h
          rw [Bool.and_eq_true] at h
          obtain ⟨ha, hb⟩ := h
          split_ifs at ha with hax
          split_ifs at hb with hbx
          obtain ⟨Sa, hSa, hla, hva⟩ := ih a hax ha
          obtain ⟨Sb, hSb, hlb, hvb⟩ := ih b hbx hb
          refine ⟨Sa ∪ Sb, ?_, ?_, ?_⟩
          · rw [deg_and hga hax hbx]
            exact le_trans (Finset.card_union_le _ _) (by omega)
          · intro l hl
            rcases Finset.mem_union.1 hl with hl | hl
            · exact hla l hl
            · exact hlb l hl
          · rw [val_and hga hax hbx, Bool.and_eq_true]
            constructor
            · have m := Api.api_val_mono D a
                (inp_mono (P := Finset.univ.filter (fun q => x (Fin.castAdd N q) = true))
                  (S := Sa) (S' := Sa ∪ Sb) Finset.subset_union_left)
              rw [hva] at m
              exact bool_true_le m
            · have m := Api.api_val_mono D b
                (inp_mono (P := Finset.univ.filter (fun q => x (Fin.castAdd N q) = true))
                  (S := Sb) (S' := Sa ∪ Sb) Finset.subset_union_right)
              rw [hvb] at m
              exact bool_true_le m
        | or a b =>
          dsimp only at h
          rw [Bool.or_eq_true] at h
          rcases h with ha | hb
          · split_ifs at ha with hax
            obtain ⟨Sa, hSa, hla, hva⟩ := ih a hax ha
            refine ⟨Sa, ?_, hla, ?_⟩
            · have : D.deg a ≤ D.deg i := Api.deg_kid ⟨_, hga, by simp [G.kids], hax⟩
              omega
            · rw [Dag.val, dif_neg hi, hg]
              dsimp only
              rw [dif_pos hax, hva]
              rfl
          · split_ifs at hb with hbx
            obtain ⟨Sb, hSb, hlb, hvb⟩ := ih b hbx hb
            refine ⟨Sb, ?_, hlb, ?_⟩
            · have : D.deg b ≤ D.deg i := Api.deg_kid ⟨_, hga, by simp [G.kids], hbx⟩
              omega
            · rw [Dag.val, dif_neg hi, hg]
              dsimp only
              rw [dif_pos hbx, hvb]
              simp
        | cst v =>
          dsimp only at h
          refine ⟨∅, by simp, by simp, ?_⟩
          rw [Dag.val, dif_neg hi, hg]
          exact h
open Classical in
noncomputable def cleanGate (I : Fin N → Fin N → Prop) (D : Dag N) : G → G
  | .and a b =>
      if D.deg a = 0 ∧ D.deg b = 1 ∧ D.deadSets I 2 a = ∅ then .or b b
      else if D.deg b = 0 ∧ D.deg a = 1 ∧ D.deadSets I 2 b = ∅ then .or a a else .and a b
  | .or a b => .or a b
  | .cst v => .cst v
noncomputable def cleanDag (I : Fin N → Fin N → Prop) (D : Dag N) : Dag N :=
  ⟨D.gates.map (cleanGate I D), D.out⟩
theorem cleanGate_and (I : Fin N → Fin N → Prop) (D : Dag N) (a b : ℕ) :
    (D.deg a = 0 ∧ D.deg b = 1 ∧ D.deadSets I 2 a = ∅ ∧
      cleanGate I D (.and a b) = .or b b) ∨
    (D.deg b = 0 ∧ D.deg a = 1 ∧ D.deadSets I 2 b = ∅ ∧
      cleanGate I D (.and a b) = .or a a) ∨
    (¬ (D.deg a = 0 ∧ D.deg b = 1 ∧ D.deadSets I 2 a = ∅) ∧
      ¬ (D.deg b = 0 ∧ D.deg a = 1 ∧ D.deadSets I 2 b = ∅) ∧
      cleanGate I D (.and a b) = .and a b) := by
  by_cases h1 : D.deg a = 0 ∧ D.deg b = 1 ∧ D.deadSets I 2 a = ∅
  · left
    exact ⟨h1.1, h1.2.1, h1.2.2, by rw [cleanGate, if_pos h1]⟩
  · by_cases h2 : D.deg b = 0 ∧ D.deg a = 1 ∧ D.deadSets I 2 b = ∅
    · right; left
      exact ⟨h2.1, h2.2.1, h2.2.2, by rw [cleanGate, if_neg h1, if_pos h2]⟩
    · right; right
      exact ⟨h1, h2, by rw [cleanGate, if_neg h1, if_neg h2]⟩
theorem clean_get (I : Fin N → Fin N → Prop) (D : Dag N) (j : ℕ) :
    (cleanDag I D).gates[j]? = (D.gates[j]?).map (cleanGate I D) := by
  simp [cleanDag]
theorem clean_size (I : Fin N → Fin N → Prop) (D : Dag N) : (cleanDag I D).size = D.size := by
  simp [cleanDag, Dag.size]
theorem clean_gateAt (I : Fin N → Fin N → Prop) (D : Dag N) (i : ℕ) :
    (cleanDag I D).gateAt i = (D.gateAt i).map (cleanGate I D) := by
  unfold Dag.gateAt
  split_ifs
  · exact clean_get I D _
  · rfl
theorem cleanGate_kids (I : Fin N → Fin N → Prop) (D : Dag N) (g : G) :
    ∀ c ∈ (cleanGate I D g).kids, c ∈ g.kids := by
  intro c hc
  cases g with
  | and a b =>
    rcases cleanGate_and I D a b with ⟨-, -, -, e⟩ | ⟨-, -, -, e⟩ | ⟨-, -, e⟩ <;>
      rw [e] at hc <;> simp_all [G.kids]
  | or a b => simpa [cleanGate] using hc
  | cst v => simp [cleanGate, G.kids] at hc
theorem clean_kid {I : Fin N → Fin N → Prop} {D : Dag N} {i c : ℕ}
    (h : (cleanDag I D).Kid i c) : D.Kid i c := by
  obtain ⟨g', hg', hc, hlt⟩ := h
  rw [clean_gateAt, Option.map_eq_some_iff] at hg'
  obtain ⟨g, hg, rfl⟩ := hg'
  exact ⟨g, hg, cleanGate_kids I D g c hc, hlt⟩
theorem clean_reach {I : Fin N → Fin N → Prop} {D : Dag N} {i j : ℕ}
    (h : (cleanDag I D).Reach i j) : D.Reach i j := by
  induction h with
  | refl => exact .refl
  | tail _ hk ih => exact Relation.ReflTransGen.tail ih (clean_kid hk)
theorem clean_deg (I : Fin N → Fin N → Prop) (D : Dag N) (i : ℕ) :
    (cleanDag I D).deg i = D.deg i := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    have hg : ∀ a, (if _ : a < i then (cleanDag I D).deg a else 0) =
        (if _ : a < i then D.deg a else 0) := by
      intro a
      split_ifs with h
      · exact ih a h
      · rfl
    conv_lhs => rw [Dag.deg]
    conv_rhs => rw [Dag.deg]
    by_cases hi : i < N + N
    · rw [if_pos hi, if_pos hi]
    · rw [if_neg hi, if_neg hi, clean_get]
      cases hgi : D.gates[i - (N + N)]? with
      | none => rfl
      | some g =>
        cases g with
        | and a b =>
          rw [Option.map_some]
          rcases cleanGate_and I D a b with ⟨h1, -, -, e⟩ | ⟨h1, -, -, e⟩ | ⟨-, -, e⟩ <;>
            rw [e] <;> dsimp only
          · simp only [hg, max_self]
            split_ifs <;> simp [h1]
          · simp only [hg, max_self]
            split_ifs <;> simp [h1]
          · simp only [hg]
        | or a b => simp only [Option.map_some, cleanGate, hg]
        | cst v => simp only [Option.map_some, cleanGate]
theorem band_le_bor_right : ∀ a b c : Bool, b ≤ c → (a && b) ≤ (c || c) := by decide
theorem band_le_bor_left : ∀ a b c : Bool, a ≤ c → (a && b) ≤ (c || c) := by decide
theorem clean_val_ge (I : Fin N → Fin N → Prop) (D : Dag N) (x : Fin (N + N) → Bool)
    (i : ℕ) : D.val x i ≤ (cleanDag I D).val x i := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    have hd : ∀ a, (if _ : a < i then D.val x a else false) ≤
        (if _ : a < i then (cleanDag I D).val x a else false) := by
      intro a
      split_ifs with h
      · exact ih a h
      · exact le_rfl
    conv_lhs => rw [Dag.val]
    conv_rhs => rw [Dag.val]
    by_cases hi : i < N + N
    · rw [dif_pos hi, dif_pos hi]
    · rw [dif_neg hi, dif_neg hi, clean_get]
      cases hgi : D.gates[i - (N + N)]? with
      | none => exact le_rfl
      | some g =>
        cases g with
        | and a b =>
          rw [Option.map_some]
          rcases cleanGate_and I D a b with ⟨-, -, -, e⟩ | ⟨-, -, -, e⟩ | ⟨-, -, e⟩ <;>
            rw [e] <;> dsimp only
          · exact band_le_bor_right _ _ _ (hd b)
          · exact band_le_bor_left _ _ _ (hd a)
          · exact Api.band_mono _ _ _ _ (hd a) (hd b)
        | or a b =>
          simp only [Option.map_some, cleanGate]
          exact Api.bor_mono _ _ _ _ (hd a) (hd b)
        | cst v => simp only [Option.map_some, cleanGate]; exact le_rfl
theorem never_dead {I : Fin N → Fin N → Prop} {D : Dag N} {a : ℕ} (h : D.deadSets I 2 a = ∅)
    {S : Finset (Fin N)} (hS : S.card ≤ 2) : D.val (testInput I S) a = true := by
  classical
  by_contra hc
  rw [Bool.not_eq_true] at hc
  have : S ∈ D.deadSets I 2 a := by
    unfold Dag.deadSets
    simp [hS, hc]
  rw [h] at this
  simp at this
theorem clean_val_test (I : Fin N → Fin N → Prop) (D : Dag N) (hwf : D.WF)
    {S : Finset (Fin N)} (hS : S.card ≤ 2) (i : ℕ) :
    (cleanDag I D).val (testInput I S) i = D.val (testInput I S) i := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    have hd : ∀ a, (if _ : a < i then (cleanDag I D).val (testInput I S) a else false) =
        (if _ : a < i then D.val (testInput I S) a else false) := by
      intro a
      split_ifs with h
      · exact ih a h
      · rfl
    conv_lhs => rw [Dag.val]
    conv_rhs => rw [Dag.val]
    by_cases hi : i < N + N
    · rw [dif_pos hi, dif_pos hi]
    · rw [dif_neg hi, dif_neg hi, clean_get]
      cases hgi : D.gates[i - (N + N)]? with
      | none => rfl
      | some g =>
        have hga := gateAt_of_get (by omega) hgi
        cases g with
        | and a b =>
          have ha := hwf _ _ hga a (by simp [G.kids])
          have hb := hwf _ _ hga b (by simp [G.kids])
          rw [Option.map_some]
          rcases cleanGate_and I D a b with ⟨-, -, h3, e⟩ | ⟨-, -, h3, e⟩ | ⟨-, -, e⟩ <;>
            rw [e] <;> dsimp only
          · simp only [hd, dif_pos ha, dif_pos hb, never_dead h3 hS]
            simp
          · simp only [hd, dif_pos ha, dif_pos hb, never_dead h3 hS]
            simp
          · simp only [hd, dif_pos ha, dif_pos hb]
        | or a b => simp only [Option.map_some, cleanGate, hd]
        | cst v => simp only [Option.map_some, cleanGate]
theorem clean_deadSets (I : Fin N → Fin N → Prop) (D : Dag N) (hwf : D.WF) (f : ℕ) :
    (cleanDag I D).deadSets I 2 f = D.deadSets I 2 f := by
  classical
  unfold Dag.deadSets
  apply Finset.filter_congr
  intro S _
  constructor
  · rintro ⟨h, h'⟩
    exact ⟨h, by rwa [clean_val_test I D hwf h] at h'⟩
  · rintro ⟨h, h'⟩
    exact ⟨h, by rwa [clean_val_test I D hwf h]⟩
theorem card09_form_clean (I : Fin N → Fin N → Prop) (D : Dag N) (W : Finset (Fin N))
    (R : Fin N → ℕ) (hs : Dag.SoundPartialForm I D W R) :
    ∃ D' : Dag N, Dag.SoundPartialForm I D' W R ∧
      (D'.rootCone W R).card ≤ (D.rootCone W R).card ∧
      D.countedEdges W R ⊆ D'.countedEdges W R ∧ D'.Cleaned I (D'.rootCone W R) := by
  classical
  obtain ⟨hwf, hdeg, hsound⟩ := hs
  refine ⟨cleanDag I D, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro i g hg c hc
    rw [clean_gateAt, Option.map_eq_some_iff] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    exact hwf i g0 hg0 c (cleanGate_kids I D g0 c hc)
  · intro w hw
    rw [clean_deg]
    exact hdeg w hw
  · rintro z ⟨w, hw, hzw, hval⟩
    by_contra hno
    push_neg at hno
    obtain ⟨S, hSc, hSl, hSv⟩ := exists_few_lines (cleanDag I D) z (R w) hval
    rw [clean_deg] at hSc
    have hd1 := hdeg w hw
    have hcard : (insert w S).card ≤ 2 := le_trans (Finset.card_insert_le _ _) (by omega)
    have hle : inp (Finset.univ.filter (fun q => z (Fin.castAdd N q) = true)) (insert w S) ≤
        testInput I (insert w S) := by
      apply inp_le
      · intro q hq
        rw [Finset.mem_filter] at hq
        rw [testInput_castAdd]
        intro l hl hql
        have hzl : z (Fin.natAdd N l) = true := by
          rcases Finset.mem_insert.1 hl with rfl | hl
          · exact hzw
          · exact hSl l hl
        exact hno q l hql hq.2 hzl
      · intro l hl
        rw [testInput_natAdd]
        exact hl
    have h1 := Api.api_val_mono (cleanDag I D) (R w) (le_trans (inp_mono (Finset.subset_insert w S)) hle)
    rw [hSv, clean_val_test I D hwf hcard] at h1
    have h2 := bool_true_le h1
    obtain ⟨q, l, hql, hq, hl⟩ := hsound _
      ⟨w, hw, by rw [testInput_natAdd]; exact Finset.mem_insert_self w S, h2⟩
    rw [testInput_castAdd] at hq
    rw [testInput_natAdd] at hl
    exact hq l hl hql
  · apply Finset.card_le_card
    intro i hi
    unfold Dag.rootCone Dag.coneOf at hi ⊢
    simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
    obtain ⟨h1, h2, r, hr, hreach⟩ := hi
    rw [clean_size] at h1
    exact ⟨h1, h2, r, hr, clean_reach hreach⟩
  · intro e he
    unfold Dag.countedEdges at he ⊢
    rw [Finset.mem_filter] at he ⊢
    refine ⟨he.1, he.2.1, ?_⟩
    have := clean_val_ge I D (ep e.1 e.2) (R e.2)
    rw [he.2.2] at this
    exact bool_true_le this
  · intro e _ f v hlab
    obtain ⟨hg, hf, hv⟩ := hlab
    rw [clean_deg] at hf hv
    rw [clean_deadSets I D hwf]
    rw [clean_gateAt] at hg
    rcases hg with hg | hg <;> obtain ⟨g0, -, hc⟩ := Option.map_eq_some_iff.1 hg
    · cases g0 with
      | and a b =>
        simp only [cleanGate] at hc
        split_ifs at hc with h1 h2 <;> cases hc
        intro hde
        exact h1 ⟨hf, hv, hde⟩
      | or a b => simp [cleanGate] at hc
      | cst _ => simp [cleanGate] at hc
    · cases g0 with
      | and a b =>
        simp only [cleanGate] at hc
        split_ifs at hc with h1 h2 <;> cases hc
        intro hde
        exact h2 ⟨hf, hv, hde⟩
      | or a b => simp [cleanGate] at hc
      | cst _ => simp [cleanGate] at hc
end Deg2.Forms
namespace Deg2
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
variable {N : ℕ}
theorem tr_val_and {D : Dag N} {h a b : ℕ} (hg : D.gateAt h = some (.and a b)) (ha : a < h)
    (hb : b < h) (x : Fin (N + N) → Bool) : D.val x h = (D.val x a && D.val x b) := by
  obtain ⟨hh, hg⟩ := Api.gateAt_some hg
  conv_lhs => rw [Dag.val]
  rw [dif_neg (by omega), hg]
  dsimp only
  rw [dif_pos ha, dif_pos hb]
theorem tr_val_or {D : Dag N} {h a b : ℕ} (hg : D.gateAt h = some (.or a b)) (ha : a < h)
    (hb : b < h) (x : Fin (N + N) → Bool) : D.val x h = (D.val x a || D.val x b) := by
  obtain ⟨hh, hg⟩ := Api.gateAt_some hg
  conv_lhs => rw [Dag.val]
  rw [dif_neg (by omega), hg]
  dsimp only
  rw [dif_pos ha, dif_pos hb]
theorem tr_deg_and {D : Dag N} {h a b : ℕ} (hg : D.gateAt h = some (.and a b)) (ha : a < h)
    (hb : b < h) : D.deg h = D.deg a + D.deg b := by
  obtain ⟨hh, hg⟩ := Api.gateAt_some hg
  conv_lhs => rw [Dag.deg]
  rw [if_neg (by omega), hg]
  dsimp only
  rw [dif_pos ha, dif_pos hb]
theorem tr_deg_or {D : Dag N} {h a b : ℕ} (hg : D.gateAt h = some (.or a b)) (ha : a < h)
    (hb : b < h) : D.deg h = max (D.deg a) (D.deg b) := by
  obtain ⟨hh, hg⟩ := Api.gateAt_some hg
  conv_lhs => rw [Dag.deg]
  rw [if_neg (by omega), hg]
  dsimp only
  rw [dif_pos ha, dif_pos hb]
theorem tr_deg_cst {D : Dag N} {h : ℕ} {v : Bool} (hg : D.gateAt h = some (.cst v)) :
    D.deg h = 0 := by
  obtain ⟨hh, hg⟩ := Api.gateAt_some hg
  rw [Dag.deg, if_neg (by omega), hg]
theorem tr_gate_of_deg {D : Dag N} {c : ℕ} (hd : 2 ≤ D.deg c) :
    ∃ g, D.gateAt c = some g ∧ c < N + N + D.size := by
  have hd' := hd
  rw [Dag.deg] at hd'
  by_cases hc : c < N + N
  · rw [if_pos hc] at hd'
    split_ifs at hd' <;> omega
  · rw [if_neg hc] at hd'
    cases hg : D.gates[c - (N + N)]? with
    | none => rw [hg] at hd'; simp at hd'
    | some g =>
      refine ⟨g, ?_, ?_⟩
      · unfold Dag.gateAt; rw [if_pos (by omega), hg]
      · have := (List.getElem?_eq_some_iff.1 hg).1
        unfold Dag.size; omega
theorem tr_kid_of {D : Dag N} {h c : ℕ} {g : G} (hg : D.gateAt h = some g) (hc : c ∈ g.kids)
    (hlt : c < h) : D.Kid h c := ⟨g, hg, hc, hlt⟩
theorem tr_top_reach {D : Dag N} {ok : ℕ → Prop} {c : ℕ} (h : D.Top ok c) :
    D.Reach D.out c := by
  induction h with
  | root => exact Relation.ReflTransGen.refl
  | @orStep h c _ _ hk _ ih => exact ih.tail hk
  | @andStep h f c _ _ hg _ _ _ hc _ ih =>
    rcases hg with hg | hg
    · exact ih.tail (tr_kid_of hg (by simp [G.kids]) hc)
    · exact ih.tail (tr_kid_of hg (by simp [G.kids]) hc)
theorem tr_top_mono {D : Dag N} {ok ok' : ℕ → Prop} (hok : ∀ f, D.deg f = 0 → ok f → ok' f)
    {c : ℕ} (h : D.Top ok c) : D.Top ok' c := by
  induction h with
  | root => exact Dag.Top.root
  | @orStep h c _ ht hk hd ih => exact Dag.Top.orStep ih ht hk hd
  | @andStep h f c _ ht hg hf hc2 hfh hch hokf ih =>
    exact Dag.Top.andStep ih ht hg hf hc2 hfh hch (hok f hf hokf)
theorem tr_top_val {D : Dag N} (hwf : D.WF) {x : Fin (N + N) → Bool} {c : ℕ}
    (h : D.Top (fun f => D.val x f = true) c) : D.val x c = true → D.val x D.out = true := by
  induction h with
  | root => exact id
  | @orStep h c _ ht hk _ ih =>
    classical
    intro hv
    apply ih
    obtain ⟨g, hg, hcg, hch⟩ := hk
    obtain ⟨-, a, b, hab⟩ := Finset.mem_filter.1 ht
    rw [hab] at hg
    cases hg
    have ha := hwf _ _ hab a (by simp [G.kids])
    have hb := hwf _ _ hab b (by simp [G.kids])
    rw [tr_val_or hab ha hb]
    simp only [G.kids, List.mem_cons, List.not_mem_nil, or_false] at hcg
    rcases hcg with rfl | rfl <;> simp [hv]
  | @andStep h f c _ _ hg _ _ hfh hch hokf ih =>
    intro hv
    apply ih
    rcases hg with hg | hg
    · rw [tr_val_and hg hfh hch]; simp [hv, hokf]
    · rw [tr_val_and hg hch hfh]; simp [hv, hokf]
theorem tr_mem_cone {D : Dag N} {c : ℕ} (h1 : N + N ≤ c) (h2 : c < N + N + D.size)
    (hr : D.Reach D.out c) : c ∈ D.cone := by
  classical
  unfold Dag.cone Dag.coneOf
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
  exact ⟨h2, h1, D.out, rfl, hr⟩
def tr_noLines (x : Fin (N + N) → Bool) : Fin (N + N) → Bool :=
  fun i => if (i : ℕ) < N then x i else false
theorem tr_noLines_pts (x : Fin (N + N) → Bool) (p : Fin N) :
    x (Fin.castAdd N p) = tr_noLines x (Fin.castAdd N p) := by
  simp [tr_noLines, Fin.coe_castAdd, p.isLt]
theorem tr_drop {D : Dag N} {I : Fin N → Fin N → Prop} (hwf : D.WF) (hc : Computes I D.fn)
    {x : Fin (N + N) → Bool} {c a : ℕ} (hT : D.Top (fun f => D.val x f = true) c)
    (ha0 : D.deg a = 0) (hva : D.val x a = true)
    (hup : D.val (tr_noLines x) a = true → D.val (tr_noLines x) c = true) : False := by
  have hx := tr_noLines_pts x
  have hT' : D.Top (fun f => D.val (tr_noLines x) f = true) c := by
    refine tr_top_mono ?_ hT
    intro f hf hv
    rw [← Api.api_val_xonly D hf hx]; exact hv
  have hva' : D.val (tr_noLines x) a = true := by
    rw [← Api.api_val_xonly D ha0 hx]; exact hva
  have hout := tr_top_val hwf hT' (hup hva')
  obtain ⟨p, l, -, -, hl⟩ := (hc (tr_noLines x)).1 hout
  simp [tr_noLines, Fin.coe_natAdd] at hl
theorem tr_descend {D : Dag N} {I : Fin N → Fin N → Prop} (hwf : D.WF) (hc : Computes I D.fn)
    (hd : D.deg D.out ≤ 2) (x : Fin (N + N) → Bool) :
    ∀ c, D.Top (fun f => D.val x f = true) c → D.val x c = true →
      ∃ b, D.IsItem b ∧ D.ctx b x = true ∧ ∀ r, D.IsFactor b r → D.val x r = true := by
  classical
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
  intro hT hv
  have hitem : D.Top (fun _ => True) c := tr_top_mono (fun _ _ _ => trivial) hT
  have hctx : D.ctx c x = true := by unfold Dag.ctx; exact decide_eq_true hT
  have hreach := tr_top_reach hT
  have hdc : D.deg c ≤ 2 := le_trans (Api.api_reach_deg D hreach) hd
  by_cases h1 : D.deg c ≤ 1
  · refine ⟨c, ⟨hitem, Or.inl h1⟩, hctx, ?_⟩
    intro r hr
    rcases hr with ⟨-, rfl⟩ | ⟨hm, -⟩
    · exact hv
    · have := (Finset.mem_filter.1 (Finset.mem_filter.1 hm).1).2; omega
  have h2 : D.deg c = 2 := by omega
  obtain ⟨g, hg, hlt⟩ := tr_gate_of_deg (D := D) (c := c) (by omega)
  have hge := (Api.gateAt_some hg).1
  have hcone := tr_mem_cone hge hlt hreach
  have hT2 : c ∈ D.T := Finset.mem_filter.2 ⟨hcone, h2⟩
  cases g with
  | cst v => rw [tr_deg_cst hg] at h2; omega
  | and a b =>
    have ha := hwf _ _ hg a (by simp [G.kids])
    have hb := hwf _ _ hg b (by simp [G.kids])
    have hdeg := tr_deg_and hg ha hb
    rw [tr_val_and hg ha hb, Bool.and_eq_true] at hv
    by_cases hab : D.deg a = 1 ∧ D.deg b = 1
    · have hmix : c ∈ D.Tmix := Finset.mem_filter.2 ⟨hT2, a, b, hg, hab⟩
      refine ⟨c, ⟨hitem, Or.inr hmix⟩, hctx, ?_⟩
      intro r hr
      rcases hr with ⟨h1', -⟩ | ⟨-, g', hg', hrg, -⟩
      · omega
      · rw [hg] at hg'; cases hg'
        simp only [G.kids, List.mem_cons, List.not_mem_nil, or_false] at hrg
        rcases hrg with rfl | rfl
        · exact hv.1
        · exact hv.2
    · have hf : D.deg a = 0 ∨ D.deg b = 0 := by omega
      have hTf : c ∈ D.Tandf := Finset.mem_filter.2 ⟨hT2, a, b, hg, hf⟩
      rcases hf with hf | hf
      · exact ih b hb (Dag.Top.andStep hT hTf (Or.inl hg) hf (by omega) ha hb hv.1) hv.2
      · exact ih a ha (Dag.Top.andStep hT hTf (Or.inr hg) hf (by omega) hb ha hv.2) hv.1
  | or a b =>
    have ha := hwf _ _ hg a (by simp [G.kids])
    have hb := hwf _ _ hg b (by simp [G.kids])
    have hTor : c ∈ D.Tor := Finset.mem_filter.2 ⟨hT2, a, b, hg⟩
    rw [tr_val_or hg ha hb, Bool.or_eq_true] at hv
    rcases hv with hv | hv
    · by_cases h0 : D.deg a = 0
      · exact (tr_drop hwf hc hT h0 hv (fun h => by rw [tr_val_or hg ha hb, h]; rfl)).elim
      · exact ih a ha (Dag.Top.orStep hT hTor (tr_kid_of hg (by simp [G.kids]) ha)
          (by omega)) hv
    · by_cases h0 : D.deg b = 0
      · exact (tr_drop hwf hc hT h0 hv
          (fun h => by rw [tr_val_or hg ha hb, h]; simp)).elim
      · exact ih b hb (Dag.Top.orStep hT hTor (tr_kid_of hg (by simp [G.kids]) hb)
          (by omega)) hv
theorem card15_identity (I : Fin N → Fin N → Prop) (D : Dag N) (hwf : D.WF)
    (hc : Computes I D.fn) (hd : D.deg D.out ≤ 2) (x : Fin (N + N) → Bool) :
    D.fn x = true ↔
      ∃ b, D.IsItem b ∧ D.ctx b x = true ∧ ∀ r, D.IsFactor b r → D.val x r = true := by
  classical
  constructor
  · intro h
    exact tr_descend hwf hc hd x D.out Dag.Top.root h
  · rintro ⟨b, ⟨-, hb⟩, hctx, hfac⟩
    have hT : D.Top (fun f => D.val x f = true) b := by
      unfold Dag.ctx at hctx; exact of_decide_eq_true hctx
    apply tr_top_val hwf hT
    rcases hb with hb | hb
    · exact hfac b (Or.inl ⟨hb, rfl⟩)
    · obtain ⟨-, a, a', hg, -, -⟩ := Finset.mem_filter.1 hb
      have ha := hwf _ _ hg a (by simp [G.kids])
      have ha' := hwf _ _ hg a' (by simp [G.kids])
      rw [tr_val_and hg ha ha', hfac a (Or.inr ⟨hb, tr_kid_of hg (by simp [G.kids]) ha⟩),
        hfac a' (Or.inr ⟨hb, tr_kid_of hg (by simp [G.kids]) ha'⟩)]
      rfl
end Deg2
namespace Deg2
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
variable {N : ℕ}
theorem tr_getElem?_prefix {gs gs' : List G} (hp : gs <+: gs') {i : ℕ} (hi : i < gs.length) :
    gs'[i]? = gs[i]? := by
  obtain ⟨t, rfl⟩ := hp
  exact List.getElem?_append_left hi
theorem tr_val_prefix {gs gs' : List G} (hp : gs <+: gs') (o o' : ℕ)
    (x : Fin (N + N) → Bool) : ∀ n, n < N + N + gs.length →
      (⟨gs', o'⟩ : Dag N).val x n = (⟨gs, o⟩ : Dag N).val x n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn
  have key : ∀ a, (if _ : a < n then (⟨gs', o'⟩ : Dag N).val x a else false) =
      (if _ : a < n then (⟨gs, o⟩ : Dag N).val x a else false) := by
    intro a
    split_ifs with ha
    · exact ih a ha (by omega)
    · rfl
  conv_lhs => rw [Dag.val]
  conv_rhs => rw [Dag.val]
  by_cases hi : n < N + N
  · rw [dif_pos hi, dif_pos hi]
  · rw [dif_neg hi, dif_neg hi]
    have hg : gs'[n - (N + N)]? = gs[n - (N + N)]? := tr_getElem?_prefix hp (by omega)
    dsimp only
    rw [hg]
    cases gs[n - (N + N)]? with
    | none => rfl
    | some g => cases g <;> first | rfl | simp only [key]
theorem tr_deg_prefix {gs gs' : List G} (hp : gs <+: gs') (o o' : ℕ) :
    ∀ n, n < N + N + gs.length → (⟨gs', o'⟩ : Dag N).deg n = (⟨gs, o⟩ : Dag N).deg n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn
  have key : ∀ a, (if _ : a < n then (⟨gs', o'⟩ : Dag N).deg a else 0) =
      (if _ : a < n then (⟨gs, o⟩ : Dag N).deg a else 0) := by
    intro a
    split_ifs with ha
    · exact ih a ha (by omega)
    · rfl
  conv_lhs => rw [Dag.deg]
  conv_rhs => rw [Dag.deg]
  by_cases hi : n < N + N
  · rw [if_pos hi, if_pos hi]
  · rw [if_neg hi, if_neg hi]
    have hg : gs'[n - (N + N)]? = gs[n - (N + N)]? := tr_getElem?_prefix hp (by omega)
    dsimp only
    rw [hg]
    cases gs[n - (N + N)]? with
    | none => rfl
    | some g => cases g <;> first | rfl | simp only [key]
theorem tr_gateAt_prefix {gs gs' : List G} (hp : gs <+: gs') (o o' : ℕ) {n : ℕ}
    (hn : n < N + N + gs.length) :
    (⟨gs', o'⟩ : Dag N).gateAt n = (⟨gs, o⟩ : Dag N).gateAt n := by
  unfold Dag.gateAt
  split_ifs with h
  · exact tr_getElem?_prefix hp (by omega)
  · rfl
theorem tr_gateAt_last (gs : List G) (g : G) (o : ℕ) :
    (⟨gs ++ [g], o⟩ : Dag N).gateAt (N + N + gs.length) = some g := by
  unfold Dag.gateAt
  rw [if_pos (by omega)]
  simp
inductive tr_W where
  | absent
  | const
  | wire (n : ℕ)
def tr_Good (D : Dag N) (len n : ℕ) : Prop :=
  n < N ∨ n ∈ D.X ∨ (N + N + D.size ≤ n ∧ n < N + N + len)
def tr_NewOK (D : Dag N) (gs : List G) : Prop :=
  D.gates <+: gs ∧ ∀ j g, D.size ≤ j → gs[j]? = some g →
    ∃ u v, (g = .and u v ∨ g = .or u v) ∧ tr_Good D j u ∧ tr_Good D j v
def tr_Ok (D : Dag N) (gs : List G) (m : tr_W) (P : (Fin (N + N) → Bool) → Prop)
    (PT : Prop) : Prop :=
  match m with
  | .absent => ¬ PT ∧ ∀ x, ¬ P x
  | .const => ∀ x, P x
  | .wire n => tr_Good D gs.length n ∧ ∀ x, ((⟨gs, D.out⟩ : Dag N).val x n = true ↔ P x)
theorem tr_X_lt {D : Dag N} {n : ℕ} (h : n ∈ D.X) : N + N ≤ n ∧ n < N + N + D.size := by
  have := Api.coneOf_sub D {D.out} (Finset.mem_filter.1 h).1
  exact Finset.mem_Ico.1 this
theorem tr_Good_mono {D : Dag N} {j len n : ℕ} (h : tr_Good D j n) (hj : j ≤ len) :
    tr_Good D len n := by
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨h.1, by omega⟩)
theorem tr_Good_lt {D : Dag N} {len n : ℕ} (h : tr_Good D len n) (hl : D.size ≤ len) :
    n < N + N + len := by
  rcases h with h | h | h
  · omega
  · have := tr_X_lt h; omega
  · exact h.2
theorem tr_NewOK_size {D : Dag N} {gs : List G} (h : tr_NewOK D gs) : D.size ≤ gs.length :=
  h.1.length_le
theorem tr_Ok_lift {D : Dag N} {gs gs' : List G} {m : tr_W} {P PT}
    (h : tr_Ok D gs m P PT) (hp : gs <+: gs') (hD : D.size ≤ gs.length) :
    tr_Ok D gs' m P PT := by
  cases m with
  | absent => exact h
  | const => exact h
  | wire n =>
    obtain ⟨hg, hv⟩ := h
    refine ⟨tr_Good_mono hg hp.length_le, fun x => ?_⟩
    rw [tr_val_prefix hp D.out D.out x n (tr_Good_lt hg hD)]
    exact hv x
theorem tr_Ok_congr {D : Dag N} {gs : List G} {m : tr_W} {P P' : (Fin (N + N) → Bool) → Prop}
    {PT PT' : Prop} (h : tr_Ok D gs m P PT) (hP : ∀ x, P x ↔ P' x) (hT : PT ↔ PT') :
    tr_Ok D gs m P' PT' := by
  cases m with
  | absent => exact ⟨fun h' => h.1 (hT.2 h'), fun x h' => h.2 x ((hP x).2 h')⟩
  | const => exact fun x => (hP x).1 (h x)
  | wire n => exact ⟨h.1, fun x => (h.2 x).trans (hP x)⟩
theorem tr_NewOK_append {D : Dag N} {gs : List G} (h : tr_NewOK D gs) {g : G} {a b : ℕ}
    (hg : g = .and a b ∨ g = .or a b) (ha : tr_Good D gs.length a)
    (hb : tr_Good D gs.length b) : tr_NewOK D (gs ++ [g]) := by
  refine ⟨h.1.trans (List.prefix_append gs [g]), fun j g' hj hg' => ?_⟩
  by_cases hjl : j < gs.length
  · rw [List.getElem?_append_left hjl] at hg'
    exact h.2 j g' hj hg'
  · by_cases hje : j = gs.length
    · subst hje
      simp at hg'
      subst hg'
      exact ⟨a, b, hg, ha, hb⟩
    · have : (gs ++ [g])[j]? = none := by
        rw [List.getElem?_eq_none_iff]; simp; omega
      rw [this] at hg'; cases hg'
def tr_merge (N : ℕ) (gs : List G) : tr_W → tr_W → List G × tr_W
  | .absent, m => (gs, m)
  | .const, _ => (gs, .const)
  | .wire a, .absent => (gs, .wire a)
  | .wire _, .const => (gs, .const)
  | .wire a, .wire b => (gs ++ [.or a b], .wire (N + N + gs.length))
theorem tr_merge_ok {D : Dag N} {gs : List G} (hN : tr_NewOK D gs) {u m : tr_W}
    {P Q PT QT} (hu : tr_Ok D gs u P PT) (hm : tr_Ok D gs m Q QT) :
    tr_NewOK D (tr_merge N gs u m).1 ∧ gs <+: (tr_merge N gs u m).1 ∧
      (tr_merge N gs u m).1.length ≤ gs.length + 1 ∧
      tr_Ok D (tr_merge N gs u m).1 (tr_merge N gs u m).2 (fun x => P x ∨ Q x) (PT ∨ QT) := by
  have hD := tr_NewOK_size hN
  cases u with
  | absent =>
    refine ⟨hN, List.prefix_refl gs, by simp [tr_merge], ?_⟩
    simp only [tr_merge]
    exact tr_Ok_congr hm (fun x => by simp [hu.2 x]) (by simp [hu.1])
  | const =>
    refine ⟨hN, List.prefix_refl gs, by simp [tr_merge], ?_⟩
    simp only [tr_merge]
    exact fun x => Or.inl (hu x)
  | wire a =>
    cases m with
    | absent =>
      refine ⟨hN, List.prefix_refl gs, by simp [tr_merge], ?_⟩
      simp only [tr_merge]
      exact tr_Ok_congr hu (fun x => by simp [hm.2 x]) (by simp [hm.1])
    | const =>
      refine ⟨hN, List.prefix_refl gs, by simp [tr_merge], ?_⟩
      simp only [tr_merge]
      exact fun x => Or.inr (hm x)
    | wire b =>
      simp only [tr_merge]
      have hp : gs <+: gs ++ [G.or a b] := List.prefix_append gs _
      refine ⟨tr_NewOK_append hN (Or.inr rfl) hu.1 hm.1, hp, by simp, ?_⟩
      have ha := tr_Good_lt hu.1 hD
      have hb := tr_Good_lt hm.1 hD
      refine ⟨Or.inr (Or.inr ⟨by omega, by simp⟩), fun x => ?_⟩
      rw [tr_val_or (tr_gateAt_last gs _ D.out) ha hb, tr_val_prefix hp D.out D.out x a ha,
        tr_val_prefix hp D.out D.out x b hb, Bool.or_eq_true, hu.2 x, hm.2 x]
def tr_msgAnd (N : ℕ) (gs : List G) (u : tr_W) (f : ℕ) : List G × tr_W :=
  match u with
  | .absent => (gs, .absent)
  | .const => (gs, .wire f)
  | .wire n => (gs ++ [.and n f], .wire (N + N + gs.length))
theorem tr_msgAnd_ok {D : Dag N} {gs : List G} (hN : tr_NewOK D gs) {u : tr_W} {P PT}
    (hu : tr_Ok D gs u P PT) {f : ℕ} (hf : f < N ∨ f ∈ D.X) :
    tr_NewOK D (tr_msgAnd N gs u f).1 ∧ gs <+: (tr_msgAnd N gs u f).1 ∧
      (tr_msgAnd N gs u f).1.length ≤ gs.length + 1 ∧
      tr_Ok D (tr_msgAnd N gs u f).1 (tr_msgAnd N gs u f).2
        (fun x => P x ∧ D.val x f = true) PT := by
  have hD := tr_NewOK_size hN
  have hfg : tr_Good D gs.length f := by
    rcases hf with hf | hf
    · exact Or.inl hf
    · exact Or.inr (Or.inl hf)
  have hfl := tr_Good_lt hfg hD
  have hfv : ∀ (gs' : List G), D.gates <+: gs' → ∀ x,
      (⟨gs', D.out⟩ : Dag N).val x f = D.val x f := by
    intro gs' hp x
    rcases hf with hf | hf
    · exact tr_val_prefix hp D.out D.out x f (by omega)
    · exact tr_val_prefix hp D.out D.out x f (tr_X_lt hf).2
  cases u with
  | absent =>
    refine ⟨hN, List.prefix_refl gs, by simp [tr_msgAnd], ?_⟩
    simp only [tr_msgAnd]
    exact ⟨hu.1, fun x h => hu.2 x h.1⟩
  | const =>
    refine ⟨hN, List.prefix_refl gs, by simp [tr_msgAnd], ?_⟩
    simp only [tr_msgAnd]
    refine ⟨hfg, fun x => ?_⟩
    rw [hfv gs hN.1 x]
    exact ⟨fun h => ⟨hu x, h⟩, fun h => h.2⟩
  | wire n =>
    simp only [tr_msgAnd]
    have hp : gs <+: gs ++ [G.and n f] := List.prefix_append gs _
    refine ⟨tr_NewOK_append hN (Or.inl rfl) hu.1 hfg, hp, by simp, ?_⟩
    have hn := tr_Good_lt hu.1 hD
    refine ⟨Or.inr (Or.inr ⟨by omega, by simp⟩), fun x => ?_⟩
    rw [tr_val_and (tr_gateAt_last gs _ D.out) hn hfl, tr_val_prefix hp D.out D.out x n hn,
      hfv _ (hN.1.trans hp), Bool.and_eq_true, hu.2 x]
def tr_upd (N : ℕ) (st : List G × (ℕ → tr_W)) (c : ℕ) (m : tr_W) : List G × (ℕ → tr_W) :=
  ((tr_merge N st.1 (st.2 c) m).1, Function.update st.2 c (tr_merge N st.1 (st.2 c) m).2)
theorem tr_upd_ok {D : Dag N} {gs : List G} {w : ℕ → tr_W} (hN : tr_NewOK D gs)
    {R : ℕ → (Fin (N + N) → Bool) → Prop} {RT : ℕ → Prop}
    (hw : ∀ c, tr_Ok D gs (w c) (R c) (RT c)) {m : tr_W} {Q QT} (hm : tr_Ok D gs m Q QT)
    (r : ℕ) :
    tr_NewOK D (tr_upd N (gs, w) r m).1 ∧ gs <+: (tr_upd N (gs, w) r m).1 ∧
      (tr_upd N (gs, w) r m).1.length ≤ gs.length + 1 ∧
      ∀ c, tr_Ok D (tr_upd N (gs, w) r m).1 ((tr_upd N (gs, w) r m).2 c)
        (fun x => R c x ∨ (c = r ∧ Q x)) (RT c ∨ (c = r ∧ QT)) := by
  obtain ⟨h1, h2, h3, h4⟩ := tr_merge_ok hN (hw r) hm
  refine ⟨h1, h2, h3, fun c => ?_⟩
  simp only [tr_upd]
  by_cases hc : c = r
  · subst hc
    rw [Function.update_self]
    exact tr_Ok_congr h4 (fun x => by simp) (by simp)
  · rw [Function.update_of_ne hc]
    exact tr_Ok_congr (tr_Ok_lift (hw c) h2 (tr_NewOK_size hN)) (fun x => by simp [hc])
      (by simp [hc])
inductive tr_TopS (D : Dag N) (S : Finset ℕ) (ok : ℕ → Prop) : ℕ → Prop
  | root : tr_TopS D S ok D.out
  | orStep {h c : ℕ} : tr_TopS D S ok h → h ∈ S → h ∈ D.Tor → D.Kid h c → 1 ≤ D.deg c →
      tr_TopS D S ok c
  | andStep {h f c : ℕ} : tr_TopS D S ok h → h ∈ S → h ∈ D.Tandf →
      (D.gateAt h = some (.and f c) ∨ D.gateAt h = some (.and c f)) →
      D.deg f = 0 → D.deg c = 2 → f < h → c < h → ok f → tr_TopS D S ok c
def tr_Step (D : Dag N) (ok : ℕ → Prop) (h c : ℕ) : Prop :=
  (h ∈ D.Tor ∧ D.Kid h c ∧ 1 ≤ D.deg c) ∨
    (h ∈ D.Tandf ∧ ∃ f, (D.gateAt h = some (.and f c) ∨ D.gateAt h = some (.and c f)) ∧
      D.deg f = 0 ∧ D.deg c = 2 ∧ f < h ∧ c < h ∧ ok f)
theorem tr_Step_lt {D : Dag N} {ok : ℕ → Prop} {h c : ℕ} (hs : tr_Step D ok h c) : c < h := by
  rcases hs with ⟨-, ⟨_, _, _, hc⟩, -⟩ | ⟨-, f, -, -, -, -, hc, -⟩
  · exact hc
  · exact hc
theorem tr_TopS_mono {D : Dag N} {S S' : Finset ℕ} {ok : ℕ → Prop} (hS : S ⊆ S') {c : ℕ}
    (h : tr_TopS D S ok c) : tr_TopS D S' ok c := by
  induction h with
  | root => exact tr_TopS.root
  | orStep _ hm ht hk hd ih => exact tr_TopS.orStep ih (hS hm) ht hk hd
  | andStep _ hm ht hg hf hc2 hfh hch hok ih =>
    exact tr_TopS.andStep ih (hS hm) ht hg hf hc2 hfh hch hok
theorem tr_TopS_step {D : Dag N} {S : Finset ℕ} {ok : ℕ → Prop} {h c : ℕ}
    (hT : tr_TopS D S ok h) (hm : h ∈ S) (hs : tr_Step D ok h c) : tr_TopS D S ok c := by
  rcases hs with ⟨ht, hk, hd⟩ | ⟨ht, f, hg, hf, hc2, hfh, hch, hok⟩
  · exact tr_TopS.orStep hT hm ht hk hd
  · exact tr_TopS.andStep hT hm ht hg hf hc2 hfh hch hok
theorem tr_TopS_insert {D : Dag N} {S : Finset ℕ} {ok : ℕ → Prop} {h : ℕ}
    (hS : ∀ s ∈ S, h < s) (c : ℕ) :
    tr_TopS D (insert h S) ok c ↔ tr_TopS D S ok c ∨ (tr_TopS D S ok h ∧ tr_Step D ok h c) := by
  constructor
  · intro hT
    induction hT with
    | root => exact Or.inl tr_TopS.root
    | @orStep h' c' _ hm ht hk hd ih =>
      have hs : tr_Step D ok h' c' := Or.inl ⟨ht, hk, hd⟩
      rcases Finset.mem_insert.1 hm with rfl | hm
      · rcases ih with ih | ⟨ih, -⟩ <;> exact Or.inr ⟨ih, hs⟩
      · rcases ih with ih | ⟨-, hs'⟩
        · exact Or.inl (tr_TopS_step ih hm hs)
        · have := tr_Step_lt hs'; have := hS h' hm; omega
    | @andStep h' f c' _ hm ht hg hf hc2 hfh hch hok ih =>
      have hs : tr_Step D ok h' c' := Or.inr ⟨ht, f, hg, hf, hc2, hfh, hch, hok⟩
      rcases Finset.mem_insert.1 hm with rfl | hm
      · rcases ih with ih | ⟨ih, -⟩ <;> exact Or.inr ⟨ih, hs⟩
      · rcases ih with ih | ⟨-, hs'⟩
        · exact Or.inl (tr_TopS_step ih hm hs)
        · have := tr_Step_lt hs'; have := hS h' hm; omega
  · rintro (hT | ⟨hT, hs⟩)
    · exact tr_TopS_mono (Finset.subset_insert h S) hT
    · exact tr_TopS_step (tr_TopS_mono (Finset.subset_insert h S) hT) (Finset.mem_insert_self h S) hs
theorem tr_TopS_empty {D : Dag N} {ok : ℕ → Prop} {c : ℕ} :
    tr_TopS D ∅ ok c ↔ c = D.out := by
  constructor
  · intro h
    induction h with
    | root => rfl
    | orStep _ hm => simp at hm
    | andStep _ hm => simp at hm
  · rintro rfl; exact tr_TopS.root
theorem tr_TopS_all {D : Dag N} {ok : ℕ → Prop} {c : ℕ} :
    tr_TopS D (D.Tor ∪ D.Tandf) ok c ↔ D.Top ok c := by
  constructor
  · intro h
    induction h with
    | root => exact Dag.Top.root
    | orStep _ _ ht hk hd ih => exact Dag.Top.orStep ih ht hk hd
    | andStep _ _ ht hg hf hc2 hfh hch hok ih => exact Dag.Top.andStep ih ht hg hf hc2 hfh hch hok
  · intro h
    induction h with
    | root => exact tr_TopS.root
    | orStep _ ht hk hd ih => exact tr_TopS.orStep ih (Finset.mem_union_left _ ht) ht hk hd
    | andStep _ ht hg hf hc2 hfh hch hok ih =>
      exact tr_TopS.andStep ih (Finset.mem_union_right _ ht) ht hg hf hc2 hfh hch hok
def tr_proc (D : Dag N) (st : List G × (ℕ → tr_W)) (h : ℕ) : List G × (ℕ → tr_W) :=
  match D.gateAt h with
  | some (.or a b) =>
      tr_upd N (tr_upd N st a (if 1 ≤ D.deg a then st.2 h else .absent)) b
        (if 1 ≤ D.deg b then st.2 h else .absent)
  | some (.and a b) =>
      if D.deg a = 0 then
        tr_upd N ((tr_msgAnd N st.1 (st.2 h) a).1, st.2) b (tr_msgAnd N st.1 (st.2 h) a).2
      else
        tr_upd N ((tr_msgAnd N st.1 (st.2 h) b).1, st.2) a (tr_msgAnd N st.1 (st.2 h) b).2
  | _ => st
def tr_Inv (D : Dag N) (st : List G × (ℕ → tr_W)) (S : Finset ℕ) : Prop :=
  tr_NewOK D st.1 ∧ st.1.length ≤ D.size + 2 * S.card ∧
    ∀ c, tr_Ok D st.1 (st.2 c) (fun x => tr_TopS D S (fun f => D.val x f = true) c)
      (tr_TopS D S (fun _ => True) c)
theorem tr_label_good {D : Dag N} {h f : ℕ} (hh : h ∈ D.cone) (hk : D.Kid h f)
    (hf : D.deg f = 0) : f < N ∨ f ∈ D.X := by
  by_cases hfN : f < N + N
  · left
    by_contra hc
    rw [Dag.deg, if_pos hfN, if_pos (by omega)] at hf
    exact one_ne_zero hf
  · right
    exact Finset.mem_filter.2 ⟨Api.api_coneOf_down D {D.out} h hh f hk (by omega), hf⟩
theorem tr_step_or {D : Dag N} {ok : ℕ → Prop} {h a b c : ℕ}
    (hg : D.gateAt h = some (.or a b)) (ha : a < h) (hb : b < h) (ht : h ∈ D.Tor) :
    tr_Step D ok h c ↔ ((c = a ∨ c = b) ∧ 1 ≤ D.deg c) := by
  constructor
  · rintro (⟨-, ⟨g, hg', hc, -⟩, hd⟩ | ⟨-, f, hg', -⟩)
    · rw [hg] at hg'; cases hg'
      simp only [G.kids, List.mem_cons, List.not_mem_nil, or_false] at hc
      exact ⟨hc, hd⟩
    · rcases hg' with hg' | hg' <;> rw [hg] at hg' <;> cases hg'
  · rintro ⟨hc, hd⟩
    left
    refine ⟨ht, ⟨_, hg, ?_, ?_⟩, hd⟩
    · simp only [G.kids, List.mem_cons, List.not_mem_nil, or_false]; exact hc
    · rcases hc with rfl | rfl <;> assumption
theorem tr_step_and {D : Dag N} {ok : ℕ → Prop} {h f0 c0 c : ℕ}
    (hg : D.gateAt h = some (.and f0 c0) ∨ D.gateAt h = some (.and c0 f0))
    (hf : D.deg f0 = 0) (hc2 : D.deg c0 = 2) (hfh : f0 < h) (hch : c0 < h)
    (ht : h ∈ D.Tandf) : tr_Step D ok h c ↔ (c = c0 ∧ ok f0) := by
  classical
  constructor
  · rintro (⟨ht', -⟩ | ⟨-, f, hg', hf', hc', -, -, hok⟩)
    · obtain ⟨-, a, b, hg'⟩ := Finset.mem_filter.1 ht'
      rcases hg with hg | hg <;> rw [hg] at hg' <;> cases hg'
    · rcases hg with hg | hg <;> rcases hg' with hg' | hg' <;> rw [hg] at hg' <;> cases hg' <;>
        first | exact ⟨rfl, hok⟩ | omega
  · rintro ⟨rfl, hok⟩
    exact Or.inr ⟨ht, f0, hg, hf, hc2, hfh, hch, hok⟩
theorem tr_proc_ok {D : Dag N} (hwf : D.WF) {st : List G × (ℕ → tr_W)} {S : Finset ℕ}
    {h : ℕ} (hI : tr_Inv D st S) (hS : ∀ s ∈ S, h < s) (hh : h ∈ D.Tor ∪ D.Tandf) :
    tr_Inv D (tr_proc D st h) (insert h S) := by
  classical
  obtain ⟨gs, w⟩ := st
  obtain ⟨hN, hlen, hw⟩ := hI
  dsimp only at hN hlen hw
  have hhS : h ∉ S := fun hm => lt_irrefl h (hS h hm)
  have hcard : (insert h S).card = S.card + 1 := Finset.card_insert_of_notMem hhS
  have hD := tr_NewOK_size hN
  rcases Finset.mem_union.1 hh with ht | ht
  · obtain ⟨hT, a, b, hg⟩ := Finset.mem_filter.1 ht
    have ha := hwf _ _ hg a (by simp [G.kids])
    have hb := hwf _ _ hg b (by simp [G.kids])
    have hm : ∀ a', tr_Ok D gs (if 1 ≤ D.deg a' then w h else .absent)
        (fun x => 1 ≤ D.deg a' ∧ tr_TopS D S (fun f => D.val x f = true) h)
        (1 ≤ D.deg a' ∧ tr_TopS D S (fun _ => True) h) := by
      intro a'
      by_cases hda : 1 ≤ D.deg a'
      · rw [if_pos hda]; exact tr_Ok_congr (hw h) (fun x => by simp [hda]) (by simp [hda])
      · rw [if_neg hda]; exact ⟨fun h' => hda h'.1, fun x h' => hda h'.1⟩
    unfold tr_proc
    rw [hg]
    dsimp only
    obtain ⟨hN1, hp1, hl1, hw1⟩ := tr_upd_ok hN hw (hm a) a
    have hmb := tr_Ok_lift (hm b) hp1 hD
    generalize tr_upd N (gs, w) a (if 1 ≤ D.deg a then w h else .absent) = st1
      at hN1 hp1 hl1 hw1 hmb ⊢
    obtain ⟨g1, w1⟩ := st1
    dsimp only at hN1 hp1 hl1 hw1 hmb ⊢
    obtain ⟨hN2, hp2, hl2, hw2⟩ := tr_upd_ok hN1 hw1 hmb b
    refine ⟨hN2, ?_, fun c => tr_Ok_congr (hw2 c) ?_ ?_⟩
    · rw [hcard]; omega
    · intro x
      beta_reduce
      rw [tr_TopS_insert hS, tr_step_or hg ha hb ht]
      constructor
      · rintro ((h1 | ⟨rfl, h2, h3⟩) | ⟨rfl, h2, h3⟩)
        · exact Or.inl h1
        · exact Or.inr ⟨h3, Or.inl rfl, h2⟩
        · exact Or.inr ⟨h3, Or.inr rfl, h2⟩
      · rintro (h1 | ⟨h3, (rfl | rfl), h2⟩)
        · exact Or.inl (Or.inl h1)
        · exact Or.inl (Or.inr ⟨rfl, h2, h3⟩)
        · exact Or.inr ⟨rfl, h2, h3⟩
    · rw [tr_TopS_insert hS, tr_step_or hg ha hb ht]
      constructor
      · rintro ((h1 | ⟨rfl, h2, h3⟩) | ⟨rfl, h2, h3⟩)
        · exact Or.inl h1
        · exact Or.inr ⟨h3, Or.inl rfl, h2⟩
        · exact Or.inr ⟨h3, Or.inr rfl, h2⟩
      · rintro (h1 | ⟨h3, (rfl | rfl), h2⟩)
        · exact Or.inl (Or.inl h1)
        · exact Or.inl (Or.inr ⟨rfl, h2, h3⟩)
        · exact Or.inr ⟨rfl, h2, h3⟩
  · obtain ⟨hT, a, b, hg, hf⟩ := Finset.mem_filter.1 ht
    have ha := hwf _ _ hg a (by simp [G.kids])
    have hb := hwf _ _ hg b (by simp [G.kids])
    have hT' := Finset.mem_filter.1 hT
    have hdeg := tr_deg_and hg ha hb
    unfold tr_proc
    rw [hg]
    dsimp only
    by_cases ha0 : D.deg a = 0
    · rw [if_pos ha0]
      have hlab := tr_label_good hT'.1 (tr_kid_of hg (by simp [G.kids]) ha) ha0
      obtain ⟨hN1, hp1, hl1, hm1⟩ := tr_msgAnd_ok hN (hw h) hlab
      obtain ⟨hN2, hp2, hl2, hw2⟩ :=
        tr_upd_ok hN1 (fun c => tr_Ok_lift (hw c) hp1 hD) hm1 b
      have hst := tr_step_and (ok := fun _ => True) (c := 0) (Or.inl hg) ha0 (by omega) ha hb ht
      refine ⟨hN2, ?_, fun c => tr_Ok_congr (hw2 c) ?_ ?_⟩
      · rw [hcard]; omega
      · intro x
        beta_reduce
        rw [tr_TopS_insert hS, tr_step_and (Or.inl hg) ha0 (by omega) ha hb ht]
        constructor
        · rintro (h1 | ⟨rfl, h2, h3⟩)
          · exact Or.inl h1
          · exact Or.inr ⟨h2, rfl, h3⟩
        · rintro (h1 | ⟨h2, rfl, h3⟩)
          · exact Or.inl h1
          · exact Or.inr ⟨rfl, h2, h3⟩
      · rw [tr_TopS_insert hS, tr_step_and (Or.inl hg) ha0 (by omega) ha hb ht]
        constructor
        · rintro (h1 | ⟨rfl, h2⟩)
          · exact Or.inl h1
          · exact Or.inr ⟨h2, rfl, trivial⟩
        · rintro (h1 | ⟨h2, rfl, -⟩)
          · exact Or.inl h1
          · exact Or.inr ⟨rfl, h2⟩
    · rw [if_neg ha0]
      have hb0 : D.deg b = 0 := by omega
      have hlab := tr_label_good hT'.1 (tr_kid_of hg (by simp [G.kids]) hb) hb0
      obtain ⟨hN1, hp1, hl1, hm1⟩ := tr_msgAnd_ok hN (hw h) hlab
      obtain ⟨hN2, hp2, hl2, hw2⟩ :=
        tr_upd_ok hN1 (fun c => tr_Ok_lift (hw c) hp1 hD) hm1 a
      refine ⟨hN2, ?_, fun c => tr_Ok_congr (hw2 c) ?_ ?_⟩
      · rw [hcard]; omega
      · intro x
        beta_reduce
        rw [tr_TopS_insert hS, tr_step_and (Or.inr hg) hb0 (by omega) hb ha ht]
        constructor
        · rintro (h1 | ⟨rfl, h2, h3⟩)
          · exact Or.inl h1
          · exact Or.inr ⟨h2, rfl, h3⟩
        · rintro (h1 | ⟨h2, rfl, h3⟩)
          · exact Or.inl h1
          · exact Or.inr ⟨rfl, h2, h3⟩
      · rw [tr_TopS_insert hS, tr_step_and (Or.inr hg) hb0 (by omega) hb ha ht]
        constructor
        · rintro (h1 | ⟨rfl, h2⟩)
          · exact Or.inl h1
          · exact Or.inr ⟨h2, rfl, trivial⟩
        · rintro (h1 | ⟨h2, rfl, -⟩)
          · exact Or.inl h1
          · exact Or.inr ⟨rfl, h2⟩
theorem tr_fold_ok {D : Dag N} (hwf : D.WF) : ∀ (L : List ℕ) (st : List G × (ℕ → tr_W))
    (S : Finset ℕ), L.Pairwise (· > ·) → (∀ h ∈ L, h ∈ D.Tor ∪ D.Tandf) →
    (∀ h ∈ L, ∀ s ∈ S, h < s) → tr_Inv D st S →
    tr_Inv D (L.foldl (tr_proc D) st) (S ∪ L.toFinset) := by
  intro L
  induction L with
  | nil => intro st S _ _ _ hI; simpa using hI
  | cons h t ih =>
    intro st S hp hm hlt hI
    rw [List.pairwise_cons] at hp
    rw [List.foldl_cons, List.toFinset_cons, Finset.union_insert, ← Finset.insert_union]
    apply ih _ _ hp.2 (fun h' h'' => hm h' (List.mem_cons_of_mem _ h''))
    · intro h' hh' s hs
      rcases Finset.mem_insert.1 hs with rfl | hs
      · exact hp.1 h' hh'
      · exact hlt h' (List.mem_cons_of_mem _ hh') s hs
    · exact tr_proc_ok hwf hI (hlt h (by simp)) (hm h (by simp))
theorem tr_wf {D : Dag N} (hwf : D.WF) {gs : List G} (hN : tr_NewOK D gs) (o : ℕ) :
    (⟨gs, o⟩ : Dag N).WF := by
  intro i g hg c hc
  obtain ⟨hi, hg'⟩ := Api.gateAt_some hg
  dsimp only at hg'
  by_cases hj : i - (N + N) < D.size
  · have e : (⟨gs, o⟩ : Dag N).gateAt i = (⟨D.gates, D.out⟩ : Dag N).gateAt i :=
      tr_gateAt_prefix hN.1 o D.out (by unfold Dag.size at hj; omega)
    rw [e] at hg
    exact hwf i g hg c hc
  · obtain ⟨u, v, hgv, hu, hv⟩ := hN.2 _ g (by omega) hg'
    have hu' := tr_Good_lt hu (by omega)
    have hv' := tr_Good_lt hv (by omega)
    rcases hgv with rfl | rfl <;>
      simp only [G.kids, List.mem_cons, List.not_mem_nil, or_false] at hc <;>
      rcases hc with rfl | rfl <;> omega
theorem tr_good_final {D : Dag N} {gs : List G} (hN : tr_NewOK D gs) (o : ℕ) :
    ∀ n, tr_Good D gs.length n → (⟨gs, o⟩ : Dag N).deg n = 0 ∧
      ∀ m, (⟨gs, o⟩ : Dag N).Kid n m → tr_Good D gs.length m := by
  have hD := tr_NewOK_size hN
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn
  rcases hn with hn | hn | ⟨hn1, hn2⟩
  · refine ⟨?_, ?_⟩
    · rw [Dag.deg, if_pos (by omega), if_neg (by omega)]
    · rintro m ⟨g, hg, -, -⟩
      have := (Api.gateAt_some hg).1
      omega
  · have hlt := tr_X_lt hn
    have hX := Finset.mem_filter.1 hn
    have hsz : n < N + N + D.gates.length := hlt.2
    refine ⟨?_, ?_⟩
    · rw [tr_deg_prefix hN.1 D.out o n hsz]
      exact hX.2
    · rintro m ⟨g, hg, hmg, hmn⟩
      rw [tr_gateAt_prefix hN.1 D.out o hsz] at hg
      have hk : D.Kid n m := ⟨g, hg, hmg, hmn⟩
      have hd0 : D.deg m = 0 := by have := Api.deg_kid hk; omega
      rcases tr_label_good hX.1 hk hd0 with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  · cases hgs : gs[n - (N + N)]? with
    | none =>
      rw [List.getElem?_eq_none_iff] at hgs
      omega
    | some g =>
      obtain ⟨u, v, hgv, hu, hv⟩ := hN.2 _ g (by omega) hgs
      have hgate : (⟨gs, o⟩ : Dag N).gateAt n = some g := by
        unfold Dag.gateAt
        rw [if_pos (by omega)]
        exact hgs
      have hdj : D.size ≤ n - (N + N) := by omega
      have hun : u < n := by have := tr_Good_lt hu hdj; omega
      have hvn : v < n := by have := tr_Good_lt hv hdj; omega
      have hu2 := tr_Good_mono hu (by omega : n - (N + N) ≤ gs.length)
      have hv2 := tr_Good_mono hv (by omega : n - (N + N) ≤ gs.length)
      refine ⟨?_, ?_⟩
      · rcases hgv with rfl | rfl
        · rw [tr_deg_and hgate hun hvn, (ih u hun hu2).1, (ih v hvn hv2).1]
        · rw [tr_deg_or hgate hun hvn, (ih u hun hu2).1, (ih v hvn hv2).1]
          rfl
      · rintro m ⟨g', hg', hmg, -⟩
        rw [hgate] at hg'
        cases hg'
        rcases hgv with rfl | rfl <;>
          simp only [G.kids, List.mem_cons, List.not_mem_nil, or_false] at hmg <;>
          rcases hmg with rfl | rfl <;> assumption
theorem tr_cone_final {D : Dag N} {gs : List G} (hN : tr_NewOK D gs) (o : ℕ) {n : ℕ}
    (hn : tr_Good D gs.length n) :
    (⟨gs, o⟩ : Dag N).coneOf {n} ⊆ D.X ∪ Finset.Ico (N + N + D.size) (N + N + gs.length) := by
  classical
  intro m hm
  unfold Dag.coneOf at hm
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton] at hm
  obtain ⟨-, hm1, r, rfl, hr⟩ := hm
  have hg : tr_Good D gs.length m := by
    clear hm1
    induction hr with
    | refl => exact hn
    | tail _ hk ih => exact (tr_good_final hN o _ ih).2 _ hk
  rcases hg with h | h | h
  · omega
  · exact Finset.mem_union_left _ h
  · exact Finset.mem_union_right _ (Finset.mem_Ico.2 h)
theorem card15c_contexts (D : Dag N) (hwf : D.WF) (hd : D.deg D.out ≤ 2) :
    ∃ D' : Dag N, D.gates <+: D'.gates ∧ D'.WF ∧
      D'.size ≤ D.size + 2 * D.Tor.card + 2 * D.Tandf.card ∧
      ∀ b, D.IsItem b → (∀ x, D.ctx b x = true) ∨
        ∃ i, D'.deg i = 0 ∧ (∀ x, D'.val x i = D.ctx b x) ∧
          D'.coneOf {i} ⊆ D.X ∪ Finset.Ico (N + N + D.size) (N + N + D'.size) := by
  classical
  have hinit : tr_Inv D (D.gates, fun c => if c = D.out then tr_W.const else tr_W.absent) ∅ := by
    refine ⟨⟨List.prefix_refl _, fun j g hj hg => ?_⟩, by simp [Dag.size], fun c => ?_⟩
    · have : D.gates[j]? = none :=
        List.getElem?_eq_none_iff.2 (by unfold Dag.size at hj; omega)
      rw [this] at hg
      cases hg
    · dsimp only
      by_cases hc : c = D.out
      · rw [if_pos hc]
        subst hc
        exact fun x => tr_TopS.root
      · rw [if_neg hc]
        exact ⟨fun h => hc (tr_TopS_empty.1 h), fun x h => hc (tr_TopS_empty.1 h)⟩
  have hpw : ((D.Tor ∪ D.Tandf).sort (· ≥ ·)).Pairwise (· > ·) := by
    have h1 := Finset.pairwise_sort (D.Tor ∪ D.Tandf) (· ≥ ·)
    have h2 := Finset.sort_nodup (D.Tor ∪ D.Tandf) (· ≥ ·)
    exact (h1.and h2).imp (fun h => lt_of_le_of_ne h.1 (Ne.symm h.2))
  have hfin := tr_fold_ok hwf ((D.Tor ∪ D.Tandf).sort (· ≥ ·)) _ ∅ hpw
    (fun h hh => (Finset.mem_sort _).1 hh) (by simp) hinit
  rw [Finset.empty_union, Finset.sort_toFinset] at hfin
  generalize List.foldl (tr_proc D) _ _ = st at hfin
  obtain ⟨hN, hlen, hw⟩ := hfin
  refine ⟨⟨st.1, D.out⟩, hN.1, tr_wf hwf hN D.out, ?_, fun b hb => ?_⟩
  · have := Finset.card_union_le D.Tor D.Tandf
    show st.1.length ≤ _
    omega
  · have hwb := tr_Ok_congr (hw b) (fun x => tr_TopS_all) tr_TopS_all
    generalize st.2 b = m at hwb
    cases m with
    | absent => exact absurd hb.1 hwb.1
    | const =>
      left
      intro x
      unfold Dag.ctx
      exact decide_eq_true (hwb x)
    | wire n =>
      right
      obtain ⟨hg, hv⟩ := hwb
      refine ⟨n, (tr_good_final hN D.out n hg).1, fun x => ?_, tr_cone_final hN D.out hg⟩
      unfold Dag.ctx
      rw [Bool.eq_iff_iff, decide_eq_true_iff]
      exact hv x
end Deg2
namespace Deg2
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
variable {N : ℕ}
theorem tr_vreach_above {D : Dag N} (hwf : D.WF) {v : ℕ} {u : Fin N} (h : D.VReach v u)
    (z : Fin (N + N) → Bool) (hz : z (Fin.natAdd N u) = true) : D.val z v = true := by
  induction h with
  | leaf u =>
    rw [Dag.val, dif_pos (by omega)]
    exact hz
  | @step v c u hor _ hk _ ih =>
    obtain ⟨a, b, hg⟩ := hor
    have ha := hwf _ _ hg a (by simp [G.kids])
    have hb := hwf _ _ hg b (by simp [G.kids])
    obtain ⟨g, hg', hcg, -⟩ := hk
    rw [hg] at hg'
    cases hg'
    rw [tr_val_or hg ha hb]
    simp only [G.kids, List.mem_cons, List.not_mem_nil, or_false] at hcg
    rcases hcg with rfl | rfl <;> simp [ih hz]
theorem tr_marker_above {D : Dag N} (hwf : D.WF) {r : ℕ} {w : Fin N} (hm : D.IsMarker r w)
    (z : Fin (N + N) → Bool) (hz : z (Fin.natAdd N w) = true) : D.val z r = true := by
  classical
  have hw : w ∈ D.Vstar r := by rw [hm.2]; exact Finset.mem_singleton_self w
  exact tr_vreach_above hwf (Finset.mem_filter.1 hw).2 z hz
theorem tr_term_sound (I : Fin N → Fin N → Prop) {D : Dag N} (hwf : D.WF)
    (hc : Computes I D.fn) (hd : D.deg D.out ≤ 2) {b r : ℕ} {w : Fin N} (hb : D.IsItem b)
    (hm : D.IsMarker r w) (z : Fin (N + N) → Bool)
    (hz : z (Fin.natAdd N w) = true) (hctx : D.ctx b z = true)
    (hrest : ∀ x, D.IsFactor b x → x ≠ r → D.val z x = true) :
    ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true := by
  refine (hc z).1 ((card15_identity I D hwf hc hd z).2 ⟨b, hb, hctx, fun x hx => ?_⟩)
  by_cases hxr : x = r
  · subst hxr; exact tr_marker_above hwf hm z hz
  · exact hrest x hx hxr
theorem tr_no_const (I : Fin N → Fin N → Prop) {D : Dag N} (hwf : D.WF)
    (hc : Computes I D.fn) (hd : D.deg D.out ≤ 2) {b : ℕ} {w : Fin N} (hb : D.IsItem b)
    (hb1 : D.deg b ≤ 1) (hm : D.IsMarker b w) : ¬ ∀ x, D.ctx b x = true := by
  classical
  intro hall
  have hz : inp (∅ : Finset (Fin N)) {w} (Fin.natAdd N w) = true := by
    unfold inp; rw [Fin.addCases_right]; simp
  obtain ⟨p, l, -, hp, -⟩ := tr_term_sound I hwf hc hd hb hm _ hz (hall _)
    (fun x hx hxb => by
      rcases hx with ⟨-, rfl⟩ | ⟨hmix, -⟩
      · exact absurd rfl hxb
      · have := (Finset.mem_filter.1 (Finset.mem_filter.1 hmix).1).2; omega)
  unfold inp at hp
  rw [Fin.addCases_left] at hp
  simp at hp
theorem tr_item_parent {D : Dag N} {ok : ℕ → Prop} {b : ℕ} (hT : D.Top ok b)
    (hne : b ≠ D.out) (hb1 : D.deg b ≤ 1) : ∃ h ∈ D.Tor, D.Kid h b := by
  cases hT with
  | root => exact absurd rfl hne
  | orStep _ ht hk _ => exact ⟨_, ht, hk⟩
  | andStep _ _ _ _ hc2 _ _ _ => omega
theorem tr_tor_low_unique {D : Dag N} (hwf : D.WF) {h b b' : ℕ} (ht : h ∈ D.Tor)
    (hk : D.Kid h b) (hk' : D.Kid h b') (hb : D.deg b ≤ 1) (hb' : D.deg b' ≤ 1) : b = b' := by
  classical
  obtain ⟨hT, a, c, hg⟩ := Finset.mem_filter.1 ht
  have h2 := (Finset.mem_filter.1 hT).2
  have ha := hwf _ _ hg a (by simp [G.kids])
  have hc := hwf _ _ hg c (by simp [G.kids])
  rw [tr_deg_or hg ha hc] at h2
  obtain ⟨g, hg1, hbg, -⟩ := hk
  obtain ⟨g', hg2, hbg', -⟩ := hk'
  rw [hg] at hg1 hg2
  cases hg1
  cases hg2
  simp only [G.kids, List.mem_cons, List.not_mem_nil, or_false] at hbg hbg'
  rcases hbg with rfl | rfl <;> rcases hbg' with rfl | rfl <;> first | rfl | omega
theorem tr_T_split (D : Dag N) : D.Tor.card + D.Tandf.card + D.Tmix.card ≤ D.T.card := by
  classical
  have h1 := Api.card_filter_disj (s := D.T) (p := D.IsOr)
    (q := fun i => ∃ a b, D.gateAt i = some (.and a b) ∧ (D.deg a = 0 ∨ D.deg b = 0)) (by
      rintro i ⟨a, b, ha⟩ ⟨a', b', hb, -⟩
      rw [ha] at hb
      cases hb)
  have h2 := Api.card_filter_disj (s := D.T)
    (p := fun i => D.IsOr i ∨ ∃ a b, D.gateAt i = some (.and a b) ∧ (D.deg a = 0 ∨ D.deg b = 0))
    (q := fun i => ∃ a b, D.gateAt i = some (.and a b) ∧ D.deg a = 1 ∧ D.deg b = 1) (by
      rintro i (⟨a, b, ha⟩ | ⟨a, b, ha, hab⟩) ⟨a', b', hb, h1, h2⟩
      · rw [ha] at hb; cases hb
      · rw [ha] at hb; cases hb; omega)
  have h3 := Finset.card_filter_le D.T (fun i => (D.IsOr i ∨
      ∃ a b, D.gateAt i = some (.and a b) ∧ (D.deg a = 0 ∨ D.deg b = 0)) ∨
      ∃ a b, D.gateAt i = some (.and a b) ∧ D.deg a = 1 ∧ D.deg b = 1)
  unfold Dag.Tor Dag.Tandf Dag.Tmix
  omega
theorem tr_top_lt {D : Dag N} {ok : ℕ → Prop} {b : ℕ} (hT : D.Top ok b) :
    b = D.out ∨ b < N + N + D.size := by
  classical
  cases hT with
  | root => exact Or.inl rfl
  | orStep _ ht hk _ =>
    right
    have := Finset.mem_Ico.1 (Api.coneOf_sub D {D.out}
      (Finset.mem_filter.1 (Finset.mem_filter.1 ht).1).1)
    obtain ⟨_, _, _, hlt⟩ := hk
    omega
  | andStep _ ht _ _ _ _ hch _ =>
    right
    have := Finset.mem_Ico.1 (Api.coneOf_sub D {D.out}
      (Finset.mem_filter.1 (Finset.mem_filter.1 ht).1).1)
    omega
theorem tr_factor_le {D : Dag N} {b r : ℕ} (h : D.IsFactor b r) : r ≤ b := by
  rcases h with ⟨-, rfl⟩ | ⟨-, _, _, _, hlt⟩
  · exact le_rfl
  · exact le_of_lt hlt
open Classical in
noncomputable def tr_jobs (D : Dag N) : Finset (ℕ × ℕ × Fin N) :=
  ((Finset.range (D.out + N + N + D.size + 1)) ×ˢ
    ((Finset.range (D.out + N + N + D.size + 1)) ×ˢ (Finset.univ : Finset (Fin N)))).filter
    (fun j => D.IsItem j.1 ∧ D.IsFactor j.1 j.2.1 ∧ D.IsMarker j.2.1 j.2.2)
theorem tr_mem_jobs {D : Dag N} {b r : ℕ} {w : Fin N} :
    (b, r, w) ∈ tr_jobs D ↔ D.IsItem b ∧ D.IsFactor b r ∧ D.IsMarker r w := by
  classical
  unfold tr_jobs
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_univ,
    and_true]
  constructor
  · exact fun h => h.2
  · rintro ⟨hb, hr, hm⟩
    have h1 := tr_top_lt hb.1
    have h2 := tr_factor_le hr
    refine ⟨⟨by omega, by omega⟩, hb, hr, hm⟩
theorem tr_marker_line {D : Dag N} {r : ℕ} {w w' : Fin N} (h : D.IsMarker r w)
    (h' : D.IsMarker r w') : w = w' := by
  have := h.2.symm.trans h'.2
  exact Finset.singleton_inj.1 this
theorem tr_jobs1_card (I : Fin N → Fin N → Prop) {D : Dag N} (hwf : D.WF)
    (hc : Computes I D.fn) (hd : D.deg D.out ≤ 2) :
    ((tr_jobs D).filter (fun j => D.deg j.1 ≤ 1)).card ≤ D.Tor.card := by
  classical
  have key : ∀ j ∈ (tr_jobs D).filter (fun j => D.deg j.1 ≤ 1),
      j.2.1 = j.1 ∧ ∃ h ∈ D.Tor, D.Kid h j.1 := by
    intro j hj
    obtain ⟨b, r, w⟩ := j
    rw [Finset.mem_filter, tr_mem_jobs] at hj
    obtain ⟨⟨hb, hr, hm⟩, h1⟩ := hj
    have hrb : r = b := by
      rcases hr with ⟨-, rfl⟩ | ⟨hmix, -⟩
      · rfl
      · have := (Finset.mem_filter.1 (Finset.mem_filter.1 hmix).1).2; dsimp only at h1; omega
    subst hrb
    refine ⟨rfl, tr_item_parent hb.1 ?_ h1⟩
    rintro rfl
    exact tr_no_const I hwf hc hd hb h1 hm (fun x => by
      unfold Dag.ctx; exact decide_eq_true Dag.Top.root)
  let f : ℕ × ℕ × Fin N → ℕ := fun j =>
    if h : ∃ h ∈ D.Tor, D.Kid h j.1 then h.choose else 0
  apply Finset.card_le_card_of_injOn f
  · intro j hj
    have hx := (key j hj).2
    simp only [f, dif_pos hx]
    exact hx.choose_spec.1
  · intro j hj j' hj' he
    have hx := (key j hj).2
    have hx' := (key j' hj').2
    simp only [f, dif_pos hx, dif_pos hx'] at he
    have hk := hx.choose_spec.2
    rw [he] at hk
    have h1 := (Finset.mem_filter.1 hj).2
    have h1' := (Finset.mem_filter.1 hj').2
    have hbb := tr_tor_low_unique hwf hx'.choose_spec.1 hk hx'.choose_spec.2 h1 h1'
    obtain ⟨b, r, w⟩ := j
    obtain ⟨b', r', w'⟩ := j'
    have hm := ((tr_mem_jobs.1 (Finset.mem_filter.1 hj).1)).2.2
    have hm' := ((tr_mem_jobs.1 (Finset.mem_filter.1 hj').1)).2.2
    have e1 := (key _ hj).1
    have e2 := (key _ hj').1
    dsimp only at hbb e1 e2 hm hm'
    subst e1 e2 hbb
    rw [tr_marker_line hm hm']
theorem tr_jobs2_card {D : Dag N} :
    ((tr_jobs D).filter (fun j => ¬ D.deg j.1 ≤ 1)).card ≤ 2 * D.Tmix.card := by
  classical
  have key : ∀ j ∈ (tr_jobs D).filter (fun j => ¬ D.deg j.1 ≤ 1),
      j.1 ∈ D.Tmix ∧ D.Kid j.1 j.2.1 := by
    intro j hj
    obtain ⟨b, r, w⟩ := j
    rw [Finset.mem_filter, tr_mem_jobs] at hj
    obtain ⟨⟨hb, hr, hm⟩, h1⟩ := hj
    rcases hr with ⟨h, -⟩ | hr
    · exact absurd h h1
    · exact hr
  let first : ℕ → ℕ := fun b =>
    match D.gateAt b with
    | some (.and a _) => a
    | _ => 0
  let f : ℕ × ℕ × Fin N → ℕ × ℕ := fun j => (j.1, if j.2.1 = first j.1 then 0 else 1)
  have hcard : (D.Tmix ×ˢ Finset.range 2).card = 2 * D.Tmix.card := by
    rw [Finset.card_product, Finset.card_range, mul_comm]
  rw [← hcard]
  apply Finset.card_le_card_of_injOn f
  · intro j hj
    show f j ∈ D.Tmix ×ˢ Finset.range 2
    rw [Finset.mem_product]
    exact ⟨(key j hj).1, by rw [Finset.mem_range]; dsimp only [f]; split_ifs <;> omega⟩
  · intro j hj j' hj' he
    obtain ⟨hmix, hk⟩ := key j hj
    obtain ⟨hmix', hk'⟩ := key j' hj'
    have hm := ((tr_mem_jobs.1 (Finset.mem_filter.1 hj).1)).2.2
    have hm' := ((tr_mem_jobs.1 (Finset.mem_filter.1 hj').1)).2.2
    obtain ⟨b, r, w⟩ := j
    obtain ⟨b', r', w'⟩ := j'
    simp only [f, Prod.mk.injEq] at he
    obtain ⟨rfl, he⟩ := he
    dsimp only at hmix hk hk' hm hm'
    obtain ⟨-, a, a', hg, -⟩ := Finset.mem_filter.1 hmix
    have hfirst : first b = a := by simp only [first, hg]
    obtain ⟨g, hg1, hr1, -⟩ := hk
    obtain ⟨g', hg2, hr2, -⟩ := hk'
    rw [hg] at hg1 hg2
    cases hg1
    cases hg2
    simp only [G.kids, List.mem_cons, List.not_mem_nil, or_false] at hr1 hr2
    have hrr : r = r' := by
      rw [hfirst] at he
      rcases hr1 with rfl | rfl <;> rcases hr2 with rfl | rfl <;> first | rfl | (split_ifs at he <;> simp_all)
    subst hrr
    rw [tr_marker_line hm hm']
end Deg2
namespace Deg2
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
variable {N : ℕ}
theorem tr_reach_le {D : Dag N} {u m : ℕ} (h : D.Reach u m) : m ≤ u := by
  induction h with
  | refl => exact le_rfl
  | tail _ hk ih =>
    obtain ⟨_, _, _, hlt⟩ := hk
    exact le_trans (le_of_lt hlt) ih
theorem tr_reach_prefix {gs gs' : List G} (hp : gs <+: gs') (o o' : ℕ) {u m : ℕ}
    (hu : u < N + N + gs.length) (h : (⟨gs', o'⟩ : Dag N).Reach u m) :
    (⟨gs, o⟩ : Dag N).Reach u m := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail a c hr hk ih =>
    have ha := tr_reach_le hr
    obtain ⟨g, hg, hc, hlt⟩ := hk
    rw [tr_gateAt_prefix hp o o' (by omega)] at hg
    exact ih.tail ⟨g, hg, hc, hlt⟩
theorem tr_val_lt {D : Dag N} {x : Fin (N + N) → Bool} {i : ℕ} (h : D.val x i = true) :
    i < N + N + D.size := by
  rw [Dag.val] at h
  split_ifs at h with hi
  · omega
  · cases hg : D.gates[i - (N + N)]? with
    | none => rw [hg] at h; simp at h
    | some g =>
      have := (List.getElem?_eq_some_iff.1 hg).1
      unfold Dag.size
      omega
theorem tr_ctx_xonly {D : Dag N} {b : ℕ} {x y : Fin (N + N) → Bool}
    (h : ∀ p : Fin N, x (Fin.castAdd N p) = y (Fin.castAdd N p)) : D.ctx b x = D.ctx b y := by
  classical
  unfold Dag.ctx
  have e : D.Top (fun f => D.val x f = true) b ↔ D.Top (fun f => D.val y f = true) b :=
    ⟨tr_top_mono (fun f hf hv => by rw [← Api.api_val_xonly D hf h]; exact hv),
     tr_top_mono (fun f hf hv => by rw [Api.api_val_xonly D hf h]; exact hv)⟩
  by_cases hb : D.Top (fun f => D.val x f = true) b
  · rw [decide_eq_true hb, decide_eq_true (e.1 hb)]
  · rw [decide_eq_false hb, decide_eq_false (fun h' => hb (e.2 h'))]
theorem tr_pt_ep (p w : Fin N) (q : Fin N) :
    pt p (Fin.castAdd N q) = ep p w (Fin.castAdd N q) := by
  simp only [pt, ep, inp, Fin.addCases_left]
def tr_Old (D D' : Dag N) (u : ℕ) : Prop :=
  u < N + N + D'.size ∧ D'.deg u ≤ 1 ∧ ∀ m, D'.Reach u m → N + N ≤ m →
    m ∈ D.M ∨ m ∈ D.X ∨ (N + N + D.size ≤ m ∧ m < N + N + D'.size)
def tr_Good4 (D D' : Dag N) (len u : ℕ) : Prop :=
  tr_Old D D' u ∨ (N + N + D'.size ≤ u ∧ u < N + N + len)
def tr_NewG (D D' : Dag N) (j : ℕ) (g : G) : Prop :=
  (∃ i v, g = .and i v ∧ tr_Old D D' i ∧ D'.deg i = 0 ∧ tr_Old D D' v) ∨
    (∃ u v, g = .or u v ∧ tr_Good4 D D' j u ∧ tr_Good4 D D' j v)
def tr_Base (D D' : Dag N) (gs : List G) : Prop :=
  D'.gates <+: gs ∧ ∀ j g, D'.size ≤ j → gs[j]? = some g → tr_NewG D D' j g
theorem tr_Good4_mono {D D' : Dag N} {j len u : ℕ} (h : tr_Good4 D D' j u) (hj : j ≤ len) :
    tr_Good4 D D' len u := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h.1, by omega⟩
theorem tr_Good4_lt {D D' : Dag N} {len u : ℕ} (h : tr_Good4 D D' len u)
    (hl : D'.size ≤ len) : u < N + N + len := by
  rcases h with h | h
  · have := h.1; omega
  · exact h.2
theorem tr_Base_append {D D' : Dag N} {gs : List G} (h : tr_Base D D' gs) {g : G}
    (hg : tr_NewG D D' gs.length g) : tr_Base D D' (gs ++ [g]) := by
  refine ⟨h.1.trans (List.prefix_append gs [g]), fun j g' hj hg' => ?_⟩
  by_cases hjl : j < gs.length
  · rw [List.getElem?_append_left hjl] at hg'
    exact h.2 j g' hj hg'
  · by_cases hje : j = gs.length
    · subst hje
      simp at hg'
      subst hg'
      exact hg
    · have : (gs ++ [g])[j]? = none := by
        rw [List.getElem?_eq_none_iff]; simp; omega
      rw [this] at hg'; cases hg'
theorem tr_val_old {D D' : Dag N} {gs : List G} (hB : tr_Base D D' gs) {u : ℕ}
    (hu : u < N + N + D'.size) (x : Fin (N + N) → Bool) :
    (⟨gs, D.out⟩ : Dag N).val x u = D'.val x u :=
  tr_val_prefix hB.1 D'.out D.out x u hu
open Classical in
noncomputable def tr_psi (D D' : Dag N) (b : ℕ) : Option ℕ :=
  if h : ∃ i, i < N + N + D'.size ∧ D'.deg i = 0 ∧ (∀ x, D'.val x i = D.ctx b x) ∧
      D'.coneOf {i} ⊆ D.X ∪ Finset.Ico (N + N + D.size) (N + N + D'.size)
  then some h.choose else none
theorem tr_psi_some {D D' : Dag N} {b i : ℕ} (h : tr_psi D D' b = some i) :
    i < N + N + D'.size ∧ D'.deg i = 0 ∧ (∀ x, D'.val x i = D.ctx b x) ∧
      D'.coneOf {i} ⊆ D.X ∪ Finset.Ico (N + N + D.size) (N + N + D'.size) := by
  unfold tr_psi at h
  split_ifs at h with hh
  cases h
  exact hh.choose_spec
theorem tr_psi_none {D D' : Dag N}
    (hit : ∀ b, D.IsItem b → (∀ x, D.ctx b x = true) ∨
      ∃ i, D'.deg i = 0 ∧ (∀ x, D'.val x i = D.ctx b x) ∧
        D'.coneOf {i} ⊆ D.X ∪ Finset.Ico (N + N + D.size) (N + N + D'.size))
    {b : ℕ} (hb : D.IsItem b) (h : tr_psi D D' b = none) :
    (∀ x, D.ctx b x = true) ∨ (∀ x, D.ctx b x = false) := by
  rcases hit b hb with h1 | ⟨i, hi0, hiv, hic⟩
  · exact Or.inl h1
  · right
    intro x
    by_contra hx
    have hx' : D'.val x i = true := by rw [hiv]; simpa using hx
    have hlt := tr_val_lt hx'
    unfold tr_psi at h
    rw [dif_pos ⟨i, hlt, hi0, hiv, hic⟩] at h
    cases h
theorem tr_old_psi {D D' : Dag N} {b i : ℕ} (h : tr_psi D D' b = some i) : tr_Old D D' i := by
  classical
  obtain ⟨hlt, h0, -, hc⟩ := tr_psi_some h
  refine ⟨hlt, by omega, fun m hr hm => ?_⟩
  have hmi := tr_reach_le hr
  have hmc : m ∈ D'.coneOf {i} := by
    unfold Dag.coneOf
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    exact ⟨by omega, hm, i, rfl, hr⟩
  rcases Finset.mem_union.1 (hc hmc) with h1 | h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (Finset.mem_Ico.1 h1))
theorem tr_old_kid {D D' : Dag N} (hpre : D.gates <+: D'.gates) {b r : ℕ} (hb : b ∈ D.cone)
    (hk : D.Kid b r) (hd : D.deg r ≤ 1) : tr_Old D D' r := by
  classical
  have hbl := Finset.mem_Ico.1 (Api.coneOf_sub D {D.out} hb)
  have hrb : r < b := by obtain ⟨_, _, _, hlt⟩ := hk; exact hlt
  have hsz : D.size ≤ D'.size := hpre.length_le
  have hrl : r < N + N + D.gates.length := by unfold Dag.size at hbl; omega
  have hreach : D.Reach D.out b := by
    unfold Dag.cone Dag.coneOf at hb
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton] at hb
    obtain ⟨-, -, r0, rfl, h⟩ := hb
    exact h
  refine ⟨by omega, ?_, fun m hr hm => ?_⟩
  · rw [tr_deg_prefix hpre D.out D'.out r hrl]; exact hd
  · have hr' : D.Reach r m := tr_reach_prefix hpre D.out D'.out hrl hr
    have hml := tr_reach_le hr'
    have hcone : m ∈ D.cone := tr_mem_cone hm (by omega) ((hreach.tail hk).trans hr')
    have hdm := le_trans (Api.api_reach_deg D hr') hd
    by_cases h0 : D.deg m = 0
    · exact Or.inr (Or.inl (Finset.mem_filter.2 ⟨hcone, h0⟩))
    · exact Or.inl (Finset.mem_filter.2 ⟨hcone, by omega⟩)
def tr_other (D : Dag N) (b r : ℕ) : ℕ :=
  match D.gateAt b with
  | some (.and a a') => if r = a then a' else a
  | _ => r
theorem tr_other_spec {D : Dag N} (hwf : D.WF) {b r : ℕ} (hb : b ∈ D.Tmix) (hk : D.Kid b r) :
    D.Kid b (tr_other D b r) ∧ D.deg (tr_other D b r) = 1 ∧
      ∀ x, D.IsFactor b x → x ≠ r → x = tr_other D b r := by
  classical
  obtain ⟨hT, a, a', hg, h1, h2⟩ := Finset.mem_filter.1 hb
  have ha := hwf _ _ hg a (by simp [G.kids])
  have ha' := hwf _ _ hg a' (by simp [G.kids])
  have hT2 := (Finset.mem_filter.1 hT).2
  have ho : tr_other D b r = if r = a then a' else a := by simp only [tr_other, hg]
  obtain ⟨g, hg1, hr1, -⟩ := hk
  rw [hg] at hg1
  cases hg1
  simp only [G.kids, List.mem_cons, List.not_mem_nil, or_false] at hr1
  rw [ho]
  refine ⟨?_, ?_, fun x hx hxr => ?_⟩
  · split_ifs
    · exact tr_kid_of hg (by simp [G.kids]) ha'
    · exact tr_kid_of hg (by simp [G.kids]) ha
  · split_ifs <;> assumption
  · rcases hx with ⟨h3, -⟩ | ⟨-, g, hg2, hx2, -⟩
    · omega
    · rw [hg] at hg2
      cases hg2
      simp only [G.kids, List.mem_cons, List.not_mem_nil, or_false] at hx2
      split_ifs with hra
      · rcases hx2 with rfl | rfl
        · exact absurd hra.symm hxr
        · rfl
      · rcases hx2 with rfl | rfl
        · rfl
        · rcases hr1 with rfl | rfl
          · exact absurd rfl hra
          · exact absurd rfl hxr
open Classical in
noncomputable def tr_term (D D' : Dag N) (gs : List G) (b r : ℕ) : List G × Option ℕ :=
  if D.deg b ≤ 1 then (gs, tr_psi D D' b)
  else
    match tr_psi D D' b with
    | some i => (gs ++ [.and i (tr_other D b r)], some (N + N + gs.length))
    | none => (gs, if ∀ x, D.ctx b x = true then some (tr_other D b r) else none)
def tr_put (N : ℕ) (gs : List G) (ρ : Fin N → Option ℕ) (w : Fin N) :
    Option ℕ → List G × (Fin N → Option ℕ)
  | none => (gs, ρ)
  | some v =>
    match ρ w with
    | none => (gs, Function.update ρ w (some v))
    | some u => (gs ++ [.or u v], Function.update ρ w (some (N + N + gs.length)))
noncomputable def tr_job (D D' : Dag N) (st : List G × (Fin N → Option ℕ))
    (j : ℕ × ℕ × Fin N) : List G × (Fin N → Option ℕ) :=
  tr_put N (tr_term D D' st.1 j.1 j.2.1).1 st.2 j.2.2 (tr_term D D' st.1 j.1 j.2.1).2
def tr_Cond (D : Dag N) (j : ℕ × ℕ × Fin N) (p : Fin N) : Prop :=
  D.ctx j.1 (pt p) = true ∧ ∀ x, D.IsFactor j.1 x → D.val (ep p j.2.2) x = true
def tr_cost (D : Dag N) (j : ℕ × ℕ × Fin N) : ℕ := if D.deg j.1 ≤ 1 then 1 else 2
def tr_Snd (I : Fin N → Fin N → Prop) (D : Dag N) (gs : List G) (w : Fin N) (u : ℕ) : Prop :=
  ∀ z, z (Fin.natAdd N w) = true → (⟨gs, D.out⟩ : Dag N).val z u = true →
    ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true
theorem tr_val_lift {D D' : Dag N} {gs gs' : List G} (hB : tr_Base D D' gs) (hp : gs <+: gs')
    {u : ℕ} (hu : tr_Good4 D D' gs.length u) (x : Fin (N + N) → Bool) :
    (⟨gs', D.out⟩ : Dag N).val x u = (⟨gs, D.out⟩ : Dag N).val x u :=
  tr_val_prefix hp D.out D.out x u (tr_Good4_lt hu hB.1.length_le)
theorem tr_lift {I : Fin N → Fin N → Prop} {D D' : Dag N} {gs gs' : List G}
    (hB : tr_Base D D' gs) (hp : gs <+: gs') {w : Fin N} {u : ℕ}
    (hu : tr_Good4 D D' gs.length u ∧ tr_Snd I D gs w u) :
    tr_Good4 D D' gs'.length u ∧ tr_Snd I D gs' w u := by
  refine ⟨tr_Good4_mono hu.1 hp.length_le, fun z hz hv => hu.2 z hz ?_⟩
  rwa [tr_val_lift hB hp hu.1] at hv
theorem tr_term_ok (I : Fin N → Fin N → Prop) {D D' : Dag N} (hwf : D.WF)
    (hc : Computes I D.fn) (hd : D.deg D.out ≤ 2) (hpre : D.gates <+: D'.gates)
    (hit : ∀ b, D.IsItem b → (∀ x, D.ctx b x = true) ∨
      ∃ i, D'.deg i = 0 ∧ (∀ x, D'.val x i = D.ctx b x) ∧
        D'.coneOf {i} ⊆ D.X ∪ Finset.Ico (N + N + D.size) (N + N + D'.size))
    {gs : List G} (hB : tr_Base D D' gs) {b r : ℕ} {w : Fin N}
    (hj : (b, r, w) ∈ tr_jobs D) :
    tr_Base D D' (tr_term D D' gs b r).1 ∧ gs <+: (tr_term D D' gs b r).1 ∧
      (tr_term D D' gs b r).1.length + 1 ≤ gs.length + tr_cost D (b, r, w) ∧
      (∀ v, (tr_term D D' gs b r).2 = some v →
        tr_Good4 D D' (tr_term D D' gs b r).1.length v ∧ tr_Snd I D (tr_term D D' gs b r).1 w v) ∧
      (∀ p, tr_Cond D (b, r, w) p → ∃ v, (tr_term D D' gs b r).2 = some v ∧
        (⟨(tr_term D D' gs b r).1, D.out⟩ : Dag N).val (ep p w) v = true) := by
  classical
  obtain ⟨hb, hr, hm⟩ := tr_mem_jobs.1 hj
  have hsz : D'.size ≤ gs.length := hB.1.length_le
  have hxo : ∀ p, ∀ q : Fin N, pt p (Fin.castAdd N q) = ep p w (Fin.castAdd N q) :=
    fun p q => tr_pt_ep p w q
  by_cases h1 : D.deg b ≤ 1
  · have hrb : r = b := by
      rcases hr with ⟨-, rfl⟩ | ⟨hmix, -⟩
      · rfl
      · have := (Finset.mem_filter.1 (Finset.mem_filter.1 hmix).1).2; omega
    subst hrb
    have e : tr_term D D' gs r r = (gs, tr_psi D D' r) := by
      unfold tr_term; rw [if_pos h1]
    have hcost : tr_cost D (r, r, w) = 1 := by unfold tr_cost; rw [if_pos h1]
    rw [e, hcost]
    refine ⟨hB, List.prefix_refl _, le_rfl, fun v hv => ?_, fun p hp => ?_⟩
    · have hold := tr_old_psi hv
      obtain ⟨hlt, -, hval, -⟩ := tr_psi_some hv
      refine ⟨Or.inl hold, fun z hz hvz => ?_⟩
      rw [tr_val_old hB hlt, hval] at hvz
      exact tr_term_sound I hwf hc hd hb hm z hz hvz (fun x hx hxr => by
        rcases hx with ⟨-, rfl⟩ | ⟨hmix, -⟩
        · exact absurd rfl hxr
        · have := (Finset.mem_filter.1 (Finset.mem_filter.1 hmix).1).2; omega)
    · cases hps : tr_psi D D' r with
      | none =>
        rcases tr_psi_none hit hb hps with hall | hall
        · exact absurd hall (tr_no_const I hwf hc hd hb h1 hm)
        · have := hp.1; rw [hall] at this; cases this
      | some v =>
        obtain ⟨hlt, -, hval, -⟩ := tr_psi_some hps
        refine ⟨v, rfl, ?_⟩
        rw [tr_val_old hB hlt, hval, ← tr_ctx_xonly (hxo p)]
        exact hp.1
  · have hbm : b ∈ D.Tmix := by
      rcases hb.2 with h | h
      · exact absurd h h1
      · exact h
    have hkr : D.Kid b r := by
      rcases hr with ⟨h, -⟩ | ⟨-, h⟩
      · exact absurd h h1
      · exact h
    obtain ⟨hko, hdo, hfo⟩ := tr_other_spec hwf hbm hkr
    have hbc : b ∈ D.cone := (Finset.mem_filter.1 (Finset.mem_filter.1 hbm).1).1
    have hoo : tr_Old D D' (tr_other D b r) := tr_old_kid hpre hbc hko (by omega)
    have hol := hoo.1
    have hoD : (tr_other D b r) < N + N + D.gates.length := by
      have := Finset.mem_Ico.1 (Api.coneOf_sub D {D.out} hbc)
      obtain ⟨_, _, _, hlt⟩ := hko
      unfold Dag.size at this; omega
    have hvo : ∀ (gs' : List G), tr_Base D D' gs' → ∀ x,
        (⟨gs', D.out⟩ : Dag N).val x (tr_other D b r) = D.val x (tr_other D b r) := by
      intro gs' hB' x
      rw [tr_val_old hB' hol]
      exact tr_val_prefix hpre D.out D'.out x _ hoD
    have hrest : ∀ z, D.val z (tr_other D b r) = true →
        ∀ x, D.IsFactor b x → x ≠ r → D.val z x = true := by
      intro z hz x hx hxr
      rw [hfo x hx hxr]; exact hz
    have hcost : tr_cost D (b, r, w) = 2 := by unfold tr_cost; dsimp only; rw [if_neg h1]
    rw [hcost]
    cases hps : tr_psi D D' b with
    | some i =>
      have e : tr_term D D' gs b r =
          (gs ++ [.and i (tr_other D b r)], some (N + N + gs.length)) := by
        unfold tr_term; rw [if_neg h1, hps]
      rw [e]
      obtain ⟨hlt, hi0, hval, -⟩ := tr_psi_some hps
      have hold := tr_old_psi hps
      have hB' := tr_Base_append hB (g := .and i (tr_other D b r)) (Or.inl ⟨_, _, rfl, hold, hi0, hoo⟩)
      have hgate := tr_gateAt_last (N := N) gs (.and i (tr_other D b r)) D.out
      have hv : ∀ z, (⟨gs ++ [.and i (tr_other D b r)], D.out⟩ : Dag N).val z (N + N + gs.length) =
          (D.ctx b z && D.val z (tr_other D b r)) := by
        intro z
        rw [tr_val_and hgate (by omega) (by omega), tr_val_old hB' hlt, hval, hvo _ hB']
      refine ⟨hB', List.prefix_append _ _, by simp, fun v hv' => ?_, fun p hp => ?_⟩
      · cases hv'
        refine ⟨Or.inr ⟨by omega, by simp⟩, fun z hz hvz => ?_⟩
        rw [hv, Bool.and_eq_true] at hvz
        exact tr_term_sound I hwf hc hd hb hm z hz hvz.1 (hrest z hvz.2)
      · refine ⟨_, rfl, ?_⟩
        rw [hv, Bool.and_eq_true, ← tr_ctx_xonly (hxo p)]
        exact ⟨hp.1, hp.2 _ (Or.inr ⟨hbm, hko⟩)⟩
    | none =>
      by_cases hall : ∀ x, D.ctx b x = true
      · have e : tr_term D D' gs b r = (gs, some (tr_other D b r)) := by
          unfold tr_term; rw [if_neg h1, hps]; dsimp only; rw [if_pos hall]
        rw [e]
        refine ⟨hB, List.prefix_refl _, by dsimp only; omega, fun v hv' => ?_, fun p hp => ?_⟩
        · cases hv'
          refine ⟨Or.inl hoo, fun z hz hvz => ?_⟩
          rw [hvo _ hB] at hvz
          exact tr_term_sound I hwf hc hd hb hm z hz (hall z) (hrest z hvz)
        · refine ⟨_, rfl, ?_⟩
          rw [hvo _ hB]
          exact hp.2 _ (Or.inr ⟨hbm, hko⟩)
      · have e : tr_term D D' gs b r = (gs, none) := by
          unfold tr_term; rw [if_neg h1, hps]; dsimp only; rw [if_neg hall]
        rw [e]
        refine ⟨hB, List.prefix_refl _, by dsimp only; omega,
          fun v hv' => absurd hv' (by simp), fun p hp => ?_⟩
        rcases tr_psi_none hit hb hps with h2 | h2
        · exact absurd h2 hall
        · have := hp.1; rw [h2] at this; cases this
theorem tr_put_ok {I : Fin N → Fin N → Prop} {D D' : Dag N} {gs : List G}
    (hB : tr_Base D D' gs) {ρ : Fin N → Option ℕ}
    (hρ : ∀ w u, ρ w = some u → tr_Good4 D D' gs.length u ∧ tr_Snd I D gs w u)
    {w : Fin N} {t : Option ℕ}
    (ht : ∀ v, t = some v → tr_Good4 D D' gs.length v ∧ tr_Snd I D gs w v) :
    tr_Base D D' (tr_put N gs ρ w t).1 ∧ gs <+: (tr_put N gs ρ w t).1 ∧
      (tr_put N gs ρ w t).1.length ≤ gs.length + 1 ∧
      (∀ w0 u, (tr_put N gs ρ w t).2 w0 = some u →
        tr_Good4 D D' (tr_put N gs ρ w t).1.length u ∧ tr_Snd I D (tr_put N gs ρ w t).1 w0 u) ∧
      (∀ w0 u z, ρ w0 = some u → (⟨gs, D.out⟩ : Dag N).val z u = true →
        ∃ u', (tr_put N gs ρ w t).2 w0 = some u' ∧
          (⟨(tr_put N gs ρ w t).1, D.out⟩ : Dag N).val z u' = true) ∧
      (∀ v z, t = some v → (⟨gs, D.out⟩ : Dag N).val z v = true →
        ∃ u', (tr_put N gs ρ w t).2 w = some u' ∧
          (⟨(tr_put N gs ρ w t).1, D.out⟩ : Dag N).val z u' = true) := by
  have hsz : D'.size ≤ gs.length := hB.1.length_le
  cases t with
  | none =>
    simp only [tr_put]
    exact ⟨hB, List.prefix_refl _, by omega, hρ, fun w0 u z h hv => ⟨u, h, hv⟩,
      fun v z h => by cases h⟩
  | some v =>
    obtain ⟨hvg, hvs⟩ := ht v rfl
    cases hw : ρ w with
    | none =>
      simp only [tr_put, hw]
      refine ⟨hB, List.prefix_refl _, by omega, fun w0 u h => ?_, fun w0 u z h hv => ?_,
        fun v' z h hv => ?_⟩
      · by_cases e : w0 = w
        · subst e; rw [Function.update_self] at h; cases h; exact ⟨hvg, hvs⟩
        · rw [Function.update_of_ne e] at h; exact hρ w0 u h
      · by_cases e : w0 = w
        · subst e; rw [hw] at h; cases h
        · exact ⟨u, by rw [Function.update_of_ne e]; exact h, hv⟩
      · cases h; exact ⟨v, Function.update_self _ _ _, hv⟩
    | some u0 =>
      simp only [tr_put, hw]
      obtain ⟨hug, hus⟩ := hρ w u0 hw
      have hp : gs <+: gs ++ [G.or u0 v] := List.prefix_append _ _
      have hB' := tr_Base_append hB (Or.inr ⟨u0, v, rfl, hug, hvg⟩)
      have hul := tr_Good4_lt hug hsz
      have hvl := tr_Good4_lt hvg hsz
      have hnew : ∀ z, (⟨gs ++ [G.or u0 v], D.out⟩ : Dag N).val z (N + N + gs.length) =
          ((⟨gs, D.out⟩ : Dag N).val z u0 || (⟨gs, D.out⟩ : Dag N).val z v) := by
        intro z
        rw [tr_val_or (tr_gateAt_last gs _ D.out) hul hvl, tr_val_lift hB hp hug,
          tr_val_lift hB hp hvg]
      refine ⟨hB', hp, by simp, fun w0 u h => ?_, fun w0 u z h hv => ?_,
        fun v' z h hv => ?_⟩
      · by_cases e : w0 = w
        · subst e
          rw [Function.update_self] at h
          cases h
          refine ⟨Or.inr ⟨by omega, by simp⟩, fun z hz hvz => ?_⟩
          rw [hnew, Bool.or_eq_true] at hvz
          rcases hvz with h1 | h1
          · exact hus z hz h1
          · exact hvs z hz h1
        · rw [Function.update_of_ne e] at h
          exact tr_lift hB hp (hρ w0 u h)
      · by_cases e : w0 = w
        · subst e
          rw [hw] at h
          cases h
          refine ⟨_, Function.update_self _ _ _, ?_⟩
          rw [hnew, hv]; rfl
        · refine ⟨u, by rw [Function.update_of_ne e]; exact h, ?_⟩
          rw [tr_val_lift hB hp (hρ w0 u h).1]; exact hv
      · cases h
        refine ⟨_, Function.update_self _ _ _, ?_⟩
        rw [hnew, hv]; simp
def tr_Inv4 (I : Fin N → Fin N → Prop) (D D' : Dag N) (st : List G × (Fin N → Option ℕ))
    (Pl : List (ℕ × ℕ × Fin N)) : Prop :=
  tr_Base D D' st.1 ∧ st.1.length ≤ D'.size + (Pl.map (tr_cost D)).sum ∧
    (∀ w u, st.2 w = some u → tr_Good4 D D' st.1.length u ∧ tr_Snd I D st.1 w u) ∧
    (∀ j ∈ Pl, ∀ p, tr_Cond D j p → ∃ u, st.2 j.2.2 = some u ∧
      (⟨st.1, D.out⟩ : Dag N).val (ep p j.2.2) u = true)
theorem tr_job_ok (I : Fin N → Fin N → Prop) {D D' : Dag N} (hwf : D.WF)
    (hc : Computes I D.fn) (hd : D.deg D.out ≤ 2) (hpre : D.gates <+: D'.gates)
    (hit : ∀ b, D.IsItem b → (∀ x, D.ctx b x = true) ∨
      ∃ i, D'.deg i = 0 ∧ (∀ x, D'.val x i = D.ctx b x) ∧
        D'.coneOf {i} ⊆ D.X ∪ Finset.Ico (N + N + D.size) (N + N + D'.size))
    {st : List G × (Fin N → Option ℕ)} {Pl : List (ℕ × ℕ × Fin N)}
    (hI : tr_Inv4 I D D' st Pl) {j : ℕ × ℕ × Fin N} (hj : j ∈ tr_jobs D) :
    tr_Inv4 I D D' (tr_job D D' st j) (Pl ++ [j]) := by
  obtain ⟨gs, ρ⟩ := st
  obtain ⟨b, r, w⟩ := j
  obtain ⟨hB, hlen, hρ, hcov⟩ := hI
  dsimp only at hB hlen hρ hcov
  obtain ⟨hB1, hp1, hl1, ht1, hc1⟩ := tr_term_ok I hwf hc hd hpre hit hB hj
  unfold tr_job
  dsimp only
  generalize tr_term D D' gs b r = t at hB1 hp1 hl1 ht1 hc1 ⊢
  obtain ⟨gs1, t⟩ := t
  dsimp only at hB1 hp1 hl1 ht1 hc1 ⊢
  have hρ1 : ∀ w u, ρ w = some u → tr_Good4 D D' gs1.length u ∧ tr_Snd I D gs1 w u :=
    fun w u h => tr_lift hB hp1 (hρ w u h)
  obtain ⟨hB2, hp2, hl2, hρ2, hmono, hnew⟩ := tr_put_ok hB1 hρ1 ht1
  generalize tr_put N gs1 ρ w t = st2 at hB2 hp2 hl2 hρ2 hmono hnew ⊢
  obtain ⟨gs2, ρ2⟩ := st2
  dsimp only at hB2 hp2 hl2 hρ2 hmono hnew ⊢
  refine ⟨hB2, ?_, hρ2, ?_⟩
  · rw [List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  · intro j hj p hp
    rcases List.mem_append.1 hj with hj | hj
    · obtain ⟨u, hu, hv⟩ := hcov j hj p hp
      exact hmono _ u _ hu (by rw [tr_val_lift hB hp1 (hρ _ u hu).1]; exact hv)
    · simp only [List.mem_singleton] at hj
      subst hj
      obtain ⟨v, hv, hvv⟩ := hc1 p hp
      exact hnew v _ hv hvv
theorem tr_fold4 (I : Fin N → Fin N → Prop) {D D' : Dag N} (hwf : D.WF)
    (hc : Computes I D.fn) (hd : D.deg D.out ≤ 2) (hpre : D.gates <+: D'.gates)
    (hit : ∀ b, D.IsItem b → (∀ x, D.ctx b x = true) ∨
      ∃ i, D'.deg i = 0 ∧ (∀ x, D'.val x i = D.ctx b x) ∧
        D'.coneOf {i} ⊆ D.X ∪ Finset.Ico (N + N + D.size) (N + N + D'.size)) :
    ∀ (L : List (ℕ × ℕ × Fin N)) st Pl, (∀ j ∈ L, j ∈ tr_jobs D) → tr_Inv4 I D D' st Pl →
      tr_Inv4 I D D' (L.foldl (tr_job D D') st) (Pl ++ L) := by
  intro L
  induction L with
  | nil => intro st Pl _ hI; simpa using hI
  | cons j t ih =>
    intro st Pl hL hI
    rw [List.foldl_cons, show Pl ++ j :: t = (Pl ++ [j]) ++ t by simp]
    exact ih _ _ (fun j' h => hL j' (List.mem_cons_of_mem _ h))
      (tr_job_ok I hwf hc hd hpre hit hI (hL j (by simp)))
theorem tr_wf4 {D D' : Dag N} (hwf' : D'.WF) {gs : List G} (hB : tr_Base D D' gs) (o : ℕ) :
    (⟨gs, o⟩ : Dag N).WF := by
  intro i g hg c hc
  obtain ⟨hi, hg'⟩ := Api.gateAt_some hg
  dsimp only at hg'
  by_cases hj : i - (N + N) < D'.size
  · have e : (⟨gs, o⟩ : Dag N).gateAt i = (⟨D'.gates, D'.out⟩ : Dag N).gateAt i :=
      tr_gateAt_prefix hB.1 D'.out o (by unfold Dag.size at hj; omega)
    rw [e] at hg
    exact hwf' i g hg c hc
  · rcases hB.2 _ g (by omega) hg' with ⟨u, v, rfl, hu, -, hv⟩ | ⟨u, v, rfl, hu, hv⟩
    · have := hu.1; have := hv.1
      simp only [G.kids, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> omega
    · have := tr_Good4_lt hu (by omega)
      have := tr_Good4_lt hv (by omega)
      simp only [G.kids, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> omega
theorem tr_old_kid' {D D' : Dag N} {n m : ℕ} (hn : tr_Old D D' n) (hk : D'.Kid n m) :
    tr_Old D D' m := by
  obtain ⟨hl, hd, hr⟩ := hn
  have hml : m < n := by obtain ⟨_, _, _, h⟩ := hk; exact h
  refine ⟨by omega, le_trans (Api.deg_kid hk) hd, fun m' hr' hm' => ?_⟩
  exact hr m' (Relation.ReflTransGen.head hk hr') hm'
theorem tr_good4_final {D D' : Dag N} {gs : List G} (hB : tr_Base D D' gs) (o : ℕ) :
    ∀ n, tr_Good4 D D' gs.length n → (⟨gs, o⟩ : Dag N).deg n ≤ 1 ∧
      ∀ m, (⟨gs, o⟩ : Dag N).Kid n m → tr_Good4 D D' gs.length m := by
  have hsz : D'.size ≤ gs.length := hB.1.length_le
  have hdeg_old : ∀ u, tr_Old D D' u → (⟨gs, o⟩ : Dag N).deg u = D'.deg u := fun u hu =>
    tr_deg_prefix hB.1 D'.out o u hu.1
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn
  rcases hn with hn | ⟨hn1, hn2⟩
  · refine ⟨by rw [hdeg_old n hn]; exact hn.2.1, fun m hk => ?_⟩
    obtain ⟨g, hg, hmg, hmn⟩ := hk
    rw [tr_gateAt_prefix hB.1 D'.out o hn.1] at hg
    exact Or.inl (tr_old_kid' hn ⟨g, hg, hmg, hmn⟩)
  · cases hgs : gs[n - (N + N)]? with
    | none =>
      rw [List.getElem?_eq_none_iff] at hgs
      omega
    | some g =>
      have hgate : (⟨gs, o⟩ : Dag N).gateAt n = some g := by
        unfold Dag.gateAt
        rw [if_pos (by omega)]
        exact hgs
      rcases hB.2 _ g (by unfold Dag.size at hn1 ⊢; omega) hgs with
        ⟨u, v, rfl, hu, hu0, hv⟩ | ⟨u, v, rfl, hu, hv⟩
      · have hun : u < n := by have := hu.1; omega
        have hvn : v < n := by have := hv.1; omega
        refine ⟨?_, fun m hk => ?_⟩
        · rw [tr_deg_and hgate hun hvn, hdeg_old u hu, hdeg_old v hv, hu0]
          have := hv.2.1; omega
        · obtain ⟨g', hg', hmg, -⟩ := hk
          rw [hgate] at hg'
          cases hg'
          simp only [G.kids, List.mem_cons, List.not_mem_nil, or_false] at hmg
          rcases hmg with rfl | rfl
          · exact Or.inl hu
          · exact Or.inl hv
      · have hj : n - (N + N) ≤ gs.length := by omega
        have hun : u < n := by have := tr_Good4_lt hu (by unfold Dag.size at hn1 ⊢; omega); omega
        have hvn : v < n := by have := tr_Good4_lt hv (by unfold Dag.size at hn1 ⊢; omega); omega
        have hu2 := tr_Good4_mono hu hj
        have hv2 := tr_Good4_mono hv hj
        refine ⟨?_, fun m hk => ?_⟩
        · rw [tr_deg_or hgate hun hvn]
          have := (ih u hun hu2).1
          have := (ih v hvn hv2).1
          omega
        · obtain ⟨g', hg', hmg, -⟩ := hk
          rw [hgate] at hg'
          cases hg'
          simp only [G.kids, List.mem_cons, List.not_mem_nil, or_false] at hmg
          rcases hmg with rfl | rfl
          · exact hu2
          · exact hv2
theorem card16_form (I : Fin N → Fin N → Prop) (D : Dag N) (hwf : D.WF)
    (hc : Computes I D.fn) (hd : D.deg D.out ≤ 2) :
    ∃ (F : Dag N) (W : Finset (Fin N)) (R : Fin N → ℕ), Dag.SoundPartialForm I F W R ∧
      D.markerEdges I ⊆ F.countedEdges W R ∧
      (F.rootCone W R).card ≤ D.M.card + D.X.card + 4 * D.T.card := by
  classical
  obtain ⟨D', hpre, hwf', hsz', hit⟩ := card15c_contexts D hwf hd
  have hinit : tr_Inv4 I D D' (D'.gates, fun _ => none) [] := by
    refine ⟨⟨List.prefix_refl _, fun j g hj hg => ?_⟩, by simp [Dag.size], ?_, ?_⟩
    rotate_left
    · intro w u h; simp at h
    · intro j hj; simp at hj
    have : D'.gates[j]? = none :=
      List.getElem?_eq_none_iff.2 (by unfold Dag.size at hj; omega)
    rw [this] at hg
    cases hg
  have hfin := tr_fold4 I hwf hc hd hpre hit (tr_jobs D).toList _ []
    (fun j hj => Finset.mem_toList.1 hj) hinit
  rw [List.nil_append] at hfin
  generalize List.foldl (tr_job D D') (D'.gates, fun _ => none) (tr_jobs D).toList = st at hfin
  obtain ⟨hB, hlen, hρ, hcov⟩ := hfin
  have hroot : ∀ w, (st.2 w).isSome → ∃ u, st.2 w = some u := fun w h =>
    Option.isSome_iff_exists.1 h
  refine ⟨⟨st.1, D.out⟩, Finset.univ.filter (fun w => (st.2 w).isSome),
    fun w => (st.2 w).getD 0, ⟨tr_wf4 hwf' hB D.out, ?_, ?_⟩, ?_, ?_⟩
  · intro w hw
    obtain ⟨u, hu⟩ := hroot w (Finset.mem_filter.1 hw).2
    simp only [hu, Option.getD_some]
    exact (tr_good4_final hB D.out u (hρ w u hu).1).1
  · rintro z ⟨w, hw, hz, hv⟩
    obtain ⟨u, hu⟩ := hroot w (Finset.mem_filter.1 hw).2
    simp only [hu, Option.getD_some] at hv
    exact (hρ w u hu).2 z hz hv
  · rintro ⟨p, w⟩ he
    unfold Dag.markerEdges at he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    obtain ⟨-, b, hb, hctx, hfac, r, hr, hm⟩ := he
    have hj : (b, r, w) ∈ (tr_jobs D).toList :=
      Finset.mem_toList.2 (tr_mem_jobs.2 ⟨hb, hr, hm⟩)
    obtain ⟨u, hu, hv⟩ := hcov _ hj p ⟨hctx, hfac⟩
    unfold Dag.countedEdges
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    dsimp only at hu hv
    refine ⟨by simp [hu], ?_⟩
    simp only [hu, Option.getD_some]
    exact hv
  · have hsz : D'.size ≤ st.1.length := hB.1.length_le
    have hDD : D.size ≤ D'.size := hpre.length_le
    have hsub : (⟨st.1, D.out⟩ : Dag N).rootCone (Finset.univ.filter (fun w => (st.2 w).isSome))
        (fun w => (st.2 w).getD 0) ⊆
        (D.M ∪ D.X) ∪ Finset.Ico (N + N + D.size) (N + N + st.1.length) := by
      intro m hm
      unfold Dag.rootCone Dag.coneOf at hm
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image] at hm
      obtain ⟨-, hm1, r, ⟨w, hw, rfl⟩, hr⟩ := hm
      obtain ⟨u, hu⟩ := hroot w hw.2
      simp only [hu, Option.getD_some] at hr
      have hg : tr_Good4 D D' st.1.length m := by
        clear hm1
        induction hr with
        | refl => exact (hρ w u hu).1
        | tail _ hk ih => exact (tr_good4_final hB D.out _ ih).2 _ hk
      rcases hg with hold | hnew
      · rcases hold.2.2 m Relation.ReflTransGen.refl hm1 with h | h | h
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
        · exact Finset.mem_union_right _ (Finset.mem_Ico.2 ⟨h.1, by omega⟩)
      · exact Finset.mem_union_right _ (Finset.mem_Ico.2 ⟨by omega, hnew.2⟩)
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (D.M ∪ D.X) (Finset.Ico (N + N + D.size) (N + N + st.1.length))
    have h3 := Finset.card_union_le D.M D.X
    have h4 : (Finset.Ico (N + N + D.size) (N + N + st.1.length)).card =
        st.1.length - D.size := by rw [Nat.card_Ico]; omega
    have hsum : ((tr_jobs D).toList.map (tr_cost D)).sum =
        ((tr_jobs D).filter (fun j => D.deg j.1 ≤ 1)).card +
          2 * ((tr_jobs D).filter (fun j => ¬ D.deg j.1 ≤ 1)).card := by
      rw [Finset.sum_map_toList]
      unfold tr_cost
      rw [Finset.sum_ite]
      simp [Finset.sum_const, smul_eq_mul, mul_comm]
    have hj1 := tr_jobs1_card I hwf hc hd
    have hj2 := tr_jobs2_card (D := D)
    have hT := tr_T_split D
    show ((⟨st.1, D.out⟩ : Dag N).rootCone _ _).card ≤ _
    omega
end Deg2
namespace Deg2.Bridge
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Deg2
variable {N : ℕ}
theorem api_prefix (D D' : Dag N) (h : D.gates <+: D'.gates) (i : ℕ) (hi : i < N + N + D.size)
    (x : Fin (N + N) → Bool) : D'.val x i = D.val x i ∧ D'.deg i = D.deg i := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    have hv : ∀ a, (if _ : a < i then D'.val x a else false) =
        (if _ : a < i then D.val x a else false) := by
      intro a
      split_ifs with ha
      · exact (ih a ha (by omega)).1
      · rfl
    have hd : ∀ a, (if _ : a < i then D'.deg a else 0) = (if _ : a < i then D.deg a else 0) := by
      intro a
      split_ifs with ha
      · exact (ih a ha (by omega)).2
      · rfl
    have hg : ¬ i < N + N → D'.gates[i - (N + N)]? = D.gates[i - (N + N)]? := by
      intro h0
      obtain ⟨t, ht⟩ := h
      rw [← ht, List.getElem?_append_left (by unfold Dag.size at hi; omega)]
    constructor
    · conv_lhs => rw [Dag.val]
      conv_rhs => rw [Dag.val]
      split_ifs with h0
      · rfl
      · rw [hg h0]
        cases D.gates[i - (N + N)]? with
        | none => rfl
        | some g =>
          cases g with
          | and a b => dsimp only; rw [hv a, hv b]
          | or a b => dsimp only; rw [hv a, hv b]
          | cst v => rfl
    · conv_lhs => rw [Dag.deg]
      conv_rhs => rw [Dag.deg]
      by_cases h0 : i < N + N
      · rw [if_pos h0, if_pos h0]
      · rw [if_neg h0, if_neg h0, hg h0]
        cases D.gates[i - (N + N)]? with
        | none => rfl
        | some g =>
          cases g with
          | and a b => dsimp only; rw [hd a, hd b]
          | or a b => dsimp only; rw [hd a, hd b]
          | cst v => rfl
def gval (r : ℕ → Bool) : G → Bool
  | .and a b => r a && r b
  | .or a b => r a || r b
  | .cst v => v
def gdeg (r : ℕ → ℕ) : G → ℕ
  | .and a b => r a + r b
  | .or a b => max (r a) (r b)
  | .cst _ => 0
theorem val_deg_ge (D : Dag N) {i : ℕ} (hi : N + N + D.size ≤ i) (x : Fin (N + N) → Bool) :
    D.val x i = false ∧ D.deg i = 0 := by
  have hn : D.gates[i - (N + N)]? = none := by
    rw [List.getElem?_eq_none]; unfold Dag.size at hi; omega
  constructor
  · rw [Dag.val, dif_neg (by omega), hn]
  · rw [Dag.deg, if_neg (by omega), hn]
theorem top_snoc (D D' : Dag N) (g : G) (h : D'.gates = D.gates ++ [g]) (x : Fin (N + N) → Bool) :
    D'.val x (N + N + D.size) =
        gval (fun a => if _ : a < N + N + D.size then D.val x a else false) g ∧
      D'.deg (N + N + D.size) = gdeg (fun a => if _ : a < N + N + D.size then D.deg a else 0) g := by
  have hp : D.gates <+: D'.gates := h ▸ List.prefix_append _ _
  have hv : ∀ a, (if _ : a < N + N + D.size then D'.val x a else false) =
      (if _ : a < N + N + D.size then D.val x a else false) := by
    intro a
    split_ifs with ha
    · exact (api_prefix D D' hp a ha x).1
    · rfl
  have hd : ∀ a, (if _ : a < N + N + D.size then D'.deg a else 0) =
      (if _ : a < N + N + D.size then D.deg a else 0) := by
    intro a
    split_ifs with ha
    · exact (api_prefix D D' hp a ha x).2
    · rfl
  have hg : D'.gates[N + N + D.size - (N + N)]? = some g := by
    rw [h, Nat.add_sub_cancel_left, List.getElem?_append_right (by unfold Dag.size; omega)]
    simp [Dag.size]
  constructor
  · rw [Dag.val, dif_neg (by omega), hg]
    cases g with
    | and a b => dsimp only; rw [hv a, hv b]; rfl
    | or a b => dsimp only; rw [hv a, hv b]; rfl
    | cst v => rfl
  · rw [Dag.deg, if_neg (by omega), hg]
    cases g with
    | and a b => dsimp only; rw [hd a, hd b]; rfl
    | or a b => dsimp only; rw [hd a, hd b]; rfl
    | cst v => rfl
theorem getD_ge_false {l : List Bool} {k : ℕ} (h : l.length ≤ k) : l.getD k false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl
theorem getD_ge_zero {l : List ℕ} {k : ℕ} (h : l.length ≤ k) : l.getD k 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl
theorem trGate_val (i : ℕ) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (r : ℕ → Bool) (hr : ∀ k, i ≤ k → r k = false) :
    gval r (trGate i g) = g.op.eval (g.inputs.map r) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hl⟩ := hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · rcases hop with rfl | rfl <;> simp [trGate, gval, GateOp.eval]
  · rcases hop with rfl | rfl <;> simp only [trGate] <;>
      (split_ifs with ha
       · simp [gval, GateOp.eval]
       · simp [gval, GateOp.eval, hr a (by omega)])
  · rcases hop with rfl | rfl <;> simp only [trGate] <;> split_ifs with h1 h2 h3 <;>
      simp only [gval, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.any_cons,
        List.all_nil, List.any_nil, id, Bool.and_true, Bool.or_false]
    · by_cases ha : a < i
      · rw [hr b (by omega), Bool.and_false]
      · rw [hr a (by omega), Bool.false_and]
    · rw [hr b (by omega), Bool.or_false, Bool.or_self]
    · rw [hr a (by omega), Bool.false_or, Bool.or_self]
    · rw [hr a (by omega), hr b (by omega), Bool.or_false]
  · simp at hl
theorem gdeg_mono {r r' : ℕ → ℕ} (h : ∀ k, r k ≤ r' k) (g : G) : gdeg r g ≤ gdeg r' g := by
  cases g with
  | and a b => exact Nat.add_le_add (h a) (h b)
  | or a b => exact max_le_max (h a) (h b)
  | cst v => exact le_rfl
theorem trGate_deg (i : ℕ) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (d : List ℕ) : gdeg (fun k => d.getD k 0) (trGate i g) ≤ g.lineDegree d := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hl⟩ := hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · rcases hop with rfl | rfl <;> simp [trGate, gdeg]
  · rcases hop with rfl | rfl <;> simp only [trGate] <;> split_ifs with ha <;>
      simp [gdeg, Gate.lineDegree]
  · rcases hop with rfl | rfl <;> simp only [trGate] <;> split_ifs with h1 h2 h3 <;>
      simp [gdeg, Gate.lineDegree]
  · simp at hl
theorem toGate_val (r : ℕ → Bool) (g : G) : gval r g = g.toGate.op.eval (g.toGate.inputs.map r) := by
  cases g with
  | and a b => simp [gval, G.toGate, GateOp.eval]
  | or a b => simp [gval, G.toGate, GateOp.eval]
  | cst v => cases v <;> simp [gval, G.toGate, GateOp.eval]
theorem toGate_deg (d : List ℕ) (g : G) : gdeg (fun k => d.getD k 0) g = g.toGate.lineDegree d := by
  cases g with
  | and a b => simp [gdeg, G.toGate, Gate.lineDegree]
  | or a b => simp [gdeg, G.toGate, Gate.lineDegree]
  | cst v => cases v <;> simp [gdeg, G.toGate, Gate.lineDegree]
open LineDegTest in
theorem card03c_val (C : Circuit) (hC : Monotone2 C) (x : Fin (N + N) → Bool) (i : ℕ) :
    (ofCircuit N C).val x i = (C.wires (List.ofFn x)).getD i false := by
  obtain ⟨gs, o⟩ := C
  induction gs using List.reverseRecOn generalizing i with
  | nil =>
    change _ = (List.ofFn x).getD i false
    rw [ofFn_getD, Dag.val]
    split_ifs with h
    · rfl
    · simp [ofCircuit]
  | append_singleton gs g ih =>
    have ih := fun k => ih k (fun g' hg' => hC g' (List.mem_append_left _ hg'))
    have hgC := hC g (List.mem_append_right _ (List.mem_singleton_self g))
    have hsz : (ofCircuit N ⟨gs, o⟩).size = gs.length := by simp [ofCircuit, Dag.size]
    have hgates : (ofCircuit N ⟨gs ++ [g], o⟩).gates =
        (ofCircuit N ⟨gs, o⟩).gates ++ [trGate (N + N + (ofCircuit N ⟨gs, o⟩).size) g] := by
      rw [hsz]; simp [ofCircuit, List.mapIdx_concat]
    have hlen : (W gs (List.ofFn x)).length = N + N + (ofCircuit N ⟨gs, o⟩).size := by
      rw [W_length, hsz]; simp
    change _ = (W (gs ++ [g]) (List.ofFn x)).getD i false
    rw [W_snoc, getD_snoc, hlen]
    rcases lt_trichotomy i (N + N + (ofCircuit N ⟨gs, o⟩).size) with h | rfl | h
    · rw [if_pos h, (api_prefix _ _ (hgates ▸ List.prefix_append _ _) i h x).1]
      exact ih i
    · rw [if_neg (lt_irrefl _), if_pos rfl, (top_snoc _ _ _ hgates x).1]
      have hr : (fun a => if _ : a < N + N + (ofCircuit N ⟨gs, o⟩).size then
          (ofCircuit N ⟨gs, o⟩).val x a else false) = fun a => (W gs (List.ofFn x)).getD a false := by
        funext a
        split_ifs with ha
        · exact ih a
        · exact (getD_ge_false (by omega)).symm
      rw [hr]
      exact trGate_val _ g hgC _ (fun k hk => getD_ge_false (by omega))
    · rw [if_neg (by omega), if_neg (by omega)]
      refine (val_deg_ge _ ?_ x).1
      unfold Dag.size; rw [hgates]; simp only [List.length_append, List.length_singleton]
      unfold Dag.size at h; omega
open LineDegTest in
theorem card03d_deg (C : Circuit) (hC : Monotone2 C) (i : ℕ) :
    (ofCircuit N C).deg i ≤ (C.lineDegrees (N + N) (lineMarks N)).getD i 0 := by
  obtain ⟨gs, o⟩ := C
  induction gs using List.reverseRecOn generalizing i with
  | nil =>
    change _ ≤ (Dg [] (N + N) (lineMarks N)).getD i 0
    rw [Dag.deg]
    by_cases h : i < N + N
    · rw [if_pos h]
      simp [Dg, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range, h, lineMarks]
    · rw [if_neg h]
      simp [ofCircuit]
  | append_singleton gs g ih =>
    have ih := fun k => ih k (fun g' hg' => hC g' (List.mem_append_left _ hg'))
    have hgC := hC g (List.mem_append_right _ (List.mem_singleton_self g))
    have hsz : (ofCircuit N ⟨gs, o⟩).size = gs.length := by simp [ofCircuit, Dag.size]
    have hgates : (ofCircuit N ⟨gs ++ [g], o⟩).gates =
        (ofCircuit N ⟨gs, o⟩).gates ++ [trGate (N + N + (ofCircuit N ⟨gs, o⟩).size) g] := by
      rw [hsz]; simp [ofCircuit, List.mapIdx_concat]
    have hlen : (Dg gs (N + N) (lineMarks N)).length = N + N + (ofCircuit N ⟨gs, o⟩).size := by
      rw [Dg_length, hsz]
    change _ ≤ (Dg (gs ++ [g]) (N + N) (lineMarks N)).getD i 0
    rw [Dg_snoc, getD_snoc, hlen]
    rcases lt_trichotomy i (N + N + (ofCircuit N ⟨gs, o⟩).size) with h | rfl | h
    · rw [if_pos h, (api_prefix _ _ (hgates ▸ List.prefix_append _ _) i h (fun _ => false)).2]
      exact ih i
    · rw [if_neg (lt_irrefl _), if_pos rfl, (top_snoc _ _ _ hgates (fun _ => false)).2]
      refine le_trans (gdeg_mono (r' := fun k => (Dg gs (N + N) (lineMarks N)).getD k 0) ?_ _)
        (trGate_deg _ g hgC _)
      intro a
      split_ifs with ha
      · exact ih a
      · exact Nat.zero_le _
    · rw [(val_deg_ge _ ?_ (fun _ => false)).2]
      · exact Nat.zero_le _
      unfold Dag.size; rw [hgates]; simp only [List.length_append, List.length_singleton]
      unfold Dag.size at h; omega
open LineDegTest in
theorem card03r_val (D : Dag N) (x : Fin (N + N) → Bool) (i : ℕ) :
    (D.toCircuit.wires (List.ofFn x)).getD i false = D.val x i ∧
      (D.toCircuit.lineDegrees (N + N) (lineMarks N)).getD i 0 = D.deg i := by
  obtain ⟨gs, o⟩ := D
  induction gs using List.reverseRecOn generalizing i with
  | nil =>
    change (List.ofFn x).getD i false = _ ∧ (Dg [] (N + N) (lineMarks N)).getD i 0 = _
    rw [ofFn_getD, Dag.val, Dag.deg]
    by_cases h : i < N + N
    · rw [dif_pos h, dif_pos h, if_pos h]
      simp [Dg, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range, h, lineMarks]
    · rw [dif_neg h, dif_neg h, if_neg h]
      simp [Dg, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range, h]
  | append_singleton gs g ih =>
    have hsz : (⟨gs, o⟩ : Dag N).size = gs.length := rfl
    have hgates : (⟨gs ++ [g], o⟩ : Dag N).gates = (⟨gs, o⟩ : Dag N).gates ++ [g] := rfl
    have hlenW : (W (gs.map G.toGate) (List.ofFn x)).length = N + N + (⟨gs, o⟩ : Dag N).size := by
      rw [W_length, hsz]; simp
    have hlenD : (Dg (gs.map G.toGate) (N + N) (lineMarks N)).length =
        N + N + (⟨gs, o⟩ : Dag N).size := by
      rw [Dg_length, hsz]; simp
    change (W ((gs ++ [g]).map G.toGate) (List.ofFn x)).getD i false = _ ∧
      (Dg ((gs ++ [g]).map G.toGate) (N + N) (lineMarks N)).getD i 0 = _
    rw [List.map_append, List.map_singleton, W_snoc, Dg_snoc, getD_snoc, getD_snoc, hlenW, hlenD]
    have ih' : ∀ k, (W (gs.map G.toGate) (List.ofFn x)).getD k false = (⟨gs, o⟩ : Dag N).val x k ∧
        (Dg (gs.map G.toGate) (N + N) (lineMarks N)).getD k 0 = (⟨gs, o⟩ : Dag N).deg k := ih
    rcases lt_trichotomy i (N + N + (⟨gs, o⟩ : Dag N).size) with h | rfl | h
    · rw [if_pos h, if_pos h, (api_prefix _ _ (hgates ▸ List.prefix_append _ _) i h x).1,
        (api_prefix _ _ (hgates ▸ List.prefix_append _ _) i h x).2]
      exact ih' i
    · rw [if_neg (lt_irrefl _), if_pos rfl, if_neg (lt_irrefl _), if_pos rfl,
        (top_snoc _ _ _ hgates x).1, (top_snoc _ _ _ hgates x).2]
      have hr : (fun a => if _ : a < N + N + (⟨gs, o⟩ : Dag N).size then
          (⟨gs, o⟩ : Dag N).val x a else false) =
          fun a => (W (gs.map G.toGate) (List.ofFn x)).getD a false := by
        funext a
        split_ifs with ha
        · exact (ih' a).1.symm
        · exact (getD_ge_false (by omega)).symm
      have hd : (fun a => if _ : a < N + N + (⟨gs, o⟩ : Dag N).size then
          (⟨gs, o⟩ : Dag N).deg a else 0) =
          fun a => (Dg (gs.map G.toGate) (N + N) (lineMarks N)).getD a 0 := by
        funext a
        split_ifs with ha
        · exact (ih' a).2.symm
        · exact (getD_ge_zero (by omega)).symm
      rw [hr, hd, toGate_val, toGate_deg]
      exact ⟨rfl, rfl⟩
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      have hs1 : (⟨gs ++ [g], o⟩ : Dag N).size = (⟨gs, o⟩ : Dag N).size + 1 := by
        simp [Dag.size]
      have := val_deg_ge (⟨gs ++ [g], o⟩ : Dag N) (i := i) (by omega) x
      exact ⟨this.1.symm, this.2.symm⟩
open Classical in
noncomputable def cleanG (I : Fin N → Fin N → Prop) (D : Dag N) : G → G
  | .and a b =>
      if D.deg a = 0 ∧ D.deg b = 1 ∧ D.deadSets I 2 a = ∅ then .or b b
      else if D.deg b = 0 ∧ D.deg a = 1 ∧ D.deadSets I 2 b = ∅ then .or a a
      else .and a b
  | .or a b => .or a b
  | .cst v => .cst v
theorem cleanG_and (I : Fin N → Fin N → Prop) (D : Dag N) (a b : ℕ) :
    ((D.deg a = 0 ∧ D.deg b = 1 ∧ D.deadSets I 2 a = ∅) ∧ cleanG I D (.and a b) = .or b b) ∨
    (¬ (D.deg a = 0 ∧ D.deg b = 1 ∧ D.deadSets I 2 a = ∅) ∧
      (D.deg b = 0 ∧ D.deg a = 1 ∧ D.deadSets I 2 b = ∅) ∧ cleanG I D (.and a b) = .or a a) ∨
    (¬ (D.deg a = 0 ∧ D.deg b = 1 ∧ D.deadSets I 2 a = ∅) ∧
      ¬ (D.deg b = 0 ∧ D.deg a = 1 ∧ D.deadSets I 2 b = ∅) ∧ cleanG I D (.and a b) = .and a b) := by
  simp only [cleanG]
  split_ifs with h1 h2
  · exact Or.inl ⟨h1, rfl⟩
  · exact Or.inr (Or.inl ⟨h1, h2, rfl⟩)
  · exact Or.inr (Or.inr ⟨h1, h2, rfl⟩)
noncomputable def clean (I : Fin N → Fin N → Prop) (D : Dag N) : Dag N :=
  ⟨D.gates.map (cleanG I D), D.out⟩
theorem clean_get (I : Fin N → Fin N → Prop) (D : Dag N) (k : ℕ) :
    (clean I D).gates[k]? = (D.gates[k]?).map (cleanG I D) := by
  simp [clean]
theorem clean_gateAt (I : Fin N → Fin N → Prop) (D : Dag N) (i : ℕ) :
    (clean I D).gateAt i = (D.gateAt i).map (cleanG I D) := by
  unfold Dag.gateAt
  split_ifs
  · exact clean_get I D _
  · rfl
theorem cleanG_kids (I : Fin N → Fin N → Prop) (D : Dag N) (g : G) :
    ∀ c ∈ (cleanG I D g).kids, c ∈ g.kids := by
  intro c hc
  cases g with
  | and a b =>
    simp only [cleanG] at hc
    split_ifs at hc <;> simp_all [G.kids]
  | or a b => exact hc
  | cst v => exact hc
theorem clean_wf (I : Fin N → Fin N → Prop) (D : Dag N) (hwf : D.WF) : (clean I D).WF := by
  intro i g hg c hc
  rw [clean_gateAt] at hg
  obtain ⟨g0, hg0, rfl⟩ := Option.map_eq_some_iff.1 hg
  exact hwf i g0 hg0 c (cleanG_kids I D g0 c hc)
theorem gate_lt {D : Dag N} (hwf : D.WF) {i a b : ℕ} (hi : ¬ i < N + N)
    (hg : D.gates[i - (N + N)]? = some (.and a b)) : a < i ∧ b < i := by
  have h : D.gateAt i = some (.and a b) := by
    unfold Dag.gateAt; rw [if_pos (by omega)]; exact hg
  exact ⟨hwf i _ h a (by simp [G.kids]), hwf i _ h b (by simp [G.kids])⟩
theorem clean_deg (I : Fin N → Fin N → Prop) (D : Dag N) (hwf : D.WF) (i : ℕ) :
    (clean I D).deg i = D.deg i := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    have hd : ∀ a, (if _ : a < i then (clean I D).deg a else 0) =
        (if _ : a < i then D.deg a else 0) := by
      intro a
      split_ifs with ha
      · exact ih a ha
      · rfl
    conv_lhs => rw [Dag.deg]
    conv_rhs => rw [Dag.deg]
    by_cases h0 : i < N + N
    · rw [if_pos h0, if_pos h0]
    · rw [if_neg h0, if_neg h0, clean_get]
      cases hg : D.gates[i - (N + N)]? with
      | none => rfl
      | some g =>
        cases g with
        | and a b =>
          obtain ⟨ha, hb⟩ := gate_lt hwf h0 hg
          rcases cleanG_and I D a b with ⟨h1, hc⟩ | ⟨-, h2, hc⟩ | ⟨-, -, hc⟩ <;>
            simp only [Option.map_some, hc]
          · rw [hd b, dif_pos ha, dif_pos hb, max_self]
            omega
          · rw [hd a, dif_pos ha, dif_pos hb, max_self]
            omega
          · rw [hd a, hd b]
        | or a b => dsimp only [Option.map_some, cleanG]; rw [hd a, hd b]
        | cst v => rfl
theorem band_le_or_right : ∀ a b c d : Bool, a ≤ c → b ≤ d → (a && b) ≤ (d || d) := by decide
theorem band_le_or_left : ∀ a b c d : Bool, a ≤ c → b ≤ d → (a && b) ≤ (c || c) := by decide
theorem clean_mono (I : Fin N → Fin N → Prop) (D : Dag N) (x : Fin (N + N) → Bool) (i : ℕ) :
    D.val x i ≤ (clean I D).val x i := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    have hv : ∀ a, (if _ : a < i then D.val x a else false) ≤
        (if _ : a < i then (clean I D).val x a else false) := by
      intro a
      split_ifs with ha
      · exact ih a ha
      · exact le_rfl
    conv_lhs => rw [Dag.val]
    conv_rhs => rw [Dag.val]
    split_ifs with h0
    · exact le_rfl
    · rw [clean_get]
      cases hg : D.gates[i - (N + N)]? with
      | none => exact le_rfl
      | some g =>
        cases g with
        | and a b =>
          rcases cleanG_and I D a b with ⟨-, hc⟩ | ⟨-, -, hc⟩ | ⟨-, -, hc⟩ <;>
            simp only [Option.map_some, hc]
          · exact band_le_or_right _ _ _ _ (hv a) (hv b)
          · exact band_le_or_left _ _ _ _ (hv a) (hv b)
          · exact Api.band_mono _ _ _ _ (hv a) (hv b)
        | or a b => exact Api.bor_mono _ _ _ _ (hv a) (hv b)
        | cst v => exact le_rfl
theorem true_of_noDead (I : Fin N → Fin N → Prop) (D : Dag N) {a : ℕ}
    (h : D.deadSets I 2 a = ∅) {S : Finset (Fin N)} (hS : S.card ≤ 2) :
    D.val (testInput I S) a = true := by
  classical
  by_contra hne
  have hmem : S ∈ D.deadSets I 2 a := by
    unfold Dag.deadSets
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hS, by simpa using hne⟩
  rw [h] at hmem
  exact Finset.notMem_empty _ hmem
theorem clean_test (I : Fin N → Fin N → Prop) (D : Dag N) (hwf : D.WF) {S : Finset (Fin N)}
    (hS : S.card ≤ 2) (i : ℕ) : (clean I D).val (testInput I S) i = D.val (testInput I S) i := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    have hv : ∀ a, (if _ : a < i then (clean I D).val (testInput I S) a else false) =
        (if _ : a < i then D.val (testInput I S) a else false) := by
      intro a
      split_ifs with ha
      · exact ih a ha
      · rfl
    conv_lhs => rw [Dag.val]
    conv_rhs => rw [Dag.val]
    split_ifs with h0
    · rfl
    · rw [clean_get]
      cases hg : D.gates[i - (N + N)]? with
      | none => rfl
      | some g =>
        cases g with
        | and a b =>
          obtain ⟨ha, hb⟩ := gate_lt hwf h0 hg
          rcases cleanG_and I D a b with ⟨h1, hc⟩ | ⟨-, h2, hc⟩ | ⟨-, -, hc⟩ <;>
            simp only [Option.map_some, hc]
          · rw [hv b, dif_pos ha, dif_pos hb, Bool.or_self,
              true_of_noDead I D h1.2.2 hS, Bool.true_and]
          · rw [hv a, dif_pos ha, dif_pos hb, Bool.or_self,
              true_of_noDead I D h2.2.2 hS, Bool.and_true]
          · rw [hv a, hv b]
        | or a b => dsimp only [Option.map_some, cleanG]; rw [hv a, hv b]
        | cst v => rfl
theorem clean_deadSets (I : Fin N → Fin N → Prop) (D : Dag N) (hwf : D.WF) (f : ℕ) :
    (clean I D).deadSets I 2 f = D.deadSets I 2 f := by
  classical
  unfold Dag.deadSets
  apply Finset.filter_congr
  intro S _
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [← clean_test I D hwf h1]; exact h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [clean_test I D hwf h1]; exact h2⟩
theorem cleanG_eq_and {I : Fin N → Fin N → Prop} {D : Dag N} {g : G} {f v : ℕ}
    (h : cleanG I D g = .and f v) :
    g = .and f v ∧ ¬ (D.deg f = 0 ∧ D.deg v = 1 ∧ D.deadSets I 2 f = ∅) ∧
      ¬ (D.deg v = 0 ∧ D.deg f = 1 ∧ D.deadSets I 2 v = ∅) := by
  cases g with
  | and a b =>
    simp only [cleanG] at h
    split_ifs at h with h1 h2
    simp only [G.and.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, h1, h2⟩
  | or a b => simp [cleanG] at h
  | cst v => simp [cleanG] at h
theorem clean_cleaned (I : Fin N → Fin N → Prop) (D : Dag N) (hwf : D.WF) (Gs : Finset ℕ) :
    (clean I D).Cleaned I Gs := by
  intro e _ f v hl
  rw [clean_deadSets I D hwf]
  obtain ⟨hg, hf, hv⟩ := hl
  rw [clean_deg I D hwf] at hf hv
  intro hdead
  rcases hg with hg | hg
  · rw [clean_gateAt] at hg
    obtain ⟨g0, -, h0⟩ := Option.map_eq_some_iff.1 hg
    exact (cleanG_eq_and h0).2.1 ⟨hf, hv, hdead⟩
  · rw [clean_gateAt] at hg
    obtain ⟨g0, -, h0⟩ := Option.map_eq_some_iff.1 hg
    exact (cleanG_eq_and h0).2.2 ⟨hf, hv, hdead⟩
theorem ble_of_imp {a b : Bool} (h : a = true → b = true) : a ≤ b := by
  cases a <;> cases b <;> simp_all
theorem testInput_noEdge (I : Fin N → Fin N → Prop) (S : Finset (Fin N)) :
    ¬ ∃ p l, I p l ∧ testInput I S (Fin.castAdd N p) = true ∧
      testInput I S (Fin.natAdd N l) = true := by
  classical
  rintro ⟨p, l, hI, hp, hl⟩
  simp only [testInput, inp, Fin.addCases_left, Fin.addCases_right, decide_eq_true_eq,
    Finset.mem_filter, Finset.mem_univ, true_and] at hp hl
  exact hp l hl hI
theorem test_computes (I : Fin N → Fin N → Prop) (D : Dag N) (hd : D.deg D.out ≤ 2)
    (hup : ∀ z, (∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
      D.fn z = true)
    (htest : ∀ S : Finset (Fin N), S.card ≤ 2 → D.fn (testInput I S) = false) :
    Computes I D.fn := by
  classical
  let Gr : SimpleGraph (Fin (N + N)) :=
    { Adj := fun i j => ∃ p l, I p l ∧
        ((i = Fin.castAdd N p ∧ j = Fin.natAdd N l) ∨ (i = Fin.natAdd N l ∧ j = Fin.castAdd N p))
      symm := ⟨by
        rintro i j ⟨p, l, hI, h⟩
        exact ⟨p, l, hI, h.symm.imp (fun h => ⟨h.2, h.1⟩) (fun h => ⟨h.2, h.1⟩)⟩⟩
      loopless := by
        refine ⟨fun i => ?_⟩
        rintro ⟨p, l, -, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
        · have := congrArg Fin.val (h1.symm.trans h2)
          simp only [Fin.val_castAdd, Fin.val_natAdd] at this
          have := p.isLt; omega
        · have := congrArg Fin.val (h1.symm.trans h2)
          simp only [Fin.val_castAdd, Fin.val_natAdd] at this
          have := p.isLt; omega }
  have hev : ∀ x, D.toCircuit.eval (List.ofFn x) = D.fn x := fun x => (card03r_val D x D.out).1
  have key := LineDegTest.main (N + N) 2 (lineMarks N) Gr D.toCircuit
    (by
      rintro i j ⟨p, l, -, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ <;>
        simp only [lineMarks, Finset.mem_Ico, Fin.val_castAdd, Fin.val_natAdd] <;>
        have := p.isLt <;> have := l.isLt <;> constructor <;> intro <;> omega)
    (fun g hg => by simpa using (Api.card03r_mono D g hg).1)
    (by
      show (D.toCircuit.lineDegrees (N + N) (lineMarks N)).getD D.out 0 ≤ 2
      rw [(card03r_val D (fun _ => false) D.out).2]
      exact hd)
    (by
      rintro i j ⟨p, l, hI, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ <;> rw [hev] <;> apply hup <;>
        exact ⟨p, l, hI, by simp, by simp⟩)
    (by
      intro S hSm hSc
      let S' : Finset (Fin N) := Finset.univ.filter (fun l => Fin.natAdd N l ∈ S)
      have hcard : S'.card ≤ 2 := by
        refine le_trans (Finset.card_le_card_of_injOn (Fin.natAdd N) ?_ ?_) hSc
        · intro l hl
          simp only [S', Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hl
          exact hl
        · intro a _ b _ hab
          exact (Fin.natAdd_inj N).1 hab
      rw [hev]
      have hle := Api.api_val_mono D D.out (x := fun k => decide (k ∈ S ∨
          (k.val ∉ lineMarks N ∧ ∀ j ∈ S, ¬ Gr.Adj k j))) (y := testInput I S') (by
        intro k
        refine Fin.addCases (fun p => ?_) (fun l => ?_) k
        · apply ble_of_imp
          intro h
          simp only [decide_eq_true_eq] at h
          simp only [testInput, inp, Fin.addCases_left, decide_eq_true_eq, Finset.mem_filter,
            Finset.mem_univ, true_and]
          rcases h with h | ⟨-, h⟩
          · have := hSm _ h
            simp only [lineMarks, Finset.mem_Ico, Fin.val_castAdd] at this
            have := p.isLt; omega
          · intro l hl hI
            simp only [S', Finset.mem_filter, Finset.mem_univ, true_and] at hl
            exact h _ hl ⟨p, l, hI, Or.inl ⟨rfl, rfl⟩⟩
        · apply ble_of_imp
          intro h
          simp only [decide_eq_true_eq] at h
          simp only [testInput, inp, Fin.addCases_right, decide_eq_true_eq]
          rcases h with h | ⟨h, -⟩
          · simpa [S'] using h
          · simp only [lineMarks, Finset.mem_Ico, Fin.val_natAdd] at h
            have := l.isLt; omega)
      have h0 := htest S' hcard
      unfold Dag.fn at h0 ⊢
      rw [h0] at hle
      revert hle
      cases D.val _ D.out <;> decide)
  intro z
  rw [← hev z, key z]
  constructor
  · rintro ⟨i, j, ⟨p, l, hI, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩, hi, hj⟩
    · exact ⟨p, l, hI, hi, hj⟩
    · exact ⟨p, l, hI, hj, hi⟩
  · rintro ⟨p, l, hI, hp, hl⟩
    exact ⟨_, _, ⟨p, l, hI, Or.inl ⟨rfl, rfl⟩⟩, hp, hl⟩
theorem card04_clean (I : Fin N → Fin N → Prop) (D : Dag N) (hwf : D.WF)
    (hc : Computes I D.fn) (hd : D.deg D.out ≤ 2) :
    ∃ D' : Dag N, D'.WF ∧ D'.size ≤ D.size ∧ Computes I D'.fn ∧ D'.deg D'.out ≤ 2 ∧
      D'.Cleaned I D'.cone := by
  have hdeg' : (clean I D).deg (clean I D).out ≤ 2 := by
    rw [clean_deg I D hwf]; exact hd
  refine ⟨clean I D, clean_wf I D hwf, by simp [clean, Dag.size], ?_, hdeg',
    clean_cleaned I D hwf _⟩
  refine test_computes I (clean I D) hdeg' ?_ ?_
  · intro z hz
    have h1 : D.fn z = true := (hc z).2 hz
    have := clean_mono I D z D.out
    unfold Dag.fn at h1 ⊢
    rw [h1] at this
    change (clean I D).val z D.out = true
    revert this
    cases (clean I D).val z D.out <;> decide
  · intro S hS
    unfold Dag.fn
    show (clean I D).val (testInput I S) D.out = false
    rw [clean_test I D hwf hS]
    cases ht : D.val (testInput I S) D.out
    · rfl
    · exact absurd ((hc _).1 ht) (testInput_noEdge I S)
end Deg2.Bridge
namespace Deg2
open Deg2.Api
theorem card14_of
    (h10e0 : ∀ {N : ℕ} (I : Fin N → Fin N → Prop) (hI : NoRect I) (D : Dag N)
      (W : Finset (Fin N)) (R : Fin N → ℕ) (hs : Dag.SoundPartialForm I D W R),
      (D.e0Set W R).card ≤ 2 * (D.rootCone W R).card + W.card)
    (h12 : ∀ {N : ℕ} (I : Fin N → Fin N → Prop) (hI : NoRect I) (D : Dag N)
      (W : Finset (Fin N)) (R : Fin N → ℕ) (hs : Dag.SoundPartialForm I D W R)
      (hcl : D.Cleaned I (D.rootCone W R)),
      (D.alphaEdges I W R \ (D.e0Set W R ∪ D.e1Set I W R ∪ D.fSet I (D.rootCone W R) 2)).card ≤
        2 * ((D.rootCone W R).filter (fun f => D.deg f = 1)).card + W.card)
    (h13 : ∀ {N : ℕ} (I : Fin N → Fin N → Prop) (hI : NoRect I) (D : Dag N)
      (W : Finset (Fin N)) (R : Fin N → ℕ) (hs : Dag.SoundPartialForm I D W R)
      (hcl : D.Cleaned I (D.rootCone W R)),
      (D.betaEdges I W R \ (D.e0Set W R ∪ D.e1Set I W R ∪ D.fSet I (D.rootCone W R) 2)).card ≤
        2 * ((D.rootCone W R).filter (fun f => D.deg f = 1)).card)
    {N : ℕ} (I : Fin N → Fin N → Prop) (hI : NoRect I) (D : Dag N)
    (W : Finset (Fin N)) (R : Fin N → ℕ) (hs : Dag.SoundPartialForm I D W R) :
    (D.countedEdges W R).card ≤ 12 * (D.rootCone W R).card + 2 * W.card := by
  obtain ⟨D', hs', hrc, hsub, hcl⟩ := Forms.card09_form_clean I D W R hs
  have h11 := Forms.card11_cover I D' W R hs'
  have hE0 := h10e0 I hI D' W R hs'
  have hE1 := Forms.card10_e1 I hI D' W R hs'
  have hA := h12 I hI D' W R hs' hcl
  have hB := h13 I hI D' W R hs' hcl
  have hF := card07_two_line I hI D' (D'.rootCone W R) (api_coneOf_down D' (W.image R))
  set A := D'.e0Set W R ∪ D'.e1Set I W R ∪ D'.fSet I (D'.rootCone W R) 2 with hAdef
  have hcov : D.countedEdges W R ⊆
      A ∪ (D'.alphaEdges I W R \ A) ∪ (D'.betaEdges I W R \ A) := by
    intro e he
    have he' := h11 (hsub he)
    by_cases hea : e ∈ A
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hea)
    · simp only [Finset.mem_union] at he'
      rcases he' with ((h | h) | h) | h
      · exact absurd (Finset.mem_union_left _ (Finset.mem_union_left _ h)) hea
      · exact absurd (Finset.mem_union_left _ (Finset.mem_union_right _ h)) hea
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨h, hea⟩))
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨h, hea⟩)
  have hc := Finset.card_le_card hcov
  have u1 := Finset.card_union_le (A ∪ (D'.alphaEdges I W R \ A)) (D'.betaEdges I W R \ A)
  have u2 := Finset.card_union_le A (D'.alphaEdges I W R \ A)
  have hAc : A.card ≤ (D'.e0Set W R).card + (D'.e1Set I W R).card +
      (D'.fSet I (D'.rootCone W R) 2).card := by
    have u3 := Finset.card_union_le (D'.e0Set W R ∪ D'.e1Set I W R)
      (D'.fSet I (D'.rootCone W R) 2)
    have u4 := Finset.card_union_le (D'.e0Set W R) (D'.e1Set I W R)
    rw [hAdef]; omega
  have hdisj := card_filter_disj (s := D'.rootCone W R) (p := fun f => D'.deg f = 0)
    (q := fun f => D'.deg f = 1) (fun i h0 h1 => by omega)
  have hle := Finset.card_filter_le (D'.rootCone W R) (fun f => D'.deg f = 0 ∨ D'.deg f = 1)
  clear_value A
  omega
end Deg2
namespace Deg2
open Deg2.Api Deg2.Path
variable {N : ℕ}
theorem cv_top_mono (D : Dag N) {ok ok' : ℕ → Prop} (h : ∀ f, D.deg f = 0 → ok f → ok' f)
    {b : ℕ} (hb : D.Top ok b) : D.Top ok' b := by
  induction hb with
  | root => exact Dag.Top.root
  | orStep _ hT hk hd ih => exact Dag.Top.orStep ih hT hk hd
  | andStep _ hT hg hf hc hfh hch hok ih =>
    exact Dag.Top.andStep ih hT hg hf hc hfh hch (h _ hf hok)
theorem cv_top_reach (D : Dag N) {ok : ℕ → Prop} {b : ℕ} (hb : D.Top ok b) :
    D.Reach D.out b := by
  induction hb with
  | root => exact Relation.ReflTransGen.refl
  | orStep _ _ hk _ ih => exact ih.tail hk
  | andStep _ _ hg _ _ _ hch _ ih =>
    rcases hg with hg | hg
    · exact ih.tail (circ_kid_of hg (by simp [G.kids]) hch)
    · exact ih.tail (circ_kid_of hg (by simp [G.kids]) hch)
theorem cv_ctx_pts (D : Dag N) (b : ℕ) {x y : Fin (N + N) → Bool}
    (h : ∀ p : Fin N, x (Fin.castAdd N p) = y (Fin.castAdd N p)) : D.ctx b x = D.ctx b y := by
  unfold Dag.ctx
  rw [decide_eq_decide]
  constructor
  · exact cv_top_mono D (fun f hf hok => by rw [← api_val_xonly D hf h]; exact hok)
  · exact cv_top_mono D (fun f hf hok => by rw [api_val_xonly D hf h]; exact hok)
theorem cv_ctx_mono (D : Dag N) (b : ℕ) : Monotone (D.ctx b) := by
  intro x y hxy
  by_cases hx : D.ctx b x = true
  · have hy : D.ctx b y = true := by
      simp only [Dag.ctx, decide_eq_true_eq] at hx ⊢
      exact cv_top_mono D (fun f _ hok => by
        have := api_val_mono D f hxy
        rw [hok] at this
        exact HonestFactor.eq_true_of_true_le' this) hx
    rw [hy]
    exact le_top
  · rw [Bool.not_eq_true] at hx
    rw [hx]
    exact Bool.false_le _
theorem cv_natAdd_ne_castAdd (j p : Fin N) : Fin.natAdd N j ≠ Fin.castAdd N p :=
  fun h => HonestFactor.castAdd_ne_natAdd' p j h.symm
theorem cv_ep_eq (p w : Fin N) :
    ep p w = fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N w) := by
  funext k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · unfold ep inp
    rw [Fin.addCases_left]
    simp only [Finset.mem_singleton, HonestFactor.castAdd_inj',
      HonestFactor.castAdd_ne_natAdd', or_false]
  · unfold ep inp
    rw [Fin.addCases_right]
    simp only [Finset.mem_singleton, HonestFactor.natAdd_inj', cv_natAdd_ne_castAdd, false_or]
theorem cv_pt_eq (p : Fin N) : pt p = fun k => decide (k = Fin.castAdd N p) := by
  funext k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · unfold pt inp
    rw [Fin.addCases_left]
    simp only [Finset.mem_singleton, HonestFactor.castAdd_inj']
  · unfold pt inp
    rw [Fin.addCases_right]
    simp only [Finset.notMem_empty, cv_natAdd_ne_castAdd, decide_false]
theorem cv_ep_eq' (p u : Fin N) :
    (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N u)) = ep p u :=
  (cv_ep_eq p u).symm
theorem cv_honest_of_list (I : Fin N → Fin N → Prop) (D : Dag N) (hc : Computes I D.fn)
    (hid : ∀ x : Fin (N + N) → Bool, D.fn x = true ↔
      ∃ b, D.IsItem b ∧ D.ctx b x = true ∧ ∀ r, D.IsFactor b r → D.val x r = true)
    (p w : Fin N) {b : ℕ} (hb : D.IsItem b) (hctx : D.ctx b (ep p w) = true)
    (hf : ∀ r, D.IsFactor b r → D.val (ep p w) r = true) (ws : List ℕ)
    (hws : ∀ r, D.IsFactor b r ↔ r ∈ ws) :
    ∃ r ∈ ws, IsHonest I (fun x => D.val x r) p := by
  have key := HonestFactor.main N I (D.ctx b) (ws.map (fun r x => D.val x r)) p w
    (cv_ctx_mono D b) (fun z z' h => cv_ctx_pts D b h)
    (by
      intro f hfm
      simp only [List.mem_map] at hfm
      obtain ⟨r, -, rfl⟩ := hfm
      intro x y hxy
      exact api_val_mono D r hxy)
    (by
      intro z hz
      rw [Bool.and_eq_true, List.all_map, List.all_eq_true] at hz
      apply (hc z).1
      apply (hid z).2
      refine ⟨b, hb, hz.1, fun r hr => ?_⟩
      have := hz.2 r ((hws r).1 hr)
      simpa using this)
    (by
      rw [cv_ep_eq', Bool.and_eq_true, List.all_map, List.all_eq_true]
      refine ⟨hctx, fun r hr => ?_⟩
      have := hf r ((hws r).2 hr)
      simpa using this)
  obtain ⟨-, f, hfm, hf0, hfu⟩ := key
  simp only [List.mem_map] at hfm
  obtain ⟨r, hr, rfl⟩ := hfm
  refine ⟨r, hr, ?_, fun u hu => hfu u ?_⟩
  · rw [cv_pt_eq]; exact hf0
  · rw [cv_ep_eq']; exact hu
theorem cv_honest_factor (I : Fin N → Fin N → Prop) (D : Dag N) (hwf : D.WF)
    (hc : Computes I D.fn)
    (hid : ∀ x : Fin (N + N) → Bool, D.fn x = true ↔
      ∃ b, D.IsItem b ∧ D.ctx b x = true ∧ ∀ r, D.IsFactor b r → D.val x r = true)
    (p w : Fin N) {b : ℕ} (hb : D.IsItem b) (hctx : D.ctx b (ep p w) = true)
    (hf : ∀ r, D.IsFactor b r → D.val (ep p w) r = true) :
    ∃ r, D.IsFactor b r ∧ D.deg r = 1 ∧ IsHonest I (fun x => D.val x r) p := by
  classical
  rcases hb.2 with hb1 | hbt
  · have hws : ∀ r, D.IsFactor b r ↔ r ∈ [b] := by
      intro r
      constructor
      · rintro (⟨_, rfl⟩ | ⟨hT, _⟩)
        · simp
        · have : D.deg b = 2 := by
            unfold Dag.Tmix Dag.T at hT
            exact (Finset.mem_filter.1 (Finset.mem_filter.1 hT).1).2
          omega
      · intro hr
        simp only [List.mem_singleton] at hr
        exact Or.inl ⟨hb1, hr⟩
    obtain ⟨r, hr, hh⟩ := cv_honest_of_list I D hc hid p w hb hctx hf [b] hws
    simp only [List.mem_singleton] at hr
    subst hr
    refine ⟨r, Or.inl ⟨hb1, rfl⟩, ?_, hh⟩
    rcases Nat.lt_or_ge (D.deg r) 1 with h0 | h1
    · exfalso
      have e1 := hf r (Or.inl ⟨hb1, rfl⟩)
      rw [← api_val_xonly D (by omega) (x := pt p) (y := ep p w)
        (fun q => by rw [circ_ep_pts])] at e1
      have := hh.1
      simp only at this
      rw [this] at e1
      exact Bool.false_ne_true e1
    · omega
  · have hbt' := hbt
    unfold Dag.Tmix at hbt'
    obtain ⟨-, a, a', hg, ha1, ha1'⟩ := Finset.mem_filter.1 hbt'
    have hlt := hwf b _ hg
    have hal : a < b := hlt a (by simp [G.kids])
    have hal' : a' < b := hlt a' (by simp [G.kids])
    have hT2 : D.deg b = 2 := by
      unfold Dag.Tmix Dag.T at hbt
      exact (Finset.mem_filter.1 (Finset.mem_filter.1 hbt).1).2
    have hws : ∀ r, D.IsFactor b r ↔ r ∈ [a, a'] := by
      intro r
      constructor
      · rintro (⟨h, _⟩ | ⟨_, hk⟩)
        · omega
        · obtain ⟨g, hg', hrg, -⟩ := hk
          rw [hg] at hg'
          cases hg'
          simpa [G.kids] using hrg
      · intro hr
        refine Or.inr ⟨hbt, circ_kid_of hg ?_ ?_⟩
        · simpa [G.kids] using hr
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> assumption
    obtain ⟨r, hr, hh⟩ := cv_honest_of_list I D hc hid p w ⟨hb.1, Or.inr hbt⟩ hctx hf [a, a'] hws
    refine ⟨r, (hws r).2 hr, ?_, hh⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> assumption
theorem cv_gate_lt (D : Dag N) {v : ℕ} {g : G} (hg : D.gateAt v = some g) :
    N + N ≤ v ∧ v < N + N + D.size := by
  obtain ⟨hi, hgs⟩ := gateAt_some hg
  have hlt : v - (N + N) < D.gates.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hgs
    cases hgs
  exact ⟨hi, by unfold Dag.size; omega⟩
theorem cv_mem_cone (D : Dag N) {v : ℕ} (h1 : N + N ≤ v) (h2 : v < N + N + D.size)
    (hr : D.Reach D.out v) : v ∈ D.cone := by
  classical
  unfold Dag.cone Dag.coneOf
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton, exists_eq_left]
  exact ⟨h2, h1, hr⟩
theorem cv_path_reach (D : Dag N) {π : List ℕ} {a b : ℕ} (hp : D.IsPath π a b) :
    ∀ j, j < π.length → D.Reach a (π.getD j 0) := by
  intro j
  induction j with
  | zero =>
    intro hj
    obtain ⟨hh, -, -⟩ := hp
    cases π with
    | nil => simp at hj
    | cons c rest =>
      simp only [List.head?_cons, Option.some.injEq] at hh
      subst hh
      exact Relation.ReflTransGen.refl
  | succ j ih =>
    intro hj
    exact (ih (by omega)).tail (hp.2.2 j hj)
theorem cv_step (D : Dag N) (hwf : D.WF) {g c : ℕ} {w : Fin N} (hk : D.Kid g c)
    (hg1 : D.deg g = 1) (hc1 : D.deg c = 1) (hnl : ∀ f, ¬ D.LabAnd g f c)
    (hv : D.VReach c w) : D.VReach g w := by
  obtain ⟨G0, hG, hcG, hcg⟩ := hk
  cases G0 with
  | or a b => exact Dag.VReach.step ⟨a, b, hG⟩ hg1 ⟨_, hG, hcG, hcg⟩ hv
  | cst v => simp [G.kids] at hcG
  | and a b =>
    exfalso
    have hlt := hwf g _ hG
    have ha : a < g := hlt a (by simp [G.kids])
    have hb : b < g := hlt b (by simp [G.kids])
    have hd := circ_deg_and D hG ha hb
    simp only [G.kids, List.mem_cons, List.not_mem_nil, or_false] at hcG
    rcases hcG with rfl | rfl
    · exact hnl b ⟨Or.inr hG, by omega, hc1⟩
    · exact hnl a ⟨Or.inl hG, by omega, hc1⟩
theorem cv_getLast (π : List ℕ) {b : ℕ} (h : π.getLast? = some b) :
    π.getD (π.length - 1) 0 = b := by
  rw [List.getLast?_eq_getElem?] at h
  rw [List.getD_eq_getElem?_getD, h]
  rfl
theorem cv_vreach_suffix (D : Dag N) (hwf : D.WF) {π : List ℕ} {a : ℕ} {w : Fin N}
    (hp : D.IsPath π a (N + w.val)) (hdeg : ∀ v ∈ π, D.deg v = 1) :
    ∀ n j, j + n + 1 = π.length →
      (∀ k f, j ≤ k → k + 1 < π.length → ¬ D.LabAnd (π.getD k 0) f (π.getD (k + 1) 0)) →
      D.VReach (π.getD j 0) w := by
  intro n
  induction n with
  | zero =>
    intro j hj _
    have := cv_getLast π hp.2.1
    rw [show j = π.length - 1 by omega, this]
    exact Dag.VReach.leaf w
  | succ n ih =>
    intro j hj hnl
    have h1 := ih (j + 1) (by omega) (fun k f hk hk' => hnl k f (by omega) hk')
    have hk := hp.2.2 j (by omega)
    exact cv_step D hwf hk (hdeg _ (circ_getD_mem (by omega)))
      (hdeg _ (circ_getD_mem (by omega))) (fun f => hnl j f le_rfl (by omega)) h1
theorem cv_vstar_mem {D : Dag N} {v : ℕ} {w : Fin N} (h : D.VReach v w) : w ∈ D.Vstar v := by
  classical
  unfold Dag.Vstar
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩
theorem cv_isOr_of_card (D : Dag N) {v : ℕ} {w : Fin N} (h : D.VReach v w)
    (h2 : 2 ≤ (D.Vstar v).card) : D.IsOr v := by
  classical
  cases h with
  | step hor _ _ _ => exact hor
  | leaf =>
    exfalso
    have : (D.Vstar (N + w.val)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      unfold Dag.Vstar at ha hb
      rw [Finset.mem_filter] at ha hb
      have h1 := circ_vreach_input D ha.2 (by omega)
      have h2 := circ_vreach_input D hb.2 (by omega)
      exact Fin.ext (by omega)
    omega
theorem cv_pinned (I : Fin N → Fin N → Prop) (D : Dag N) {v : ℕ} {p w : Fin N}
    (hv : D.VReach v w) (hr : D.Reach D.out v) (hd : D.deg v = 1)
    (hsub : D.Vstar v ⊆ pencil I p) (h2 : 2 ≤ (D.Vstar v).card) : (p, w) ∈ D.pinned I := by
  classical
  have hor := cv_isOr_of_card D hv h2
  obtain ⟨a, b, hg⟩ := hor
  have hlt := cv_gate_lt D hg
  have hcone := cv_mem_cone D hlt.1 hlt.2 hr
  have hOrM : v ∈ D.OrM := by
    unfold Dag.OrM Dag.M
    exact Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hcone, hd⟩, ⟨a, b, hg⟩⟩
  unfold Dag.pinned
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _, v, hOrM, ⟨⟨a, b, hg⟩, hd, h2, hsub⟩,
    cv_vstar_mem hv⟩
theorem cv_card_split {s : Finset (Fin N)} {w : Fin N} (hw : w ∈ s) :
    2 ≤ s.card ∨ s = {w} := by
  by_cases h : 2 ≤ s.card
  · exact Or.inl h
  · right
    rw [Finset.eq_singleton_iff_unique_mem]
    exact ⟨hw, fun x hx => Finset.card_le_one.1 (by omega) x hx w hw⟩
theorem cv_cover_of_identity
    (hid : ∀ (I : Fin N → Fin N → Prop) (D : Dag N), D.WF → Computes I D.fn →
      D.deg D.out ≤ 2 → ∀ (x : Fin (N + N) → Bool), D.fn x = true ↔
        ∃ b, D.IsItem b ∧ D.ctx b x = true ∧ ∀ r, D.IsFactor b r → D.val x r = true)
    (I : Fin N → Fin N → Prop) (D : Dag N) (hwf : D.WF)
    (hc : Computes I D.fn) (hd : D.deg D.out ≤ 2) (hcl : D.Cleaned I D.cone) :
    ∀ p w : Fin N, I p w →
      (p, w) ∈ D.pinned I ∪ D.served I ∪ D.fSet I D.cone 2 ∪ D.markerEdges I := by
  classical
  intro p w hpw
  have hid' := hid I D hwf hc hd
  have hacc : D.fn (ep p w) = true := by
    apply (hc _).2
    refine ⟨p, w, hpw, ?_, ?_⟩
    · unfold ep inp; rw [Fin.addCases_left]; simp
    · unfold ep inp; rw [Fin.addCases_right]; simp
  obtain ⟨b, hb, hctx, hf⟩ := (hid' _).1 hacc
  obtain ⟨r, hfac, hr1, hh⟩ := cv_honest_factor I D hwf hc hid' p w hb hctx hf
  have hrw := hf r hfac
  obtain ⟨π, hπ, hπv, hlab, hpen⟩ := card06_honest_path I D r p w hr1 hh hrw
  have hdeg : ∀ v ∈ π, D.deg v = 1 := fun v hv => (hπv v hv).1
  have hreach_r : D.Reach D.out r := by
    rcases hfac with ⟨_, rfl⟩ | ⟨_, hk⟩
    · exact cv_top_reach D hb.1
    · exact (cv_top_reach D hb.1).tail hk
  have hreach : ∀ j, j < π.length → D.Reach D.out (π.getD j 0) :=
    fun j hj => hreach_r.trans (cv_path_reach D hπ j hj)
  have hlen : 0 < π.length := by
    cases π with
    | nil => simp [Dag.IsPath] at hπ
    | cons _ _ => simp
  have hhead : π.getD 0 0 = r := by
    obtain ⟨hh0, -, -⟩ := hπ
    cases π with
    | nil => simp at hh0
    | cons c _ => simpa using hh0
  simp only [Finset.mem_union]
  let P : ℕ → Prop := fun k => k + 1 < π.length ∧ ∃ f, D.LabAnd (π.getD k 0) f (π.getD (k + 1) 0)
  by_cases hex : ∃ k, P k
  ·
    obtain ⟨k0, hk0⟩ := hex
    let K := Nat.findGreatest P π.length
    have hPK : P K := Nat.findGreatest_spec (P := P) (by have := hk0.1; omega) hk0
    have hmax : ∀ k, K < k → ¬ P k := by
      intro k hk hPk
      exact Nat.findGreatest_is_greatest hk (by have := hPk.1; omega) hPk
    obtain ⟨hK, f, hfl⟩ := hPK
    set e := π.getD K 0 with he
    set v := π.getD (K + 1) 0 with hv
    have hvr : D.VReach v w := by
      refine cv_vreach_suffix D hwf hπ hdeg (π.length - (K + 1) - 1) (K + 1) (by omega) ?_
      intro k f' hk hk' hl
      exact hmax k (by omega) ⟨hk', f', hl⟩
    have hvmem : v ∈ π := circ_getD_mem hK
    rcases cv_card_split (cv_vstar_mem hvr) with h2 | h1
    · left; left; left
      exact cv_pinned I D hvr (hreach _ hK) (hdeg v hvmem) (hpen v hvmem) h2
    ·
      obtain ⟨hgate, hf0, -⟩ := hfl
      have hemem : e ∈ π := circ_getD_mem (by omega)
      have hgE : ∃ g, D.gateAt e = some g := by
        rcases hgate with h | h
        · exact ⟨_, h⟩
        · exact ⟨_, h⟩
      obtain ⟨gE, hgE⟩ := hgE
      have hElt := cv_gate_lt D hgE
      have hEcone := cv_mem_cone D hElt.1 hElt.2 (hreach K (by omega))
      have hAndM : e ∈ D.AndM := by
        unfold Dag.AndM Dag.M
        refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hEcone, hdeg e hemem⟩, ?_⟩
        rcases hgate with h | h
        · exact ⟨_, _, h⟩
        · exact ⟨_, _, h⟩
      have hdead := hcl e hEcone f v ⟨hgate, hf0, hdeg v hvmem⟩
      have halive : p ∈ D.alive f := by
        unfold Dag.alive
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hlab K f hK ⟨hgate, hf0, hdeg v hvmem⟩⟩
      by_cases hle : (D.alive f ∩ ptsOn I w).card ≤ 2
      · left; left; right
        unfold Dag.served
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, e, hAndM, f, v,
          ⟨hgate, hf0, hdeg v hvmem⟩, h1, halive, hpw, hle⟩
      · left; right
        have hfk : D.Kid e f := by
          rcases hgate with h | h
          · exact circ_kid_of h (by simp [G.kids]) (hwf e _ h f (by simp [G.kids]))
          · exact circ_kid_of h (by simp [G.kids]) (hwf e _ h f (by simp [G.kids]))
        have hfgate : N + N ≤ f := by
          by_contra hlt
          have h1' := circ_alive_input D (i := f) (by omega)
          have := Finset.card_le_card (Finset.inter_subset_left (s₁ := D.alive f)
            (s₂ := ptsOn I w))
          omega
        have hfcone : f ∈ D.cone :=
          cv_mem_cone D hfgate (by have := circ_kid_lt hfk; omega)
            ((hreach K (by omega)).tail hfk)
        unfold Dag.fSet
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hpw, f, hfcone, hf0, hdead, halive,
          by show 2 + 1 ≤ (D.alive f ∩ ptsOn I w).card; omega⟩
  ·
    have hrv : D.VReach r w := by
      have := cv_vreach_suffix D hwf hπ hdeg (π.length - 1) 0 (by omega)
        (fun k f' _ hk' hl => hex ⟨k, hk', f', hl⟩)
      rwa [hhead] at this
    have hrmem : r ∈ π := by rw [← hhead]; exact circ_getD_mem hlen
    rcases cv_card_split (cv_vstar_mem hrv) with h2 | h1
    · left; left; left
      exact cv_pinned I D hrv hreach_r hr1 (hpen r hrmem) h2
    · right
      unfold Dag.markerEdges
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, hpw, b, hb, ?_, hf, r, hfac, hr1, h1⟩
      rw [cv_ctx_pts D b (y := ep p w) (fun q => by rw [circ_ep_pts])]
      exact hctx
end Deg2
namespace Deg2
variable {N : ℕ}
theorem card17_cover (I : Fin N → Fin N → Prop) (D : Dag N) (hwf : D.WF)
    (hc : Computes I D.fn) (hd : D.deg D.out ≤ 2) (hcl : D.Cleaned I D.cone) :
    ∀ p w : Fin N, I p w →
      (p, w) ∈ D.pinned I ∪ D.served I ∪ D.fSet I D.cone 2 ∪ D.markerEdges I :=
  cv_cover_of_identity (fun I D hwf hc hd x => card15_identity I D hwf hc hd x) I D hwf hc hd hcl
end Deg2
namespace Deg2
open Deg2.Forms
variable {N : ℕ}
theorem e0_rootFalse {I : Fin N → Fin N → Prop} {D : Dag N} {W : Finset (Fin N)}
    {R : Fin N → ℕ} (hs : Dag.SoundPartialForm I D W R) {w : Fin N} (hw : w ∈ W) :
    D.val (testInput I {w}) (R w) = false := by
  by_contra hf
  rw [Bool.not_eq_false] at hf
  obtain ⟨p, l, hpl, hp, hl⟩ :=
    hs.2.2 _ ⟨w, hw, (testInput_natAdd I {w} w).2 (Finset.mem_singleton_self w), hf⟩
  rw [testInput_natAdd, Finset.mem_singleton] at hl
  subst hl
  exact (testInput_castAdd I {l} p).1 hp l (Finset.mem_singleton_self l) hpl
theorem card10_e0 (I : Fin N → Fin N → Prop) (hI : NoRect I) (D : Dag N) (W : Finset (Fin N))
    (R : Fin N → ℕ) (hs : Dag.SoundPartialForm I D W R) :
    (D.e0Set W R).card ≤ 2 * (D.rootCone W R).card + W.card := by
  classical
  let T : ℕ → Finset (Fin N × Fin N) := fun g =>
    (Finset.univ.filter (fun q : Fin N => ∃ c, D.Kid g c ∧ D.alive c = {q})) ×ˢ
      (Finset.univ.filter (fun w : Fin N =>
        D.val (testInput I {w}) g = false ∧ 2 ≤ (D.alive g).card))
  have hT : ∀ g, (T g).card ≤ 2 := by
    intro g
    rw [Finset.card_product]
    have h1 := kid_points_card D g
    have h2 : (Finset.univ.filter (fun w : Fin N =>
        D.val (testInput I {w}) g = false ∧ 2 ≤ (D.alive g).card)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      rw [Finset.mem_filter] at ha hb
      exact line_unique I hI D ha.2.2 ha.2.1 hb.2.1
    calc _ ≤ 2 * 1 := Nat.mul_le_mul h1 h2
      _ = 2 := rfl
  let U : Fin N → Finset (Fin N × Fin N) := fun w =>
    if (D.alive (R w)).card ≤ 1 then D.alive (R w) ×ˢ {w} else ∅
  have hU : ∀ w, (U w).card ≤ 1 := by
    intro w
    simp only [U]
    split_ifs with h
    · rw [Finset.card_product, Finset.card_singleton, mul_one]; exact h
    · simp
  have hsub : D.e0Set W R ⊆ (D.rootCone W R).biUnion T ∪ W.biUnion U := by
    intro e he
    unfold Dag.e0Set at he
    rw [Finset.mem_filter] at he
    obtain ⟨-, hw, hp⟩ := he
    by_cases h2 : 2 ≤ (D.alive (R e.2)).card
    · obtain ⟨g, c, hr, hk, hg2, hc, hg0⟩ :=
        walk_two D e.1 _ (R e.2) hp (e0_rootFalse hs hw) h2
      obtain ⟨hgN, hgs⟩ := kid_gate hk
      apply Finset.mem_union_left
      rw [Finset.mem_biUnion]
      refine ⟨g, mem_rootCone hw hr hgN hgs, ?_⟩
      rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter]
      exact ⟨⟨Finset.mem_univ _, c, hk, hc⟩, Finset.mem_univ _, hg0, hg2⟩
    · apply Finset.mem_union_right
      rw [Finset.mem_biUnion]
      refine ⟨e.2, hw, ?_⟩
      have h1 : (D.alive (R e.2)).card ≤ 1 := by omega
      simp only [U, h1, ↓reduceIte]
      rw [Finset.mem_product, Finset.mem_singleton]
      exact ⟨mem_alive.2 hp, rfl⟩
  calc (D.e0Set W R).card ≤ _ := Finset.card_le_card hsub
    _ ≤ ((D.rootCone W R).biUnion T).card + (W.biUnion U).card := Finset.card_union_le _ _
    _ ≤ (∑ g ∈ D.rootCone W R, (T g).card) + ∑ w ∈ W, (U w).card :=
        Nat.add_le_add Finset.card_biUnion_le Finset.card_biUnion_le
    _ ≤ (∑ _g ∈ D.rootCone W R, 2) + ∑ _w ∈ W, 1 :=
        Nat.add_le_add (Finset.sum_le_sum (fun g _ => hT g)) (Finset.sum_le_sum (fun w _ => hU w))
    _ = 2 * (D.rootCone W R).card + W.card := by
        rw [Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul, mul_comm, mul_one]
end Deg2
namespace Deg2.Alpha
open Deg2
variable {N : ℕ}
def Step (D : Dag N) (x : Fin (N + N) → Bool) (a b : ℕ) : Prop :=
  D.Kid a b ∧ ∀ f, D.LabAnd a f b → D.val x f = true
def Lab (D : Dag N) (π : List ℕ) (i : ℕ) : Prop :=
  ∃ f, D.LabAnd (π.getD i 0) f (π.getD (i + 1) 0)
def AW (I : Fin N → Fin N → Prop) (D : Dag N) (W : Finset (Fin N)) (R : Fin N → ℕ)
    (p w : Fin N) (π : List ℕ) (k : ℕ) : Prop :=
  D.EdgePath R p w π ∧ D.PGateAt p π k ∧ ¬ D.IsBeta I W R p (π.getD (k + 1) 0)
def Pref (I : Fin N → Fin N → Prop) (D : Dag N) (W : Finset (Fin N)) (R : Fin N → ℕ)
    (p w : Fin N) (o : ℕ) : Prop :=
  ∃ π k i, AW I D W R p w π k ∧ (∀ i' < i, ¬ Lab D π i') ∧ π.getD i 0 = o
noncomputable def Aset (I : Fin N → Fin N → Prop) (D : Dag N) (W : Finset (Fin N))
    (R : Fin N → ℕ) : Finset (Fin N × Fin N) :=
  D.alphaEdges I W R \ (D.e0Set W R ∪ D.e1Set I W R ∪ D.fSet I (D.rootCone W R) 2)
open Classical in
noncomputable def Q (I : Fin N → Fin N → Prop) (D : Dag N) (W : Finset (Fin N))
    (R : Fin N → ℕ) (o : ℕ) : Finset (Fin N) :=
  Finset.univ.filter (fun p => ∃ w, (p, w) ∈ Aset I D W R ∧ Pref I D W R p w o)
open Classical in
noncomputable def T (I : Fin N → Fin N → Prop) (D : Dag N) (W : Finset (Fin N))
    (R : Fin N → ℕ) (o : ℕ) : Finset (Fin N × Fin N) :=
  (Aset I D W R).filter (fun e => Pref I D W R e.1 e.2 o ∧ 2 ≤ (Q I D W R o).card ∧
    (((∀ f v, ¬ D.LabAnd o f v) ∧ ∃ c, D.Kid o c ∧ Q I D W R c = {e.1}) ∨
      ∃ f v, D.LabAnd o f v ∧ e.1 ∈ D.alive f))
theorem labelsAlive_cons {D : Dag N} {π : List ℕ} {a c b : ℕ} {x : Fin (N + N) → Bool}
    (hp : D.IsPath π c b) (hl : D.LabelsAlive π x)
    (ha : ∀ f, D.LabAnd a f c → D.val x f = true) : D.LabelsAlive (a :: π) x := by
  intro k f hk hlab
  cases k with
  | zero =>
    rw [List.getD_cons_zero, List.getD_cons_succ, Forms.path_head hp] at hlab
    exact ha f hlab
  | succ k =>
    rw [List.getD_cons_succ, List.getD_cons_succ] at hlab
    simp only [List.length_cons] at hk
    exact hl k f (by omega) hlab
theorem reach_path {D : Dag N} {x : Fin (N + N) → Bool} {a b : ℕ}
    (h : Relation.ReflTransGen (Step D x) a b) :
    ∃ π, D.IsPath π a b ∧ D.LabelsAlive π x := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[b], Path.isPath_single D b, fun k f hk _ => by simp at hk⟩
  | head hs _ ih =>
    obtain ⟨π, hπ, hl⟩ := ih
    exact ⟨_ :: π, Path.isPath_cons D hs.1 hπ, labelsAlive_cons hπ hl hs.2⟩
theorem chain_reach {r : ℕ → ℕ → Prop} {π : List ℕ} {i j : ℕ}
    (h : ∀ k, i ≤ k → k < j → r (π.getD k 0) (π.getD (k + 1) 0)) (hij : i ≤ j) :
    Relation.ReflTransGen r (π.getD i 0) (π.getD j 0) := by
  induction j with
  | zero =>
    obtain rfl : i = 0 := by omega
    exact .refl
  | succ j ih =>
    rcases Nat.eq_or_lt_of_le hij with rfl | hlt
    · exact .refl
    · exact (ih (fun k h1 h2 => h k h1 (by omega)) (by omega)).tail (h j (by omega) (by omega))
variable {I : Fin N → Fin N → Prop} {D : Dag N} {W : Finset (Fin N)} {R : Fin N → ℕ}
theorem label_alive (hwf : D.WF) {p w : Fin N} {a f b : ℕ}
    (ha : D.val (ep p w) a = true) (h : D.LabAnd a f b) : D.val (pt p) f = true := by
  rw [Forms.labAnd_val hwf h] at ha
  rw [Api.api_val_xonly D h.2.1 (y := ep p w) (fun q => Forms.pt_ep_points p w q)]
  rw [Bool.and_eq_true] at ha
  exact ha.1
theorem counted_inc (hs : Dag.SoundPartialForm I D W R) {e : Fin N × Fin N}
    (h : e ∈ D.countedEdges W R) : I e.1 e.2 ∧ e.2 ∈ W := by
  classical
  unfold Dag.countedEdges at h
  rw [Finset.mem_filter] at h
  obtain ⟨-, hw, hv⟩ := h
  have hl : ep e.1 e.2 (Fin.natAdd N e.2) = true := by
    unfold ep
    rw [Forms.inp_natAdd]
    simp
  obtain ⟨p0, l, hI0, hp0, hl0⟩ := hs.2.2 (ep e.1 e.2) ⟨e.2, hw, hl, hv⟩
  unfold ep at hp0 hl0
  rw [Forms.inp_castAdd, decide_eq_true_eq, Finset.mem_singleton] at hp0
  rw [Forms.inp_natAdd, decide_eq_true_eq, Finset.mem_singleton] at hl0
  subst hp0
  subst hl0
  exact ⟨hI0, hw⟩
theorem aset_counted {e : Fin N × Fin N} (he : e ∈ Aset I D W R) : e ∈ D.countedEdges W R := by
  classical
  unfold Aset at he
  have h := (Finset.mem_sdiff.1 he).1
  unfold Dag.alphaEdges at h
  exact (Finset.mem_filter.1 h).1
theorem aset_not_fSet {e : Fin N × Fin N} (he : e ∈ Aset I D W R) :
    e ∉ D.fSet I (D.rootCone W R) 2 := by
  intro hf
  unfold Aset at he
  exact (Finset.mem_sdiff.1 he).2 (Finset.mem_union_right _ hf)
theorem aw_of_mem {e : Fin N × Fin N} (he : e ∈ Aset I D W R) :
    ∃ π k, AW I D W R e.1 e.2 π k := by
  classical
  unfold Aset at he
  have h := (Finset.mem_sdiff.1 he).1
  unfold Dag.alphaEdges at h
  rw [Finset.mem_filter] at h
  obtain ⟨-, π, hep, k, hpg, -, hnb⟩ := h
  exact ⟨π, k, hep, hpg, hnb⟩
theorem pref_le {p w : Fin N} {π : List ℕ} {k i : ℕ} (ha : AW I D W R p w π k)
    (hn : ∀ i' < i, ¬ Lab D π i') : i ≤ k := by
  by_contra h
  obtain ⟨-, f, hf, -⟩ := ha.2.1
  exact hn k (by omega) ⟨f, hf⟩
theorem pref_reach {p w : Fin N} {π : List ℕ} {k i : ℕ} (ha : AW I D W R p w π k)
    (hn : ∀ i' < i, ¬ Lab D π i') (x : Fin (N + N) → Bool) :
    Relation.ReflTransGen (Step D x) (R w) (π.getD i 0) := by
  have hle := pref_le ha hn
  have hk := ha.2.1.1
  rw [← Forms.path_head ha.1.1]
  exact chain_reach (fun j _ hj => ⟨ha.1.1.2.2 j (by omega),
    fun f hf => absurd ⟨f, hf⟩ (hn j hj)⟩) (Nat.zero_le i)
theorem tail_reach (hwf : D.WF) {p w : Fin N} {π : List ℕ} {k : ℕ} (ha : AW I D W R p w π k)
    {i : ℕ} (hi : i ≤ k + 1) :
    Relation.ReflTransGen (Step D (pt p)) (π.getD i 0) (π.getD (k + 1) 0) := by
  have hk := ha.2.1.1
  exact chain_reach (fun j _ hj => ⟨ha.1.1.2.2 j (by omega),
    fun f hf => label_alive hwf (ha.1.2 _ (Forms.path_getD_mem (by omega))).1 hf⟩) hi
theorem aw_deg (hs : Dag.SoundPartialForm I D W R) {p w : Fin N} {π : List ℕ} {k : ℕ}
    (ha : AW I D W R p w π k) (hw : w ∈ W) {i : ℕ} (hi : i < π.length) :
    D.deg (π.getD i 0) = 1 ∧ D.Reach (R w) (π.getD i 0) := by
  have hr : D.Reach (R w) (π.getD i 0) := by
    rw [← Forms.path_head ha.1.1]
    exact chain_reach (fun j _ hj => ha.1.1.2.2 j (by omega)) (Nat.zero_le i)
  refine ⟨?_, hr⟩
  have h1 := Api.api_reach_deg D hr
  have h2 := hs.2.1 w hw
  have hv := ha.1.2 _ (Forms.path_getD_mem hi)
  by_contra hne
  have h0 : D.deg (π.getD i 0) = 0 := by omega
  have := Api.api_val_xonly D h0 (x := pt p) (y := ep p w) (fun q => Forms.pt_ep_points p w q)
  rw [hv.1, hv.2] at this
  cases this
theorem labAnd_of_kid {o f v c : ℕ} (h : D.LabAnd o f v) (hk : D.Kid o c)
    (hc : D.deg c = 1) : D.LabAnd o f c := by
  obtain ⟨g, hg, hcm, -⟩ := hk
  obtain ⟨hgo, hf, hv⟩ := h
  rcases hgo with h1 | h1
  · rw [h1] at hg
    obtain rfl := Option.some.inj hg
    simp only [G.kids, List.mem_cons, List.not_mem_nil, or_false] at hcm
    rcases hcm with rfl | rfl
    · omega
    · exact ⟨Or.inl h1, hf, hc⟩
  · rw [h1] at hg
    obtain rfl := Option.some.inj hg
    simp only [G.kids, List.mem_cons, List.not_mem_nil, or_false] at hcm
    rcases hcm with rfl | rfl
    · exact ⟨Or.inr h1, hf, hc⟩
    · omega
theorem inc_of_pref (hwf : D.WF) {p1 w1 p2 w2 : Fin N} {o : ℕ}
    (h1 : Pref I D W R p1 w1 o) (h2 : Pref I D W R p2 w2 o) (hw2 : w2 ∈ W) : I p1 w2 := by
  by_contra hn
  obtain ⟨π1, k1, i1, ha1, hn1, ho1⟩ := h1
  obtain ⟨π2, k2, i2, ha2, hn2, ho2⟩ := h2
  have hle1 := pref_le ha1 hn1
  have r2 := pref_reach ha2 hn2 (pt p1)
  have r1 := tail_reach hwf ha1 (i := i1) (by omega)
  rw [ho2] at r2
  rw [ho1] at r1
  obtain ⟨ρ, hρ, hl⟩ := reach_path (r2.trans r1)
  exact ha1.2.2 ⟨w2, hw2, hn, ρ, hρ, hl⟩
theorem privacy (hI : NoRect I) (hs : Dag.SoundPartialForm I D W R) {p1 w1 p2 w2 : Fin N}
    {o : ℕ} (ha1 : (p1, w1) ∈ Aset I D W R) (hp1 : Pref I D W R p1 w1 o)
    (ha2 : (p2, w2) ∈ Aset I D W R) (hp2 : Pref I D W R p2 w2 o) (hne : p1 ≠ p2) :
    w1 = w2 := by
  obtain ⟨hi1, hw1⟩ := counted_inc hs (aset_counted ha1)
  obtain ⟨hi2, hw2⟩ := counted_inc hs (aset_counted ha2)
  have h12 := inc_of_pref hs.1 hp1 hp2 hw2
  have h21 := inc_of_pref hs.1 hp2 hp1 hw1
  by_contra hw
  exact hI p1 p2 w1 w2 hne hw ⟨hi1, h12, h21, hi2⟩
theorem line_common (hI : NoRect I) (hs : Dag.SoundPartialForm I D W R) {o : ℕ}
    (h2 : 2 ≤ (Q I D W R o).card) {p w p' w' : Fin N}
    (ha : (p, w) ∈ Aset I D W R) (hp : Pref I D W R p w o)
    (ha' : (p', w') ∈ Aset I D W R) (hp' : Pref I D W R p' w' o) : w = w' := by
  classical
  obtain ⟨q, hq, hqp⟩ := Finset.exists_mem_ne (by omega : 1 < (Q I D W R o).card) p
  unfold Q at hq
  rw [Finset.mem_filter] at hq
  obtain ⟨-, u, hau, hpu⟩ := hq
  have h1 : w = u := privacy hI hs ha hp hau hpu (Ne.symm hqp)
  by_cases hpq : p' = q
  · subst hpq
    exact privacy hI hs ha hp ha' hp' (Ne.symm hqp)
  · exact h1.trans (privacy hI hs ha' hp' hau hpu hpq).symm
open Classical in
theorem kid_points_card' (D : Dag N) (Φ : ℕ → Finset (Fin N)) (g : ℕ) :
    (Finset.univ.filter (fun q : Fin N => ∃ c, D.Kid g c ∧ Φ c = {q})).card ≤ 2 := by
  classical
  cases hg : D.gateAt g with
  | none =>
    have : Finset.univ.filter (fun q : Fin N => ∃ c, D.Kid g c ∧ Φ c = {q}) = ∅ := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        iff_false, not_exists, not_and]
      intro c hk
      obtain ⟨g', hg', -⟩ := hk
      rw [hg] at hg'
      cases hg'
    rw [this]
    simp
  | some gg =>
    have hsub : Finset.univ.filter (fun q : Fin N => ∃ c, D.Kid g c ∧ Φ c = {q}) ⊆
        gg.kids.toFinset.biUnion (fun c => if (Φ c).card ≤ 1 then Φ c else ∅) := by
      intro q hq
      rw [Finset.mem_filter] at hq
      obtain ⟨c, hk, hc⟩ := hq.2
      obtain ⟨g', hg', hcm, -⟩ := hk
      rw [hg] at hg'
      cases hg'
      rw [Finset.mem_biUnion]
      refine ⟨c, List.mem_toFinset.2 hcm, ?_⟩
      rw [hc]
      simp
    have hb := Finset.card_biUnion_le (s := gg.kids.toFinset)
      (t := fun c => if (Φ c).card ≤ 1 then Φ c else ∅)
    have hs : ∑ c ∈ gg.kids.toFinset,
        (if (Φ c).card ≤ 1 then Φ c else ∅).card ≤ ∑ _c ∈ gg.kids.toFinset, 1 := by
      apply Finset.sum_le_sum
      intro c _
      split_ifs with h
      · exact h
      · simp
    have hk : gg.kids.toFinset.card ≤ 2 := by
      refine le_trans (List.toFinset_card_le _) ?_
      cases gg <;> simp [G.kids]
    have := Finset.card_le_card hsub
    simp only [Finset.sum_const, smul_eq_mul, mul_one] at hs
    omega
theorem mem_Q_root {e : Fin N × Fin N} (he : e ∈ Aset I D W R) : e.1 ∈ Q I D W R (R e.2) := by
  classical
  obtain ⟨π, k, ha⟩ := aw_of_mem he
  unfold Q
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, e.2, he, π, k, 0, ha, fun i' h => absurd h (Nat.not_lt_zero _),
    Forms.path_head ha.1.1⟩
theorem small_card (hs : Dag.SoundPartialForm I D W R) :
    ((Aset I D W R).filter (fun e => (Q I D W R (R e.2)).card ≤ 1)).card ≤ W.card := by
  classical
  apply Finset.card_le_card_of_injOn Prod.snd
  · intro e he
    rw [Finset.mem_coe, Finset.mem_filter] at he
    exact (counted_inc hs (aset_counted he.1)).2
  · intro e he e' he' h
    rw [Finset.mem_coe, Finset.mem_filter] at he he'
    have hq1 := mem_Q_root he.1
    have hq2 := mem_Q_root he'.1
    rw [h] at hq1
    exact Prod.ext (Finset.card_le_one.1 he'.2 _ hq1 _ hq2) h
theorem T_card (hI : NoRect I) (hs : Dag.SoundPartialForm I D W R)
    (hcl : D.Cleaned I (D.rootCone W R)) {o : ℕ} (ho : o ∈ D.rootCone W R) :
    (T I D W R o).card ≤ 2 := by
  classical
  have hwf := hs.1
  have hmem : ∀ e ∈ T I D W R o, e ∈ Aset I D W R ∧ Pref I D W R e.1 e.2 o ∧
      2 ≤ (Q I D W R o).card ∧
      (((∀ f v, ¬ D.LabAnd o f v) ∧ ∃ c, D.Kid o c ∧ Q I D W R c = {e.1}) ∨
        ∃ f v, D.LabAnd o f v ∧ e.1 ∈ D.alive f) := by
    intro e he
    unfold T at he
    rw [Finset.mem_filter] at he
    exact ⟨he.1, he.2⟩
  have hline : ∀ e ∈ T I D W R o, ∀ e' ∈ T I D W R o, e.2 = e'.2 := by
    intro e he e' he'
    obtain ⟨ha, hp, h2, -⟩ := hmem e he
    obtain ⟨ha', hp', -, -⟩ := hmem e' he'
    exact line_common hI hs h2 ha hp ha' hp'
  have hinj : Set.InjOn Prod.fst (T I D W R o : Set (Fin N × Fin N)) := by
    intro e he e' he' h
    exact Prod.ext h (hline e he e' he')
  rw [← Finset.card_image_of_injOn hinj]
  by_cases hlab : ∃ f v, D.LabAnd o f v
  · obtain ⟨f0, v0, h0⟩ := hlab
    rcases (T I D W R o).eq_empty_or_nonempty with hT | ⟨e0, he0⟩
    · rw [hT]
      simp
    have hsub : (T I D W R o).image Prod.fst ⊆ D.alive f0 ∩ ptsOn I e0.2 := by
      intro q hq
      rw [Finset.mem_image] at hq
      obtain ⟨e, he, rfl⟩ := hq
      obtain ⟨ha, -, -, hc⟩ := hmem e he
      rcases hc with ⟨hno, -⟩ | ⟨f, v, hf, hal⟩
      · exact absurd h0 (hno f0 v0)
      · obtain ⟨rfl, -⟩ := Api.labAnd_unique hf h0
        rw [Finset.mem_inter]
        refine ⟨hal, ?_⟩
        unfold ptsOn
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [← hline e he e0 he0]
        exact (counted_inc hs (aset_counted ha)).1
    refine le_trans (Finset.card_le_card hsub) ?_
    by_contra h3
    obtain ⟨ha0, -, -, hc0⟩ := hmem e0 he0
    have hal0 : e0.1 ∈ D.alive f0 := by
      rcases hc0 with ⟨hno, -⟩ | ⟨f, v, hf, hal⟩
      · exact absurd h0 (hno f0 v0)
      · obtain ⟨rfl, -⟩ := Api.labAnd_unique hf h0
        exact hal
    have hkid := Forms.labAnd_kid hwf h0
    have hint := Finset.card_le_card (Finset.inter_subset_left (s₁ := D.alive f0)
      (s₂ := ptsOn I e0.2))
    have hfN : N + N ≤ f0 := by
      by_contra hlt
      have := Forms.alive_input_card D (i := f0) (by omega)
      omega
    obtain ⟨-, hos⟩ := Forms.kid_gate hkid
    obtain ⟨_, _, _, hflt⟩ := id hkid
    have hfc : f0 ∈ D.rootCone W R :=
      Forms.mem_coneOf_reach ho (Relation.ReflTransGen.single hkid) hfN (by omega)
    apply aset_not_fSet ha0
    unfold Dag.fSet
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (counted_inc hs (aset_counted ha0)).1, f0, hfc, h0.2.1,
      hcl o ho f0 v0 h0, hal0, by omega⟩
  · refine le_trans (Finset.card_le_card ?_) (kid_points_card' D (Q I D W R) o)
    intro q hq
    rw [Finset.mem_image] at hq
    obtain ⟨e, he, rfl⟩ := hq
    obtain ⟨-, -, -, hc⟩ := hmem e he
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases hc with ⟨-, c, hk, hq⟩ | ⟨f, v, hf, -⟩
    · exact ⟨c, hk, hq⟩
    · exact absurd ⟨f, v, hf⟩ hlab
theorem big_mem (hs : Dag.SoundPartialForm I D W R) {e : Fin N × Fin N}
    (he : e ∈ Aset I D W R) (h2 : 2 ≤ (Q I D W R (R e.2)).card) :
    ∃ o ∈ (D.rootCone W R).filter (fun f => D.deg f = 1), e ∈ T I D W R o := by
  classical
  obtain ⟨p, w⟩ := e
  dsimp only at h2
  have hwf := hs.1
  obtain ⟨π, k, ha⟩ := aw_of_mem he
  have hw := (counted_inc hs (aset_counted he)).2
  have hk := ha.2.1.1
  let J : ℕ → Prop := fun i => (∀ i' < i, ¬ Lab D π i') ∧ 2 ≤ (Q I D W R (π.getD i 0)).card
  have hJ0 : J 0 := ⟨fun i' h => absurd h (Nat.not_lt_zero _), by
    show 2 ≤ (Q I D W R (π.getD 0 0)).card
    rw [Forms.path_head ha.1.1]
    exact h2⟩
  obtain ⟨m, hm⟩ : ∃ m, m = Nat.findGreatest J k := ⟨_, rfl⟩
  have hJm : J m := by
    rw [hm]
    exact Nat.findGreatest_spec (Nat.zero_le k) hJ0
  have hmk : m ≤ k := by
    rw [hm]
    exact Nat.findGreatest_le k
  have hgr : ∀ j, m < j → j ≤ k → ¬ J j := fun j h1 h2 =>
    Nat.findGreatest_is_greatest (by rw [← hm]; exact h1) h2
  have hmlen : m + 1 < π.length := by omega
  obtain ⟨hdo, hro⟩ := aw_deg hs ha hw (i := m) (by omega)
  obtain ⟨hdc, -⟩ := aw_deg hs ha hw (i := m + 1) hmlen
  have hkid : D.Kid (π.getD m 0) (π.getD (m + 1) 0) := ha.1.1.2.2 m hmlen
  obtain ⟨hoN, hos⟩ := Forms.kid_gate hkid
  refine ⟨π.getD m 0, Finset.mem_filter.2 ⟨Forms.mem_rootCone hw hro hoN hos, hdo⟩, ?_⟩
  unfold T
  rw [Finset.mem_filter]
  refine ⟨he, ⟨π, k, m, ha, hJm.1, rfl⟩, hJm.2, ?_⟩
  by_cases hL : Lab D π m
  · right
    obtain ⟨f, hf⟩ := hL
    exact ⟨f, _, hf, Forms.mem_alive.2
      (label_alive hwf (ha.1.2 _ (Forms.path_getD_mem (by omega))).1 hf)⟩
  · left
    refine ⟨fun f v hfv => hL ⟨f, labAnd_of_kid hfv hkid hdc⟩, π.getD (m + 1) 0, hkid, ?_⟩
    have hnl : ∀ i' < m + 1, ¬ Lab D π i' := by
      intro i' hi'
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with h | h
      · exact hJm.1 i' h
      · rw [h]
        exact hL
    have hp : p ∈ Q I D W R (π.getD (m + 1) 0) := by
      unfold Q
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, w, he, π, k, m + 1, ha, hnl, rfl⟩
    have hmk' : m + 1 ≤ k := by
      rcases Nat.lt_or_eq_of_le hmk with h | h
      · omega
      · exfalso
        rw [h] at hL
        obtain ⟨-, f, hf, -⟩ := ha.2.1
        exact hL ⟨f, hf⟩
    have hc1 : (Q I D W R (π.getD (m + 1) 0)).card ≤ 1 := by
      by_contra hc
      exact hgr (m + 1) (Nat.lt_succ_self m) hmk' ⟨hnl, by omega⟩
    rw [Finset.eq_singleton_iff_unique_mem]
    exact ⟨hp, fun q hq => Finset.card_le_one.1 hc1 q hq p hp⟩
end Deg2.Alpha
namespace Deg2
variable {N : ℕ}
theorem card12_alpha (I : Fin N → Fin N → Prop) (hI : NoRect I) (D : Dag N)
    (W : Finset (Fin N)) (R : Fin N → ℕ) (hs : Dag.SoundPartialForm I D W R)
    (hcl : D.Cleaned I (D.rootCone W R)) :
    (D.alphaEdges I W R \ (D.e0Set W R ∪ D.e1Set I W R ∪ D.fSet I (D.rootCone W R) 2)).card ≤
      2 * ((D.rootCone W R).filter (fun f => D.deg f = 1)).card + W.card := by
  classical
  change (Alpha.Aset I D W R).card ≤ _
  have hsub : Alpha.Aset I D W R ⊆
      (Alpha.Aset I D W R).filter (fun e => (Alpha.Q I D W R (R e.2)).card ≤ 1) ∪
        ((D.rootCone W R).filter (fun f => D.deg f = 1)).biUnion (Alpha.T I D W R) := by
    intro e he
    by_cases hsm : (Alpha.Q I D W R (R e.2)).card ≤ 1
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨he, hsm⟩)
    · apply Finset.mem_union_right
      obtain ⟨o, ho, het⟩ := Alpha.big_mem hs he (by omega)
      exact Finset.mem_biUnion.2 ⟨o, ho, het⟩
  have hsm := Alpha.small_card hs
  have hb : (((D.rootCone W R).filter (fun f => D.deg f = 1)).biUnion
      (Alpha.T I D W R)).card ≤ 2 * ((D.rootCone W R).filter (fun f => D.deg f = 1)).card := by
    calc _ ≤ ∑ o ∈ (D.rootCone W R).filter (fun f => D.deg f = 1), (Alpha.T I D W R o).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _o ∈ (D.rootCone W R).filter (fun f => D.deg f = 1), 2 :=
          Finset.sum_le_sum (fun o ho => Alpha.T_card hI hs hcl (Finset.mem_filter.1 ho).1)
      _ = 2 * ((D.rootCone W R).filter (fun f => D.deg f = 1)).card := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hu := Finset.card_union_le
    ((Alpha.Aset I D W R).filter (fun e => (Alpha.Q I D W R (R e.2)).card ≤ 1))
    (((D.rootCone W R).filter (fun f => D.deg f = 1)).biUnion (Alpha.T I D W R))
  have hc := Finset.card_le_card hsub
  omega
end Deg2
namespace Deg2.Beta
open Deg2 Deg2.Api
  Deg2.Forms
variable {N : ℕ}
def LStep (D : Dag N) (x : Fin (N + N) → Bool) (a b : ℕ) : Prop :=
  D.Kid a b ∧ ∀ f, D.LabAnd a f b → D.val x f = true
theorem lstep_reach {D : Dag N} {x : Fin (N + N) → Bool} {a b : ℕ}
    (h : Relation.ReflTransGen (LStep D x) a b) : D.Reach a b :=
  by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail hs.1
theorem path_lstep {D : Dag N} {x : Fin (N + N) → Bool} :
    ∀ (π : List ℕ) (a b : ℕ), D.IsPath π a b → D.LabelsAlive π x →
      Relation.ReflTransGen (LStep D x) a b := by
  intro π
  induction π with
  | nil => intro a b h; exact absurd h.1 (by simp)
  | cons a' rest ih =>
    intro a b hp hl
    obtain ⟨hh, hlast, hs⟩ := hp
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    cases rest with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hlast
      subst hlast
      exact .refl
    | cons c rest' =>
      have hk : D.Kid a' c := by simpa using hs 0 (by simp)
      have hpc : D.IsPath (c :: rest') c b := by
        refine ⟨rfl, ?_, ?_⟩
        · rw [List.getLast?_cons_cons] at hlast; exact hlast
        · intro k hk'
          have := hs (k + 1) (by simp only [List.length_cons] at hk' ⊢; omega)
          simpa using this
      have hlc : D.LabelsAlive (c :: rest') x := by
        intro k f hk' hlab
        exact hl (k + 1) f (by simp only [List.length_cons] at hk' ⊢; omega) (by simpa using hlab)
      exact Relation.ReflTransGen.head ⟨hk, fun f hf => hl 0 f (by simp) (by simpa using hf)⟩
        (ih c b hpc hlc)
theorem path_reach {D : Dag N} {π : List ℕ} {a b : ℕ} (hp : D.IsPath π a b) :
    ∀ k, k < π.length → D.Reach a (π.getD k 0) := by
  intro k
  induction k with
  | zero => intro _; rw [path_head hp]; exact .refl
  | succ k ih =>
    intro hk
    exact Relation.ReflTransGen.tail (ih (by omega)) (hp.2.2 k hk)
theorem gate_bounds {D : Dag N} {i : ℕ} {g : G} (h : D.gateAt i = some g) :
    N + N ≤ i ∧ i < N + N + D.size := by
  obtain ⟨hi, hg⟩ := gateAt_some h
  have := (List.getElem?_eq_some_iff.1 hg).1
  unfold Dag.size
  omega
theorem deg_eq_one {D : Dag N} {r v : ℕ} {p w : Fin N} (hr : D.deg r ≤ 1) (hreach : D.Reach r v)
    (h1 : D.val (ep p w) v = true) (h0 : D.val (pt p) v = false) : D.deg v = 1 := by
  have := api_reach_deg D hreach
  by_contra hne
  have hd : D.deg v = 0 := by omega
  have := api_val_xonly D hd (x := pt p) (y := ep p w) (fun q => pt_ep_points p w q)
  rw [h1, h0] at this
  cases this
theorem label_alive {D : Dag N} (hwf : D.WF) {e f v : ℕ} {p w : Fin N} (h : D.LabAnd e f v)
    (he : D.val (ep p w) e = true) : D.val (pt p) f = true := by
  rw [labAnd_val hwf h, Bool.and_eq_true] at he
  rw [api_val_xonly D h.2.1 (x := pt p) (y := ep p w) (fun q => pt_ep_points p w q)]
  exact he.1
theorem vreach_deg {D : Dag N} {v : ℕ} {u : Fin N} (h : D.VReach v u) : D.deg v = 1 := by
  cases h with
  | leaf => exact deg_line D u
  | step _ hd _ _ => exact hd
theorem mem_vstar {D : Dag N} {v : ℕ} {u : Fin N} : u ∈ D.Vstar v ↔ D.VReach v u := by
  classical
  unfold Dag.Vstar
  simp
theorem labAnd_kid_v {D : Dag N} (hwf : D.WF) {e f v : ℕ} (h : D.LabAnd e f v) : D.Kid e v := by
  rcases h.1 with hg | hg
  · exact ⟨_, hg, by simp [G.kids], hwf _ _ hg v (by simp [G.kids])⟩
  · exact ⟨_, hg, by simp [G.kids], hwf _ _ hg v (by simp [G.kids])⟩
theorem lstep_up {D : Dag N} (hwf : D.WF) {x y : Fin (N + N) → Bool} (hxy : x ≤ y) {a b : ℕ}
    (h : Relation.ReflTransGen (LStep D x) a b) (ha : D.deg a ≤ 1) (hb : 1 ≤ D.deg b)
    (hy : D.val y b = true) : D.val y a = true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hy
  | @head a a' hst hrest ih =>
    obtain ⟨hk, hlab⟩ := hst
    have ha' : D.deg a' ≤ 1 := le_trans (deg_kid hk) ha
    have hva' := ih ha'
    have hda' : 1 ≤ D.deg a' := le_trans hb (api_reach_deg D (lstep_reach hrest))
    obtain ⟨g, hg, hcm, hlt⟩ := id hk
    cases g with
    | and c d =>
      have hc := hwf _ _ hg c (by simp [G.kids])
      have hd := hwf _ _ hg d (by simp [G.kids])
      have hdeg := deg_and hg hc hd
      rw [val_and hg hc hd]
      simp only [G.kids, List.mem_cons, List.not_mem_nil, or_false] at hcm
      rcases hcm with h | h
      · subst h
        have hlb : D.LabAnd a d a' := ⟨Or.inr hg, by omega, by omega⟩
        have hm := Api.api_val_mono D d hxy
        rw [hlab d hlb] at hm
        rw [hva', bool_true_le hm]
        rfl
      · subst h
        have hlb : D.LabAnd a c a' := ⟨Or.inl hg, by omega, by omega⟩
        have hm := Api.api_val_mono D c hxy
        rw [hlab c hlb] at hm
        rw [hva', bool_true_le hm]
        rfl
    | or c d => exact circ_val_or_kid D hg hk hva'
    | cst _ => simp [G.kids] at hcm
def IsB (I : Fin N → Fin N → Prop) (D : Dag N) (W : Finset (Fin N)) (R : Fin N → ℕ) (p : Fin N)
    (v : ℕ) : Prop :=
  ∃ u ∈ W, ¬ I p u ∧ Relation.ReflTransGen (LStep D (pt p)) (R u) v
theorem beta_line (I : Fin N → Fin N → Prop) {D : Dag N} {W : Finset (Fin N)} {R : Fin N → ℕ}
    (hs : Dag.SoundPartialForm I D W R) {p u' : Fin N} {v : ℕ} (hb : IsB I D W R p v)
    (hv : D.VReach v u') : I p u' := by
  classical
  obtain ⟨u, hu, hpu, hρ⟩ := hb
  obtain ⟨hwf, hdeg, hsound⟩ := hs
  have hxz : pt p ≤ inp {p} {u, u'} := inp_mono (Finset.empty_subset _)
  have hzv : D.val (inp {p} {u, u'}) v = true := circ_vreach_val D hv (by rw [inp_natAdd]; simp)
  have hzr := lstep_up hwf hxz hρ (hdeg u hu) (by rw [vreach_deg hv]) hzv
  obtain ⟨p0, l, hI, hp0, hl⟩ := hsound _ ⟨u, hu, by rw [inp_natAdd]; simp, hzr⟩
  simp only [inp_castAdd, inp_natAdd, decide_eq_true_eq, Finset.mem_singleton,
    Finset.mem_insert] at hp0 hl
  subst hp0
  rcases hl with rfl | rfl
  · exact absurd hI hpu
  · exact hI
theorem counted_incident (I : Fin N → Fin N → Prop) {D : Dag N} {W : Finset (Fin N)}
    {R : Fin N → ℕ} (hs : Dag.SoundPartialForm I D W R) {p w : Fin N} (hw : w ∈ W)
    (h : D.val (ep p w) (R w) = true) : I p w := by
  obtain ⟨-, -, hsound⟩ := hs
  obtain ⟨p0, l, hI, hp0, hl⟩ := hsound (ep p w) ⟨w, hw, by unfold ep; rw [inp_natAdd]; simp, h⟩
  simp only [ep, inp_castAdd, inp_natAdd, decide_eq_true_eq, Finset.mem_singleton] at hp0 hl
  subst hp0; subst hl
  exact hI
def OrCh (I : Fin N → Fin N → Prop) (D : Dag N) (g : ℕ) (e : Fin N × Fin N) : Prop :=
  Dag.PinnedTo I D g e.1 ∧ ∃ c, D.Kid g c ∧ D.Vstar c = {e.2}
def AndCh (I : Fin N → Fin N → Prop) (D : Dag N) (g : ℕ) (e : Fin N × Fin N) : Prop :=
  ∃ f v, D.LabAnd g f v ∧ D.Vstar v = {e.2} ∧ e.1 ∈ D.alive f ∧ I e.1 e.2 ∧
    (D.alive f ∩ ptsOn I e.2).card ≤ 2
def Charged (I : Fin N → Fin N → Prop) (D : Dag N) (Gs : Finset ℕ) (e : Fin N × Fin N) : Prop :=
  ∃ g ∈ Gs, OrCh I D g e ∨ AndCh I D g e
theorem charge_at (I : Fin N → Fin N → Prop) {D : Dag N} {W : Finset (Fin N)}
    {R : Fin N → ℕ} (hs : Dag.SoundPartialForm I D W R) (hcl : D.Cleaned I (D.rootCone W R))
    {p w : Fin N} (hw : w ∈ W) (hpw : I p w) (hnf : (p, w) ∉ D.fSet I (D.rootCone W R) 2)
    {e f v : ℕ} (he : D.LabAnd e f v) (hre : D.Reach (R w) e) (hde : D.deg e = 1)
    (hf : D.val (pt p) f = true) (hb : IsB I D W R p v) (hwv : w ∈ D.Vstar v) :
    Charged I D ((D.rootCone W R).filter (fun f => D.deg f = 1)) (p, w) := by
  classical
  have hwf := hs.1
  have hkv := labAnd_kid_v hwf he
  have hkf := labAnd_kid hwf he
  have heb := kid_gate hkv
  have hecone : e ∈ D.rootCone W R := mem_rootCone hw hre heb.1 heb.2
  by_cases h2 : 2 ≤ (D.Vstar v).card
  · obtain ⟨o, c, hr, ho, hod, ho2, hos, hk, hc⟩ := circ_pin_charge D (mem_vstar.1 hwv) h2
    obtain ⟨a', b', hga⟩ := ho
    have hob := gate_bounds hga
    have hro : D.Reach (R w) o :=
      Relation.ReflTransGen.trans (Relation.ReflTransGen.tail hre hkv) hr
    refine ⟨o, Finset.mem_filter.2 ⟨mem_rootCone hw hro hob.1 hob.2, hod⟩, Or.inl ⟨⟨⟨a', b', hga⟩,
      hod, ho2, ?_⟩, c, hk, hc⟩⟩
    intro u' hu'
    have := beta_line I hs hb (mem_vstar.1 (hos hu'))
    unfold pencil
    simpa using this
  · have hsing : D.Vstar v = {w} := by
      rw [Finset.eq_singleton_iff_unique_mem]
      exact ⟨hwv, fun x hx => Finset.card_le_one.1 (by omega) x hx w hwv⟩
    refine ⟨e, Finset.mem_filter.2 ⟨hecone, hde⟩, Or.inr ⟨f, v, he, hsing, mem_alive.2 hf, hpw, ?_⟩⟩
    by_contra hgt
    rw [not_le] at hgt
    apply hnf
    have hsubf := Finset.card_le_card
      (Finset.inter_subset_left (s₁ := D.alive f) (s₂ := ptsOn I w))
    have hf2 : 2 ≤ (D.alive f).card := by simp only at hgt; omega
    have hfg := two_le_alive_gate D hf2
    obtain ⟨_, _, _, hfe⟩ := id hkf
    have hfcone : f ∈ D.rootCone W R :=
      mem_rootCone hw (Relation.ReflTransGen.tail hre hkf) hfg (by omega)
    unfold Dag.fSet
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hpw, f, hfcone, he.2.1, hcl e hecone f v he, mem_alive.2 hf,
      by omega⟩
theorem or_of_not_lab {D : Dag N} (hwf : D.WF) {v c : ℕ} (hk : D.Kid v c) (hv : D.deg v = 1)
    (hc : D.deg c = 1) (hn : ¬ ∃ f, D.LabAnd v f c) : D.IsOr v := by
  obtain ⟨g, hg, hcm, -⟩ := hk
  cases g with
  | and a b =>
    exfalso
    have ha := hwf _ _ hg a (by simp [G.kids])
    have hb := hwf _ _ hg b (by simp [G.kids])
    rw [deg_and hg ha hb] at hv
    simp only [G.kids, List.mem_cons, List.not_mem_nil, or_false] at hcm
    rcases hcm with rfl | rfl
    · exact hn ⟨b, Or.inr hg, by omega, hc⟩
    · exact hn ⟨a, Or.inl hg, by omega, hc⟩
  | or a b => exact ⟨a, b, hg⟩
  | cst _ => simp [G.kids] at hcm
theorem descend (I : Fin N → Fin N → Prop) {D : Dag N} {W : Finset (Fin N)}
    {R : Fin N → ℕ} (hs : Dag.SoundPartialForm I D W R) (hcl : D.Cleaned I (D.rootCone W R))
    {p w : Fin N} (hw : w ∈ W) (hpw : I p w) (hnf : (p, w) ∉ D.fSet I (D.rootCone W R) 2) :
    ∀ v, D.val (ep p w) v = true → D.val (pt p) v = false → D.Reach (R w) v → IsB I D W R p v →
      w ∈ D.Vstar v ∨ Charged I D ((D.rootCone W R).filter (fun f => D.deg f = 1)) (p, w) := by
  have hwf := hs.1
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    intro h1 h0 hr hb
    by_cases hi : v < N + N
    · left
      rw [circ_val_input D _ hi] at h1
      rw [circ_val_input D _ hi] at h0
      have := ep_input hi h1 h0
      subst this
      exact mem_vstar.2 (Dag.VReach.leaf w)
    · obtain ⟨c, hk, hc1, hc0⟩ := exists_kid D (by omega) h1 h0
      have hrc : D.Reach (R w) c := Relation.ReflTransGen.tail hr hk
      have hdv := deg_eq_one (hs.2.1 w hw) hr h1 h0
      have hdc := deg_eq_one (hs.2.1 w hw) hrc hc1 hc0
      have hbc : IsB I D W R p c := by
        obtain ⟨u, hu, hpu, hρ⟩ := hb
        exact ⟨u, hu, hpu, Relation.ReflTransGen.tail hρ ⟨hk, fun f hf => label_alive hwf hf h1⟩⟩
      rcases ih c (circ_kid_lt hk) hc1 hc0 hrc hbc with hwc | hch
      · by_cases hl : ∃ f, D.LabAnd v f c
        · obtain ⟨f, hlab⟩ := hl
          exact Or.inr (charge_at I hs hcl hw hpw hnf hlab hr hdv (label_alive hwf hlab h1)
            hbc hwc)
        · exact Or.inl (circ_vstar_sub D (or_of_not_lab hwf hk hdv hdc hl) hdv hk hwc)
      · exact Or.inr hch
open Classical in
theorem fibre_le (I : Fin N → Fin N → Prop) (hI : NoRect I) (D : Dag N) (g : ℕ) :
    (Finset.univ.filter (fun e => OrCh I D g e ∨ AndCh I D g e)).card ≤ 2 := by
  classical
  by_cases hor : D.IsOr g
  · let U : ℕ → Finset (Fin N × Fin N) := fun c =>
      Finset.univ.filter (fun e => Dag.PinnedTo I D g e.1 ∧ D.Vstar c = {e.2})
    have hU : ∀ c, (U c).card ≤ 1 := by
      intro c
      rw [Finset.card_le_one]
      intro e he e' he'
      simp only [U, Finset.mem_filter, Finset.mem_univ, true_and] at he he'
      have h1 := circ_pinned_unique I hI D he.1 he'.1
      have h2 : e.2 = e'.2 := Finset.singleton_inj.1 (he.2.symm.trans he'.2)
      exact Prod.ext h1 h2
    have hsub : Finset.univ.filter (fun e => OrCh I D g e ∨ AndCh I D g e) ⊆
        (circKids D g).biUnion U := by
      intro e he
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
      rcases he with ⟨hp, c, hk, hc⟩ | ⟨f, v, hlab, -⟩
      · rw [Finset.mem_biUnion]
        exact ⟨c, circKids_mem hk, by simp [U, hp, hc]⟩
      · exfalso
        obtain ⟨a, b, hg⟩ := hor
        rcases hlab.1 with h | h <;> rw [hg] at h <;> simp at h
    refine le_trans (Finset.card_le_card hsub) ?_
    refine le_trans (Finset.card_biUnion_le_card_mul _ _ 1 (fun c _ => hU c)) ?_
    have := circKids_card D g
    omega
  · have hsub : Finset.univ.filter (fun e => OrCh I D g e ∨ AndCh I D g e) ⊆
        Finset.univ.filter (fun e => AndCh I D g e) := by
      intro e he
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
      rcases he with ⟨hp, -⟩ | h
      · exact absurd hp.1 hor
      · exact h
    refine le_trans (Finset.card_le_card hsub) ?_
    by_cases hne : (Finset.univ.filter (fun e => AndCh I D g e)).Nonempty
    · obtain ⟨e0, he0⟩ := hne
      obtain ⟨f0, v0, h1, h2, -, -, h5⟩ := (Finset.mem_filter.1 he0).2
      have hsub' : Finset.univ.filter (fun e => AndCh I D g e) ⊆
          (D.alive f0 ∩ ptsOn I e0.2).image (fun p => (p, e0.2)) := by
        intro e he
        obtain ⟨f, v, k1, k2, k3, k4, -⟩ := (Finset.mem_filter.1 he).2
        obtain ⟨rfl, rfl⟩ := labAnd_unique k1 h1
        have hw : e.2 = e0.2 := by
          rw [h2] at k2
          exact (Finset.singleton_inj.1 k2).symm
        rw [Finset.mem_image]
        refine ⟨e.1, Finset.mem_inter.2 ⟨k3, ?_⟩, ?_⟩
        · unfold ptsOn
          rw [Finset.mem_filter, ← hw]
          exact ⟨Finset.mem_univ _, k4⟩
        · ext <;> simp [hw]
      exact le_trans (Finset.card_le_card hsub') (le_trans Finset.card_image_le h5)
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne]; simp
end Deg2.Beta
namespace Deg2
open Deg2.Api Deg2.Forms
  Deg2.Beta
variable {N : ℕ}
theorem card13_beta (I : Fin N → Fin N → Prop) (hI : NoRect I) (D : Dag N)
    (W : Finset (Fin N)) (R : Fin N → ℕ) (hs : Dag.SoundPartialForm I D W R)
    (hcl : D.Cleaned I (D.rootCone W R)) :
    (D.betaEdges I W R \ (D.e0Set W R ∪ D.e1Set I W R ∪ D.fSet I (D.rootCone W R) 2)).card ≤
      2 * ((D.rootCone W R).filter (fun f => D.deg f = 1)).card := by
  classical
  set Gs := (D.rootCone W R).filter (fun f => D.deg f = 1) with hGs
  let T : ℕ → Finset (Fin N × Fin N) := fun g =>
    Finset.univ.filter (fun e => OrCh I D g e ∨ AndCh I D g e)
  have hsub : D.betaEdges I W R \ (D.e0Set W R ∪ D.e1Set I W R ∪ D.fSet I (D.rootCone W R) 2) ⊆
      Gs.biUnion T := by
    intro e he
    rw [Finset.mem_sdiff] at he
    obtain ⟨hbe, hout⟩ := he
    have hnf : e ∉ D.fSet I (D.rootCone W R) 2 := fun h => hout (Finset.mem_union_right _ h)
    unfold Dag.betaEdges at hbe
    rw [Finset.mem_filter] at hbe
    obtain ⟨hce, π, hEP, k, hPG, -, hB⟩ := hbe
    unfold Dag.countedEdges at hce
    rw [Finset.mem_filter] at hce
    obtain ⟨-, hw, hval⟩ := hce
    obtain ⟨p, w⟩ := e
    dsimp only at hw hval hnf hEP hPG hB ⊢
    have hpw := counted_incident I hs hw hval
    obtain ⟨hk1, f, hlab, hal⟩ := hPG
    have hpath := hEP.1
    have hm0 := path_getD_mem (π := π) (k := k) (by omega)
    have hm1 := path_getD_mem (π := π) (k := k + 1) hk1
    obtain ⟨he1, he0⟩ := hEP.2 _ hm0
    obtain ⟨hg1, hg0⟩ := hEP.2 _ hm1
    have hr0 := path_reach hpath k (by omega)
    have hr1 := path_reach hpath (k + 1) hk1
    have hdeg0 := deg_eq_one (hs.2.1 w hw) hr0 he1 he0
    have hbeta : IsB I D W R p (π.getD (k + 1) 0) := by
      obtain ⟨u, hu, hpu, ρ, hρ, hla⟩ := hB
      exact ⟨u, hu, hpu, path_lstep ρ _ _ hρ hla⟩
    have hfp : D.val (pt p) f = true := by
      rw [← mem_alive, hal]; exact Finset.mem_singleton_self p
    have hch : Charged I D Gs (p, w) := by
      rcases descend I hs hcl hw hpw hnf _ hg1 hg0 hr1 hbeta with hwv | hch
      · exact charge_at I hs hcl hw hpw hnf hlab hr0 hdeg0 hfp hbeta hwv
      · exact hch
    obtain ⟨g, hg, hc⟩ := hch
    rw [Finset.mem_biUnion]
    exact ⟨g, hg, Finset.mem_filter.2 ⟨Finset.mem_univ _, hc⟩⟩
  calc _ ≤ (Gs.biUnion T).card := Finset.card_le_card hsub
    _ ≤ ∑ g ∈ Gs, (T g).card := Finset.card_biUnion_le
    _ ≤ ∑ _g ∈ Gs, 2 := Finset.sum_le_sum (fun g _ => fibre_le I hI D g)
    _ = 2 * Gs.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
end Deg2
namespace Deg2
open PEqualNP.CircuitLowerBounds Deg2.Api
theorem assembly_core
    (h14 : ∀ {N : ℕ} (I : Fin N → Fin N → Prop) (hI : NoRect I) (D : Dag N)
      (W : Finset (Fin N)) (R : Fin N → ℕ) (hs : Dag.SoundPartialForm I D W R),
      (D.countedEdges W R).card ≤ 12 * (D.rootCone W R).card + 2 * W.card)
    (h16 : ∀ {N : ℕ} (I : Fin N → Fin N → Prop) (D : Dag N) (hwf : D.WF)
      (hc : Computes I D.fn) (hd : D.deg D.out ≤ 2),
      ∃ (F : Dag N) (W : Finset (Fin N)) (R : Fin N → ℕ), Dag.SoundPartialForm I F W R ∧
        D.markerEdges I ⊆ F.countedEdges W R ∧
        (F.rootCone W R).card ≤ D.M.card + D.X.card + 4 * D.T.card)
    (h17 : ∀ {N : ℕ} (I : Fin N → Fin N → Prop) (D : Dag N) (hwf : D.WF)
      (hc : Computes I D.fn) (hd : D.deg D.out ≤ 2) (hcl : D.Cleaned I D.cone),
      ∀ p w : Fin N, I p w →
        (p, w) ∈ D.pinned I ∪ D.served I ∪ D.fSet I D.cone 2 ∪ D.markerEdges I) :
    ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : PEqualNP.CircuitLowerBounds.Circuit),
    (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
    PEqualNP.MetaComplexity.Monotone2 C →
    PEqualNP.CircuitLowerBounds.HasLineDegree (N + N) (Finset.Ico N (N + N)) C 2 →
    (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
    (Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)).card ≤ 48 * C.size + 2 * N := by
  intro N I _ C hI hmono hdeg hfun
  have hI' : NoRect I := hI
  let D : Dag N := ofCircuit N C
  have hwf : D.WF := card03b_wf C
  have hsize : D.size = C.size := by simp [D, Dag.size, ofCircuit, Circuit.size]
  have hcomp : Computes I D.fn := by
    intro z
    rw [← hfun z]
    show (ofCircuit N C).val z C.output = true ↔ C.eval (List.ofFn z) = true
    rw [Bridge.card03c_val C hmono z C.output]
    rfl
  have hd : D.deg D.out ≤ 2 := le_trans (Bridge.card03d_deg C hmono C.output) hdeg
  obtain ⟨D', hwf', hs', hc', hd', hcl'⟩ := Bridge.card04_clean I D hwf hcomp hd
  have hcov := h17 I D' hwf' hc' hd' hcl'
  obtain ⟨F, W, R, hsound, hmk, hF⟩ := h16 I D' hwf' hc' hd'
  have h14' := h14 I hI' F W R hsound
  have hW : W.card ≤ N := by
    simpa using Finset.card_le_univ W
  have hp := card08_pinned I hI' D'
  have hsv := card17s_served I D'
  have h7 : (D'.fSet I D'.cone 2).card ≤ 8 * D'.X.card :=
    card07_two_line I hI' D' D'.cone (api_coneOf_down D' {D'.out})
  have hcl := api_classes_card D'
  have hao := api_andor_card D'
  have hE : Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2) ⊆
      D'.pinned I ∪ D'.served I ∪ D'.fSet I D'.cone 2 ∪ F.countedEdges W R := by
    intro e he
    have he' : I e.1 e.2 := (Finset.mem_filter.1 he).2
    have h := hcov e.1 e.2 he'
    simp only [Finset.mem_union] at h ⊢
    rcases h with ((h | h) | h) | h
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inr h)
    · exact Or.inr (hmk h)
  have hU := Finset.card_le_card hE
  have hU1 := Finset.card_union_le (D'.pinned I ∪ D'.served I ∪ D'.fSet I D'.cone 2)
    (F.countedEdges W R)
  have hU2 := Finset.card_union_le (D'.pinned I ∪ D'.served I) (D'.fSet I D'.cone 2)
  have hU3 := Finset.card_union_le (D'.pinned I) (D'.served I)
  omega
theorem assembly_of
    (h10e0 : ∀ {N : ℕ} (I : Fin N → Fin N → Prop) (hI : NoRect I) (D : Dag N)
      (W : Finset (Fin N)) (R : Fin N → ℕ) (hs : Dag.SoundPartialForm I D W R),
      (D.e0Set W R).card ≤ 2 * (D.rootCone W R).card + W.card)
    (h12 : ∀ {N : ℕ} (I : Fin N → Fin N → Prop) (hI : NoRect I) (D : Dag N)
      (W : Finset (Fin N)) (R : Fin N → ℕ) (hs : Dag.SoundPartialForm I D W R)
      (hcl : D.Cleaned I (D.rootCone W R)),
      (D.alphaEdges I W R \ (D.e0Set W R ∪ D.e1Set I W R ∪ D.fSet I (D.rootCone W R) 2)).card ≤
        2 * ((D.rootCone W R).filter (fun f => D.deg f = 1)).card + W.card)
    (h13 : ∀ {N : ℕ} (I : Fin N → Fin N → Prop) (hI : NoRect I) (D : Dag N)
      (W : Finset (Fin N)) (R : Fin N → ℕ) (hs : Dag.SoundPartialForm I D W R)
      (hcl : D.Cleaned I (D.rootCone W R)),
      (D.betaEdges I W R \ (D.e0Set W R ∪ D.e1Set I W R ∪ D.fSet I (D.rootCone W R) 2)).card ≤
        2 * ((D.rootCone W R).filter (fun f => D.deg f = 1)).card)
    (_h15 : ∀ {N : ℕ} (I : Fin N → Fin N → Prop) (D : Dag N) (hwf : D.WF)
      (hc : Computes I D.fn) (hd : D.deg D.out ≤ 2) (x : Fin (N + N) → Bool),
      D.fn x = true ↔
        ∃ b, D.IsItem b ∧ D.ctx b x = true ∧ ∀ r, D.IsFactor b r → D.val x r = true)
    (_h15c : ∀ {N : ℕ} (D : Dag N) (hwf : D.WF) (hd : D.deg D.out ≤ 2),
      ∃ D' : Dag N, D.gates <+: D'.gates ∧ D'.WF ∧
        D'.size ≤ D.size + 2 * D.Tor.card + 2 * D.Tandf.card ∧
        ∀ b, D.IsItem b → (∀ x, D.ctx b x = true) ∨
          ∃ i, D'.deg i = 0 ∧ (∀ x, D'.val x i = D.ctx b x) ∧
            D'.coneOf {i} ⊆ D.X ∪ Finset.Ico (N + N + D.size) (N + N + D'.size))
    (h16 : ∀ {N : ℕ} (I : Fin N → Fin N → Prop) (D : Dag N) (hwf : D.WF)
      (hc : Computes I D.fn) (hd : D.deg D.out ≤ 2),
      ∃ (F : Dag N) (W : Finset (Fin N)) (R : Fin N → ℕ), Dag.SoundPartialForm I F W R ∧
        D.markerEdges I ⊆ F.countedEdges W R ∧
        (F.rootCone W R).card ≤ D.M.card + D.X.card + 4 * D.T.card)
    (h17 : ∀ {N : ℕ} (I : Fin N → Fin N → Prop) (D : Dag N) (hwf : D.WF)
      (hc : Computes I D.fn) (hd : D.deg D.out ≤ 2) (hcl : D.Cleaned I D.cone),
      ∀ p w : Fin N, I p w →
        (p, w) ∈ D.pinned I ∪ D.served I ∪ D.fSet I D.cone 2 ∪ D.markerEdges I) :
    ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : PEqualNP.CircuitLowerBounds.Circuit),
    (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
    PEqualNP.MetaComplexity.Monotone2 C →
    PEqualNP.CircuitLowerBounds.HasLineDegree (N + N) (Finset.Ico N (N + N)) C 2 →
    (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
    (Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)).card ≤ 48 * C.size + 2 * N :=
  assembly_core (fun I hI D W R hs => card14_of h10e0 h12 h13 I hI D W R hs) h16 h17
theorem assembly_of_identity
    (h10e0 : ∀ {N : ℕ} (I : Fin N → Fin N → Prop) (hI : NoRect I) (D : Dag N)
      (W : Finset (Fin N)) (R : Fin N → ℕ) (hs : Dag.SoundPartialForm I D W R),
      (D.e0Set W R).card ≤ 2 * (D.rootCone W R).card + W.card)
    (h12 : ∀ {N : ℕ} (I : Fin N → Fin N → Prop) (hI : NoRect I) (D : Dag N)
      (W : Finset (Fin N)) (R : Fin N → ℕ) (hs : Dag.SoundPartialForm I D W R)
      (hcl : D.Cleaned I (D.rootCone W R)),
      (D.alphaEdges I W R \ (D.e0Set W R ∪ D.e1Set I W R ∪ D.fSet I (D.rootCone W R) 2)).card ≤
        2 * ((D.rootCone W R).filter (fun f => D.deg f = 1)).card + W.card)
    (h13 : ∀ {N : ℕ} (I : Fin N → Fin N → Prop) (hI : NoRect I) (D : Dag N)
      (W : Finset (Fin N)) (R : Fin N → ℕ) (hs : Dag.SoundPartialForm I D W R)
      (hcl : D.Cleaned I (D.rootCone W R)),
      (D.betaEdges I W R \ (D.e0Set W R ∪ D.e1Set I W R ∪ D.fSet I (D.rootCone W R) 2)).card ≤
        2 * ((D.rootCone W R).filter (fun f => D.deg f = 1)).card)
    (h15 : ∀ {N : ℕ} (I : Fin N → Fin N → Prop) (D : Dag N) (hwf : D.WF)
      (hc : Computes I D.fn) (hd : D.deg D.out ≤ 2) (x : Fin (N + N) → Bool),
      D.fn x = true ↔
        ∃ b, D.IsItem b ∧ D.ctx b x = true ∧ ∀ r, D.IsFactor b r → D.val x r = true)
    (h16 : ∀ {N : ℕ} (I : Fin N → Fin N → Prop) (D : Dag N) (hwf : D.WF)
      (hc : Computes I D.fn) (hd : D.deg D.out ≤ 2),
      ∃ (F : Dag N) (W : Finset (Fin N)) (R : Fin N → ℕ), Dag.SoundPartialForm I F W R ∧
        D.markerEdges I ⊆ F.countedEdges W R ∧
        (F.rootCone W R).card ≤ D.M.card + D.X.card + 4 * D.T.card) :
    ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : PEqualNP.CircuitLowerBounds.Circuit),
    (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
    PEqualNP.MetaComplexity.Monotone2 C →
    PEqualNP.CircuitLowerBounds.HasLineDegree (N + N) (Finset.Ico N (N + N)) C 2 →
    (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
    (Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)).card ≤ 48 * C.size + 2 * N :=
  assembly_core (fun I hI D W R hs => card14_of h10e0 h12 h13 I hI D W R hs) h16
    (fun I D hwf hc hd hcl => cv_cover_of_identity (fun I D => h15 I D) I D hwf hc hd hcl)
end Deg2
theorem l649 : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.CircuitLowerBounds.HasLineDegree (N + N) (Finset.Ico N (N + N)) C 2 → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → (Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)).card ≤ 48 * C.size + 2 * N :=
  Deg2.assembly_of Deg2.card10_e0 Deg2.card12_alpha Deg2.card13_beta Deg2.card15_identity
    Deg2.card15c_contexts Deg2.card16_form Deg2.card17_cover

theorem card14_form_count {N : ℕ} (I : Fin N → Fin N → Prop) (hI : Deg2.NoRect I) (D : Deg2.Dag N)
    (W : Finset (Fin N)) (R : Fin N → ℕ) (hs : Deg2.Dag.SoundPartialForm I D W R) :
    (D.countedEdges W R).card ≤ 12 * (D.rootCone W R).card + 2 * W.card :=
  Deg2.card14_of Deg2.card10_e0 Deg2.card12_alpha Deg2.card13_beta I hI D W R hs

theorem card18_assembly : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.CircuitLowerBounds.HasLineDegree (N + N) (Finset.Ico N (N + N)) C 2 → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → (Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)).card ≤ 48 * C.size + 2 * N :=
  l649

theorem shortPivots {N : ℕ} {I : Fin N → Fin N → Prop}
    (hc : ∀ p q a b, p ≠ q → a ≠ b → ¬ (I p a ∧ I p b ∧ I q a ∧ I q b))
    (W : Finset (Fin N)) :
    ∃ V ⊆ W, V.card ≤ 3 ∧ ∀ p, (∃ u ∈ V, ¬ I p u) ↔ (∃ u ∈ W, ¬ I p u) := by
  classical
  by_cases h : 1 < W.card
  · obtain ⟨u,hu,v,hv,huv⟩ := Finset.one_lt_card.mp h
    by_cases hall : ∀ p, I p u → I p v → ∀ w ∈ W, I p w
    · refine ⟨{u,v},Finset.insert_subset hu (Finset.singleton_subset_iff.mpr hv),?_,?_⟩
      · have := Finset.card_insert_le u ({v} : Finset (Fin N))
        simpa using this.trans (by simp)
      · intro p
        constructor
        · rintro ⟨a,ha,hn⟩
          simp only [Finset.mem_insert, Finset.mem_singleton] at ha
          exact ⟨a,ha.elim (fun e => e ▸ hu) (fun e => e ▸ hv),hn⟩
        · rintro ⟨w,hw,hn⟩
          by_contra! he
          exact hn (hall p (he u (by simp)) (he v (by simp)) w hw)
    · push Not at hall
      obtain ⟨p,hpu,hpv,w,hw,hpw⟩ := hall
      have hh : ({u,v,w} : Finset (Fin N)) ⊆ W :=
        Finset.insert_subset hu (Finset.insert_subset hv (Finset.singleton_subset_iff.mpr hw))
      refine ⟨{u,v,w},hh,?_,?_⟩
      · have h₁ := Finset.card_insert_le u ({v,w} : Finset (Fin N))
        have h₂ := Finset.card_insert_le v ({w} : Finset (Fin N))
        simp only [Finset.card_singleton] at h₂
        omega
      · intro q
        have has : ∃ a ∈ ({u,v,w} : Finset (Fin N)), ¬ I q a := by
          by_contra! ht
          by_cases e : p = q
          · subst q
            exact hpw (ht w (by simp))
          · exact hc p q u v e huv ⟨hpu,hpv,ht u (by simp),ht v (by simp)⟩
        refine ⟨?_,fun _ => has⟩
        rintro ⟨a,ha,hn⟩
        exact ⟨a,hh ha,hn⟩
  · exact ⟨W,Finset.Subset.rfl,by omega,fun _ => Iff.rfl⟩

def SinglePivotBound : Prop :=
  ∀ (N Jn : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (Ckt : PEqualNP.CircuitLowerBounds.Circuit) (fg : Fin Jn → ℕ) (lp : Fin Jn → Fin N),
    (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
    PEqualNP.MetaComplexity.Monotone2 Ckt →
    (∀ jd : Fin Jn, (Ckt.lineDegrees (N + N) (Finset.Ico N (N + N))).getD (fg jd) 0 ≤ 2) →
    (∀ (jb : Fin Jn) (zz : Fin (N + N) → Bool),
      (∀ pz : Fin N, I pz (lp jb) → zz (Fin.castAdd N pz) = false) →
      (Ckt.wires (List.ofFn zz)).getD (fg jb) false = true →
      ∃ (pa lb : Fin N), I pa lb ∧ zz (Fin.castAdd N pa) = true ∧ zz (Fin.natAdd N lb) = true) →
    (Finset.univ.filter (fun e2 : Fin N × Fin N => I e2.1 e2.2 ∧ ∃ jc : Fin Jn,
      ¬ I e2.1 (lp jc) ∧
      (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true
        else if vq = Fin.natAdd N e2.2 then true else false))).getD (fg jc) false = true)).card ≤
      64 * (Ckt.size + Jn) + 8 * N

theorem of_single_pivot (hS : SinglePivotBound) : ∀ (N Jn : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (Ckt : PEqualNP.CircuitLowerBounds.Circuit) (fg : Fin Jn → ℕ) (Wl : Fin Jn → Finset (Fin N)), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 Ckt → (∀ jd : Fin Jn, (Ckt.lineDegrees (N + N) (Finset.Ico N (N + N))).getD (fg jd) 0 ≤ 2) → (∀ (jb : Fin Jn) (zz : Fin (N + N) → Bool), (∃ uz ∈ Wl jb, ∀ pz : Fin N, I pz uz → zz (Fin.castAdd N pz) = false) → (Ckt.wires (List.ofFn zz)).getD (fg jb) false = true → ∃ (pa lb : Fin N), I pa lb ∧ zz (Fin.castAdd N pa) = true ∧ zz (Fin.natAdd N lb) = true) → (Finset.univ.filter (fun e2 : Fin N × Fin N => I e2.1 e2.2 ∧ ∃ jc : Fin Jn, (∃ uc ∈ Wl jc, ¬ I e2.1 uc) ∧ (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fg jc) false = true)).card ≤ 192 * (Ckt.size + Jn) + 8 * N := by
  intro N Jn I _ Ckt fg Wl hI hM hdeg hsnd
  classical
  choose V hVsub hVcard hVeq using fun j => shortPivots hI (Wl j)
  let S : Finset ((_ : Fin Jn) × Fin N) := Finset.univ.sigma V
  let e : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
  have hSc : Fintype.card S ≤ 3 * Jn := by
    rw [Fintype.card_coe, Finset.card_sigma]
    calc ∑ j, (V j).card ≤ ∑ _j : Fin Jn, 3 := Finset.sum_le_sum fun j _ => hVcard j
      _ = 3 * Jn := by simp [mul_comm]
  have key := hS N (Fintype.card S) I Ckt (fun d => fg (e d).1.1) (fun d => (e d).1.2) hI hM
    (fun d => hdeg _)
    (fun d zz hz hw => by
      have hm := (e d).2
      simp only [S, Finset.mem_sigma, Finset.mem_univ, true_and] at hm
      exact hsnd _ zz ⟨_, hVsub _ hm, hz⟩ hw)
  refine le_trans (Finset.card_le_card ?_) (key.trans (by omega))
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  obtain ⟨hxI, j, hj, hw⟩ := hx
  obtain ⟨u, hu, hpu⟩ := (hVeq j x.1).mpr hj
  have hmem : (⟨j, u⟩ : (_ : Fin Jn) × Fin N) ∈ S := by simp [S, hu]
  refine ⟨hxI, e.symm ⟨_, hmem⟩, ?_, ?_⟩
  · simpa using hpu
  · simpa using hw
end PEqualNP.Outside.L_meta_1321
namespace PEqualNP.Outside.L_meta_1321
open PEqualNP PEqualNP.MetaComplexity
namespace Deg1
open Deg2 Deg2.Api Deg2.Bridge
variable {N : ℕ}
def allG (D : Dag N) : Finset ℕ := Finset.Ico (N + N) (N + N + D.size)
open Classical in
noncomputable def XA (D : Dag N) : Finset ℕ := (allG D).filter (fun i => D.deg i = 0)
open Classical in
noncomputable def OrA (D : Dag N) : Finset ℕ := (allG D).filter (fun i => D.deg i = 1 ∧ D.IsOr i)
open Classical in
noncomputable def AndA (D : Dag N) : Finset ℕ := (allG D).filter (fun i => D.deg i = 1 ∧ D.IsAnd i)
open Classical in
noncomputable def pinnedA (I : Fin N → Fin N → Prop) (D : Dag N) : Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun e => ∃ v ∈ OrA D, Dag.PinnedTo I D v e.1 ∧ e.2 ∈ D.Vstar v)
open Classical in
noncomputable def servedA (I : Fin N → Fin N → Prop) (D : Dag N) : Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun e => ∃ g ∈ AndA D, ∃ f v, D.LabAnd g f v ∧ D.Vstar v = {e.2} ∧
    e.1 ∈ D.alive f ∧ I e.1 e.2 ∧ (D.alive f ∩ ptsOn I e.2).card ≤ 2)
theorem mem_allG {D : Dag N} {v : ℕ} {g : G} (hg : D.gateAt v = some g) : v ∈ allG D := by
  have := cv_gate_lt D hg
  unfold allG
  rw [Finset.mem_Ico]
  exact this
theorem pinnedA_card (I : Fin N → Fin N → Prop) (hI : NoRect I) (D : Dag N) :
    (pinnedA I D).card ≤ 2 * (OrA D).card := by
  classical
  let T : ℕ → ℕ → Finset (Fin N × Fin N) := fun o c =>
    Finset.univ.filter (fun e => Dag.PinnedTo I D o e.1 ∧ D.Vstar c = {e.2})
  have hT : ∀ o c, (T o c).card ≤ 1 := by
    intro o c
    rw [Finset.card_le_one]
    intro e he e' he'
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at he he'
    have h1 := circ_pinned_unique I hI D he.1 he'.1
    have h2 : e.2 = e'.2 := by
      have := he.2.symm.trans he'.2
      exact Finset.singleton_inj.1 this
    exact Prod.ext h1 h2
  have hsub : pinnedA I D ⊆ (OrA D).biUnion (fun o => (circKids D o).biUnion (fun c => T o c)) := by
    intro e he
    unfold pinnedA at he
    rw [Finset.mem_filter] at he
    obtain ⟨-, v, -, hpin, hu⟩ := he
    have hvr : D.VReach v e.2 := by
      unfold Dag.Vstar at hu; exact (Finset.mem_filter.1 hu).2
    obtain ⟨o, c, -, ho, hod, ho2, hos, hk, hc⟩ := circ_pin_charge D hvr hpin.2.2.1
    simp only [Finset.mem_biUnion]
    obtain ⟨a, b, hg⟩ := ho
    refine ⟨o, Finset.mem_filter.2 ⟨mem_allG hg, hod, ⟨a, b, hg⟩⟩, c, circKids_mem hk, ?_⟩
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨⟨⟨a, b, hg⟩, hod, ho2, hos.trans hpin.2.2.2⟩, hc⟩
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans (Finset.card_biUnion_le_card_mul _ _ 2 ?_) (by rw [mul_comm])
  intro o _
  refine le_trans (Finset.card_biUnion_le_card_mul _ _ 1 (fun c _ => hT o c)) ?_
  have := circKids_card D o
  omega
theorem servedA_card (I : Fin N → Fin N → Prop) (D : Dag N) :
    (servedA I D).card ≤ 2 * (AndA D).card := by
  classical
  let T : ℕ → Finset (Fin N × Fin N) := fun g => Finset.univ.filter (fun e => ∃ f v,
    D.LabAnd g f v ∧ D.Vstar v = {e.2} ∧ e.1 ∈ D.alive f ∧ I e.1 e.2 ∧
      (D.alive f ∩ ptsOn I e.2).card ≤ 2)
  have hsub : servedA I D ⊆ (AndA D).biUnion T := by
    intro e he
    unfold servedA at he
    rw [Finset.mem_filter] at he
    obtain ⟨-, g, hg, f, v, h1, h2, h3, h4, h5⟩ := he
    rw [Finset.mem_biUnion]
    exact ⟨g, hg, Finset.mem_filter.2 ⟨Finset.mem_univ _, f, v, h1, h2, h3, h4, h5⟩⟩
  have hT : ∀ g ∈ AndA D, (T g).card ≤ 2 := by
    intro g _
    by_cases hne : (T g).Nonempty
    · obtain ⟨e0, he0⟩ := hne
      obtain ⟨-, f0, v0, h1, h2, -, -, h5⟩ := Finset.mem_filter.1 he0
      have hsub' : T g ⊆ (D.alive f0 ∩ ptsOn I e0.2).image (fun p => (p, e0.2)) := by
        intro e he
        obtain ⟨-, f, v, k1, k2, k3, k4, -⟩ := Finset.mem_filter.1 he
        obtain ⟨rfl, rfl⟩ := labAnd_unique k1 h1
        have hw : e.2 = e0.2 := by
          rw [h2] at k2
          exact (Finset.singleton_inj.1 k2).symm
        rw [Finset.mem_image]
        refine ⟨e.1, Finset.mem_inter.2 ⟨k3, ?_⟩, ?_⟩
        · unfold ptsOn
          rw [Finset.mem_filter, ← hw]
          exact ⟨Finset.mem_univ _, k4⟩
        · ext <;> simp [hw]
      exact le_trans (Finset.card_le_card hsub') (le_trans Finset.card_image_le h5)
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne]; simp
  calc (servedA I D).card ≤ ((AndA D).biUnion T).card := Finset.card_le_card hsub
    _ ≤ ∑ g ∈ AndA D, (T g).card := Finset.card_biUnion_le
    _ ≤ ∑ _g ∈ AndA D, 2 := Finset.sum_le_sum hT
    _ = 2 * (AndA D).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
theorem classes_card (D : Dag N) :
    8 * (XA D).card + 2 * (OrA D).card + 2 * (AndA D).card ≤ 8 * D.size := by
  classical
  have hall : (allG D).card = D.size := by unfold allG; simp
  let Y := (allG D).filter (fun i => ¬ D.deg i = 0)
  have h1 : (XA D).card + Y.card = (allG D).card := by
    unfold XA; exact Finset.card_filter_add_card_filter_not _
  have h2 : (Y.filter D.IsOr).card + (Y.filter (fun i => ¬ D.IsOr i)).card = Y.card :=
    Finset.card_filter_add_card_filter_not _
  have h3 : OrA D ⊆ Y.filter D.IsOr := by
    intro i hi
    unfold OrA at hi
    simp only [Y, Finset.mem_filter] at hi ⊢
    exact ⟨⟨hi.1, by omega⟩, hi.2.2⟩
  have h4 : AndA D ⊆ Y.filter (fun i => ¬ D.IsOr i) := by
    intro i hi
    unfold AndA at hi
    simp only [Y, Finset.mem_filter] at hi ⊢
    refine ⟨⟨hi.1, by omega⟩, ?_⟩
    obtain ⟨a, b, hab⟩ := hi.2.2
    rintro ⟨c, d, hcd⟩
    rw [hab] at hcd
    cases hcd
  have := Finset.card_le_card h3
  have := Finset.card_le_card h4
  omega
theorem cover1 (I : Fin N → Fin N → Prop) (D : Dag N) (hwf : D.WF)
    (hcl : D.Cleaned I (allG D)) (r : ℕ) (p w : Fin N) (hpw : I p w)
    (hr1 : D.deg r = 1) (hh : IsHonest I (fun x => D.val x r) p)
    (hrw : D.val (ep p w) r = true) (hline : D.val (inp ∅ {w}) r = false) :
    (p, w) ∈ pinnedA I D ∪ servedA I D ∪ D.fSet I (allG D) 2 := by
  classical
  obtain ⟨π, hπ, hπv, hlab, hpen⟩ := card06_honest_path I D r p w hr1 hh hrw
  have hdeg : ∀ v ∈ π, D.deg v = 1 := fun v hv => (hπv v hv).1
  have hlen : 0 < π.length := by
    cases π with
    | nil => simp [Dag.IsPath] at hπ
    | cons _ _ => simp
  have hhead : π.getD 0 0 = r := by
    obtain ⟨hh0, -, -⟩ := hπ
    cases π with
    | nil => simp at hh0
    | cons c _ => simpa using hh0
  simp only [Finset.mem_union]
  let P : ℕ → Prop := fun k => k + 1 < π.length ∧ ∃ f, D.LabAnd (π.getD k 0) f (π.getD (k + 1) 0)
  by_cases hex : ∃ k, P k
  · obtain ⟨k0, hk0⟩ := hex
    let K := Nat.findGreatest P π.length
    have hPK : P K := Nat.findGreatest_spec (P := P) (by have := hk0.1; omega) hk0
    have hmax : ∀ k, K < k → ¬ P k := by
      intro k hk hPk
      exact Nat.findGreatest_is_greatest hk (by have := hPk.1; omega) hPk
    obtain ⟨hK, f, hfl⟩ := hPK
    set e := π.getD K 0 with he
    set v := π.getD (K + 1) 0 with hv
    have hvr : D.VReach v w := by
      refine cv_vreach_suffix D hwf hπ hdeg (π.length - (K + 1) - 1) (K + 1) (by omega) ?_
      intro k f' hk hk' hl
      exact hmax k (by omega) ⟨hk', f', hl⟩
    have hvmem : v ∈ π := circ_getD_mem hK
    rcases cv_card_split (cv_vstar_mem hvr) with h2 | h1
    · left; left
      have hor := cv_isOr_of_card D hvr h2
      obtain ⟨a, b, hg⟩ := hor
      unfold pinnedA
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, v,
        Finset.mem_filter.2 ⟨mem_allG hg, hdeg v hvmem, ⟨a, b, hg⟩⟩,
        ⟨⟨a, b, hg⟩, hdeg v hvmem, h2, hpen v hvmem⟩, cv_vstar_mem hvr⟩
    · obtain ⟨hgate, hf0, -⟩ := hfl
      have hemem : e ∈ π := circ_getD_mem (by omega)
      have hgE : ∃ g, D.gateAt e = some g := by
        rcases hgate with h | h
        · exact ⟨_, h⟩
        · exact ⟨_, h⟩
      obtain ⟨gE, hgE⟩ := hgE
      have hElt := cv_gate_lt D hgE
      have hEall : e ∈ allG D := mem_allG hgE
      have hAndA : e ∈ AndA D := by
        unfold AndA
        refine Finset.mem_filter.2 ⟨hEall, hdeg e hemem, ?_⟩
        rcases hgate with h | h
        · exact ⟨_, _, h⟩
        · exact ⟨_, _, h⟩
      have hdead := hcl e hEall f v ⟨hgate, hf0, hdeg v hvmem⟩
      have halive : p ∈ D.alive f := by
        unfold Dag.alive
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hlab K f hK ⟨hgate, hf0, hdeg v hvmem⟩⟩
      by_cases hle : (D.alive f ∩ ptsOn I w).card ≤ 2
      · left; right
        unfold servedA
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, e, hAndA, f, v,
          ⟨hgate, hf0, hdeg v hvmem⟩, h1, halive, hpw, hle⟩
      · right
        have hfk : D.Kid e f := by
          rcases hgate with h | h
          · exact circ_kid_of h (by simp [G.kids]) (hwf e _ h f (by simp [G.kids]))
          · exact circ_kid_of h (by simp [G.kids]) (hwf e _ h f (by simp [G.kids]))
        have hfgate : N + N ≤ f := by
          by_contra hlt
          have h1' := circ_alive_input D (i := f) (by omega)
          have := Finset.card_le_card (Finset.inter_subset_left (s₁ := D.alive f)
            (s₂ := ptsOn I w))
          omega
        have hfall : f ∈ allG D := by
          unfold allG
          rw [Finset.mem_Ico]
          exact ⟨hfgate, by have := circ_kid_lt hfk; omega⟩
        unfold Dag.fSet
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hpw, f, hfall, hf0, hdead, halive,
          by show 2 + 1 ≤ (D.alive f ∩ ptsOn I w).card; omega⟩
  · exfalso
    have hrv : D.VReach r w := by
      have := cv_vreach_suffix D hwf hπ hdeg (π.length - 1) 0 (by omega)
        (fun k f' _ hk' hl => hex ⟨k, hk', f', hl⟩)
      rwa [hhead] at this
    have hx : (inp ∅ {w} : Fin (N + N) → Bool) (Fin.natAdd N w) = true := by
      unfold inp; rw [Fin.addCases_right]; simp
    have := circ_vreach_val D hrv hx
    rw [hline] at this
    exact absurd this (by decide)
theorem inp_le_test (I : Fin N → Fin N → Prop) {P L S : Finset (Fin N)}
    (hP : ∀ q ∈ P, ∀ l ∈ S, ¬ I q l) (hL : L ⊆ S) : inp P L ≤ testInput I S := by
  classical
  intro k
  refine Fin.addCases (fun q => ?_) (fun l => ?_) k
  · unfold testInput inp
    rw [Fin.addCases_left, Fin.addCases_left]
    by_cases hq : q ∈ P
    · have : q ∈ Finset.univ.filter (fun p => ∀ l ∈ S, ¬ I p l) :=
        Finset.mem_filter.2 ⟨Finset.mem_univ _, hP q hq⟩
      simp [hq, this]
    · simp [hq]
  · unfold testInput inp
    rw [Fin.addCases_right, Fin.addCases_right]
    by_cases hl : l ∈ L
    · simp [hl, hL hl]
    · simp [hl]
theorem bfalse_of_le {a b : Bool} (h : a ≤ b) (hb : b = false) : a = false := by
  subst hb; revert h; cases a <;> decide
theorem deg1_bound : ∀ (N Jn : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (Ckt : PEqualNP.CircuitLowerBounds.Circuit) (fg : Fin Jn → ℕ) (Wl : Fin Jn → Finset (Fin N)), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 Ckt → (∀ jd : Fin Jn, (Ckt.lineDegrees (N + N) (Finset.Ico N (N + N))).getD (fg jd) 0 ≤ 1) → (∀ (jb : Fin Jn) (zz : Fin (N + N) → Bool), (∃ uz ∈ Wl jb, ∀ pz : Fin N, I pz uz → zz (Fin.castAdd N pz) = false) → (Ckt.wires (List.ofFn zz)).getD (fg jb) false = true → ∃ (pa lb : Fin N), I pa lb ∧ zz (Fin.castAdd N pa) = true ∧ zz (Fin.natAdd N lb) = true) → (Finset.univ.filter (fun e2 : Fin N × Fin N => I e2.1 e2.2 ∧ ∃ jc : Fin Jn, (∃ uc ∈ Wl jc, ¬ I e2.1 uc) ∧ (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fg jc) false = true)).card ≤ 8 * Ckt.size := by
  intro N Jn I _ Ckt fg Wl hI hM hdeg hsnd
  classical
  have hwf0 : (ofCircuit N Ckt).WF := card03b_wf Ckt
  set D := clean I (ofCircuit N Ckt) with hD
  have hwf : D.WF := clean_wf I _ hwf0
  have hsz : D.size = Ckt.size := by
    rw [← card03a_size (N := N) Ckt]
    simp [hD, clean, Dag.size]
  have hfalse : ∀ (j : Fin Jn) (S : Finset (Fin N)) (u : Fin N), S.card ≤ 2 → u ∈ Wl j → u ∈ S →
      D.val (testInput I S) (fg j) = false := by
    intro j S u hS hu huS
    rw [hD, clean_test I _ hwf0 hS, card03c_val Ckt hM]
    by_contra hne
    obtain ⟨pa, lb, hab, h1, h2⟩ := hsnd j (testInput I S) ⟨u, hu, fun pz hpz => by
      unfold testInput inp
      rw [Fin.addCases_left]
      simp only [decide_eq_false_iff_not, Finset.mem_filter, Finset.mem_univ, true_and, not_forall]
      exact ⟨u, huS, fun h => h hpz⟩⟩ (by simpa using hne)
    exact testInput_noEdge I S ⟨pa, lb, hab, h1, h2⟩
  have hcard2 : ∀ a b : Fin N, ({a, b} : Finset (Fin N)).card ≤ 2 := fun a b => by
    have := Finset.card_insert_le a ({b} : Finset (Fin N))
    simpa using this
  have hsub : Finset.univ.filter (fun e2 : Fin N × Fin N => I e2.1 e2.2 ∧ ∃ jc : Fin Jn, (∃ uc ∈ Wl jc, ¬ I e2.1 uc) ∧ (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fg jc) false = true) ⊆
      pinnedA I D ∪ servedA I D ∪ D.fSet I (allG D) 2 := by
    rintro ⟨p, w⟩ hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨hpw, j, ⟨u, hu, hpu⟩, hacc⟩ := hx
    have hfun : (fun vq : Fin (N + N) => if vq = Fin.castAdd N p then true
        else if vq = Fin.natAdd N w then true else false) = ep p w := by
      rw [cv_ep_eq]
      funext k
      by_cases h1 : k = Fin.castAdd N p <;> by_cases h2 : k = Fin.natAdd N w <;> simp [h1, h2]
    rw [hfun, ← card03c_val Ckt hM] at hacc
    have hrw : D.val (ep p w) (fg j) = true := by
      have := clean_mono I (ofCircuit N Ckt) (ep p w) (fg j)
      rw [hacc] at this
      revert this; rw [← hD]; cases D.val (ep p w) (fg j) <;> decide
    have hpt : D.val (pt p) (fg j) = false := by
      refine bfalse_of_le (api_val_mono D (fg j) (inp_le_test I (S := {u}) ?_ (by simp)))
        (hfalse j {u} u (by simp) hu (by simp))
      intro q hq l hl
      simp only [Finset.mem_singleton] at hq hl
      subst hq; subst hl; exact hpu
    have hh : IsHonest I (fun x => D.val x (fg j)) p := by
      refine ⟨hpt, fun u' hu' => ?_⟩
      by_contra hn
      have h0 := hfalse j {u, u'} u (hcard2 u u') hu (by simp)
      have hle := api_val_mono D (fg j) (inp_le_test I (P := {p}) (L := {u'}) (S := {u, u'})
        (by
          intro q hq l hl
          simp only [Finset.mem_singleton, Finset.mem_insert] at hq hl
          subst hq
          rcases hl with rfl | rfl
          · exact hpu
          · exact hn)
        (by simp))
      have := bfalse_of_le hle h0
      have hu2 : D.val (ep p u') (fg j) = true := hu'
      unfold ep at hu2
      rw [hu2] at this
      exact absurd this (by decide)
    have hline : D.val (inp ∅ {w}) (fg j) = false :=
      bfalse_of_le (api_val_mono D (fg j) (inp_le_test I (by simp) (by simp)))
        (hfalse j {u, w} u (hcard2 u w) hu (by simp))
    have hr1 : D.deg (fg j) = 1 := by
      have h1 : D.deg (fg j) ≤ 1 := by
        rw [hD, clean_deg I _ hwf0]
        exact le_trans (card03d_deg Ckt hM (fg j)) (hdeg j)
      by_contra hne
      have h0 : D.deg (fg j) = 0 := by omega
      have := api_val_xonly D h0 (x := ep p w) (y := pt p) (fun q => circ_ep_pts p w q)
      rw [hrw, hpt] at this
      exact absurd this (by decide)
    exact cover1 I D hwf (by rw [hD]; exact clean_cleaned I _ hwf0 _) (fg j) p w hpw hr1 hh hrw hline
  refine le_trans (Finset.card_le_card hsub) ?_
  have hU1 := Finset.card_union_le (pinnedA I D ∪ servedA I D) (D.fSet I (allG D) 2)
  have hU2 := Finset.card_union_le (pinnedA I D) (servedA I D)
  have hP := pinnedA_card I hI D
  have hS := servedA_card I D
  have hF := card07_two_line I hI D (allG D) (by
    intro i hi c hk hc
    unfold allG at hi ⊢
    rw [Finset.mem_Ico] at hi ⊢
    exact ⟨hc, by have := circ_kid_lt hk; omega⟩)
  have hC := classes_card D
  have hX : ((allG D).filter (fun f => D.deg f = 0)) = XA D := rfl
  rw [hX] at hF
  omega
end Deg1
end PEqualNP.Outside.L_meta_1321
namespace PEqualNP.Outside.L_meta_1321
open PEqualNP PEqualNP.MetaComplexity
namespace Clean3
open Deg2 Deg2.Api
variable {N : ℕ}
open Classical in
noncomputable def cleanGd (I : Fin N → Fin N → Prop) (D : Dag N) (d : ℕ) : G → G
  | .and a b =>
      if D.deg a = 0 ∧ 1 ≤ D.deg b ∧ D.deadSets I d a = ∅ then .or b b
      else if D.deg b = 0 ∧ 1 ≤ D.deg a ∧ D.deadSets I d b = ∅ then .or a a
      else .and a b
  | .or a b => .or a b
  | .cst v => .cst v
noncomputable def cleanD (I : Fin N → Fin N → Prop) (D : Dag N) (d : ℕ) : Dag N :=
  ⟨D.gates.map (cleanGd I D d), D.out⟩
def CleanedD (I : Fin N → Fin N → Prop) (D : Dag N) (d : ℕ) (Gs : Finset ℕ) : Prop :=
  ∀ e ∈ Gs, ∀ f v, (D.gateAt e = some (.and f v) ∨ D.gateAt e = some (.and v f)) →
    D.deg f = 0 → 1 ≤ D.deg v → D.deadSets I d f ≠ ∅
def PivotSound (I : Fin N → Fin N → Prop) (D : Dag N) (r : ℕ) (u : Fin N) : Prop :=
  ∀ x : Fin (N + N) → Bool, (∀ p, I p u → x (Fin.castAdd N p) = false) → D.val x r = true →
    ∃ p l, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true
theorem cleanGd_and (I : Fin N → Fin N → Prop) (D : Dag N) (d a b : ℕ) :
    ((D.deg a = 0 ∧ 1 ≤ D.deg b ∧ D.deadSets I d a = ∅) ∧ cleanGd I D d (.and a b) = .or b b) ∨
    (¬ (D.deg a = 0 ∧ 1 ≤ D.deg b ∧ D.deadSets I d a = ∅) ∧
      (D.deg b = 0 ∧ 1 ≤ D.deg a ∧ D.deadSets I d b = ∅) ∧ cleanGd I D d (.and a b) = .or a a) ∨
    (¬ (D.deg a = 0 ∧ 1 ≤ D.deg b ∧ D.deadSets I d a = ∅) ∧
      ¬ (D.deg b = 0 ∧ 1 ≤ D.deg a ∧ D.deadSets I d b = ∅) ∧ cleanGd I D d (.and a b) = .and a b) := by
  simp only [cleanGd]
  split_ifs with h1 h2
  · exact Or.inl ⟨h1, rfl⟩
  · exact Or.inr (Or.inl ⟨h1, h2, rfl⟩)
  · exact Or.inr (Or.inr ⟨h1, h2, rfl⟩)
theorem cleanD_get (I : Fin N → Fin N → Prop) (D : Dag N) (d k : ℕ) :
    (cleanD I D d).gates[k]? = (D.gates[k]?).map (cleanGd I D d) := by
  simp [cleanD]
theorem cleanD_gateAt (I : Fin N → Fin N → Prop) (D : Dag N) (d i : ℕ) :
    (cleanD I D d).gateAt i = (D.gateAt i).map (cleanGd I D d) := by
  unfold Dag.gateAt
  split_ifs
  · exact cleanD_get I D d _
  · rfl
theorem cleanD_size (I : Fin N → Fin N → Prop) (D : Dag N) (d : ℕ) :
    (cleanD I D d).size = D.size := by
  simp [cleanD, Dag.size]
theorem cleanGd_kids (I : Fin N → Fin N → Prop) (D : Dag N) (d : ℕ) (g : G) :
    ∀ c ∈ (cleanGd I D d g).kids, c ∈ g.kids := by
  intro c hc
  cases g with
  | and a b =>
    simp only [cleanGd] at hc
    split_ifs at hc <;> simp_all [G.kids]
  | or a b => exact hc
  | cst v => exact hc
theorem cleanD_wf (I : Fin N → Fin N → Prop) (D : Dag N) (d : ℕ) (hwf : D.WF) :
    (cleanD I D d).WF := by
  intro i g hg c hc
  rw [cleanD_gateAt] at hg
  obtain ⟨g0, hg0, rfl⟩ := Option.map_eq_some_iff.1 hg
  exact hwf i g0 hg0 c (cleanGd_kids I D d g0 c hc)
theorem cleanD_deg (I : Fin N → Fin N → Prop) (D : Dag N) (d : ℕ) (hwf : D.WF) (i : ℕ) :
    (cleanD I D d).deg i = D.deg i := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    have hd : ∀ a, (if _ : a < i then (cleanD I D d).deg a else 0) =
        (if _ : a < i then D.deg a else 0) := by
      intro a
      split_ifs with ha
      · exact ih a ha
      · rfl
    conv_lhs => rw [Dag.deg]
    conv_rhs => rw [Dag.deg]
    by_cases h0 : i < N + N
    · rw [if_pos h0, if_pos h0]
    · rw [if_neg h0, if_neg h0, cleanD_get]
      cases hg : D.gates[i - (N + N)]? with
      | none => rfl
      | some g =>
        cases g with
        | and a b =>
          obtain ⟨ha, hb⟩ := Bridge.gate_lt hwf h0 hg
          rcases cleanGd_and I D d a b with ⟨h1, hc⟩ | ⟨-, h2, hc⟩ | ⟨-, -, hc⟩ <;>
            simp only [Option.map_some, hc]
          · rw [hd b, dif_pos ha, dif_pos hb, max_self]
            omega
          · rw [hd a, dif_pos ha, dif_pos hb, max_self]
            omega
          · rw [hd a, hd b]
        | or a b => dsimp only [Option.map_some, cleanGd]; rw [hd a, hd b]
        | cst v => rfl
theorem cleanD_mono (I : Fin N → Fin N → Prop) (D : Dag N) (d : ℕ) (x : Fin (N + N) → Bool) (i : ℕ) :
    D.val x i ≤ (cleanD I D d).val x i := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    have hv : ∀ a, (if _ : a < i then D.val x a else false) ≤
        (if _ : a < i then (cleanD I D d).val x a else false) := by
      intro a
      split_ifs with ha
      · exact ih a ha
      · exact le_rfl
    conv_lhs => rw [Dag.val]
    conv_rhs => rw [Dag.val]
    split_ifs with h0
    · exact le_rfl
    · rw [cleanD_get]
      cases hg : D.gates[i - (N + N)]? with
      | none => exact le_rfl
      | some g =>
        cases g with
        | and a b =>
          rcases cleanGd_and I D d a b with ⟨-, hc⟩ | ⟨-, -, hc⟩ | ⟨-, -, hc⟩ <;>
            simp only [Option.map_some, hc]
          · exact Bridge.band_le_or_right _ _ _ _ (hv a) (hv b)
          · exact Bridge.band_le_or_left _ _ _ _ (hv a) (hv b)
          · exact Api.band_mono _ _ _ _ (hv a) (hv b)
        | or a b => exact Api.bor_mono _ _ _ _ (hv a) (hv b)
        | cst v => exact le_rfl
theorem true_of_noDeadD (I : Fin N → Fin N → Prop) (D : Dag N) {d a : ℕ}
    (h : D.deadSets I d a = ∅) {S : Finset (Fin N)} (hS : S.card ≤ d) :
    D.val (testInput I S) a = true := by
  classical
  by_contra hne
  have hmem : S ∈ D.deadSets I d a := by
    unfold Dag.deadSets
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hS, by simpa using hne⟩
  rw [h] at hmem
  exact Finset.notMem_empty _ hmem
theorem cleanD_test (I : Fin N → Fin N → Prop) (D : Dag N) (d : ℕ) (hwf : D.WF)
    {S : Finset (Fin N)} (hS : S.card ≤ d) (i : ℕ) :
    (cleanD I D d).val (testInput I S) i = D.val (testInput I S) i := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    have hv : ∀ a, (if _ : a < i then (cleanD I D d).val (testInput I S) a else false) =
        (if _ : a < i then D.val (testInput I S) a else false) := by
      intro a
      split_ifs with ha
      · exact ih a ha
      · rfl
    conv_lhs => rw [Dag.val]
    conv_rhs => rw [Dag.val]
    split_ifs with h0
    · rfl
    · rw [cleanD_get]
      cases hg : D.gates[i - (N + N)]? with
      | none => rfl
      | some g =>
        cases g with
        | and a b =>
          obtain ⟨ha, hb⟩ := Bridge.gate_lt hwf h0 hg
          rcases cleanGd_and I D d a b with ⟨h1, hc⟩ | ⟨-, h2, hc⟩ | ⟨-, -, hc⟩ <;>
            simp only [Option.map_some, hc]
          · rw [hv b, dif_pos ha, dif_pos hb, Bool.or_self,
              true_of_noDeadD I D h1.2.2 hS, Bool.true_and]
          · rw [hv a, dif_pos ha, dif_pos hb, Bool.or_self,
              true_of_noDeadD I D h2.2.2 hS, Bool.and_true]
          · rw [hv a, hv b]
        | or a b => dsimp only [Option.map_some, cleanGd]; rw [hv a, hv b]
        | cst v => rfl
theorem cleanD_deadSets (I : Fin N → Fin N → Prop) (D : Dag N) (d : ℕ) (hwf : D.WF) (f : ℕ) :
    (cleanD I D d).deadSets I d f = D.deadSets I d f := by
  classical
  unfold Dag.deadSets
  apply Finset.filter_congr
  intro S _
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [← cleanD_test I D d hwf h1]; exact h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [cleanD_test I D d hwf h1]; exact h2⟩
theorem cleanGd_eq_and {I : Fin N → Fin N → Prop} {D : Dag N} {d : ℕ} {g : G} {f v : ℕ}
    (h : cleanGd I D d g = .and f v) :
    g = .and f v ∧ ¬ (D.deg f = 0 ∧ 1 ≤ D.deg v ∧ D.deadSets I d f = ∅) ∧
      ¬ (D.deg v = 0 ∧ 1 ≤ D.deg f ∧ D.deadSets I d v = ∅) := by
  cases g with
  | and a b =>
    simp only [cleanGd] at h
    split_ifs at h with h1 h2
    simp only [G.and.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, h1, h2⟩
  | or a b => simp [cleanGd] at h
  | cst v => simp [cleanGd] at h
theorem cleanD_cleaned (I : Fin N → Fin N → Prop) (D : Dag N) (d : ℕ) (hwf : D.WF) (Gs : Finset ℕ) :
    CleanedD I (cleanD I D d) d Gs := by
  intro e _ f v hg hf hv
  rw [cleanD_deadSets I D d hwf]
  rw [cleanD_deg I D d hwf] at hf hv
  intro hdead
  rcases hg with hg | hg
  · rw [cleanD_gateAt] at hg
    obtain ⟨g0, -, h0⟩ := Option.map_eq_some_iff.1 hg
    exact (cleanGd_eq_and h0).2.1 ⟨hf, hv, hdead⟩
  · rw [cleanD_gateAt] at hg
    obtain ⟨g0, -, h0⟩ := Option.map_eq_some_iff.1 hg
    exact (cleanGd_eq_and h0).2.2 ⟨hf, hv, hdead⟩
theorem cleaned_of_cleanedD {I : Fin N → Fin N → Prop} {D : Dag N} {Gs : Finset ℕ}
    (h : CleanedD I D 2 Gs) : D.Cleaned I Gs := by
  intro e he f v hl
  obtain ⟨hg, hf, hv⟩ := hl
  exact h e he f v hg hf (by omega)
theorem pivotSound_test {I : Fin N → Fin N → Prop} {D : Dag N} {r : ℕ} {u : Fin N}
    (hs : PivotSound I D r u) {S : Finset (Fin N)} (hu : u ∈ S) :
    D.val (testInput I S) r = false := by
  by_contra hne
  have ht : D.val (testInput I S) r = true := by simpa using hne
  obtain ⟨p, l, hpl, h1, h2⟩ := hs _ (fun p hp => by
    by_contra hx
    have := (Forms.testInput_castAdd I S p).1 (by simpa using hx)
    exact this u hu hp) ht
  exact Bridge.testInput_noEdge I S ⟨p, l, hpl, h1, h2⟩
theorem cleanD_pivotSound (I : Fin N → Fin N → Prop) (D : Dag N) (d : ℕ) (hwf : D.WF)
    {r : ℕ} {u : Fin N} (hdeg : D.deg r + 1 ≤ d) (hs : PivotSound I D r u) :
    PivotSound I (cleanD I D d) r u := by
  classical
  intro x hx hval
  by_contra hno
  push Not at hno
  obtain ⟨S, hSc, hSl, hSv⟩ := Forms.exists_few_lines (cleanD I D d) x r hval
  rw [cleanD_deg I D d hwf] at hSc
  have hcard : (insert u S).card ≤ d := le_trans (Finset.card_insert_le _ _) (by omega)
  have hle : inp (Finset.univ.filter (fun q => x (Fin.castAdd N q) = true)) S ≤
      testInput I (insert u S) := by
    apply Forms.inp_le
    · intro q hq
      rw [Finset.mem_filter] at hq
      rw [Forms.testInput_castAdd]
      intro l hl hql
      rcases Finset.mem_insert.1 hl with rfl | hl
      · rw [hx q hql] at hq; exact absurd hq.2 (by decide)
      · exact hno q l hql hq.2 (hSl l hl)
    · intro l hl
      rw [Forms.testInput_natAdd]
      exact Finset.mem_insert_of_mem hl
  have h1 := Api.api_val_mono (cleanD I D d) r hle
  rw [hSv, cleanD_test I D d hwf hcard, pivotSound_test hs (Finset.mem_insert_self u S)] at h1
  exact absurd h1 (by decide)
theorem t01_clean (I : Fin N → Fin N → Prop) (D : Dag N) (d : ℕ) (hwf : D.WF) :
    ∃ D' : Dag N, D'.WF ∧ D'.size = D.size ∧ D'.out = D.out ∧ (∀ i, D'.deg i = D.deg i) ∧
      (∀ x i, D.val x i ≤ D'.val x i) ∧
      (∀ S : Finset (Fin N), S.card ≤ d → ∀ i, D'.val (testInput I S) i = D.val (testInput I S) i) ∧
      (∀ f, D'.deadSets I d f = D.deadSets I d f) ∧
      (∀ r u, D.deg r + 1 ≤ d → PivotSound I D r u → PivotSound I D' r u) ∧
      (∀ Gs, CleanedD I D' d Gs) :=
  ⟨cleanD I D d, cleanD_wf I D d hwf, cleanD_size I D d, rfl, cleanD_deg I D d hwf,
    cleanD_mono I D d, fun _ hS i => cleanD_test I D d hwf hS i, cleanD_deadSets I D d hwf,
    fun _ _ hd hs => cleanD_pivotSound I D d hwf hd hs, cleanD_cleaned I D d hwf⟩
theorem pivotSound_ofCircuit {I : Fin N → Fin N → Prop} {Jn : ℕ}
    (Ckt : PEqualNP.CircuitLowerBounds.Circuit) (hM : PEqualNP.MetaComplexity.Monotone2 Ckt)
    (fg : Fin Jn → ℕ) (Wl : Fin Jn → Finset (Fin N))
    (hsnd : ∀ (jb : Fin Jn) (zz : Fin (N + N) → Bool), (∃ uz ∈ Wl jb, ∀ pz : Fin N, I pz uz → zz (Fin.castAdd N pz) = false) → (Ckt.wires (List.ofFn zz)).getD (fg jb) false = true → ∃ (pa lb : Fin N), I pa lb ∧ zz (Fin.castAdd N pa) = true ∧ zz (Fin.natAdd N lb) = true)
    (j : Fin Jn) {u : Fin N} (hu : u ∈ Wl j) : PivotSound I (ofCircuit N Ckt) (fg j) u := by
  intro x hx hv
  rw [Bridge.card03c_val Ckt hM] at hv
  exact hsnd j x ⟨u, hu, hx⟩ hv
end Clean3
end PEqualNP.Outside.L_meta_1321
namespace PEqualNP.Outside.L_meta_1321
open PEqualNP PEqualNP.MetaComplexity
namespace Rich5
open Deg2
variable {N : ℕ}
private theorem cover_unique (I : Fin N → Fin N → Prop) (hI : NoRect I)
    (R : Finset (Fin N)) (hR : 5 < R.card) {a b c d q t : Fin N}
    (h : R ⊆ {a,b} ∪ pencil I q) (h' : R ⊆ {c,d} ∪ pencil I t) : q = t := by
  classical
  let L : Finset (Fin N) := {a,b} ∪ {c,d}
  have hp (x y : Fin N) : ({x,y} : Finset (Fin N)).card ≤ 2 := by
    simpa using Finset.card_insert_le x ({y} : Finset (Fin N))
  have hL : L.card ≤ 4 := (Finset.card_union_le _ _).trans (Nat.add_le_add (hp a b) (hp c d))
  have hk : 1 < (R \ L).card := by
    have hl := Finset.le_card_sdiff L R
    omega
  have on (w : Fin N) (hw : w ∈ R \ L) : I q w ∧ I t w := by
    obtain ⟨hr,ho⟩ := Finset.mem_sdiff.mp hw
    have ha : w ∉ ({a,b} : Finset (Fin N)) := fun hx => ho (Finset.mem_union_left _ hx)
    have hc : w ∉ ({c,d} : Finset (Fin N)) := fun hx => ho (Finset.mem_union_right _ hx)
    have hq := (Finset.mem_union.mp (h hr)).resolve_left ha
    have ht := (Finset.mem_union.mp (h' hr)).resolve_left hc
    simpa [pencil] using And.intro hq ht
  obtain ⟨w,hw,v,hv,hne⟩ := Finset.one_lt_card.mp hk
  by_contra hn
  exact hI q t w v hn hne ⟨(on w hw).1,(on v hv).1,(on w hw).2,(on v hv).2⟩
theorem rich_le_five (I : Fin N → Fin N → Prop) (hI : NoRect I) (R : Finset (Fin N))
    (h : ∀ w ∈ R, ∃ q u, ¬ I q w ∧ R ⊆ {w,u} ∪ pencil I q) : R.card ≤ 5 := by
  classical
  by_contra! hn
  obtain ⟨w,hw⟩ := Finset.card_pos.mp (show 0 < R.card by omega)
  obtain ⟨q,u,_,hc⟩ := h w hw
  have hh : R ⊆ {w,u} := by
    intro l hl
    obtain ⟨t,v,ht,hv⟩ := h l hl
    have he := cover_unique I hI R hn hc hv
    subst t
    rcases Finset.mem_union.mp (hc hl) with ha|ha
    · exact ha
    · exact (ht (by simpa [pencil] using ha)).elim
  have hs := Finset.card_le_card hh
  have hi := Finset.card_insert_le w ({u} : Finset (Fin N))
  simp only [Finset.card_singleton] at hi
  omega
theorem edges_le_four (I : Fin N → Fin N → Prop) [DecidableRel I] (hI : NoRect I)
    (w u : Fin N) (hcover : ∀ p, I p w ∨ I p u) : (edges N I).card ≤ 4 * N := by
  classical
  let A : Finset (Fin N) := {w,u}
  let B : Finset (Fin N) := Finset.univ \ A
  let allP : Finset (Fin N) := Finset.univ
  let F : Fin N → Finset (Fin N × Fin N) := fun l => ptsOn I l ×ˢ {l}
  have hthin : ∀ l ∈ B, (F l).card ≤ 2 := by
    intro l hl
    rw [show (F l).card = (ptsOn I l).card by simp [F]]
    have hnot := (Finset.mem_sdiff.mp hl).2
    have hsub : ptsOn I l ⊆ A.biUnion (fun k => ptsOn I k ∩ ptsOn I l) := by
      intro p hp
      rcases hcover p with hw|hu
      · exact Finset.mem_biUnion.mpr ⟨w,by simp [A],Finset.mem_inter.mpr ⟨by simpa [ptsOn] using hw,hp⟩⟩
      · exact Finset.mem_biUnion.mpr ⟨u,by simp [A],Finset.mem_inter.mpr ⟨by simpa [ptsOn] using hu,hp⟩⟩
    have hb := Finset.card_biUnion_le_card_mul A (fun k => ptsOn I k ∩ ptsOn I l) 1 (by
      intro k hk
      rw [Finset.card_le_one]
      intro p hp q hq
      by_contra hne
      have hkl : k ≠ l := fun e => hnot (e ▸ hk)
      simp only [ptsOn, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
      exact hI p q k l hne hkl ⟨hp.1,hp.2,hq.1,hq.2⟩)
    have hc := Finset.card_le_card hsub
    have ha : A.card ≤ 2 := Finset.card_le_two
    omega
  have hsub : edges N I ⊆ (allP ×ˢ A) ∪ B.biUnion F := by
    intro e he
    by_cases h : e.2 ∈ A
    · exact Finset.mem_union_left _ (Finset.mem_product.mpr ⟨Finset.mem_univ _,h⟩)
    · apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨e.2,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,h⟩,Finset.mem_product.mpr ⟨?_,by simp⟩⟩
      simpa [ptsOn, edges] using he
  have ha : A.card ≤ 2 := Finset.card_le_two
  have hp : (allP ×ˢ A).card ≤ N * 2 := by
    rw [Finset.card_product]
    exact Nat.mul_le_mul (by simp [allP]) ha
  have hB : B.card ≤ N := by simpa using Finset.card_le_univ B
  have hf := Finset.card_biUnion_le_card_mul B F 2 hthin
  have hs := Finset.card_union_le (allP ×ˢ A) (B.biUnion F)
  have ht := Finset.card_le_card hsub
  omega
end Rich5
end PEqualNP.Outside.L_meta_1321
namespace PEqualNP.Outside.L_meta_1321
open PEqualNP PEqualNP.MetaComplexity
namespace Rich
open Deg2 Deg2.Api Deg2.Bridge Deg2.Path
variable {N : ℕ}
open Classical in
noncomputable def fSetU (I : Fin N → Fin N → Prop) (D : Dag N) (Gs : Finset ℕ) (d : ℕ) :
    Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun e => I e.1 e.2 ∧ ∃ f ∈ Gs, D.deadSets I d f ≠ ∅ ∧
    e.1 ∈ D.alive f ∧ d + 1 ≤ (D.alive f ∩ ptsOn I e.2).card)
theorem lines_le (I : Fin N → Fin N → Prop) (hI : NoRect I) (D : Dag N) {f d : ℕ}
    {S : Finset (Fin N)} (hS : S.card ≤ d) (h0 : D.val (testInput I S) f = false) :
    (Finset.univ.filter (fun l => d + 1 ≤ (D.alive f ∩ ptsOn I l).card)).card ≤ d := by
  classical
  refine le_trans (Finset.card_le_card (t := S) ?_) hS
  intro l hl
  rw [Finset.mem_filter] at hl
  by_contra hlS
  have hsub : D.alive f ∩ ptsOn I l ⊆ S.biUnion (fun s => ptsOn I s ∩ ptsOn I l) := by
    intro q hq
    rw [Finset.mem_inter] at hq
    obtain ⟨s, hs, hqs⟩ := circ_alive_on I D h0 hq.1
    rw [Finset.mem_biUnion]
    refine ⟨s, hs, Finset.mem_inter.2 ⟨?_, hq.2⟩⟩
    unfold ptsOn; rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hqs⟩
  have hb := Finset.card_biUnion_le_card_mul S (fun s => ptsOn I s ∩ ptsOn I l) 1 (by
    intro s hs
    rw [Finset.card_le_one]
    intro a ha b hb
    by_contra hab
    have hsl : s ≠ l := by rintro rfl; exact hlS hs
    unfold ptsOn at ha hb
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    exact hI a b s l hab hsl ⟨ha.1, ha.2, hb.1, hb.2⟩)
  have := Finset.card_le_card hsub
  omega
theorem charge (I : Fin N → Fin N → Prop) (D : Dag N) (Gs : Finset ℕ)
    (hdown : ∀ i ∈ Gs, ∀ c, D.Kid i c → N + N ≤ c → c ∈ Gs) (p l : Fin N) (d : ℕ)
    (S : Finset (Fin N)) (hS : S.card ≤ d) :
    ∀ f, f ∈ Gs → D.val (pt p) f = true → D.val (testInput I S) f = false →
      d + 1 ≤ (D.alive f ∩ ptsOn I l).card →
      ∃ g ∈ Gs, N + N ≤ g ∧ D.val (testInput I S) g = false ∧
        d + 1 ≤ (D.alive g ∩ ptsOn I l).card ∧
        ∃ c, D.Kid g c ∧ p ∈ D.alive c ∧ (D.alive c ∩ ptsOn I l).card ≤ d := by
  have hpa : ∀ f, D.val (pt p) f = true → p ∈ D.alive f := fun f h => by
    unfold Dag.alive; rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, h⟩
  have hin : ∀ f, f < N + N → d + 1 ≤ (D.alive f ∩ ptsOn I l).card → d = 0 := fun f hi h3 => by
    have := le_trans (Finset.card_le_card (Finset.inter_subset_left (s₁ := D.alive f)
      (s₂ := ptsOn I l))) (circ_alive_input D hi)
    omega
  intro f
  induction f using Nat.strong_induction_on with
  | _ f ih =>
    intro hf h1 h0 h3
    by_cases hi : f < N + N
    · have hd := hin f hi h3
      subst hd
      obtain ⟨s, hs, -⟩ := circ_alive_on I D h0 (hpa f h1)
      rw [Finset.card_eq_zero.1 (Nat.le_zero.1 hS)] at hs
      exact absurd hs (Finset.notMem_empty s)
    · obtain ⟨π, hπ, hv⟩ := card05_path I D f p S h1 h0
      have hne : f ≠ p.val := by have := p.isLt; omega
      obtain ⟨c, hk, hcπ⟩ := circ_path_first hπ hne
      obtain ⟨hc1, hc0⟩ := hv c hcπ
      by_cases hc3 : d + 1 ≤ (D.alive c ∩ ptsOn I l).card
      · by_cases hcg : N + N ≤ c
        · exact ih c (circ_kid_lt hk) (hdown f hf c hk hcg) hc1 hc0 hc3
        · have hd := hin c (by omega) hc3
          subst hd
          obtain ⟨s, hs, -⟩ := circ_alive_on I D h0 (hpa f h1)
          rw [Finset.card_eq_zero.1 (Nat.le_zero.1 hS)] at hs
          exact absurd hs (Finset.notMem_empty s)
      · exact ⟨f, hf, by omega, h0, h3, c, hk, hpa c hc1, by omega⟩
theorem richU_card (I : Fin N → Fin N → Prop) (hI : NoRect I) (D : Dag N) (Gs : Finset ℕ)
    (hdown : ∀ i ∈ Gs, ∀ c, D.Kid i c → N + N ≤ c → c ∈ Gs) (d : ℕ) :
    (fSetU I D Gs d).card ≤ 2 * d * d * (Gs.filter (fun g => N + N ≤ g)).card := by
  classical
  let Lg : ℕ → Finset (Fin N) := fun g => Finset.univ.filter (fun l =>
    d + 1 ≤ (D.alive g ∩ ptsOn I l).card ∧
      ∃ S : Finset (Fin N), S.card ≤ d ∧ D.val (testInput I S) g = false)
  let Tc : Fin N → ℕ → Finset (Fin N × Fin N) := fun l c =>
    if (D.alive c ∩ ptsOn I l).card ≤ d then (D.alive c ∩ ptsOn I l).image (fun q => (q, l))
    else ∅
  have hLg : ∀ g, (Lg g).card ≤ d := by
    intro g
    by_cases hS : ∃ S : Finset (Fin N), S.card ≤ d ∧ D.val (testInput I S) g = false
    · obtain ⟨S, hS2, hS0⟩ := hS
      refine le_trans (Finset.card_le_card ?_) (lines_le I hI D hS2 hS0)
      intro l hl
      simp only [Lg, Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
      exact hl.1
    · have : Lg g = ∅ := by
        ext l
        simp only [Lg, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
          iff_false, not_and]
        intro _ h; exact hS h
      rw [this]; simp
  have hTc : ∀ l c, (Tc l c).card ≤ d := by
    intro l c
    simp only [Tc]
    split_ifs with h
    · exact le_trans Finset.card_image_le h
    · simp
  have hsub : fSetU I D Gs d ⊆ (Gs.filter (fun g => N + N ≤ g)).biUnion
      (fun g => (Lg g).biUnion (fun l => (circKids D g).biUnion (fun c => Tc l c))) := by
    intro e he
    unfold fSetU at he
    rw [Finset.mem_filter] at he
    obtain ⟨-, hIe, f, hf, hdead, hp, h3⟩ := he
    obtain ⟨S, hS⟩ := Finset.nonempty_iff_ne_empty.2 hdead
    unfold Dag.deadSets at hS
    rw [Finset.mem_filter] at hS
    obtain ⟨-, hS2, hS0⟩ := hS
    unfold Dag.alive at hp
    rw [Finset.mem_filter] at hp
    obtain ⟨g, hg, hgN, hg0, hg3, c, hk, hpc, hc2⟩ :=
      charge I D Gs hdown e.1 e.2 d S hS2 f hf hp.2 hS0 h3
    simp only [Finset.mem_biUnion]
    refine ⟨g, Finset.mem_filter.2 ⟨hg, hgN⟩, e.2, ?_, c, circKids_mem hk, ?_⟩
    · simp only [Lg, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hg3, S, hS2, hg0⟩
    · simp only [Tc]
      rw [if_pos hc2, Finset.mem_image]
      refine ⟨e.1, Finset.mem_inter.2 ⟨hpc, ?_⟩, rfl⟩
      unfold ptsOn; rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hIe⟩
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans (Finset.card_biUnion_le_card_mul _ _ (2 * d * d) ?_) (by rw [mul_comm])
  intro g _
  refine le_trans (Finset.card_biUnion_le_card_mul _ _ (2 * d) ?_) ?_
  · intro l _
    refine le_trans (Finset.card_biUnion_le_card_mul _ _ d (fun c _ => hTc l c)) ?_
    have := circKids_card D g
    exact Nat.mul_le_mul_right d this
  · have := Nat.mul_le_mul_right (2 * d) (hLg g)
    rw [mul_comm d (2 * d)] at this
    exact this
theorem rich_card (I : Fin N → Fin N → Prop) (hI : NoRect I) (D : Dag N) (Gs : Finset ℕ)
    (hdown : ∀ i ∈ Gs, ∀ c, D.Kid i c → N + N ≤ c → c ∈ Gs) (d : ℕ) :
    (D.fSet I Gs d).card ≤ 2 * d * d * (Gs.filter (fun f => D.deg f = 0)).card := by
  classical
  have hsub : D.fSet I Gs d ⊆ fSetU I D (Gs.filter (fun f => D.deg f = 0)) d := by
    intro e he
    unfold Dag.fSet at he
    unfold fSetU
    rw [Finset.mem_filter] at he ⊢
    obtain ⟨-, hIe, f, hf, hfd, hrest⟩ := he
    exact ⟨Finset.mem_univ _, hIe, f, Finset.mem_filter.2 ⟨hf, hfd⟩, hrest⟩
  refine le_trans (Finset.card_le_card hsub) (le_trans (richU_card I hI D _ ?_ d) ?_)
  · intro i hi c hk hc
    rw [Finset.mem_filter] at hi ⊢
    exact ⟨hdown i hi.1 c hk hc, by have := deg_kid hk; omega⟩
  · exact Nat.mul_le_mul_left _ (Finset.card_le_card (Finset.filter_subset _ _))
theorem allG_down (D : Dag N) : ∀ i ∈ Deg1.allG D, ∀ c, D.Kid i c → N + N ≤ c →
    c ∈ Deg1.allG D := by
  intro i hi c hk hc
  have := circ_kid_lt hk
  unfold Deg1.allG at hi ⊢
  rw [Finset.mem_Ico] at hi ⊢
  omega
theorem allG_gate (D : Dag N) : (Deg1.allG D).filter (fun g => N + N ≤ g) = Deg1.allG D :=
  Finset.filter_true_of_mem (fun _ hg => (Finset.mem_Ico.1 hg).1)
theorem richU_allG (I : Fin N → Fin N → Prop) (hI : NoRect I) (D : Dag N) (d : ℕ) :
    (fSetU I D (Deg1.allG D) d).card ≤ 2 * d * d * D.size := by
  have := richU_card I hI D _ (allG_down D) d
  rw [allG_gate] at this
  have hc : (Deg1.allG D).card = D.size := by unfold Deg1.allG; simp
  rw [hc] at this
  exact this
theorem rich3_allG (I : Fin N → Fin N → Prop) (hI : NoRect I) (D : Dag N) :
    (D.fSet I (Deg1.allG D) 3).card ≤ 18 * (Deg1.XA D).card := by
  have := rich_card I hI D _ (allG_down D) 3
  unfold Deg1.XA
  convert this using 3
theorem low_sub (D : Dag N) :
    (Deg1.allG D).filter (fun f => D.deg f ≤ 1) ⊆ Deg1.XA D ∪ Deg1.AndA D ∪ Deg1.OrA D := by
  intro v hv
  rw [Finset.mem_filter] at hv
  obtain ⟨hvA, hd⟩ := hv
  have hA := Finset.mem_Ico.1 hvA
  have hg : D.gateAt v = D.gates[v - (N + N)]? := by unfold Dag.gateAt; rw [if_pos hA.1]
  obtain ⟨g, hgs⟩ : ∃ g, D.gateAt v = some g := by
    rw [hg]; exact ⟨_, List.getElem?_eq_getElem (by unfold Dag.size at hA; omega)⟩
  simp only [Deg1.XA, Deg1.AndA, Deg1.OrA, Finset.mem_union, Finset.mem_filter]
  rcases Nat.lt_or_ge (D.deg v) 1 with h0 | h1
  · left; left; exact ⟨hvA, by omega⟩
  cases g with
  | and a b => left; right; exact ⟨hvA, by omega, a, b, hgs⟩
  | or a b => right; exact ⟨hvA, by omega, a, b, hgs⟩
  | cst c =>
    exfalso
    rw [hg] at hgs
    have : D.deg v = 0 := by rw [Dag.deg, if_neg (by omega), hgs]
    omega
theorem low_down (D : Dag N) : ∀ i ∈ (Deg1.allG D).filter (fun f => D.deg f ≤ 1), ∀ c,
    D.Kid i c → N + N ≤ c → c ∈ (Deg1.allG D).filter (fun f => D.deg f ≤ 1) := by
  intro i hi c hk hc
  rw [Finset.mem_filter] at hi ⊢
  exact ⟨allG_down D i hi.1 c hk hc, by have := deg_kid hk; omega⟩
theorem rich2low_allG (I : Fin N → Fin N → Prop) (hI : NoRect I) (D : Dag N) :
    (fSetU I D ((Deg1.allG D).filter (fun f => D.deg f ≤ 1)) 2).card ≤
      8 * ((Deg1.XA D).card + (Deg1.AndA D).card + (Deg1.OrA D).card) := by
  refine le_trans (richU_card I hI D _ (low_down D) 2) (Nat.mul_le_mul_left _ ?_)
  refine le_trans (Finset.card_le_card (Finset.filter_subset _ _)) ?_
  refine le_trans (Finset.card_le_card (low_sub D)) ?_
  refine le_trans (Finset.card_union_le _ _) ?_
  have := Finset.card_union_le (Deg1.XA D) (Deg1.AndA D)
  omega
open Classical in
noncomputable def rich (I : Fin N → Fin N → Prop) (D : Dag N) (k d : ℕ) :
    Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun e => I e.1 e.2 ∧ ∃ f, D.deg f ≤ k ∧ D.deadSets I d f ≠ ∅ ∧
    e.1 ∈ D.alive f ∧ d + 1 ≤ (D.alive f ∩ ptsOn I e.2).card)
theorem rich_sub (I : Fin N → Fin N → Prop) (D : Dag N) (k d : ℕ) :
    rich I D k d ⊆ fSetU I D ((Deg1.allG D).filter (fun f => D.deg f ≤ k)) d := by
  classical
  intro e he
  unfold rich at he
  unfold fSetU
  rw [Finset.mem_filter] at he ⊢
  obtain ⟨-, hIe, f, hfk, hdead, hp, h3⟩ := he
  refine ⟨Finset.mem_univ _, hIe, f, Finset.mem_filter.2 ⟨?_, hfk⟩, hdead, hp, h3⟩
  obtain ⟨S, hS⟩ := Finset.nonempty_iff_ne_empty.2 hdead
  unfold Dag.deadSets at hS
  rw [Finset.mem_filter] at hS
  have hp' := hp
  unfold Dag.alive at hp'
  rw [Finset.mem_filter] at hp'
  unfold Deg1.allG
  rw [Finset.mem_Ico]
  by_cases hi : f < N + N
  · have := le_trans (Finset.card_le_card (Finset.inter_subset_left (s₁ := D.alive f)
      (s₂ := ptsOn I e.2))) (circ_alive_input D hi)
    have hS0 : S = ∅ := Finset.card_eq_zero.1 (by omega)
    obtain ⟨s, hs, -⟩ := circ_alive_on I D hS.2.2 hp
    rw [hS0] at hs
    exact absurd hs (Finset.notMem_empty s)
  · refine ⟨by omega, ?_⟩
    by_contra hf
    have hv := hp'.2
    rw [Dag.val, dif_neg hi, List.getElem?_eq_none (by unfold Dag.size at hf; omega)] at hv
    exact absurd hv (by simp)
theorem rich_card_k (I : Fin N → Fin N → Prop) (hI : NoRect I) (D : Dag N) (k d : ℕ) :
    (rich I D k d).card ≤ 2 * d * d * ((Deg1.allG D).filter (fun f => D.deg f ≤ k)).card := by
  refine le_trans (Finset.card_le_card (rich_sub I D k d)) ?_
  refine le_trans (richU_card I hI D _ ?_ d) (Nat.mul_le_mul_left _
    (Finset.card_le_card (Finset.filter_subset _ _)))
  intro i hi c hk hc
  rw [Finset.mem_filter] at hi ⊢
  exact ⟨allG_down D i hi.1 c hk hc, by have := deg_kid hk; omega⟩
theorem t02_rich3 (I : Fin N → Fin N → Prop) (hI : NoRect I) (D : Dag N) :
    (rich I D 0 3).card ≤ 18 * (Deg1.XA D).card := by
  refine le_trans (rich_card_k I hI D 0 3) (Nat.mul_le_mul_left _ (Finset.card_le_card ?_))
  intro v hv
  rw [Finset.mem_filter] at hv
  unfold Deg1.XA
  rw [Finset.mem_filter]
  exact ⟨hv.1, by omega⟩
theorem t02_rich2 (I : Fin N → Fin N → Prop) (hI : NoRect I) (D : Dag N) :
    (rich I D 1 2).card ≤ 8 * ((Deg1.XA D).card + (Deg1.AndA D).card + (Deg1.OrA D).card) := by
  refine le_trans (rich_card_k I hI D 1 2) (Nat.mul_le_mul_left _ ?_)
  refine le_trans (Finset.card_le_card (low_sub D)) ?_
  refine le_trans (Finset.card_union_le _ _) ?_
  have := Finset.card_union_le (Deg1.XA D) (Deg1.AndA D)
  omega
end Rich
end PEqualNP.Outside.L_meta_1321
namespace PEqualNP.Outside.L_meta_1321
open PEqualNP PEqualNP.MetaComplexity
namespace Cross
variable {P L : Type*} [DecidableEq P] (line : L → Finset P) (A C : Finset P)
def NoRectangle : Prop :=
  ∀ ⦃v w : L⦄, v ≠ w → (line v ∩ line w).card ≤ 1
structure GateWitness (p : P) (w u : L) : Prop where
  common : p ∈ A ∩ C
  outside : p ∉ line u
  coverA : A ⊆ line w ∪ line u
  coverC : C ⊆ line w ∪ line u
  heavy : 2 ≤ (A \ line u).card
  single : C \ line u = {p}
def IsGate (x : P × L) : Prop := ∃ u, GateWitness line A C x.1 x.2 u
variable {line A C}
private theorem pin {p q : P} {v w : L} (nr : NoRectangle line) (hne : q ≠ p)
    (hpv : p ∈ line v) (hqv : q ∈ line v) (hpw : p ∈ line w) (hqw : q ∈ line w) : v = w := by
  by_contra h
  exact hne (Finset.card_le_one_iff.mp (nr h) (Finset.mem_inter.mpr ⟨hqv,hqw⟩)
    (Finset.mem_inter.mpr ⟨hpv,hpw⟩))
private theorem onGate {p w u} (h : GateWitness line A C p w u) : p ∈ line w :=
  (Finset.mem_union.mp (h.coverA (Finset.mem_inter.mp h.common).1)).resolve_right h.outside
private theorem encode {x : P × L} (g : IsGate line A C x) :
    ∃ q ∈ A \ C, q ∈ line x.2 ∧ q ≠ x.1 := by
  obtain ⟨u,h⟩ := g
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp h.heavy
  have other : ∃ q ∈ A \ line u, q ≠ x.1 := by
    by_cases e : a = x.1
    · exact ⟨b,hb,fun eb => hab (e.trans eb.symm)⟩
    · exact ⟨a,ha,e⟩
  obtain ⟨q,hq,hne⟩ := other
  obtain ⟨qa,qu⟩ := Finset.mem_sdiff.mp hq
  refine ⟨q,Finset.mem_sdiff.mpr ⟨qa,?_⟩,(Finset.mem_union.mp (h.coverA qa)).resolve_right qu,hne⟩
  intro qc
  have : q ∈ C \ line u := Finset.mem_sdiff.mpr ⟨qc,qu⟩
  rw [h.single, Finset.mem_singleton] at this
  exact hne this
private theorem gateData {x : P × L} (g : IsGate line A C x) :
    x.1 ∈ A ∩ C ∧ x.1 ∈ line x.2 := by
  obtain ⟨u,h⟩ := g
  exact ⟨h.common,onGate h⟩
private theorem smallProduct {a b : ℕ} (h : a + b ≤ 4) : a * b ≤ 4 := by
  have ha : a ≤ 4 := by omega
  interval_cases a <;> omega
theorem gate_card_small (nr : NoRectangle line) (S : Finset (P × L))
    (good : ∀ x ∈ S, IsGate line A C x) (small : A.card ≤ 4) : S.card ≤ 4 := by
  classical
  have pick : ∀ x : P × L, ∃ q, x ∈ S → q ∈ A \ C ∧ q ∈ line x.2 ∧ q ≠ x.1 := by
    intro x
    by_cases hx : x ∈ S
    · obtain ⟨q,hq⟩ := encode (good x hx)
      exact ⟨q,fun _ => hq⟩
    · exact ⟨x.1,fun h => (hx h).elim⟩
  choose q hq using pick
  calc
    S.card ≤ ((A ∩ C) ×ˢ (A \ C)).card := by
      apply Finset.card_le_card_of_injOn (fun x : P × L => (x.1,q x))
      · intro x hx
        exact Finset.mem_product.mpr ⟨(gateData (good x hx)).1,(hq x hx).1⟩
      · intro x hx y hy he
        have ep : x.1 = y.1 := congrArg (Prod.fst : P × P → P) he
        have eq : q x = q y := congrArg Prod.snd he
        exact Prod.ext ep (pin nr (hq x hx).2.2 (gateData (good x hx)).2 (hq x hx).2.1
          (ep ▸ (gateData (good y hy)).2) (eq ▸ (hq y hy).2.1))
    _ = _ := Finset.card_product _ _
    _ ≤ 4 := smallProduct (by have := Finset.card_sdiff_add_card_inter A C; omega)
private theorem coverSum {X B D : Finset P} (cov : X ⊆ B ∪ D) :
    X.card ≤ (X ∩ B).card + (X ∩ D).card := by
  apply le_trans (Finset.card_le_card (t := (X ∩ B) ∪ (X ∩ D)) ?_) (Finset.card_union_le _ _)
  intro x hx
  rcases Finset.mem_union.mp (cov hx) with hb|hd
  · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hx,hb⟩)
  · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hx,hd⟩)
private theorem forced {v w u : L} (nr : NoRectangle line) (big : 3 ≤ (A ∩ line v).card)
    (cov : A ⊆ line w ∪ line u) : v = w ∨ v = u := by
  by_contra! h
  have part (z : L) (hz : v ≠ z) : ((A ∩ line v) ∩ line z).card ≤ 1 := by
    refine le_trans (Finset.card_le_card ?_) (nr hz)
    intro x hx
    obtain ⟨xv,xz⟩ := Finset.mem_inter.mp hx
    exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp xv).2,xz⟩
  have k := coverSum (X := A ∩ line v) (B := line w) (D := line u)
    (fun _ hx => cov (Finset.mem_inter.mp hx).1)
  have kw := part w h.1
  have ku := part u h.2
  omega
private theorem commonPivot {p q : P} {w z v : L} (nr : NoRectangle line)
    (h : GateWitness line A C p w v) (j : GateWitness line A C q z v) : w = z := by
  obtain ⟨a,ha,b,hb,hn⟩ := Finset.one_lt_card.mp h.heavy
  have lift {x : P} {y : L} (hx : x ∈ A \ line v) (cov : A ⊆ line y ∪ line v) : x ∈ line y :=
    (Finset.mem_union.mp (cov (Finset.mem_sdiff.mp hx).1)).resolve_right (Finset.mem_sdiff.mp hx).2
  exact pin nr hn (lift hb h.coverA) (lift ha h.coverA) (lift hb j.coverA) (lift ha j.coverA)
private theorem commonOnLine {p w u} (nr : NoRectangle line) (h : GateWitness line A C p w u) :
    (C ∩ line w).card ≤ 2 := by
  have hne : w ≠ u := fun e => h.outside (e ▸ onGate h)
  have sub : C ∩ line w ⊆ insert p (line w ∩ line u) := by
    intro x hx
    obtain ⟨xc,xw⟩ := Finset.mem_inter.mp hx
    by_cases xu : x ∈ line u
    · exact Finset.mem_insert_of_mem (Finset.mem_inter.mpr ⟨xw,xu⟩)
    · have out := Finset.mem_sdiff.mpr ⟨xc,xu⟩
      rw [h.single, Finset.mem_singleton] at out
      exact Finset.mem_insert.mpr (Or.inl out)
  have hi := Finset.card_insert_le p (line w ∩ line u)
  have hs := Finset.card_le_card sub
  have hr := nr hne
  omega
private theorem fiber {S : Finset (P × L)} {w : L} (nr : NoRectangle line)
    (good : ∀ x ∈ S, IsGate line A C x) (same : ∀ x ∈ S, x.2 = w) : S.card ≤ 2 := by
  classical
  obtain he|⟨y,hy⟩ := S.eq_empty_or_nonempty
  · simp [he]
  obtain ⟨u,h⟩ := good y hy
  calc
    S.card ≤ (C ∩ line w).card := by
      apply Finset.card_le_card_of_injOn Prod.fst
      · intro x hx
        obtain ⟨hc,hw⟩ := gateData (good x hx)
        exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hc).2,(same x hx) ▸ hw⟩
      · intro x hx z hz e
        exact Prod.ext e ((same x hx).trans (same z hz).symm)
    _ ≤ 2 := (same y hy) ▸ commonOnLine nr h
theorem gate_card_le_four (nr : NoRectangle line) (S : Finset (P × L))
    (good : ∀ x ∈ S, IsGate line A C x) : S.card ≤ 4 := by
  classical
  by_cases small : A.card ≤ 4
  · exact gate_card_small nr S good small
  obtain he|⟨x,hx⟩ := S.eq_empty_or_nonempty
  · simp [he]
  obtain ⟨u,h⟩ := good x hx
  have existsBig : ∃ v, 3 ≤ (A ∩ line v).card := by
    have sum := coverSum h.coverA
    by_cases hw : 3 ≤ (A ∩ line x.2).card
    · exact ⟨_,hw⟩
    · exact ⟨u,by omega⟩
  obtain ⟨v,hv⟩ := existsBig
  let F := S.filter (fun z => z.2 = v)
  let R := S.filter (fun z => ¬z.2 = v)
  have partition : F.card + R.card = S.card := Finset.card_filter_add_card_filter_not _
  have fsmall : F.card ≤ 2 := fiber nr
    (fun z hz => good z (Finset.mem_filter.mp hz).1) (fun _ hz => (Finset.mem_filter.mp hz).2)
  have off (z : P × L) (hz : z ∈ R) : GateWitness line A C z.1 z.2 v := by
    obtain ⟨hs,hn⟩ := Finset.mem_filter.mp hz
    obtain ⟨t,ht⟩ := good z hs
    have ev := (forced nr hv ht.coverA).resolve_left (Ne.symm hn)
    exact ev ▸ ht
  obtain er|⟨y,hy⟩ := R.eq_empty_or_nonempty
  · rw [er,Finset.card_empty] at partition
    omega
  · have rsmall : R.card ≤ 2 := fiber (w := y.2) nr
      (fun z hz => good z (Finset.mem_filter.mp hz).1)
      (fun z hz => commonPivot nr (off z hz) (off y hy))
    omega
noncomputable def gatePairs [Fintype P] [Fintype L] (line : L → Finset P) (A C : Finset P) :
    Finset (P × L) := by
  classical
  exact Finset.univ.filter (IsGate line A C)
theorem gatePairs_card_le_four [Fintype P] [Fintype L] (nr : NoRectangle line) :
    (gatePairs line A C).card ≤ 4 := by
  classical
  apply gate_card_le_four nr (A := A) (C := C)
  intro x hx
  exact (Finset.mem_filter.mp hx).2
end Cross
namespace Cross
open Finset
variable {W Q P : Type*} [DecidableEq W]
noncomputable def survivors (A : Finset W) (pencil : Q → Finset W) : Finset W := by
  classical
  exact A.filter (fun w => ∃ q, A \ pencil q = {w})
@[simp] theorem mem_survivors {A : Finset W} {pencil : Q → Finset W} {w : W} :
    w ∈ survivors A pencil ↔ ∃ q, A \ pencil q = {w} := by
  classical
  constructor
  · exact fun h => (mem_filter.mp h).2
  · rintro ⟨q, hq⟩
    have hw : w ∈ A \ pencil q := hq.symm ▸ mem_singleton_self w
    exact mem_filter.mpr ⟨(mem_sdiff.mp hw).1, q, hq⟩
theorem card_le_three_of_ne_survivors {A : Finset W} {pencil : Q → Finset W}
    (hsep : ∀ q r, q ≠ r → (pencil q ∩ pencil r).card ≤ 1)
    {u v : W} (hu : u ∈ survivors A pencil) (hv : v ∈ survivors A pencil) (hne : u ≠ v) :
    A.card ≤ 3 := by
  obtain ⟨q, hq⟩ := mem_survivors.mp hu
  obtain ⟨r, hr⟩ := mem_survivors.mp hv
  have hqr : q ≠ r := by
    rintro rfl
    exact hne (singleton_injective (hq.symm.trans hr))
  have hsub : A ⊆ insert u (insert v (pencil q ∩ pencil r)) := by
    intro x hx
    by_cases hxu : x = u
    · simp [hxu]
    by_cases hxv : x = v
    · simp [hxv]
    apply mem_insert_of_mem
    apply mem_insert_of_mem
    apply mem_inter.mpr
    constructor
    · by_contra hn
      exact hxu (mem_singleton.mp (hq ▸ mem_sdiff.mpr ⟨hx, hn⟩))
    · by_contra hn
      exact hxv (mem_singleton.mp (hr ▸ mem_sdiff.mpr ⟨hx, hn⟩))
  have := card_le_card hsub
  have := card_insert_le u (insert v (pencil q ∩ pencil r))
  have := card_insert_le v (pencil q ∩ pencil r)
  have := hsep q r hqr
  omega
theorem card_survivors_le_one {A : Finset W} {pencil : Q → Finset W}
    (hsep : ∀ q r, q ≠ r → (pencil q ∩ pencil r).card ≤ 1) (hA : 4 ≤ A.card) :
    (survivors A pencil).card ≤ 1 := by
  apply card_le_one.mpr
  intro u hu v hv
  by_contra hne
  have := card_le_three_of_ne_survivors hsep hu hv hne
  omega
theorem card_survivors_le_three {A : Finset W} {pencil : Q → Finset W}
    (hsep : ∀ q r, q ≠ r → (pencil q ∩ pencil r).card ≤ 1) :
    (survivors A pencil).card ≤ 3 := by
  classical
  by_cases hA : 4 ≤ A.card
  · exact (card_survivors_le_one hsep hA).trans (by decide)
  · have hsub : survivors A pencil ⊆ A := filter_subset _ _
    exact (card_le_card hsub).trans (by omega)
variable [DecidableEq P]
noncomputable def thinPairs (A : Finset W) (pencil : Q → Finset W)
    (B : Finset P) (line : W → Finset P) : Finset (P × W) :=
  ((survivors A pencil).filter (fun w => (B ∩ line w).card ≤ 3)).biUnion
    (fun w => (B ∩ line w) ×ˢ {w})
@[simp] theorem mem_thinPairs {A : Finset W} {pencil : Q → Finset W}
    {B : Finset P} {line : W → Finset P} {p : P} {w : W} :
    (p, w) ∈ thinPairs A pencil B line ↔
      w ∈ survivors A pencil ∧ p ∈ B ∩ line w ∧ (B ∩ line w).card ≤ 3 := by
  simp only [thinPairs, mem_biUnion, mem_filter, mem_product, mem_singleton]
  constructor
  · rintro ⟨v, ⟨hs, hl⟩, hp, rfl⟩
    exact ⟨hs, hp, hl⟩
  · rintro ⟨hs, hp, hl⟩
    exact ⟨w, ⟨hs, hl⟩, hp, rfl⟩
theorem card_thinPairs_le_nine {A : Finset W} {pencil : Q → Finset W}
    (hsep : ∀ q r, q ≠ r → (pencil q ∩ pencil r).card ≤ 1)
    (B : Finset P) (line : W → Finset P) :
    (thinPairs A pencil B line).card ≤ 9 := by
  let S := (survivors A pencil).filter (fun w => (B ∩ line w).card ≤ 3)
  have hS : S.card ≤ 3 := (card_le_card (filter_subset _ _)).trans
    (card_survivors_le_three hsep)
  calc
    (thinPairs A pencil B line).card ≤ S.card * 3 := by
      apply card_biUnion_le_card_mul
      intro w hw
      simpa using (mem_filter.mp hw).2
    _ ≤ 9 := by omega
end Cross
namespace Cross
open Deg2
variable {N : ℕ}
theorem walkOff (D : Dag N) (F : Finset (Fin N)) {v : ℕ} {w : Fin N}
    (h : D.VReach v w) :
    w ∉ F → 2 ≤ (D.Vstar v \ F).card →
    ∃ g c, D.Reach v g ∧ D.IsOr g ∧ D.deg g = 1 ∧ D.Kid g c ∧
      w ∈ D.Vstar c ∧ 2 ≤ (D.Vstar g \ F).card ∧
      D.Vstar c \ F = {w} ∧ D.Vstar c ⊆ D.Vstar g ∧ D.Vstar g ⊆ D.Vstar v := by
  classical
  induction h with
  | leaf w =>
    intro _ h2
    have hle : (D.Vstar (N + w.val) \ F).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      have ha' := circ_vreach_input D (Beta.mem_vstar.mp (Finset.mem_sdiff.mp ha).1) (by omega)
      have hb' := circ_vreach_input D (Beta.mem_vstar.mp (Finset.mem_sdiff.mp hb).1) (by omega)
      exact Fin.ext (by omega)
    omega
  | @step v c w hor hd hk hc ih =>
    intro hw h2
    have hsub := circ_vstar_sub D hor hd hk
    by_cases h2c : 2 ≤ (D.Vstar c \ F).card
    · obtain ⟨g,d,hr,ho,hg1,hk',hw',hg2,hsing,hdg,hgc⟩ := ih hw h2c
      exact ⟨g,d,Relation.ReflTransGen.head hk hr,ho,hg1,hk',hw',hg2,hsing,hdg,hgc.trans hsub⟩
    · have hwc := Beta.mem_vstar.mpr hc
      have hm := Finset.mem_sdiff.mpr ⟨hwc,hw⟩
      exact ⟨v,c,Relation.ReflTransGen.refl,hor,hd,hk,hwc,h2,
        Finset.eq_singleton_iff_unique_mem.mpr ⟨hm, fun x hx =>
          Finset.card_le_one.mp (by omega) x hx w hm⟩, hsub, Finset.Subset.rfl⟩
theorem walk (I : Fin N → Fin N → Prop) (D : Dag N) {q w : Fin N} {v : ℕ}
    (h : D.VReach v w) (hw : ¬ I q w) (h2 : 2 ≤ (D.Vstar v \ pencil I q).card) :
    ∃ g c, D.Reach v g ∧ D.IsOr g ∧ D.deg g = 1 ∧ D.Kid g c ∧
      w ∈ D.Vstar c ∧ 2 ≤ (D.Vstar g \ pencil I q).card ∧
      D.Vstar c \ pencil I q = {w} ∧ D.Vstar c ⊆ D.Vstar g ∧ D.Vstar g ⊆ D.Vstar v := by
  classical
  exact walkOff D (pencil I q) h (fun hm => hw (Finset.mem_filter.mp hm).2) h2
theorem countCharges {α : Type*} [DecidableEq α] (D : Dag N) (E : Finset α)
    (Gs : Finset ℕ) (F : ℕ → ℕ → Finset α)
    (hcover : ∀ e ∈ E, ∃ g ∈ Gs, ∃ c, D.Kid g c ∧ e ∈ F g c)
    (hfour : ∀ g ∈ Gs, ∀ c ∈ circKids D g, (F g c).card ≤ 4) :
    E.card ≤ 8 * Gs.card := by
  classical
  have hsub : E ⊆ Gs.biUnion (fun g => (circKids D g).biUnion (F g)) := by
    intro e he
    obtain ⟨g,hg,c,hc,hmem⟩ := hcover e he
    exact Finset.mem_biUnion.mpr ⟨g,hg,Finset.mem_biUnion.mpr ⟨c,circKids_mem hc,hmem⟩⟩
  refine (Finset.card_le_card hsub).trans ?_
  refine le_trans (Finset.card_biUnion_le_card_mul _ _ 8 ?_) (by rw [mul_comm])
  intro g hg
  refine le_trans (Finset.card_biUnion_le_card_mul _ _ 4 (hfour g hg)) ?_
  have := circKids_card D g
  omega
end Cross
namespace Cross
open PEqualNP.Outside.L_meta_1321
open Deg2
variable {N : ℕ} {I : Fin N → Fin N → Prop}
theorem pencil_nr (hr : NoRect I) : Cross.NoRectangle (pencil I) := by
  classical
  intro a b hab
  apply Finset.card_le_one.mpr
  intro v hv w hw
  rcases Finset.mem_inter.mp hv with ⟨hav,hbv⟩
  rcases Finset.mem_inter.mp hw with ⟨haw,hbw⟩
  simp only [pencil, Finset.mem_filter, Finset.mem_univ, true_and] at hav hbv haw hbw
  by_contra hvw
  exact hr a b v w hab hvw ⟨hav,haw,hbv,hbw⟩
theorem ptsOn_nr (hr : NoRect I) : Cross.NoRectangle (ptsOn I) := by
  classical
  intro v w hvw
  apply Finset.card_le_one.mpr
  intro a ha b hb
  rcases Finset.mem_inter.mp ha with ⟨hav,haw⟩
  rcases Finset.mem_inter.mp hb with ⟨hbv,hbw⟩
  simp only [ptsOn, Finset.mem_filter, Finset.mem_univ, true_and] at hav hbv haw hbw
  by_contra hab
  exact hr a b v w hab hvw ⟨hav,haw,hbv,hbw⟩
theorem tail_fiber (D : Dag N) (g c : ℕ) (hr : NoRect I)
    (E : Finset (Fin N × Fin N))
    (good : ∀ e ∈ E, ∃ q, e.2 ∈ D.Vstar g ∩ D.Vstar c ∧ ¬ I q e.2 ∧
      D.Vstar g ⊆ pencil I e.1 ∪ pencil I q ∧
      D.Vstar c ⊆ pencil I e.1 ∪ pencil I q ∧
      2 ≤ (D.Vstar g \ pencil I q).card ∧ D.Vstar c \ pencil I q = {e.2}) :
    E.card ≤ 4 := by
  classical
  let F := E.image Prod.swap
  have ht : E.card ≤ F.card := by
    apply Finset.card_le_card_of_injOn Prod.swap
    · intro e he
      exact Finset.mem_image.mpr ⟨e, he, rfl⟩
    · intro x hx y hy h
      simpa using congrArg Prod.swap h
  apply ht.trans (Cross.gate_card_le_four (pencil_nr hr) (A := D.Vstar g) (C := D.Vstar c) F ?_)
  intro z hz
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨q, hp, hn, hc1, hc2, h2, h1⟩ := good e he
  exact ⟨q, hp, by simpa [pencil] using hn, hc1, hc2, h2, h1⟩
theorem tailHeavy_card (D : Dag N) (E : Finset (Fin N × Fin N)) (Gs : Finset ℕ) (hr : NoRect I)
    (h : ∀ e ∈ E, ∃ v q, D.VReach v e.2 ∧ ¬ I q e.2 ∧
      2 ≤ (D.Vstar v \ pencil I q).card ∧ D.Vstar v ⊆ pencil I e.1 ∪ pencil I q ∧
      ∀ g, D.Reach v g → D.IsOr g → D.deg g = 1 → g ∈ Gs) :
    E.card ≤ 8 * Gs.card := by
  classical
  let F := fun (g c : ℕ) => E.filter (fun e => ∃ q, e.2 ∈ D.Vstar g ∩ D.Vstar c ∧ ¬ I q e.2 ∧
    D.Vstar g ⊆ pencil I e.1 ∪ pencil I q ∧ D.Vstar c ⊆ pencil I e.1 ∪ pencil I q ∧
    2 ≤ (D.Vstar g \ pencil I q).card ∧ D.Vstar c \ pencil I q = {e.2})
  apply countCharges D E Gs F
  · intro e he
    obtain ⟨v, q, hv, hn, h2, hsub, hgs⟩ := h e he
    obtain ⟨g, c, hg, hor, hd, hk, hw, ha, hs, hcg, hgv⟩ := walk I D hv hn h2
    refine ⟨g, hgs _ hg hor hd, c, hk, Finset.mem_filter.mpr ⟨he, ?_⟩⟩
    exact ⟨q, Finset.mem_inter.mpr ⟨hcg hw, hw⟩, hn,
      Finset.Subset.trans hgv hsub, Finset.Subset.trans hcg (Finset.Subset.trans hgv hsub), ha, hs⟩
  · intro g hg c hc
    exact tail_fiber D g c hr _ (fun e he => (Finset.mem_filter.mp he).2)
end Cross
namespace Cross
open Deg2
variable {N : ℕ} (I : Fin N → Fin N → Prop) (D : Dag N)
def ThinAt (g : ℕ) (e : Fin N × Fin N) : Prop :=
  ∃ f v q, D.LabAnd g f v ∧ D.Vstar v \ pencil I q = {e.2} ∧
    e.1 ∈ D.alive f ∩ ptsOn I e.2 ∧ (D.alive f ∩ ptsOn I e.2).card ≤ 3
theorem thinAt_card (hr : NoRect I) (g : ℕ) (E : Finset (Fin N × Fin N))
    (h : ∀ e ∈ E, ThinAt I D g e) : E.card ≤ 9 := by
  classical
  obtain he | ⟨e, he⟩ := E.eq_empty_or_nonempty
  · simp [he]
  obtain ⟨f, v, _, hfv, _⟩ := h e he
  apply (Finset.card_le_card (t := thinPairs (D.Vstar v) (pencil I) (D.alive f) (ptsOn I)) ?_).trans
    (card_thinPairs_le_nine (fun _ _ hne => pencil_nr hr hne) _ _)
  rintro ⟨p, w⟩ hp
  obtain ⟨f', v', q, hfv', hs, hi, hc⟩ := h _ hp
  obtain ⟨rfl, rfl⟩ := Api.labAnd_unique hfv' hfv
  exact mem_thinPairs.mpr ⟨mem_survivors.mpr ⟨q, hs⟩, hi, hc⟩
theorem betaCost (hr : NoRect I) (E : Finset (Fin N × Fin N)) (As Os : Finset ℕ)
    (h : ∀ e ∈ E, ∃ g ∈ As, ∃ f v q,
      D.LabAnd g f v ∧ D.VReach v e.2 ∧ ¬ I q e.2 ∧
      D.Vstar v ⊆ pencil I e.1 ∪ pencil I q ∧
      e.1 ∈ D.alive f ∩ ptsOn I e.2 ∧ (D.alive f ∩ ptsOn I e.2).card ≤ 3 ∧
      ∀ o, D.Reach v o → D.IsOr o → D.deg o = 1 → o ∈ Os) :
    E.card ≤ 9 * As.card + 8 * Os.card := by
  classical
  let B := fun e => ∃ g ∈ As, ThinAt I D g e
  let S := E.filter B
  let T := E.filter (fun e => ¬ B e)
  have hst : S.card + T.card = E.card := Finset.card_filter_add_card_filter_not _
  let G := fun g => E.filter (ThinAt I D g)
  have hss : S ⊆ As.biUnion G := by
    intro e he
    obtain ⟨hg, g, hga, hs⟩ := Finset.mem_filter.mp he
    exact Finset.mem_biUnion.mpr ⟨g, hga, Finset.mem_filter.mpr ⟨hg, hs⟩⟩
  have hsmall : S.card ≤ As.card * 9 :=
    (Finset.card_le_card hss).trans (Finset.card_biUnion_le_card_mul _ _ 9
      (fun g _ => thinAt_card I D hr g (G g) (fun _ he => (Finset.mem_filter.mp he).2)))
  have hlarge : T.card ≤ 8 * Os.card := by
    apply tailHeavy_card D _ _ hr
    intro e he
    obtain ⟨he', hno⟩ := Finset.mem_filter.mp he
    obtain ⟨g, hg, f, v, q, hfv, hv, hn, hcover, hi, hc, hos⟩ := h e he'
    refine ⟨v, q, hv, hn, ?_, hcover, hos⟩
    by_contra! hle
    have hm : e.2 ∈ D.Vstar v \ pencil I q := Finset.mem_sdiff.mpr
      ⟨Beta.mem_vstar.mpr hv, by simpa [pencil] using hn⟩
    have hs := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hm, fun t ht => Finset.card_le_one.mp (by omega : (D.Vstar v \ pencil I q).card ≤ 1)
        t ht e.2 hm⟩
    exact hno ⟨g, hg, f, v, q, hfv, hs, hi, hc⟩
  omega
end Cross
namespace Cross
open Deg2
variable {N : ℕ} {I : Fin N → Fin N → Prop} {D : Dag N}
theorem mixedCover (hwf : D.WF) {H v : ℕ} {p q b u : Fin N}
    (hpw : ¬ I p b) (hpu : ¬ I p u) (hqw : ¬ I q b) (hqu : ¬ I q u)
    (hd : D.deg H ≤ 1) (path : Relation.ReflTransGen (Beta.LStep D (pt p)) H v)
    (cert : ∀ z : Fin (N + N) → Bool,
      (∀ a, I a u → z (Fin.castAdd N a) = false) →
      z (Fin.castAdd N q) = true → z (Fin.natAdd N b) = true → D.val z H = true →
      ∃ a l, I a l ∧ z (Fin.castAdd N a) = true ∧ z (Fin.natAdd N l) = true) :
    D.Vstar v ⊆ pencil I p ∪ pencil I q := by
  classical
  intro k hk
  let z := inp ({p, q} : Finset (Fin N)) ({b, k} : Finset (Fin N))
  have hpz : pt p ≤ z := by
    apply Forms.inp_le
    · intro t ht
      simp only [Finset.mem_singleton] at ht
      simp [z, Forms.inp_castAdd, ht]
    · simp
  have hvr := Beta.mem_vstar.mp hk
  have hvz := circ_vreach_val D hvr (x := z) (by dsimp only [z]; rw [Forms.inp_natAdd]; simp)
  have hHz := Beta.lstep_up hwf hpz path hd (by rw [Beta.vreach_deg hvr]) hvz
  have hmiss : ∀ a, I a u → z (Fin.castAdd N a) = false := by
    intro a ha
    have hp : a ≠ p := fun eq => hpu (eq ▸ ha)
    have hq : a ≠ q := fun eq => hqu (eq ▸ ha)
    simp [z, Forms.inp_castAdd, hp, hq]
  obtain ⟨a, l, ha, hp, hl⟩ := cert z hmiss
    (by simp [z, Forms.inp_castAdd]) (by dsimp only [z]; rw [Forms.inp_natAdd]; simp) hHz
  simp only [z, Forms.inp_castAdd, Forms.inp_natAdd, decide_eq_true_eq,
    Finset.mem_insert, Finset.mem_singleton] at hp hl
  rcases hp with rfl | rfl <;> rcases hl with rfl | rfl
  · exact False.elim (hpw ha)
  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩)
  · exact False.elim (hqw ha)
  · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩)
end Cross
end PEqualNP.Outside.L_meta_1321
namespace PEqualNP.Outside.L_meta_1321
open PEqualNP PEqualNP.MetaComplexity
namespace Plan
open Deg2 Deg2.Api Deg2.Bridge
variable {N : ℕ}
def TLab (D : Dag N) (e f c : ℕ) : Prop :=
  (D.gateAt e = some (.and f c) ∨ D.gateAt e = some (.and c f)) ∧ D.deg f = 0 ∧ D.deg c = 2
def MixAnd (D : Dag N) (b t H : ℕ) : Prop :=
  (D.gateAt b = some (.and t H) ∨ D.gateAt b = some (.and H t)) ∧ D.deg t = 1 ∧ D.deg H = 1
open Classical in
noncomputable def UA (D : Dag N) : Finset ℕ :=
  (Deg1.allG D).filter (fun i => D.deg i = 2 ∧ D.IsOr i)
open Classical in
noncomputable def VA (D : Dag N) : Finset ℕ :=
  (Deg1.allG D).filter (fun i => D.deg i = 2 ∧ ∃ f c, TLab D i f c)
open Classical in
noncomputable def KA (D : Dag N) : Finset ℕ :=
  (Deg1.allG D).filter (fun i => D.deg i = 2 ∧ ∃ t H, MixAnd D i t H)
def TOr (D : Dag N) (e c : ℕ) : Prop := D.IsOr e ∧ D.deg e = 2 ∧ D.Kid e c ∧ 1 ≤ D.deg c
def TStep (D : Dag N) (x : Fin (N + N) → Bool) (e c : ℕ) : Prop :=
  TOr D e c ∨ ∃ f, TLab D e f c ∧ D.val x f = true
def OStep (D : Dag N) (a b : ℕ) : Prop := D.IsOr a ∧ D.deg a = 1 ∧ D.Kid a b
open Classical in
noncomputable def Pos (I : Fin N → Fin N → Prop) (D : Dag N) {J : ℕ} (r : Fin J → ℕ)
    (u : Fin J → Fin N) : Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun e => I e.1 e.2 ∧ ∃ j, ¬ I e.1 (u j) ∧ D.val (ep e.1 e.2) (r j) = true)
open Classical in
noncomputable def allEdges (I : Fin N → Fin N → Prop) : Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun e => I e.1 e.2)
noncomputable def drop3 (I : Fin N → Fin N → Prop) (D : Dag N) : Finset (Fin N × Fin N) :=
  Rich.rich I D 0 3
noncomputable def drop2 (I : Fin N → Fin N → Prop) (D : Dag N) : Finset (Fin N × Fin N) :=
  Rich.rich I D 1 2
open Classical in
noncomputable def served3 (I : Fin N → Fin N → Prop) (D : Dag N) : Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun e => ∃ g ∈ Deg1.AndA D, ∃ f v, D.LabAnd g f v ∧ D.Vstar v = {e.2} ∧
    e.1 ∈ D.alive f ∧ I e.1 e.2 ∧ (D.alive f ∩ ptsOn I e.2).card ≤ 3)
def Bad (I : Fin N → Fin N → Prop) (D : Dag N) {J : ℕ} (r : Fin J → ℕ) (u : Fin J → Fin N)
    (b : ℕ) (w : Fin N) (a : Fin J) (q : Fin N) : Prop :=
  ¬ I q w ∧ ¬ I q (u a) ∧ Relation.ReflTransGen (TStep D (pt q)) (r a) b
def Unsafe (I : Fin N → Fin N → Prop) (D : Dag N) {J : ℕ} (r : Fin J → ℕ) (u : Fin J → Fin N)
    (b : ℕ) (w : Fin N) : Prop := ∃ a q, Bad I D r u b w a q
def JobAt (D : Dag N) (b : ℕ) (w : Fin N) : Prop :=
  D.IsMarker b w ∨ ∃ t H, MixAnd D b t H ∧ D.Vstar t = {w}
def SafeJob (I : Fin N → Fin N → Prop) (D : Dag N) {J : ℕ} (r : Fin J → ℕ) (u : Fin J → Fin N)
    (b : ℕ) (w : Fin N) : Prop := JobAt D b w ∧ ¬ Unsafe I D r u b w
def UJob (I : Fin N → Fin N → Prop) (D : Dag N) {J : ℕ} (r : Fin J → ℕ) (u : Fin J → Fin N)
    (H : ℕ) (w : Fin N) : Prop :=
  ∃ b t, MixAnd D b t H ∧ D.Vstar t = {w} ∧ Unsafe I D r u b w
open Classical in
noncomputable def ujobs (I : Fin N → Fin N → Prop) (D : Dag N) {J : ℕ} (r : Fin J → ℕ)
    (u : Fin J → Fin N) : Finset (ℕ × Fin N) :=
  ((Finset.range (N + N + D.size)) ×ˢ Finset.univ).filter (fun i => UJob I D r u i.1 i.2)
open Classical in
noncomputable def safeFlags (I : Fin N → Fin N → Prop) (D : Dag N) {J : ℕ} (r : Fin J → ℕ)
    (u : Fin J → Fin N) : Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun e => I e.1 e.2 ∧ ∃ b, SafeJob I D r u b e.2 ∧
    ∃ j, ¬ I e.1 (u j) ∧ Relation.ReflTransGen (TStep D (pt e.1)) (r j) b)
open Classical in
noncomputable def Tset (I : Fin N → Fin N → Prop) (D : Dag N) {J : ℕ} (r : Fin J → ℕ)
    (u : Fin J → Fin N) (h : ℕ) : Finset (Fin N) :=
  Finset.univ.filter (fun k => ∃ b, SafeJob I D r u b k ∧ Relation.ReflTransGen (TOr D) h b)
def Degenerate (I : Fin N → Fin N → Prop) (D : Dag N) {J : ℕ} (r : Fin J → ℕ)
    (u : Fin J → Fin N) : Prop :=
  ∃ j b k, SafeJob I D r u b k ∧ k ≠ u j ∧ Relation.ReflTransGen (TOr D) (r j) b
open Classical in
noncomputable def badPt0 (I : Fin N → Fin N → Prop) (D : Dag N) {J : ℕ} (r : Fin J → ℕ)
    (u : Fin J → Fin N) : Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun e => I e.1 e.2 ∧ ∃ H, UJob I D r u H e.2 ∧ D.val (pt e.1) H = true)
def LWit (I : Fin N → Fin N → Prop) (D : Dag N) {J : ℕ} (r : Fin J → ℕ) (u : Fin J → Fin N)
    (p w : Fin N) (H g1 g v : ℕ) : Prop :=
  UJob I D r u H w ∧ I p w ∧ Relation.ReflTransGen (OStep D) H g1 ∧
    (∃ f1 v1, D.LabAnd g1 f1 v1 ∧ D.val (pt p) f1 = true) ∧
    Relation.ReflTransGen (Beta.LStep D (pt p)) g1 g ∧
    (∃ f, D.LabAnd g f v ∧ D.val (pt p) f = true) ∧ D.VReach v w
def BetaAt (I : Fin N → Fin N → Prop) (D : Dag N) {J : ℕ} (r : Fin J → ℕ) (u : Fin J → Fin N)
    (v : ℕ) (p w : Fin N) : Prop :=
  ∃ b t H k a q, MixAnd D b t H ∧ D.Vstar t = {k} ∧ Bad I D r u b k a q ∧
    ¬ I p k ∧ ¬ I p (u a) ∧ ¬ I q w ∧ Relation.ReflTransGen (Beta.LStep D (pt p)) H v
open Classical in
noncomputable def eBeta (I : Fin N → Fin N → Prop) (D : Dag N) {J : ℕ} (r : Fin J → ℕ)
    (u : Fin J → Fin N) : Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun e => ∃ H g1 g v, LWit I D r u e.1 e.2 H g1 g v ∧
    BetaAt I D r u v e.1 e.2)
open Classical in
noncomputable def eAlpha (I : Fin N → Fin N → Prop) (D : Dag N) {J : ℕ} (r : Fin J → ℕ)
    (u : Fin J → Fin N) : Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun e => ∃ H g1 g v, LWit I D r u e.1 e.2 H g1 g v ∧
    ¬ BetaAt I D r u v e.1 e.2)
open Classical in
noncomputable def Eset (I : Fin N → Fin N → Prop) (D : Dag N) {J : ℕ} (r : Fin J → ℕ)
    (u : Fin J → Fin N) (h : ℕ) : Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun e => ∃ H g1 g v, LWit I D r u e.1 e.2 H g1 g v ∧
    ¬ BetaAt I D r u v e.1 e.2 ∧ Relation.ReflTransGen (OStep D) H h ∧
    Relation.ReflTransGen (OStep D) h g1)
open Classical in
noncomputable def Rset (I : Fin N → Fin N → Prop) (D : Dag N) {J : ℕ} (r : Fin J → ℕ)
    (u : Fin J → Fin N) (h : ℕ) : Finset (Fin N) :=
  Finset.univ.filter (fun w => 3 ≤ (Finset.univ.filter (fun p => (p, w) ∈ Eset I D r u h)).card)
def Std (I : Fin N → Fin N → Prop) (D : Dag N) {J : ℕ} (r : Fin J → ℕ) (u : Fin J → Fin N) :
    Prop :=
  NoRect I ∧ D.WF ∧ (∀ j, D.deg (r j) ≤ 2) ∧ (∀ j, Clean3.PivotSound I D (r j) (u j)) ∧
    Clean3.CleanedD I D 3 (Deg1.allG D)
def CardT04 : Prop := ∀ (N : ℕ) (I : Fin N → Fin N → Prop) (D : Dag N) (J : ℕ) (r : Fin J → ℕ)
  (u : Fin J → Fin N), Std I D r u → ∀ (j : Fin J) (p w : Fin N), I p w → ¬ I p (u j) →
  D.val (ep p w) (r j) = true →
  (p, w) ∈ Deg1.pinnedA I D ∪ served3 I D ∪ drop3 I D ∨
  ∃ b, Relation.ReflTransGen (TStep D (pt p)) (r j) b ∧
    (D.IsMarker b w ∨ ∃ t H, MixAnd D b t H ∧ D.Vstar t = {w} ∧ D.val (ep p w) H = true)
def CardT05a : Prop := ∀ (N : ℕ) (I : Fin N → Fin N → Prop) (D : Dag N) (J : ℕ) (r : Fin J → ℕ)
  (u : Fin J → Fin N), Std I D r u → ∀ (b : ℕ) (w : Fin N), D.IsMarker b w →
  ¬ Unsafe I D r u b w
def CardT05b : Prop := ∀ (N : ℕ) (I : Fin N → Fin N → Prop) (D : Dag N) (J : ℕ) (r : Fin J → ℕ)
  (u : Fin J → Fin N), Std I D r u → ∀ (b t H : ℕ) (k : Fin N) (a : Fin J) (q : Fin N),
  MixAnd D b t H → D.Vstar t = {k} → Bad I D r u b k a q →
  ∀ z : Fin (N + N) → Bool, (∀ x, I x (u a) → z (Fin.castAdd N x) = false) →
    z (Fin.castAdd N q) = true → z (Fin.natAdd N k) = true → D.val z H = true →
    ∃ x l, I x l ∧ z (Fin.castAdd N x) = true ∧ z (Fin.natAdd N l) = true
def CardT05c : Prop := ∀ (N : ℕ) (I : Fin N → Fin N → Prop) (D : Dag N) (J : ℕ) (r : Fin J → ℕ)
  (u : Fin J → Fin N), D.WF → (ujobs I D r u).card ≤ 2 * (KA D).card
def CardT06b : Prop := ∀ (N : ℕ) (I : Fin N → Fin N → Prop) (D : Dag N) (J : ℕ) (r : Fin J → ℕ)
  (u : Fin J → Fin N), NoRect I → Degenerate I D r u → (allEdges I).card ≤ 4 * N
def CardT06c : Prop := ∀ (N : ℕ) (I : Fin N → Fin N → Prop) (D : Dag N) (J : ℕ) (r : Fin J → ℕ)
  (u : Fin J → Fin N), Std I D r u → ¬ Degenerate I D r u →
  (safeFlags I D r u \ drop3 I D).card ≤ 4 * (UA D).card + 6 * (VA D).card
def CardT07b : Prop := ∀ (N : ℕ) (I : Fin N → Fin N → Prop) (D : Dag N) (J : ℕ) (r : Fin J → ℕ)
  (u : Fin J → Fin N), Std I D r u →
  (badPt0 I D r u \ drop2 I D).card ≤ 2 * (ujobs I D r u).card
def CardT07c : Prop := ∀ (N : ℕ) (I : Fin N → Fin N → Prop) (D : Dag N) (J : ℕ) (r : Fin J → ℕ)
  (u : Fin J → Fin N), Std I D r u → ∀ (H : ℕ) (p w : Fin N), UJob I D r u H w → I p w →
  D.val (ep p w) H = true → D.val (pt p) H = false → ∃ g1 g v, LWit I D r u p w H g1 g v
def CardT10 : Prop := ∀ (N : ℕ) (I : Fin N → Fin N → Prop) (D : Dag N) (J : ℕ) (r : Fin J → ℕ)
  (u : Fin J → Fin N), NoRect I → D.WF → ∀ (h : ℕ) (w : Fin N), w ∈ Rset I D r u h →
  ∃ q k, ¬ I q w ∧ Rset I D r u h ⊆ {w, k} ∪ pencil I q
def CardT12 : Prop := ∀ (N : ℕ) (I : Fin N → Fin N → Prop) (D : Dag N) (J : ℕ) (r : Fin J → ℕ)
  (u : Fin J → Fin N), Std I D r u → (∀ h, (Rset I D r u h).card ≤ 5) →
  (eAlpha I D r u \ drop3 I D).card ≤
    2 * (ujobs I D r u).card + 15 * (Deg1.AndA D).card + 20 * (Deg1.OrA D).card
theorem served3_card (I : Fin N → Fin N → Prop) (D : Dag N) :
    (served3 I D).card ≤ 3 * (Deg1.AndA D).card := by
  classical
  let T : ℕ → Finset (Fin N × Fin N) := fun g => Finset.univ.filter (fun e => ∃ f v,
    D.LabAnd g f v ∧ D.Vstar v = {e.2} ∧ e.1 ∈ D.alive f ∧ I e.1 e.2 ∧
      (D.alive f ∩ ptsOn I e.2).card ≤ 3)
  have hsub : served3 I D ⊆ (Deg1.AndA D).biUnion T := by
    intro e he
    unfold served3 at he
    rw [Finset.mem_filter] at he
    obtain ⟨-, g, hg, f, v, h1, h2, h3, h4, h5⟩ := he
    rw [Finset.mem_biUnion]
    exact ⟨g, hg, Finset.mem_filter.2 ⟨Finset.mem_univ _, f, v, h1, h2, h3, h4, h5⟩⟩
  have hT : ∀ g ∈ Deg1.AndA D, (T g).card ≤ 3 := by
    intro g _
    by_cases hne : (T g).Nonempty
    · obtain ⟨e0, he0⟩ := hne
      obtain ⟨-, f0, v0, h1, h2, -, -, h5⟩ := Finset.mem_filter.1 he0
      have hsub' : T g ⊆ (D.alive f0 ∩ ptsOn I e0.2).image (fun p => (p, e0.2)) := by
        intro e he
        obtain ⟨-, f, v, k1, k2, k3, k4, -⟩ := Finset.mem_filter.1 he
        obtain ⟨rfl, rfl⟩ := labAnd_unique k1 h1
        have hw : e.2 = e0.2 := by
          rw [h2] at k2
          exact (Finset.singleton_inj.1 k2).symm
        rw [Finset.mem_image]
        refine ⟨e.1, Finset.mem_inter.2 ⟨k3, ?_⟩, ?_⟩
        · unfold ptsOn
          rw [Finset.mem_filter, ← hw]
          exact ⟨Finset.mem_univ _, k4⟩
        · ext <;> simp [hw]
      exact le_trans (Finset.card_le_card hsub') (le_trans Finset.card_image_le h5)
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne]; simp
  calc (served3 I D).card ≤ ((Deg1.AndA D).biUnion T).card := Finset.card_le_card hsub
    _ ≤ ∑ g ∈ Deg1.AndA D, (T g).card := Finset.card_biUnion_le
    _ ≤ ∑ _g ∈ Deg1.AndA D, 3 := Finset.sum_le_sum hT
    _ = 3 * (Deg1.AndA D).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
theorem classes6 (D : Dag N) :
    (Deg1.XA D).card + (Deg1.AndA D).card + (Deg1.OrA D).card + (UA D).card + (VA D).card +
      (KA D).card ≤ D.size := by
  classical
  have hall : (Deg1.allG D).card = D.size := by unfold Deg1.allG; simp
  have hno : ∀ i, D.IsAnd i → ¬ D.IsOr i := by
    rintro i ⟨a, b, hab⟩ ⟨c, d, hcd⟩
    rw [hab] at hcd
    cases hcd
  let Y := (Deg1.allG D).filter (fun i => ¬ D.deg i = 0)
  have h1 : (Deg1.XA D).card + Y.card = (Deg1.allG D).card := by
    unfold Deg1.XA; exact Finset.card_filter_add_card_filter_not _
  let Y1 := Y.filter (fun i => D.deg i = 1)
  let Y2 := Y.filter (fun i => ¬ D.deg i = 1)
  have h2 : Y1.card + Y2.card = Y.card := Finset.card_filter_add_card_filter_not _
  have h3 : (Y1.filter D.IsOr).card + (Y1.filter (fun i => ¬ D.IsOr i)).card = Y1.card :=
    Finset.card_filter_add_card_filter_not _
  have h4 : Deg1.OrA D ⊆ Y1.filter D.IsOr := by
    intro i hi
    unfold Deg1.OrA at hi
    simp only [Y1, Y, Finset.mem_filter] at hi ⊢
    exact ⟨⟨⟨hi.1, by omega⟩, hi.2.1⟩, hi.2.2⟩
  have h5 : Deg1.AndA D ⊆ Y1.filter (fun i => ¬ D.IsOr i) := by
    intro i hi
    unfold Deg1.AndA at hi
    simp only [Y1, Y, Finset.mem_filter] at hi ⊢
    exact ⟨⟨⟨hi.1, by omega⟩, hi.2.1⟩, hno i hi.2.2⟩
  have h6 : (Y2.filter D.IsOr).card + (Y2.filter (fun i => ¬ D.IsOr i)).card = Y2.card :=
    Finset.card_filter_add_card_filter_not _
  have h7 : UA D ⊆ Y2.filter D.IsOr := by
    intro i hi
    unfold UA at hi
    simp only [Y2, Y, Finset.mem_filter] at hi ⊢
    exact ⟨⟨⟨hi.1, by omega⟩, by omega⟩, hi.2.2⟩
  have h8 : ((Y2.filter (fun i => ¬ D.IsOr i)).filter (fun i => ∃ f c, TLab D i f c)).card +
      ((Y2.filter (fun i => ¬ D.IsOr i)).filter (fun i => ¬ ∃ f c, TLab D i f c)).card = (Y2.filter (fun i => ¬ D.IsOr i)).card :=
    Finset.card_filter_add_card_filter_not _
  have h9 : VA D ⊆ (Y2.filter (fun i => ¬ D.IsOr i)).filter (fun i => ∃ f c, TLab D i f c) := by
    intro i hi
    unfold VA at hi
    simp only [Y2, Y, Finset.mem_filter] at hi ⊢
    obtain ⟨hi1, hi2, f, c, hl⟩ := hi
    refine ⟨⟨⟨⟨hi1, by omega⟩, by omega⟩, hno i ?_⟩, f, c, hl⟩
    rcases hl.1 with h | h
    · exact ⟨_, _, h⟩
    · exact ⟨_, _, h⟩
  have h10 : KA D ⊆ (Y2.filter (fun i => ¬ D.IsOr i)).filter (fun i => ¬ ∃ f c, TLab D i f c) := by
    intro i hi
    unfold KA at hi
    simp only [Y2, Y, Finset.mem_filter] at hi ⊢
    obtain ⟨hi1, hi2, t, H, hm⟩ := hi
    refine ⟨⟨⟨⟨hi1, by omega⟩, by omega⟩, hno i ?_⟩, ?_⟩
    · rcases hm.1 with h | h
      · exact ⟨_, _, h⟩
      · exact ⟨_, _, h⟩
    · rintro ⟨f, c, hl, hf, hc⟩
      obtain ⟨hm1, ht, hH⟩ := hm
      rcases hm1 with h | h <;> rcases hl with h' | h' <;> rw [h] at h' <;>
        simp only [Option.some.injEq, G.and.injEq] at h' <;> obtain ⟨rfl, rfl⟩ := h' <;> omega
  have := Finset.card_le_card h4
  have := Finset.card_le_card h5
  have := Finset.card_le_card h7
  have := Finset.card_le_card h9
  have := Finset.card_le_card h10
  omega
theorem betaBound (h05b : CardT05b) (I : Fin N → Fin N → Prop) (D : Dag N) {J : ℕ}
    (r : Fin J → ℕ) (u : Fin J → Fin N) (hstd : Std I D r u) :
    (eBeta I D r u \ drop3 I D).card ≤ 9 * (Deg1.AndA D).card + 8 * (Deg1.OrA D).card := by
  classical
  have hstd' := hstd
  obtain ⟨hI, hwf, -, -, hcl⟩ := hstd
  refine Cross.betaCost I D hI _ _ _ ?_
  rintro ⟨p, w⟩ he
  rw [Finset.mem_sdiff] at he
  obtain ⟨he1, he3⟩ := he
  unfold eBeta at he1
  rw [Finset.mem_filter] at he1
  obtain ⟨-, H, g1, g, v, ⟨-, hpw, -, -, -, ⟨f, hlab, hf⟩, hvr⟩,
    b, t, H', k, a, q, hmix, hvs, hbad, hpk, hpu, hqw, hpath⟩ := he1
  have hbad' := hbad
  obtain ⟨hqk, hqu, -⟩ := hbad
  obtain ⟨hgate, hf0, hv1⟩ := hlab
  have hgA : g ∈ Deg1.allG D := by
    rcases hgate with h | h
    · exact Deg1.mem_allG h
    · exact Deg1.mem_allG h
  have hgdeg : D.deg g = 1 := by
    rcases hgate with h | h
    · rw [Forms.deg_and h (hwf _ _ h f (by simp [G.kids])) (hwf _ _ h v (by simp [G.kids]))]; omega
    · rw [Forms.deg_and h (hwf _ _ h v (by simp [G.kids])) (hwf _ _ h f (by simp [G.kids]))]; omega
  have hgand : D.IsAnd g := by
    rcases hgate with h | h
    · exact ⟨_, _, h⟩
    · exact ⟨_, _, h⟩
  have hpf : p ∈ D.alive f := by
    unfold Dag.alive
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hf⟩
  have hpon : p ∈ ptsOn I w := by
    unfold ptsOn
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hpw⟩
  refine ⟨g, ?_, f, v, q, ⟨hgate, hf0, hv1⟩, hvr, hqw, ?_, Finset.mem_inter.2 ⟨hpf, hpon⟩, ?_, ?_⟩
  · unfold Deg1.AndA
    exact Finset.mem_filter.2 ⟨hgA, hgdeg, hgand⟩
  · exact Cross.mixedCover hwf hpk hpu hqk hqu (le_of_eq hmix.2.2) hpath
      (h05b N I D J r u hstd' b t H' k a q hmix hvs hbad')
  · by_contra hc
    apply he3
    unfold drop3 Rich.rich
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, hpw, f, le_of_eq hf0, ?_, hpf, by omega⟩
    exact hcl g hgA f v hgate hf0 (by omega)
  · intro o _ hor hd
    obtain ⟨a', b', hab⟩ := hor
    unfold Deg1.OrA
    exact Finset.mem_filter.2 ⟨Deg1.mem_allG hab, hd, ⟨a', b', hab⟩⟩
theorem coverPos (h04 : CardT04) (h05a : CardT05a) (h07c : CardT07c)
    (I : Fin N → Fin N → Prop) (D : Dag N) {J : ℕ}
    (r : Fin J → ℕ) (u : Fin J → Fin N) (hstd : Std I D r u) :
    Pos I D r u ⊆ Deg1.pinnedA I D ∪ served3 I D ∪ drop3 I D ∪ drop2 I D ∪
      (safeFlags I D r u \ drop3 I D) ∪ (badPt0 I D r u \ drop2 I D) ∪
      (eAlpha I D r u \ drop3 I D) ∪ (eBeta I D r u \ drop3 I D) := by
  classical
  rintro ⟨p, w⟩ he
  unfold Pos at he
  rw [Finset.mem_filter] at he
  obtain ⟨-, hpw, j, hpu, hval⟩ := he
  simp only [Finset.mem_union, Finset.mem_sdiff]
  by_cases h3 : (p, w) ∈ drop3 I D
  · tauto
  by_cases h2 : (p, w) ∈ drop2 I D
  · tauto
  have hsafe : ∀ b, JobAt D b w → ¬ Unsafe I D r u b w →
      Relation.ReflTransGen (TStep D (pt p)) (r j) b → (p, w) ∈ safeFlags I D r u := by
    intro b hj hs htop
    unfold safeFlags
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hpw, b, ⟨hj, hs⟩, j, hpu, htop⟩
  rcases h04 N I D J r u hstd j p w hpw hpu hval with h | ⟨b, htop, hb⟩
  · simp only [Finset.mem_union] at h
    tauto
  rcases hb with hm | ⟨t, H, hmix, hvs, hH⟩
  · have := hsafe b (Or.inl hm) (h05a N I D J r u hstd b w hm) htop
    tauto
  by_cases hu : Unsafe I D r u b w
  · have huj : UJob I D r u H w := ⟨b, t, hmix, hvs, hu⟩
    by_cases hpt : D.val (pt p) H = true
    · have : (p, w) ∈ badPt0 I D r u := by
        unfold badPt0
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hpw, H, huj, hpt⟩
      tauto
    · obtain ⟨g1, g, v, hw⟩ := h07c N I D J r u hstd H p w huj hpw hH (by simpa using hpt)
      by_cases hbeta : BetaAt I D r u v p w
      · have : (p, w) ∈ eBeta I D r u := by
          unfold eBeta
          exact Finset.mem_filter.2 ⟨Finset.mem_univ _, H, g1, g, v, hw, hbeta⟩
        tauto
      · have : (p, w) ∈ eAlpha I D r u := by
          unfold eAlpha
          exact Finset.mem_filter.2 ⟨Finset.mem_univ _, H, g1, g, v, hw, hbeta⟩
        tauto
  · have := hsafe b (Or.inr ⟨t, H, hmix, hvs⟩) hu htop
    tauto
theorem dagBound (h04 : CardT04) (h05a : CardT05a) (h05b : CardT05b) (h05c : CardT05c)
    (h06b : CardT06b) (h06c : CardT06c) (h07b : CardT07b) (h07c : CardT07c) (h10 : CardT10)
    (h12 : CardT12) (I : Fin N → Fin N → Prop) (D : Dag N) {J : ℕ}
    (r : Fin J → ℕ) (u : Fin J → Fin N) (hstd : Std I D r u) :
    (Pos I D r u).card ≤ 38 * D.size + 4 * N := by
  classical
  have hI : NoRect I := hstd.1
  have hwf : D.WF := hstd.2.1
  by_cases hdg : Degenerate I D r u
  · have hsub : Pos I D r u ⊆ allEdges I := by
      intro e he
      unfold Pos at he
      unfold allEdges
      rw [Finset.mem_filter] at he ⊢
      exact ⟨he.1, he.2.1⟩
    have := Finset.card_le_card hsub
    have := h06b N I D J r u hI hdg
    omega
  have hc := Finset.card_le_card (coverPos h04 h05a h07c I D r u hstd)
  have hR : ∀ h, (Rset I D r u h).card ≤ 5 := fun h =>
    Rich5.rich_le_five I hI _ (fun w hw => h10 N I D J r u hI hwf h w hw)
  have e1 := Deg1.pinnedA_card I hI D
  have e2 := served3_card I D
  have e3 : (drop3 I D).card ≤ 18 * (Deg1.XA D).card := Rich.t02_rich3 I hI D
  have e4 : (drop2 I D).card ≤
      8 * ((Deg1.XA D).card + (Deg1.AndA D).card + (Deg1.OrA D).card) := Rich.t02_rich2 I hI D
  have e5 := h06c N I D J r u hstd hdg
  have e6 := h07b N I D J r u hstd
  have e7 := h12 N I D J r u hstd hR
  have e8 := betaBound h05b I D r u hstd
  have e9 := h05c N I D J r u hwf
  have e10 := classes6 D
  have u1 := Finset.card_union_le (Deg1.pinnedA I D ∪ served3 I D ∪ drop3 I D ∪ drop2 I D ∪
      (safeFlags I D r u \ drop3 I D) ∪ (badPt0 I D r u \ drop2 I D) ∪
      (eAlpha I D r u \ drop3 I D)) (eBeta I D r u \ drop3 I D)
  have u2 := Finset.card_union_le (Deg1.pinnedA I D ∪ served3 I D ∪ drop3 I D ∪ drop2 I D ∪
      (safeFlags I D r u \ drop3 I D) ∪ (badPt0 I D r u \ drop2 I D))
      (eAlpha I D r u \ drop3 I D)
  have u3 := Finset.card_union_le (Deg1.pinnedA I D ∪ served3 I D ∪ drop3 I D ∪ drop2 I D ∪
      (safeFlags I D r u \ drop3 I D)) (badPt0 I D r u \ drop2 I D)
  have u4 := Finset.card_union_le (Deg1.pinnedA I D ∪ served3 I D ∪ drop3 I D ∪ drop2 I D)
      (safeFlags I D r u \ drop3 I D)
  have u5 := Finset.card_union_le (Deg1.pinnedA I D ∪ served3 I D ∪ drop3 I D) (drop2 I D)
  have u6 := Finset.card_union_le (Deg1.pinnedA I D ∪ served3 I D) (drop3 I D)
  have u7 := Finset.card_union_le (Deg1.pinnedA I D) (served3 I D)
  omega
theorem mem_Pos {I : Fin N → Fin N → Prop} {D : Dag N} {J : ℕ} {r : Fin J → ℕ}
    {u : Fin J → Fin N} {e : Fin N × Fin N} :
    e ∈ Pos I D r u ↔ I e.1 e.2 ∧ ∃ j, ¬ I e.1 (u j) ∧ D.val (ep e.1 e.2) (r j) = true := by
  classical
  unfold Pos
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
theorem singlePivot (h04 : CardT04) (h05a : CardT05a) (h05b : CardT05b) (h05c : CardT05c)
    (h06b : CardT06b) (h06c : CardT06c) (h07b : CardT07b) (h07c : CardT07c) (h10 : CardT10)
    (h12 : CardT12) : SinglePivotBound := by
  intro N Jn I _ Ckt fg lp hI hM hdeg hsnd
  classical
  have hwf0 : (ofCircuit N Ckt).WF := card03b_wf Ckt
  obtain ⟨D, hwf, hsz, -, hdg, hmono, -, -, hps, hcl⟩ := Clean3.t01_clean I (ofCircuit N Ckt) 3 hwf0
  have hd0 : ∀ j, (ofCircuit N Ckt).deg (fg j) ≤ 2 := fun j =>
    le_trans (card03d_deg Ckt hM (fg j)) (hdeg j)
  have hstd : Std I D fg lp := by
    refine ⟨hI, hwf, fun j => by rw [hdg]; exact hd0 j, fun j => ?_, hcl _⟩
    refine hps _ _ (by have := hd0 j; omega) ?_
    intro x hx hv
    rw [card03c_val Ckt hM] at hv
    exact hsnd j x hx hv
  have hsub : Finset.univ.filter (fun e2 : Fin N × Fin N => I e2.1 e2.2 ∧ ∃ jc : Fin Jn,
      ¬ I e2.1 (lp jc) ∧
      (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true
        else if vq = Fin.natAdd N e2.2 then true else false))).getD (fg jc) false = true) ⊆
      Pos I D fg lp := by
    rintro ⟨p, w⟩ hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨hpw, j, hpu, hacc⟩ := hx
    have hfun : (fun vq : Fin (N + N) => if vq = Fin.castAdd N p then true
        else if vq = Fin.natAdd N w then true else false) = ep p w := by
      rw [cv_ep_eq]
      funext k
      by_cases h1 : k = Fin.castAdd N p <;> by_cases h2 : k = Fin.natAdd N w <;> simp [h1, h2]
    rw [hfun, ← card03c_val Ckt hM] at hacc
    have hrw : D.val (ep p w) (fg j) = true := by
      have := hmono (ep p w) (fg j)
      rw [hacc] at this
      revert this; cases D.val (ep p w) (fg j) <;> decide
    exact mem_Pos.2 ⟨hpw, j, hpu, hrw⟩
  have h1 := Finset.card_le_card hsub
  have h2 := dagBound h04 h05a h05b h05c h06b h06c h07b h07c h10 h12 I D fg lp hstd
  have h3 : D.size = Ckt.size := by rw [hsz]; exact card03a_size Ckt
  rw [h3] at h2
  omega
theorem assembly (h04 : CardT04) (h05a : CardT05a) (h05b : CardT05b) (h05c : CardT05c)
    (h06b : CardT06b) (h06c : CardT06c) (h07b : CardT07b) (h07c : CardT07c) (h10 : CardT10)
    (h12 : CardT12) : ∀ (N Jn : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (Ckt : PEqualNP.CircuitLowerBounds.Circuit) (fg : Fin Jn → ℕ) (Wl : Fin Jn → Finset (Fin N)), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 Ckt → (∀ jd : Fin Jn, (Ckt.lineDegrees (N + N) (Finset.Ico N (N + N))).getD (fg jd) 0 ≤ 2) → (∀ (jb : Fin Jn) (zz : Fin (N + N) → Bool), (∃ uz ∈ Wl jb, ∀ pz : Fin N, I pz uz → zz (Fin.castAdd N pz) = false) → (Ckt.wires (List.ofFn zz)).getD (fg jb) false = true → ∃ (pa lb : Fin N), I pa lb ∧ zz (Fin.castAdd N pa) = true ∧ zz (Fin.natAdd N lb) = true) → (Finset.univ.filter (fun e2 : Fin N × Fin N => I e2.1 e2.2 ∧ ∃ jc : Fin Jn, (∃ uc ∈ Wl jc, ¬ I e2.1 uc) ∧ (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fg jc) false = true)).card ≤ 192 * (Ckt.size + Jn) + 8 * N :=
  of_single_pivot (singlePivot h04 h05a h05b h05c h06b h06c h07b h07c h10 h12)
end Plan
end PEqualNP.Outside.L_meta_1321
namespace PEqualNP.Outside.L_meta_1321
open PEqualNP PEqualNP.MetaComplexity
namespace SafeCount
open Deg2
variable {N : ℕ}
def UpperLabel (D : Dag N) (g f v : ℕ) : Prop :=
  (D.gateAt g = some (.and f v) ∨ D.gateAt g = some (.and v f)) ∧
    D.deg f = 0 ∧ D.deg v = 2
def AndCharge (I : Fin N → Fin N → Prop) (D : Dag N) (T : ℕ → Finset (Fin N))
    (g : ℕ) (e : Fin N × Fin N) : Prop :=
  ∃ f v, UpperLabel D g f v ∧ (T v).card ≤ 2 ∧ e.2 ∈ T v ∧
    e.1 ∈ D.alive f ∩ ptsOn I e.2 ∧ (D.alive f ∩ ptsOn I e.2).card ≤ 3
def OrCharge (I : Fin N → Fin N → Prop) (D : Dag N) (T : ℕ → Finset (Fin N))
    (g : ℕ) (e : Fin N × Fin N) : Prop :=
  T g ⊆ pencil I e.1 ∧ 3 ≤ (T g).card ∧
    ∃ c, D.Kid g c ∧ e.2 ∈ T c ∧ (T c).card ≤ 2
theorem upperLabel_unique {D : Dag N} {g f v a b : ℕ}
    (h : UpperLabel D g f v) (k : UpperLabel D g a b) : f = a ∧ v = b := by
  obtain ⟨hg, hf, hv⟩ := h
  obtain ⟨kg, ka, kb⟩ := k
  rcases hg with hg | hg <;> rcases kg with kg | kg <;> rw [hg] at kg <;>
    simp only [Option.some.injEq, G.and.injEq] at kg <;> obtain ⟨rfl, rfl⟩ := kg <;>
    first | exact ⟨rfl,rfl⟩ | omega
theorem card_and_fibre (I : Fin N → Fin N → Prop) (D : Dag N) (T : ℕ → Finset (Fin N))
    (g : ℕ) (S : Finset (Fin N × Fin N)) (h : ∀ e ∈ S, AndCharge I D T g e) :
    S.card ≤ 6 := by
  classical
  by_cases hn : S.Nonempty
  · obtain ⟨e0, he0⟩ := hn
    obtain ⟨a, b, hab, hb, -⟩ := h e0 he0
    let F (w : Fin N) : Finset (Fin N × Fin N) :=
      if (D.alive a ∩ ptsOn I w).card ≤ 3 then
        (D.alive a ∩ ptsOn I w).image (fun p => (p, w)) else ∅
    have hF (w : Fin N) : (F w).card ≤ 3 := by
      unfold F
      split
      · exact Finset.card_image_le.trans (by assumption)
      · simp
    have hs : S ⊆ (T b).biUnion F := by
      intro e he
      obtain ⟨f, v, hfv, -, hw, hp, hle⟩ := h e he
      obtain ⟨rfl, rfl⟩ := upperLabel_unique hfv hab
      refine Finset.mem_biUnion.mpr ⟨e.2, hw, ?_⟩
      simp only [F, ite_eq_left_of_eq_true _ _ (eq_true hle), Finset.mem_image]
      exact ⟨e.1, hp, rfl⟩
    have hh := Finset.card_biUnion_le_card_mul (T b) F 3 (fun w _ => hF w)
    have := Finset.card_le_card hs
    omega
  · rw [Finset.not_nonempty_iff_eq_empty.mp hn]
    simp
theorem card_or_fibre (I : Fin N → Fin N → Prop) (hI : NoRect I) (D : Dag N)
    (T : ℕ → Finset (Fin N)) (g : ℕ) (S : Finset (Fin N × Fin N))
    (h : ∀ e ∈ S, OrCharge I D T g e) : S.card ≤ 4 := by
  classical
  by_cases hn : S.Nonempty
  · obtain ⟨e0, he0⟩ := hn
    obtain ⟨hpin, hbig, -⟩ := h e0 he0
    obtain ⟨w, hw, z, hz, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < (T g).card)
    let F (c : ℕ) : Finset (Fin N × Fin N) :=
      if (T c).card ≤ 2 then (T c).image (fun l => (e0.1, l)) else ∅
    have hF (c : ℕ) : (F c).card ≤ 2 := by
      unfold F
      split
      · exact Finset.card_image_le.trans (by assumption)
      · simp
    have hs : S ⊆ (circKids D g).biUnion F := by
      intro e he
      obtain ⟨hpin', -, c, hkid, hc, hle⟩ := h e he
      have hp : e0.1 = e.1 := by
        by_contra hdiff
        have inc := fun {p l} (hm : l ∈ pencil I p) => (Finset.mem_filter.mp hm).2
        exact hI e0.1 e.1 w z hdiff hne
          ⟨inc (hpin hw), inc (hpin hz), inc (hpin' hw), inc (hpin' hz)⟩
      refine Finset.mem_biUnion.mpr ⟨c, circKids_mem hkid, ?_⟩
      simp only [F, ite_eq_left_of_eq_true _ _ (eq_true hle), Finset.mem_image]
      exact ⟨e.2, hc, Prod.ext hp rfl⟩
    have hh := Finset.card_biUnion_le_card_mul (circKids D g) F 2 (fun c _ => hF c)
    have := circKids_card D g
    have := Finset.card_le_card hs
    omega
  · rw [Finset.not_nonempty_iff_eq_empty.mp hn]
    simp
theorem card_safe (I : Fin N → Fin N → Prop) (hI : NoRect I) (D : Dag N)
    (T : ℕ → Finset (Fin N)) (As Os : Finset ℕ) (S : Finset (Fin N × Fin N))
    (hcharge : ∀ e ∈ S, (∃ g ∈ As, AndCharge I D T g e) ∨
      (∃ g ∈ Os, OrCharge I D T g e)) : S.card ≤ 6 * As.card + 4 * Os.card := by
  classical
  let A (g : ℕ) := S.filter (AndCharge I D T g)
  let O (g : ℕ) := S.filter (OrCharge I D T g)
  have ha (g : ℕ) : (A g).card ≤ 6 :=
    card_and_fibre I D T g _ (fun _ he => (Finset.mem_filter.mp he).2)
  have ho (g : ℕ) : (O g).card ≤ 4 :=
    card_or_fibre I hI D T g _ (fun _ he => (Finset.mem_filter.mp he).2)
  have hs : S ⊆ As.biUnion A ∪ Os.biUnion O := by
    intro e he
    rcases hcharge e he with ⟨g, hg, hh⟩ | ⟨g, hg, hh⟩
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨g, hg, Finset.mem_filter.mpr ⟨he, hh⟩⟩)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨g, hg, Finset.mem_filter.mpr ⟨he, hh⟩⟩)
  have := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
  have := Finset.card_biUnion_le_card_mul As A 6 (fun g _ => ha g)
  have := Finset.card_biUnion_le_card_mul Os O 4 (fun g _ => ho g)
  omega
end SafeCount
end PEqualNP.Outside.L_meta_1321
namespace PEqualNP.Outside.L_meta_1321
open PEqualNP PEqualNP.MetaComplexity
namespace AlphaCount
open Deg2
variable {N : ℕ}
def row (E : ℕ → Finset (Fin N × Fin N)) (g : ℕ) (w : Fin N) : Finset (Fin N) :=
  Finset.univ.filter (fun p => (p, w) ∈ E g)
private def pack (s : Finset (Fin N)) (w : Fin N) (k : ℕ) : Finset (Fin N × Fin N) :=
  if s.card ≤ k then s.image (fun p => (p, w)) else ∅
private theorem pack_card (s : Finset (Fin N)) (w : Fin N) (k : ℕ) :
    (pack s w k).card ≤ k := by
  unfold pack
  split_ifs with h
  · exact Finset.card_image_le.trans h
  · simp
private theorem mem_pack {s : Finset (Fin N)} {p w : Fin N} {k : ℕ}
    (hp : p ∈ s) (hk : s.card ≤ k) : (p, w) ∈ pack s w k := by
  rw [pack, ite_eq_left hk]
  exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
theorem alpha_card {J : Type*} (jobs : Finset J) (H : J → ℕ) (target : J → Fin N)
    (I : Fin N → Fin N → Prop) (D : Dag N) (As Os : Finset ℕ)
    (E : ℕ → Finset (Fin N × Fin N)) (R : ℕ → Finset (Fin N))
    (hrich : ∀ g, (R g).card ≤ 5)
    (hsparse : ∀ g w, w ∉ R g → (row E g w).card ≤ 2)
    (flags : Finset (Fin N × Fin N))
    (hclass : ∀ p w, (p, w) ∈ flags →
      (∃ j ∈ jobs, w = target j ∧ (p, w) ∈ E (H j) ∧ w ∉ R (H j)) ∨
      (∃ g ∈ As, w ∈ R g ∧ ∃ f c, D.LabAnd g f c ∧ p ∈ D.alive f ∧ I p w ∧
        (D.alive f ∩ ptsOn I w).card ≤ 3) ∨
      (∃ g ∈ Os, w ∈ R g ∧ ∃ c, D.Kid g c ∧ (p, w) ∈ E c ∧ w ∉ R c)) :
    flags.card ≤ 2 * jobs.card + 15 * As.card + 20 * Os.card := by
  classical
  let small := fun g w => pack (row E g w) w 2
  have hsmall {p w : Fin N} {g : ℕ} (hm : (p, w) ∈ E g) (hn : w ∉ R g) :
      (p, w) ∈ small g w :=
    mem_pack (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩) (hsparse g w hn)
  let byJob := jobs.biUnion (fun j => small (H j) (target j))
  have hjobs : byJob.card ≤ 2 * jobs.card := by
    rw [mul_comm]
    exact Finset.card_biUnion_le_card_mul _ _ 2 (fun j _ => pack_card _ _ _)
  let label := fun g => if h : ∃ f c, D.LabAnd g f c then h.choose else 0
  have hlabel {g f c : ℕ} (hl : D.LabAnd g f c) : label g = f := by
    have h : ∃ a b, D.LabAnd g a b := ⟨f, c, hl⟩
    simp only [label, dite_eq_left h]
    obtain ⟨b, hb⟩ := h.choose_spec
    exact (Api.labAnd_unique hb hl).1
  let byAnd := As.biUnion (fun g => (R g).biUnion (fun w =>
    pack (D.alive (label g) ∩ ptsOn I w) w 3))
  have hands : byAnd.card ≤ 15 * As.card := by
    rw [mul_comm]
    refine Finset.card_biUnion_le_card_mul _ _ 15 ?_
    intro g _
    exact (Finset.card_biUnion_le_card_mul _ _ 3 (fun w _ => pack_card _ w 3)).trans
      (Nat.mul_le_mul_right 3 (hrich g))
  let byOr := Os.biUnion (fun g => (R g).biUnion (fun w =>
    (circKids D g).biUnion (fun c => small c w)))
  have hors : byOr.card ≤ 20 * Os.card := by
    rw [mul_comm]
    refine Finset.card_biUnion_le_card_mul _ _ 20 ?_
    intro g _
    refine (Finset.card_biUnion_le_card_mul _ _ 4 ?_).trans (Nat.mul_le_mul_right 4 (hrich g))
    intro w _
    exact (Finset.card_biUnion_le_card_mul _ _ 2 (fun c _ => pack_card _ w 2)).trans
      (Nat.mul_le_mul_right 2 (circKids_card D g))
  have hcover : flags ⊆ (byJob ∪ byAnd) ∪ byOr := by
    rintro ⟨p, w⟩ hpw
    rcases hclass p w hpw with hj | ha | ho
    · obtain ⟨j, hj, rfl, he, hn⟩ := hj
      exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_biUnion.mpr ⟨j, hj, hsmall he hn⟩))
    · obtain ⟨g, hg, hw, f, c, hl, hp, hi, hk⟩ := ha
      apply Finset.mem_union_left
      apply Finset.mem_union_right
      refine Finset.mem_biUnion.mpr ⟨g, hg, Finset.mem_biUnion.mpr ⟨w, hw, ?_⟩⟩
      rw [hlabel hl]
      exact mem_pack (Finset.mem_inter.mpr ⟨hp, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩) hk
    · obtain ⟨g, hg, hw, c, hc, he, hn⟩ := ho
      apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr ⟨g, hg, Finset.mem_biUnion.mpr ⟨w, hw,
        Finset.mem_biUnion.mpr ⟨c, circKids_mem hc, hsmall he hn⟩⟩⟩
  have hab := Finset.card_union_le byJob byAnd
  have habc := Finset.card_union_le (byJob ∪ byAnd) byOr
  have h := Finset.card_le_card hcover
  omega
end AlphaCount
end PEqualNP.Outside.L_meta_1321
namespace PEqualNP.Outside.L_meta_1321
open PEqualNP PEqualNP.MetaComplexity
namespace TTerm
open Deg2 Deg2.Api Deg2.Bridge
variable {N J : ℕ} {I : Fin N → Fin N → Prop} {D : Dag N} {r : Fin J → ℕ} {u : Fin J → Fin N}
private theorem mix_degree {b t H : ℕ} (wf : D.WF) (m : Plan.MixAnd D b t H) : D.deg b = 2 := by
  obtain ⟨g | g, dt, dH⟩ := m <;>
    rw [Forms.deg_and g (wf _ _ g _ (by simp [G.kids])) (wf _ _ g _ (by simp [G.kids])), dt, dH]
private theorem terminal_no_or {b c : ℕ} {w : Fin N} (job : Plan.JobAt D b w) :
    ¬ Plan.TOr D b c := by
  rintro ⟨⟨x,y,g⟩, db, _⟩
  rcases job with ⟨d, _⟩ | ⟨t,H,⟨g' | g', _, _⟩, _⟩
  · omega
  all_goals rw [g] at g'; cases g'
theorem card_terminal {b : ℕ} {w : Fin N} (wf : D.WF) (job : Plan.JobAt D b w) :
    (Plan.Tset I D r u b).card ≤ 2 := by
  classical
  have localJob : ∀ k ∈ Plan.Tset I D r u b, Plan.JobAt D b k := by
    intro k hk
    obtain ⟨c, sc, path⟩ := (Finset.mem_filter.mp hk).2
    rcases path.cases_head with rfl | ⟨_, st, _⟩
    · exact sc.1
    · exact (terminal_no_or job st).elim
  rcases job with mark | ⟨t,H,m,v⟩
  · have sub : Plan.Tset I D r u b ⊆ {w} := by
      intro k hk
      rcases localJob k hk with mk | ⟨_,_,m',_⟩
      · simpa [← mark.2] using (show k ∈ D.Vstar b by simp [mk.2])
      · have := mix_degree wf m'
        have := mark.1
        omega
    exact (Finset.card_le_card sub).trans (by simp)
  · let f (a : ℕ) : Fin N := if ex : ∃ k, D.Vstar a = {k} then ex.choose else w
    have single {a : ℕ} {k : Fin N} (sk : D.Vstar a = {k}) : f a = k := by
      have ex : ∃ l, D.Vstar a = {l} := ⟨_,sk⟩
      simp only [f, dite_eq_left ex]
      simpa using ex.choose_spec.symm.trans sk
    have sub : Plan.Tset I D r u b ⊆ ({t,H} : Finset ℕ).image f := by
      intro k hk
      rcases localJob k hk with mk | ⟨t',H',m',sk⟩
      · have := mix_degree wf m
        have := mk.1
        omega
      · refine Finset.mem_image.mpr ⟨t', ?_, single sk⟩
        rcases m.1 with g | g <;> rcases m'.1 with g' | g' <;>
          rw [g] at g' <;> cases g' <;> simp
    exact (Finset.card_le_card sub).trans (Finset.card_image_le.trans Finset.card_le_two)
theorem source_pencil {j : Fin J} {p : Fin N} {h : ℕ}
    (reach : Relation.ReflTransGen (Plan.TStep D (pt p)) (r j) h) (hoff : ¬ I p (u j)) :
    Plan.Tset I D r u h ⊆ pencil I p := by
  classical
  intro k hk
  obtain ⟨b, safe, path⟩ := (Finset.mem_filter.mp hk).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  by_contra hnot
  apply safe.2
  refine ⟨j, p, hnot, hoff, reach.trans ?_⟩
  exact Relation.ReflTransGen.mono (fun _ _ st => Or.inl st) _ _ path
end TTerm
end PEqualNP.Outside.L_meta_1321
namespace PEqualNP.Outside.L_meta_1321
open PEqualNP PEqualNP.MetaComplexity
namespace SafeWrap
open Deg2 Plan
variable {N : ℕ}
private theorem liftBare {D : Dag N} {a b : ℕ} (x : Fin (N+N) → Bool)
    (h : Relation.ReflTransGen (TOr D) a b) : Relation.ReflTransGen (TStep D x) a b := by
  induction h with
  | refl => exact .refl
  | tail _ e ih => exact ih.tail (Or.inl e)
private theorem lastLabel {D : Dag N} {x : Fin (N+N) → Bool} {a b : ℕ}
    (h : Relation.ReflTransGen (TStep D x) a b) :
    Relation.ReflTransGen (TOr D) a b ∨
      ∃ g f v, Relation.ReflTransGen (TStep D x) a g ∧ TLab D g f v ∧
        D.val x f = true ∧ Relation.ReflTransGen (TOr D) v b := by
  induction h with
  | refl => exact Or.inl .refl
  | @tail g c prev step ih =>
    rcases step with hbare | ⟨f, hlabel, hf⟩
    · rcases ih with hprev | ⟨t, f, v, hp, hl, hv, hvc⟩
      · exact Or.inl (hprev.tail hbare)
      · exact Or.inr ⟨t, f, v, hp, hl, hv, hvc.tail hbare⟩
    · exact Or.inr ⟨g, f, c, prev, hlabel, hf, .refl⟩
private theorem cut {α : Type*} {R : α → α → Prop} (P : α → Prop) {a b : α}
    (h : Relation.ReflTransGen R a b) : P a → ¬P b →
    ∃ g c, Relation.ReflTransGen R a g ∧ R g c ∧ P g ∧ ¬P c ∧ Relation.ReflTransGen R c b := by
  classical
  induction h with
  | refl => exact fun h hn => False.elim (hn h)
  | @tail g c prev step ih =>
    intro ha hc
    by_cases hg : P g
    · exact ⟨g, c, prev, step, hg, hc, .refl⟩
    · obtain ⟨t,v,hp,hl,ht,hv,hr⟩ := ih ha hg
      exact ⟨t,v,hp,hl,ht,hv,hr.tail step⟩
private theorem topLabel_mem {D : Dag N} (wf : D.WF) {g f v : ℕ} (h : TLab D g f v) :
    g ∈ VA D := by
  classical
  obtain ⟨hgate, hf, hv⟩ := h
  obtain hfv | hvf := hgate
  · have hdeg := Forms.deg_and hfv (wf _ _ hfv f (by simp [G.kids])) (wf _ _ hfv v (by simp [G.kids]))
    exact Finset.mem_filter.mpr ⟨Deg1.mem_allG hfv, by omega, f, v, Or.inl hfv, hf, hv⟩
  · have hdeg := Forms.deg_and hvf (wf _ _ hvf v (by simp [G.kids])) (wf _ _ hvf f (by simp [G.kids]))
    exact Finset.mem_filter.mpr ⟨Deg1.mem_allG hvf, by omega, f, v, Or.inr hvf, hf, hv⟩
theorem t06c : CardT06c := by
  classical
  intro N I D J r u hstd hnd
  let T := Tset I D r u
  let S := safeFlags I D r u \ drop3 I D
  suffices h : S.card ≤ 6*(VA D).card + 4*(UA D).card by
    dsimp only [S] at h
    omega
  apply SafeCount.card_safe I hstd.1 D T
  rintro ⟨p,w⟩ he
  obtain ⟨hs, hn⟩ := Finset.mem_sdiff.mp he
  obtain ⟨hi, b, hb, j, hpu, path⟩ := (Finset.mem_filter.mp hs).2
  have has : ∀ a, Relation.ReflTransGen (TOr D) a b → w ∈ T a :=
    fun _ h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, b, hb, h⟩
  obtain naked | ⟨g, f, v, pathg, glab, hval, suffix⟩ := lastLabel path
  · exact False.elim (hnd ⟨j,b,w,hb,fun h => hpu (h ▸ hi),naked⟩)
  have hg : g ∈ VA D := topLabel_mem hstd.2.1 glab
  have hp : p ∈ D.alive f := Forms.mem_alive.mpr hval
  by_cases small : (T v).card ≤ 2
  · refine Or.inl ⟨g, hg, f, v, glab, small, has v suffix,
      Finset.mem_inter.mpr ⟨hp, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩, ?_⟩
    by_contra! hbig
    apply hn
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi, f, by rw [glab.2.1], ?_, hp, by omega⟩
    exact hstd.2.2.2.2 g (Finset.mem_filter.mp hg).1 f v glab.1 glab.2.1 (by rw [glab.2.2]; decide)
  · have terminal : (T b).card ≤ 2 := TTerm.card_terminal hstd.2.1 hb.1
    obtain ⟨o, c, vor, oc, ho, hc, cb⟩ := cut (fun i => 3 ≤ (T i).card) suffix (by omega) (by omega)
    have hOo : o ∈ UA D := by
      obtain ⟨a, d, hgate⟩ := oc.1
      exact Finset.mem_filter.mpr ⟨Deg1.mem_allG hgate, oc.2.1, a, d, hgate⟩
    have pref := (pathg.tail (Or.inr ⟨f, glab, hval⟩)).trans (liftBare (pt p) vor)
    exact Or.inr ⟨o, hOo, TTerm.source_pencil pref hpu, ho, c, oc.2.2.1, has c cb, by omega⟩
end SafeWrap
end PEqualNP.Outside.L_meta_1321
namespace PEqualNP.Outside.L_meta_1321
open PEqualNP PEqualNP.MetaComplexity
namespace AlphaWrap
open Deg2 Deg2.Api Deg2.Bridge Plan
private theorem path_exit {α : Type*} {s : α → α → Prop} (P : α → Prop)
    {a b : α} (hab : Relation.ReflTransGen s a b) (ha : P a) (hb : ¬ P b) :
    ∃ i c, Relation.ReflTransGen s a i ∧ P i ∧ s i c ∧ ¬ P c ∧
      Relation.ReflTransGen s c b := by
  induction hab with
  | refl => exact (hb ha).elim
  | @tail i b hai hib ih =>
    by_cases hi : P i
    · exact ⟨i, b, hai, hi, hib, hb, .refl⟩
    · obtain ⟨k, c, hak, hk, hkc, hc, hci⟩ := ih hi
      exact ⟨k, c, hak, hk, hkc, hc, hci.tail hib⟩
theorem t12 : Plan.CardT12 := by
  classical
  intro N I D J r u hstd hrich
  obtain ⟨_, hwf, _, _, hclean⟩ := hstd
  apply AlphaCount.alpha_card (ujobs I D r u) Prod.fst Prod.snd I D
    (Deg1.AndA D) (Deg1.OrA D) (Eset I D r u) (Rset I D r u) hrich
  · intro i w hw
    by_contra! h
    apply hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
  · intro p w hpw
    obtain ⟨halpha, hkeep⟩ := Finset.mem_sdiff.mp hpw
    obtain ⟨H, g1, g, v, hlw, hnb⟩ := (Finset.mem_filter.mp halpha).2
    have he {i} (hHi : Relation.ReflTransGen (OStep D) H i)
        (hi1 : Relation.ReflTransGen (OStep D) i g1) : (p, w) ∈ Eset I D r u i :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, H, g1, g, v, hlw, hnb, hHi, hi1⟩
    obtain ⟨hjob, hI, hpath, ⟨f, c, hlab, hf⟩, _⟩ := hlw
    by_cases hH : w ∈ Rset I D r u H
    · by_cases h1 : w ∈ Rset I D r u g1
      · right; left
        have hg1 : g1 ∈ Deg1.AndA D := by
          obtain ⟨hh, hf0, hc1⟩ := hlab
          rcases hh with hh | hh <;>
            refine Finset.mem_filter.mpr ⟨Deg1.mem_allG hh, ?_, _, _, hh⟩ <;>
            rw [circ_deg_and D hh (hwf _ _ hh _ (by simp [G.kids]))
              (hwf _ _ hh _ (by simp [G.kids])), hf0, hc1]
        have hp : p ∈ D.alive f := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf⟩
        refine ⟨g1, hg1, h1, f, c, hlab, hp, hI, ?_⟩
        by_contra! hk
        have hdead := hclean g1 (Finset.mem_filter.mp hg1).1 f c hlab.1 hlab.2.1
          (by rw [hlab.2.2])
        exact hkeep (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hI, f,
          Nat.le_of_eq hlab.2.1, hdead, hp, hk⟩)
      · right; right
        obtain ⟨i, c', hHi, hi, hstep, hc', hc1⟩ :=
          path_exit (fun i => w ∈ Rset I D r u i) hpath hH h1
        obtain ⟨hor, hd, hkid⟩ := hstep
        obtain ⟨a, b, hab⟩ := hor
        exact ⟨i, Finset.mem_filter.mpr ⟨Deg1.mem_allG hab, hd, a, b, hab⟩, hi, c',
          hkid, he (hHi.tail ⟨⟨a, b, hab⟩, hd, hkid⟩) hc1, hc'⟩
    · left
      have hbound : H < N + N + D.size := by
        obtain ⟨b, t, ⟨hg, _, _⟩, _, _⟩ := hjob
        rcases hg with hg | hg <;>
          exact (hwf _ _ hg H (by simp [G.kids])).trans
            (Finset.mem_Ico.mp (Deg1.mem_allG hg)).2
      exact ⟨(H, w), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr hbound, Finset.mem_univ _⟩, hjob⟩,
        rfl, he .refl hpath, hH⟩
end AlphaWrap
end PEqualNP.Outside.L_meta_1321
namespace PEqualNP.Outside.L_meta_1321
open PEqualNP PEqualNP.MetaComplexity
namespace Honest
open Deg2 Deg2.Api Plan
variable {N : ℕ}
theorem tstep_kid {D : Dag N} (hwf : D.WF) {x : Fin (N + N) → Bool} {e c : ℕ}
    (h : TStep D x e c) : D.Kid e c := by
  rcases h with ⟨-, -, hk, -⟩ | ⟨f, ⟨hg, -, -⟩, -⟩
  · exact hk
  · rcases hg with hg | hg
    · exact circ_kid_of hg (by simp [G.kids]) (hwf e _ hg c (by simp [G.kids]))
    · exact circ_kid_of hg (by simp [G.kids]) (hwf e _ hg c (by simp [G.kids]))
theorem tstar_reach {D : Dag N} (hwf : D.WF) {x : Fin (N + N) → Bool} {r b : ℕ}
    (h : Relation.ReflTransGen (TStep D x) r b) : D.Reach r b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact ih.tail (tstep_kid hwf hs)
theorem tstar_val {D : Dag N} (hwf : D.WF) {x z : Fin (N + N) → Bool} {r b : ℕ}
    (hlab : ∀ f, D.deg f = 0 → D.val x f = true → D.val z f = true)
    (h : Relation.ReflTransGen (TStep D x) r b) : D.val z b = true → D.val z r = true := by
  induction h with
  | refl => exact id
  | @tail e c _ hs ih =>
    intro hc
    apply ih
    rcases hs with ⟨⟨a, a', hg⟩, -, ⟨g, hg', hcg, hce⟩, -⟩ | ⟨f, ⟨hg, hf0, -⟩, hfx⟩
    · rw [hg] at hg'
      cases hg'
      have ha := hwf _ _ hg a (by simp [G.kids])
      have ha' := hwf _ _ hg a' (by simp [G.kids])
      rw [Deg2.tr_val_or hg ha ha']
      simp only [G.kids, List.mem_cons, List.not_mem_nil, or_false] at hcg
      rcases hcg with rfl | rfl <;> simp [hc]
    · have hfz := hlab f hf0 hfx
      rcases hg with hg | hg
      · have ha := hwf _ _ hg f (by simp [G.kids])
        have hb := hwf _ _ hg c (by simp [G.kids])
        rw [Deg2.tr_val_and hg ha hb]; simp [hc, hfz]
      · have ha := hwf _ _ hg c (by simp [G.kids])
        have hb := hwf _ _ hg f (by simp [G.kids])
        rw [Deg2.tr_val_and hg ha hb]; simp [hc, hfz]
theorem pt_castAdd (p q : Fin N) : pt p (Fin.castAdd N q) = decide (q = p) := by
  unfold pt; rw [Forms.inp_castAdd]; simp
theorem pt_natAdd (p l : Fin N) : pt p (Fin.natAdd N l) = false := by
  unfold pt; rw [Forms.inp_natAdd]; simp
theorem honest_of_wires (I : Fin N → Fin N → Prop) (D : Dag N) (p : Fin N) (ws : List ℕ)
    (honly : ∀ z : Fin (N + N) → Bool, (∀ q, z (Fin.castAdd N q) = decide (q = p)) →
      (∀ t ∈ ws, D.val z t = true) →
        ∃ a l, I a l ∧ z (Fin.castAdd N a) = true ∧ z (Fin.natAdd N l) = true) :
    ∃ t ∈ ws, IsHonest I (fun x => D.val x t) p := by
  classical
  by_contra hno
  push Not at hno
  let z : Fin (N + N) → Bool := inp {p} (Finset.univ.filter (fun l => ¬ I p l))
  have hzp : ∀ q, z (Fin.castAdd N q) = decide (q = p) := by
    intro q; simp only [z, Forms.inp_castAdd, Finset.mem_singleton]
  have hall : ∀ t ∈ ws, D.val z t = true := by
    intro t ht
    have hn := hno t ht
    unfold IsHonest at hn
    by_cases h0 : D.val (pt p) t = false
    · have h1 : ¬ ∀ u, D.val (ep p u) t = true → I p u := fun h => hn ⟨h0, h⟩
      push Not at h1
      obtain ⟨u, hu, hnu⟩ := h1
      have hle : ep p u ≤ z := by
        unfold ep
        apply Forms.inp_mono
        intro l hl
        rw [Finset.mem_singleton] at hl
        subst hl
        simp [hnu]
      have := api_val_mono D t hle
      rw [hu] at this
      exact HonestFactor.eq_true_of_true_le' this
    · have h1 : D.val (pt p) t = true := by simpa using h0
      have hle : pt p ≤ z := by
        unfold pt
        exact Forms.inp_mono (Finset.empty_subset _)
      have := api_val_mono D t hle
      rw [h1] at this
      exact HonestFactor.eq_true_of_true_le' this
  obtain ⟨a, l, hal, ha, hl⟩ := honly z hzp hall
  rw [hzp] at ha
  have hap : a = p := by simpa using ha
  subst hap
  simp only [z, Forms.inp_natAdd, Finset.mem_filter, Finset.mem_univ, true_and,
    decide_eq_true_eq] at hl
  exact hl hal
theorem no_drop {I : Fin N → Fin N → Prop} {D : Dag N} (hwf : D.WF) {r c : ℕ} {u p w : Fin N}
    (hs : Clean3.PivotSound I D r u) (hpu : ¬ I p u)
    (hT : Relation.ReflTransGen (TStep D (pt p)) r c) (hc0 : D.deg c = 0)
    (hv : D.val (ep p w) c = true) : False := by
  have hv' : D.val (pt p) c = true := by
    rw [← api_val_xonly D hc0 (fun q => circ_ep_pts p w q)]; exact hv
  have hr := tstar_val hwf (fun f _ h => h) hT hv'
  obtain ⟨a, l, -, -, hl⟩ := hs (pt p) (fun q hq => by
    rw [pt_castAdd]; simp only [decide_eq_false_iff_not]; rintro rfl; exact hpu hq) hr
  rw [pt_natAdd] at hl
  exact Bool.false_ne_true hl
theorem sound_at_p {I : Fin N → Fin N → Prop} {D : Dag N} (hwf : D.WF) {r b : ℕ} {u p : Fin N}
    (hs : Clean3.PivotSound I D r u) (hpu : ¬ I p u)
    (hT : Relation.ReflTransGen (TStep D (pt p)) r b) (z : Fin (N + N) → Bool)
    (hz : ∀ q, z (Fin.castAdd N q) = decide (q = p)) (hb : D.val z b = true) :
    ∃ a l, I a l ∧ z (Fin.castAdd N a) = true ∧ z (Fin.natAdd N l) = true := by
  have hzr := tstar_val hwf (z := z) (fun f hf h => by
    rw [← api_val_xonly D hf (x := pt p) (y := z) (fun q => by rw [pt_castAdd, hz])]; exact h) hT hb
  exact hs z (fun q hq => by rw [hz]; simp only [decide_eq_false_iff_not]; rintro rfl; exact hpu hq) hzr
theorem t03_item (I : Fin N → Fin N → Prop) (D : Dag N) (hwf : D.WF) (r : ℕ) (u p w : Fin N)
    (hd : D.deg r ≤ 2) (hs : Clean3.PivotSound I D r u) (hpu : ¬ I p u)
    (hacc : D.val (ep p w) r = true) :
    ∃ b, Relation.ReflTransGen (TStep D (pt p)) r b ∧
      ((D.deg b = 1 ∧ D.val (ep p w) b = true ∧ IsHonest I (fun x => D.val x b) p) ∨
       ∃ t H, MixAnd D b t H ∧ D.val (ep p w) t = true ∧ D.val (ep p w) H = true ∧
         IsHonest I (fun x => D.val x t) p) := by
  classical
  suffices key : ∀ c, Relation.ReflTransGen (TStep D (pt p)) r c → D.val (ep p w) c = true →
      ∃ b, Relation.ReflTransGen (TStep D (pt p)) r b ∧
      ((D.deg b = 1 ∧ D.val (ep p w) b = true ∧ IsHonest I (fun x => D.val x b) p) ∨
       ∃ t H, MixAnd D b t H ∧ D.val (ep p w) t = true ∧ D.val (ep p w) H = true ∧
         IsHonest I (fun x => D.val x t) p) from key r Relation.ReflTransGen.refl hacc
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
  intro hT hv
  have hdc : D.deg c ≤ 2 := le_trans (api_reach_deg D (tstar_reach hwf hT)) hd
  by_cases h0 : D.deg c = 0
  · exact (no_drop hwf hs hpu hT h0 hv).elim
  by_cases h1 : D.deg c = 1
  · obtain ⟨t, ht, hh⟩ := honest_of_wires I D p [c] (fun z hz hall =>
      sound_at_p hwf hs hpu hT z hz (hall c (by simp)))
    simp only [List.mem_singleton] at ht
    subst ht
    exact ⟨t, hT, Or.inl ⟨h1, hv, hh⟩⟩
  have h2 : D.deg c = 2 := by omega
  obtain ⟨g, hg, -⟩ := Deg2.tr_gate_of_deg (D := D) (c := c) (by omega)
  cases g with
  | cst v => rw [Deg2.tr_deg_cst hg] at h2; omega
  | and a b =>
    have ha := hwf _ _ hg a (by simp [G.kids])
    have hb := hwf _ _ hg b (by simp [G.kids])
    have hdeg := Deg2.tr_deg_and hg ha hb
    rw [Deg2.tr_val_and hg ha hb, Bool.and_eq_true] at hv
    by_cases hab : D.deg a = 1 ∧ D.deg b = 1
    · obtain ⟨t, ht, hh⟩ := honest_of_wires I D p [a, b] (fun z hz hall =>
        sound_at_p hwf hs hpu hT z hz (by
          rw [Deg2.tr_val_and hg ha hb, hall a (by simp), hall b (by simp)]; rfl))
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · exact ⟨c, hT, Or.inr ⟨t, b, ⟨Or.inl hg, hab.1, hab.2⟩, hv.1, hv.2, hh⟩⟩
      · exact ⟨c, hT, Or.inr ⟨t, a, ⟨Or.inr hg, hab.2, hab.1⟩, hv.2, hv.1, hh⟩⟩
    · have hf : D.deg a = 0 ∨ D.deg b = 0 := by omega
      rcases hf with hf | hf
      · have hfp : D.val (pt p) a = true := by
          rw [← api_val_xonly D hf (fun q => circ_ep_pts p w q)]; exact hv.1
        exact ih b hb (hT.tail (Or.inr ⟨a, ⟨Or.inl hg, hf, by omega⟩, hfp⟩)) hv.2
      · have hfp : D.val (pt p) b = true := by
          rw [← api_val_xonly D hf (fun q => circ_ep_pts p w q)]; exact hv.2
        exact ih a ha (hT.tail (Or.inr ⟨b, ⟨Or.inr hg, hf, by omega⟩, hfp⟩)) hv.1
  | or a b =>
    have ha := hwf _ _ hg a (by simp [G.kids])
    have hb := hwf _ _ hg b (by simp [G.kids])
    rw [Deg2.tr_val_or hg ha hb, Bool.or_eq_true] at hv
    rcases hv with hv | hv
    · by_cases ha0 : D.deg a = 0
      · exfalso
        have hva : D.val (pt p) a = true := by
          rw [← api_val_xonly D ha0 (fun q => circ_ep_pts p w q)]; exact hv
        have hvc : D.val (ep p w) c = true := by
          rw [Deg2.tr_val_or hg ha hb, api_val_xonly D ha0 (fun q => circ_ep_pts p w q), hva]; rfl
        have hr := tstar_val hwf (fun f _ h => h) hT (by
          rw [Deg2.tr_val_or hg ha hb, hva]; rfl)
        obtain ⟨a', l, -, -, hl⟩ := hs (pt p) (fun q hq => by
          rw [pt_castAdd]; simp only [decide_eq_false_iff_not]; rintro rfl; exact hpu hq) hr
        rw [pt_natAdd] at hl
        exact Bool.false_ne_true hl
      · exact ih a ha (hT.tail (Or.inl ⟨⟨a, b, hg⟩, h2, circ_kid_of hg (by simp [G.kids]) ha,
          by omega⟩)) hv
    · by_cases hb0 : D.deg b = 0
      · exfalso
        have hvb : D.val (pt p) b = true := by
          rw [← api_val_xonly D hb0 (fun q => circ_ep_pts p w q)]; exact hv
        have hr := tstar_val hwf (fun f _ h => h) hT (by
          rw [Deg2.tr_val_or hg ha hb, hvb]; simp)
        obtain ⟨a', l, -, -, hl⟩ := hs (pt p) (fun q hq => by
          rw [pt_castAdd]; simp only [decide_eq_false_iff_not]; rintro rfl; exact hpu hq) hr
        rw [pt_natAdd] at hl
        exact Bool.false_ne_true hl
      · exact ih b hb (hT.tail (Or.inl ⟨⟨a, b, hg⟩, h2, circ_kid_of hg (by simp [G.kids]) hb,
          by omega⟩)) hv
theorem served3_card (I : Fin N → Fin N → Prop) (D : Dag N) :
    (served3 I D).card ≤ 3 * (Deg1.AndA D).card := by
  classical
  let T : ℕ → Finset (Fin N × Fin N) := fun g => Finset.univ.filter (fun e => ∃ f v,
    D.LabAnd g f v ∧ D.Vstar v = {e.2} ∧ e.1 ∈ D.alive f ∧ I e.1 e.2 ∧
      (D.alive f ∩ ptsOn I e.2).card ≤ 3)
  have hsub : served3 I D ⊆ (Deg1.AndA D).biUnion T := by
    intro e he
    unfold served3 at he
    rw [Finset.mem_filter] at he
    obtain ⟨-, g, hg, f, v, h1, h2, h3, h4, h5⟩ := he
    rw [Finset.mem_biUnion]
    exact ⟨g, hg, Finset.mem_filter.2 ⟨Finset.mem_univ _, f, v, h1, h2, h3, h4, h5⟩⟩
  have hT : ∀ g ∈ Deg1.AndA D, (T g).card ≤ 3 := by
    intro g _
    by_cases hne : (T g).Nonempty
    · obtain ⟨e0, he0⟩ := hne
      obtain ⟨-, f0, v0, h1, h2, -, -, h5⟩ := Finset.mem_filter.1 he0
      have hsub' : T g ⊆ (D.alive f0 ∩ ptsOn I e0.2).image (fun p => (p, e0.2)) := by
        intro e he
        obtain ⟨-, f, v, k1, k2, k3, k4, -⟩ := Finset.mem_filter.1 he
        obtain ⟨rfl, rfl⟩ := labAnd_unique k1 h1
        have hw : e.2 = e0.2 := by
          rw [h2] at k2
          exact (Finset.singleton_inj.1 k2).symm
        rw [Finset.mem_image]
        refine ⟨e.1, Finset.mem_inter.2 ⟨k3, ?_⟩, ?_⟩
        · unfold ptsOn
          rw [Finset.mem_filter, ← hw]
          exact ⟨Finset.mem_univ _, k4⟩
        · ext <;> simp [hw]
      exact le_trans (Finset.card_le_card hsub') (le_trans Finset.card_image_le h5)
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne]; simp
  calc (served3 I D).card ≤ ((Deg1.AndA D).biUnion T).card := Finset.card_le_card hsub
    _ ≤ ∑ g ∈ Deg1.AndA D, (T g).card := Finset.card_biUnion_le
    _ ≤ ∑ _g ∈ Deg1.AndA D, 3 := Finset.sum_le_sum hT
    _ = 3 * (Deg1.AndA D).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
theorem t04_cover (I : Fin N → Fin N → Prop) (D : Dag N) (hwf : D.WF)
    (hcl : Clean3.CleanedD I D 3 (Deg1.allG D)) (t : ℕ) (p w : Fin N) (hpw : I p w)
    (ht1 : D.deg t = 1) (hh : IsHonest I (fun x => D.val x t) p)
    (htw : D.val (ep p w) t = true) :
    (p, w) ∈ Deg1.pinnedA I D ∪ served3 I D ∪ drop3 I D ∨ D.Vstar t = {w} := by
  classical
  obtain ⟨π, hπ, hπv, hlab, hpen⟩ := card06_honest_path I D t p w ht1 hh htw
  have hdeg : ∀ v ∈ π, D.deg v = 1 := fun v hv => (hπv v hv).1
  have hlen : 0 < π.length := by
    cases π with
    | nil => simp [Dag.IsPath] at hπ
    | cons _ _ => simp
  have hhead : π.getD 0 0 = t := by
    obtain ⟨hh0, -, -⟩ := hπ
    cases π with
    | nil => simp at hh0
    | cons c _ => simpa using hh0
  let P : ℕ → Prop := fun k => k + 1 < π.length ∧ ∃ f, D.LabAnd (π.getD k 0) f (π.getD (k + 1) 0)
  by_cases hex : ∃ k, P k
  · left
    simp only [Finset.mem_union]
    obtain ⟨k0, hk0⟩ := hex
    let K := Nat.findGreatest P π.length
    have hPK : P K := Nat.findGreatest_spec (P := P) (by have := hk0.1; omega) hk0
    have hmax : ∀ k, K < k → ¬ P k := by
      intro k hk hPk
      exact Nat.findGreatest_is_greatest hk (by have := hPk.1; omega) hPk
    obtain ⟨hK, f, hfl⟩ := hPK
    set e := π.getD K 0 with he
    set v := π.getD (K + 1) 0 with hv
    have hvr : D.VReach v w := by
      refine cv_vreach_suffix D hwf hπ hdeg (π.length - (K + 1) - 1) (K + 1) (by omega) ?_
      intro k f' hk hk' hl
      exact hmax k (by omega) ⟨hk', f', hl⟩
    have hvmem : v ∈ π := circ_getD_mem hK
    rcases cv_card_split (cv_vstar_mem hvr) with h2 | h1
    · left; left
      have hor := cv_isOr_of_card D hvr h2
      obtain ⟨a, b, hg⟩ := hor
      unfold Deg1.pinnedA
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, v,
        Finset.mem_filter.2 ⟨Deg1.mem_allG hg, hdeg v hvmem, ⟨a, b, hg⟩⟩,
        ⟨⟨a, b, hg⟩, hdeg v hvmem, h2, hpen v hvmem⟩, cv_vstar_mem hvr⟩
    · obtain ⟨hgate, hf0, -⟩ := hfl
      have hemem : e ∈ π := circ_getD_mem (by omega)
      have hgE : ∃ g, D.gateAt e = some g := by
        rcases hgate with h | h
        · exact ⟨_, h⟩
        · exact ⟨_, h⟩
      obtain ⟨gE, hgE⟩ := hgE
      have hEall : e ∈ Deg1.allG D := Deg1.mem_allG hgE
      have hAndA : e ∈ Deg1.AndA D := by
        unfold Deg1.AndA
        refine Finset.mem_filter.2 ⟨hEall, hdeg e hemem, ?_⟩
        rcases hgate with h | h
        · exact ⟨_, _, h⟩
        · exact ⟨_, _, h⟩
      have hdead := hcl e hEall f v hgate hf0 (by rw [hdeg v hvmem])
      have halive : p ∈ D.alive f := by
        unfold Dag.alive
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hlab K f hK ⟨hgate, hf0, hdeg v hvmem⟩⟩
      by_cases hle : (D.alive f ∩ ptsOn I w).card ≤ 3
      · left; right
        unfold served3
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, e, hAndA, f, v,
          ⟨hgate, hf0, hdeg v hvmem⟩, h1, halive, hpw, hle⟩
      · right
        unfold drop3 Rich.rich
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hpw, f, by omega, hdead, halive,
          by show 3 + 1 ≤ (D.alive f ∩ ptsOn I w).card; omega⟩
  · have htv : D.VReach t w := by
      have := cv_vreach_suffix D hwf hπ hdeg (π.length - 1) 0 (by omega)
        (fun k f' _ hk' hl => hex ⟨k, hk', f', hl⟩)
      rwa [hhead] at this
    have htmem : t ∈ π := by rw [← hhead]; exact circ_getD_mem hlen
    rcases cv_card_split (cv_vstar_mem htv) with h2 | h1
    · left
      simp only [Finset.mem_union]
      left; left
      obtain ⟨a, b, hg⟩ := cv_isOr_of_card D htv h2
      unfold Deg1.pinnedA
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, t,
        Finset.mem_filter.2 ⟨Deg1.mem_allG hg, ht1, ⟨a, b, hg⟩⟩,
        ⟨⟨a, b, hg⟩, ht1, h2, hpen t htmem⟩, cv_vstar_mem htv⟩
    · exact Or.inr h1
theorem tstar_rev {D : Dag N} (hwf : D.WF) {x z : Fin (N + N) → Bool} {a b : ℕ} (hxz : x ≤ z)
    (hT : Relation.ReflTransGen (TStep D x) a b) (hb : D.val z b = true) : D.val z a = true := tstar_val hwf (fun f _ hf => by
    have := api_val_mono D f hxz
    rw [hf] at this
    exact HonestFactor.eq_true_of_true_le' this) hT hb
theorem cardT04 : CardT04 := by
  intro N I D J r u hstd j p w hpw hpu hacc
  obtain ⟨-, hwf, hdeg, hps, hcl⟩ := hstd
  obtain ⟨b, hT, hb⟩ := t03_item I D hwf (r j) (u j) p w (hdeg j) (hps j) hpu hacc
  rcases hb with ⟨hb1, hbw, hh⟩ | ⟨t, H, hmix, htw, hHw, hh⟩
  · rcases t04_cover I D hwf hcl b p w hpw hb1 hh hbw with hc | hv
    · exact Or.inl hc
    · exact Or.inr ⟨b, hT, Or.inl ⟨hb1, hv⟩⟩
  · rcases t04_cover I D hwf hcl t p w hpw hmix.2.1 hh htw with hc | hv
    · exact Or.inl hc
    · exact Or.inr ⟨b, hT, Or.inr ⟨t, H, hmix, hv, hHw⟩⟩
end Honest
end PEqualNP.Outside.L_meta_1321
namespace PEqualNP.Outside.L_meta_1321
open PEqualNP PEqualNP.MetaComplexity
namespace Splice
open Deg2 Plan
variable {N J : ℕ}
theorem t06b : CardT06b := by
  classical
  intro n I D j r u hI h
  obtain ⟨a,b,k,hs,_,hp⟩ := h
  have hc (p : Fin n) : I p k ∨ I p (u a) := by
    by_contra! hn
    apply hs.2
    refine ⟨a,p,hn.1,hn.2,?_⟩
    clear hs
    induction hp with
    | refl => exact .refl
    | tail _ ht ih => exact ih.tail (Or.inl ht)
  simpa only [allEdges, edges] using Rich5.edges_le_four I hI k (u a) hc
private theorem bareLo {D : Dag N} (p : Fin N) {a b : ℕ}
    (h : Relation.ReflTransGen (OStep D) a b) :
    Relation.ReflTransGen (Beta.LStep D (pt p)) a b := by
  induction h with
  | refl => exact .refl
  | tail _ ht ih =>
    obtain ⟨⟨x,y,ho⟩,_,hk⟩ := ht
    apply ih.tail
    refine ⟨hk,fun f hf => ?_⟩
    rcases hf.1 with hg|hg <;> rw [ho] at hg <;> cases hg
private theorem two_lines (I : Fin N → Fin N → Prop) (hI : NoRect I)
    (R : Finset (Fin N)) (l w u : Fin N) (hlw : l ≠ w) (hlu : l ≠ u)
    (hc : ∀ p ∈ R, I p l ∧ (I p w ∨ I p u)) : R.card ≤ 2 := by
  classical
  let A : Finset (Fin N) := {w,u}
  have sub : R ⊆ A.biUnion (fun t => ptsOn I l ∩ ptsOn I t) := by
    intro p hp
    obtain ⟨hl,ht⟩ := hc p hp
    rcases ht with hw|hu
    · exact Finset.mem_biUnion.mpr ⟨w,by simp [A],by simpa [ptsOn] using And.intro hl hw⟩
    · exact Finset.mem_biUnion.mpr ⟨u,by simp [A],by simpa [ptsOn] using And.intro hl hu⟩
  have hf := Finset.card_biUnion_le_card_mul A (fun t => ptsOn I l ∩ ptsOn I t) 1 (by
    intro t ht
    have hlt : l ≠ t := by
      simp only [A, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl|rfl <;> assumption
    rw [Finset.card_le_one]
    intro p hp q hq
    by_contra hpq
    simp only [ptsOn, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    exact hI p q l t hpq hlt ⟨hp.1,hp.2,hq.1,hq.2⟩)
  have ha : A.card ≤ 2 := Finset.card_le_two
  have hs := Finset.card_le_card sub
  omega
theorem rich_cert (I : Fin N → Fin N → Prop) (D : Dag N) (r : Fin J → ℕ) (u : Fin J → Fin N)
    (hI : NoRect I) (wf : D.WF) (h : ℕ) (w : Fin N) (hw : w ∈ Rset I D r u h) :
    ∃ q k, ¬ I q w ∧ Rset I D r u h ⊆ {w,k} ∪ pencil I q := by
  classical
  obtain ⟨p0,hp0⟩ := Finset.card_pos.mp (Nat.zero_lt_of_lt ((Finset.mem_filter.mp hw).2))
  obtain ⟨H0,g0,gg0,v0,W0,_,oh0,_⟩ := (Finset.mem_filter.mp (Finset.mem_filter.mp hp0).2).2
  obtain ⟨b,t,hm,ht,a,q,hbad⟩ := W0.1
  refine ⟨q,u a,hbad.1,?_⟩
  intro l hl
  by_contra hh
  have hn (hl' : l = w ∨ l = u a) : False :=
    hh (Finset.mem_union_left _ (by simpa using hl'))
  have hw' : l ≠ w := fun e => hn (Or.inl e)
  have hu' : l ≠ u a := fun e => hn (Or.inr e)
  have hq' : ¬ I q l := fun e => hh (Finset.mem_union_right _ (by simpa [pencil] using e))
  have hc (p : Fin N) (hp : (p,l) ∈ Eset I D r u h) : I p l ∧ (I p w ∨ I p (u a)) := by
    obtain ⟨H,g1,g,v,W,hno,_,hgp⟩ := (Finset.mem_filter.mp hp).2
    refine ⟨W.2.1,?_⟩
    by_contra! hn'
    apply hno
    refine ⟨b,t,H0,w,a,q,hm,ht,hbad,hn'.1,hn'.2,hq',?_⟩
    obtain ⟨_,_,_,_,hen,⟨f,hf,hv⟩,_⟩ := W
    refine (((bareLo p oh0).trans (bareLo p hgp)).trans hen).tail ?_
    refine ⟨Beta.labAnd_kid_v wf hf,fun z hz => ?_⟩
    exact (Api.labAnd_unique hf hz).1 ▸ hv
  have hs := two_lines I hI (Finset.univ.filter (fun p => (p,l) ∈ Eset I D r u h)) l w
    (u a) hw' hu' (fun p hp => hc p (Finset.mem_filter.mp hp).2)
  have hb := (Finset.mem_filter.mp hl).2
  omega
theorem t10 : CardT10 := by
  intro n I D j r u hI hwf h w hw
  exact rich_cert I D r u hI hwf h w hw
end Splice
end PEqualNP.Outside.L_meta_1321
namespace PEqualNP.Outside.L_meta_1321
open PEqualNP PEqualNP.MetaComplexity
namespace Unsafe
open Deg2 Deg2.Api Deg2.Bridge
variable {N : ℕ}
theorem okv {D : Dag N} (hwf : D.WF) {e c : ℕ} (ho : D.IsOr e) (hk : D.Kid e c)
    {z : Fin (N + N) → Bool} (h : D.val z c = true) : D.val z e = true := by
  obtain ⟨a, b, hg⟩ := ho
  obtain ⟨g, hg', hc, -⟩ := hk
  rw [hg] at hg'
  cases hg'
  rw [Forms.val_or hg (hwf e _ hg a (by simp [G.kids])) (hwf e _ hg b (by simp [G.kids]))]
  simp only [G.kids, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> simp [h]
theorem av {D : Dag N} (hwf : D.WF) {e f c : ℕ}
    (hg : D.gateAt e = some (.and f c) ∨ D.gateAt e = some (.and c f)) (z : Fin (N + N) → Bool) :
    D.val z e = (D.val z f && D.val z c) := by
  rcases hg with hg | hg
  · exact Forms.val_and hg (hwf e _ hg f (by simp [G.kids])) (hwf e _ hg c (by simp [G.kids])) z
  · rw [Forms.val_and hg (hwf e _ hg c (by simp [G.kids])) (hwf e _ hg f (by simp [G.kids])) z,
      Bool.and_comm]
theorem vv {D : Dag N} (hwf : D.WF) {v : ℕ} {u : Fin N} (h : D.VReach v u) {z : Fin (N + N) → Bool}
    (hz : z (Fin.natAdd N u) = true) : D.val z v = true := by
  induction h with
  | leaf u => rw [Forms.val_line, hz]
  | step ho _ hk _ ih => exact okv hwf ho hk (ih hz)
theorem ptle {q : Fin N} {z : Fin (N + N) → Bool} (hq : z (Fin.castAdd N q) = true) :
    pt q ≤ z := by
  intro i
  refine Fin.addCases (fun p => ?_) (fun l => ?_) i
  · rw [Honest.pt_castAdd]
    by_cases h : p = q
    · subst h
      simp [hq]
    · simp [h]
  · rw [Honest.pt_natAdd]
    exact Bool.false_le _
theorem epc (q w x : Fin N) : ep q w (Fin.castAdd N x) = decide (x = q) := by
  unfold ep; rw [Forms.inp_castAdd]; simp
theorem epn (q w l : Fin N) : ep q w (Fin.natAdd N l) = decide (l = w) := by
  unfold ep; rw [Forms.inp_natAdd]; simp
theorem vs {D : Dag N} {t : ℕ} {k : Fin N} (h : D.Vstar t = {k}) : D.VReach t k := by
  classical
  have : k ∈ D.Vstar t := by rw [h]; exact Finset.mem_singleton_self k
  exact (Finset.mem_filter.1 this).2
theorem ps {I : Fin N → Fin N → Prop} {D : Dag N} {J : ℕ} {r : Fin J → ℕ} {u : Fin J → Fin N}
    (hS : Plan.Std I D r u) {b : ℕ} {k : Fin N} {a : Fin J} {q : Fin N}
    (hB : Plan.Bad I D r u b k a q) {z : Fin (N + N) → Bool}
    (h0 : ∀ x, I x (u a) → z (Fin.castAdd N x) = false) (hq : z (Fin.castAdd N q) = true)
    (hb : D.val z b = true) :
    ∃ x l, I x l ∧ z (Fin.castAdd N x) = true ∧ z (Fin.natAdd N l) = true :=
  hS.2.2.2.1 a z h0 (Honest.tstar_rev hS.2.1 (ptle hq) hB.2.2 hb)
theorem t05b : Plan.CardT05b := by
  intro N I D J r u hS b t H k a q hM hV hB z h0 hq hk hH
  refine ps hS hB h0 hq ?_
  rw [av hS.2.1 hM.1, vv hS.2.1 (vs hV) hk, hH]
  rfl
theorem t05a : Plan.CardT05a := by
  intro N I D J r u hS b w hM ⟨a, q, hB⟩
  obtain ⟨x, l, hI, hx, hl⟩ := ps (z := ep q w) hS hB
    (fun x hx => by
      rw [epc]
      simp only [decide_eq_false_iff_not]
      rintro rfl
      exact hB.2.1 hx)
    (by rw [epc]; simp) (vv hS.2.1 (vs hM.2) (by rw [epn]; simp))
  rw [epc] at hx
  rw [epn] at hl
  simp only [decide_eq_true_eq] at hx hl
  subst hx
  subst hl
  exact hB.1 hI
theorem t05c : Plan.CardT05c := by
  classical
  intro N I D J r u hwf
  let S : ℕ → Finset (ℕ × Fin N) := fun b =>
    ((Finset.range (N + N + D.size)) ×ˢ Finset.univ).filter (fun i => ∃ t, Plan.MixAnd D b t i.1 ∧ D.Vstar t = {i.2})
  have hsub : Plan.ujobs I D r u ⊆ (Plan.KA D).biUnion S := by
    intro i hi
    obtain ⟨b, t, hM, hV, -⟩ := (Finset.mem_filter.1 hi).2
    refine Finset.mem_biUnion.2 ⟨b, Finset.mem_filter.2 ⟨?_, ?_, _, _, hM⟩,
      Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hi).1, t, hM, hV⟩⟩
    · rcases hM.1 with h | h <;> exact Deg1.mem_allG h
    · rcases hM.1 with h | h <;>
        rw [Forms.deg_and h (hwf b _ h _ (by simp [G.kids])) (hwf b _ h _ (by simp [G.kids])),
          hM.2.1, hM.2.2]
  refine (Finset.card_le_card hsub).trans ?_
  rw [Nat.mul_comm]
  refine Finset.card_biUnion_le_card_mul _ _ _ (fun b _ => ?_)
  rcases Finset.eq_empty_or_nonempty (S b) with h | ⟨i0, h0⟩
  · rw [h]
    simp
  obtain ⟨t0, hM0, -⟩ := (Finset.mem_filter.1 h0).2
  obtain ⟨x, y, hxy⟩ : ∃ x y, D.gateAt b = some (.and x y) := by
    rcases hM0.1 with h | h <;> exact ⟨_, _, h⟩
  have key : ∀ i ∈ S b, ∃ t, D.Vstar t = {i.2} ∧ (i.1 = y → t = x) ∧ (i.1 ≠ y → i.1 = x ∧ t = y) := by
    intro i hi
    obtain ⟨t, hM, hV⟩ := (Finset.mem_filter.1 hi).2
    refine ⟨t, hV, ?_⟩
    rcases hM.1 with h | h <;> rw [hxy] at h <;> cases h <;> grind
  have : (S b).card ≤ (Finset.univ : Finset Bool).card :=
    Finset.card_le_card_of_injOn (fun i => decide (i.1 = y)) (fun _ _ => Finset.mem_univ _) (by
      intro i hi j hj hij
      obtain ⟨t, hV, h1, h2⟩ := key i hi
      obtain ⟨t', hV', h1', h2'⟩ := key j hj
      have hij' : i.1 = y ↔ j.1 = y := by simpa using hij
      have ht : t = t' ∧ i.1 = j.1 := by grind
      rw [ht.1, hV'] at hV
      exact Prod.ext ht.2 (Finset.singleton_injective hV).symm)
  simpa using this
end Unsafe
end PEqualNP.Outside.L_meta_1321
namespace PEqualNP.Outside.L_meta_1321
open PEqualNP PEqualNP.MetaComplexity
namespace Lower0
open Deg2 Deg2.Api Deg2.Bridge Deg2.Forms
variable {N : ℕ}
theorem ostep_lstep {D : Dag N} {x : Fin (N + N) → Bool} {a b : ℕ} (h : Plan.OStep D a b) :
    Beta.LStep D x a b := by
  obtain ⟨⟨c, d, hg⟩, -, hk⟩ := h
  refine ⟨hk, fun f hl => ?_⟩
  rcases hl.1 with h1 | h1 <;> rw [hg] at h1 <;> cases h1
theorem ostar_lstar {D : Dag N} {x : Fin (N + N) → Bool} {a b : ℕ}
    (h : Relation.ReflTransGen (Plan.OStep D) a b) :
    Relation.ReflTransGen (Beta.LStep D x) a b := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (ostep_lstep hs)
def Desc (D : Dag N) (p w : Fin N) (h : ℕ) : Prop :=
  D.VReach h w ∨ ∃ g1 g v, Relation.ReflTransGen (Plan.OStep D) h g1 ∧
    (∃ f1 v1, D.LabAnd g1 f1 v1 ∧ D.val (pt p) f1 = true) ∧
    Relation.ReflTransGen (Beta.LStep D (pt p)) g1 g ∧
    (∃ f, D.LabAnd g f v ∧ D.val (pt p) f = true) ∧ D.VReach v w
theorem descend (D : Dag N) (p w : Fin N) :
    ∀ h, D.deg h = 1 → D.val (ep p w) h = true → D.val (pt p) h = false → Desc D p w h := by
  intro h
  induction h using Nat.strong_induction_on with
  | _ g ih =>
    intro hd h1 h0
    by_cases hi : g < N + N
    · rw [circ_deg_input D hi] at hd
      have hN : N ≤ g := by
        by_contra hN; rw [if_neg hN] at hd; exact absurd hd zero_ne_one
      rw [circ_val_input D _ hi] at h1
      rw [circ_ep_line hi hN h1]
      exact Or.inl (.leaf w)
    · cases hg : D.gates[g - (N + N)]? with
      | none =>
        rw [Dag.deg, if_neg hi, hg] at hd
        exact absurd hd zero_ne_one
      | some gg =>
        have hgA : D.gateAt g = some gg := by
          unfold Dag.gateAt; rw [if_pos (by omega)]; exact hg
        cases gg with
        | cst v =>
          rw [Dag.deg, if_neg hi, hg] at hd
          exact absurd hd zero_ne_one
        | or a b =>
          have hstep : ∀ c, c < g → (c = a ∨ c = b) → D.val (ep p w) c = true →
              D.val (pt p) c = false → Desc D p w g := by
            intro c hcg hcab hc1 hc0
            have hk : D.Kid g c :=
              circ_kid_of hgA (by rcases hcab with rfl | rfl <;> simp [G.kids]) hcg
            have hle : D.deg c ≤ 1 := hd ▸ deg_kid hk
            have hcd : D.deg c = 1 := by
              by_contra hne
              have := api_val_xonly D (by omega : D.deg c = 0) (x := ep p w) (y := pt p)
                (circ_ep_pts p w)
              rw [hc1, hc0] at this
              cases this
            have hos : Plan.OStep D g c := ⟨⟨a, b, hgA⟩, hd, hk⟩
            rcases ih c hcg hcd hc1 hc0 with hv | ⟨g1, g', v, ho, hl1, hl, hl2, hv⟩
            · exact Or.inl (.step ⟨a, b, hgA⟩ hd hk hv)
            · exact Or.inr ⟨g1, g', v, .head hos ho, hl1, hl, hl2, hv⟩
          have h0' := circ_val_or_false D hgA h0
          rcases circ_val_or_true D hgA h1 with ⟨ha, ha1⟩ | ⟨hb, hb1⟩
          · exact hstep a ha (Or.inl rfl) ha1 (h0'.1 ha)
          · exact hstep b hb (Or.inr rfl) hb1 (h0'.2 hb)
        | and a b =>
          obtain ⟨ha, hb, ha1, hb1⟩ := circ_val_and D hgA h1
          have hdeg := circ_deg_and D hgA ha hb
          have hstep : ∀ f v, v < g → (D.gateAt g = some (.and f v) ∨
              D.gateAt g = some (.and v f)) → D.deg f = 0 → D.deg v = 1 →
              D.val (ep p w) f = true → D.val (ep p w) v = true →
              (∀ x, D.val x g = (D.val x f && D.val x v)) → Desc D p w g := by
            intro f v hvg hgt hf hv hf1 hv1 heq
            have hk : D.Kid g v :=
              circ_kid_of hgA (by rcases hgt with h | h <;> rw [hgA] at h <;> cases h <;>
                simp [G.kids]) hvg
            have hfpt : D.val (pt p) f = true := by
              rw [api_val_xonly D hf (x := pt p) (y := ep p w) (fun q => by rw [circ_ep_pts])]
              exact hf1
            have hv0 : D.val (pt p) v = false := by
              rw [heq, hfpt, Bool.true_and] at h0; exact h0
            have hlab : D.LabAnd g f v := ⟨hgt, hf, hv⟩
            have hls : Beta.LStep D (pt p) g v := by
              refine ⟨hk, fun f' hl' => ?_⟩
              have : f' = f := by
                rcases hl'.1 with h | h <;> rcases hgt with h' | h' <;> rw [h] at h' <;>
                  cases h' <;> rfl
              rw [this]; exact hfpt
            rcases ih v hvg hv hv1 hv0 with hvr | ⟨g1, g', v', ho, -, hl, hl2, hvr⟩
            · exact Or.inr ⟨g, g, v, .refl, ⟨f, v, hlab, hfpt⟩, .refl, ⟨f, hlab, hfpt⟩, hvr⟩
            · exact Or.inr ⟨g, g', v', .refl, ⟨f, v, hlab, hfpt⟩,
                .head hls (Relation.ReflTransGen.trans (ostar_lstar ho) hl), hl2, hvr⟩
          by_cases hda : D.deg a = 0
          · exact hstep a b hb (Or.inl hgA) hda (by omega) ha1 hb1
              (circ_val_and_eq D hgA ha hb)
          · exact hstep b a ha (Or.inr hgA) (by omega) (by omega) hb1 ha1
              (fun x => by rw [circ_val_and_eq D hgA ha hb x, Bool.and_comm])
theorem t07c_of (h5 : Plan.CardT05b) : Plan.CardT07c := by
  intro N I D J r u hstd H p w hj hpw h1 h0
  obtain ⟨b, t, hmix, hvs, a, q, hbad⟩ := id hj
  rcases descend D p w H hmix.2.2 h1 h0 with hv | ⟨g1, g, v, ho, hl1, hl, hl2, hv⟩
  · exfalso
    obtain ⟨x, l, hxl, hx, hl⟩ := h5 N I D J r u hstd b t H w a q hmix hvs hbad (ep q w)
      (fun x hx => by
        unfold ep; rw [inp_castAdd]
        simp only [Finset.mem_singleton, decide_eq_false_iff_not]
        rintro rfl; exact hbad.2.1 hx)
      (by unfold ep; rw [inp_castAdd]; simp) (by unfold ep; rw [inp_natAdd]; simp)
      (circ_vreach_val D hv (by unfold ep; rw [inp_natAdd]; simp))
    unfold ep at hx hl
    rw [inp_castAdd] at hx
    rw [inp_natAdd] at hl
    simp only [Finset.mem_singleton, decide_eq_true_eq] at hx hl
    subst hx hl
    exact hbad.1 hxl
  · exact ⟨g1, g, v, hj, hpw, ho, hl1, hl, hl2, hv⟩
theorem t07b_of (h5 : Plan.CardT05b) : Plan.CardT07b := by
  classical
  intro N I D J r u hstd
  let F : ℕ × Fin N → Finset (Fin N × Fin N) := fun i =>
    if (D.alive i.1 ∩ ptsOn I i.2).card ≤ 2 then (D.alive i.1 ∩ ptsOn I i.2) ×ˢ {i.2} else ∅
  have hF : ∀ i ∈ Plan.ujobs I D r u, (F i).card ≤ 2 := by
    intro i _
    simp only [F]
    split_ifs with h
    · rw [Finset.card_product, Finset.card_singleton, mul_one]; exact h
    · simp
  have hsub : Plan.badPt0 I D r u \ Plan.drop2 I D ⊆ (Plan.ujobs I D r u).biUnion F := by
    intro e he
    obtain ⟨p, w⟩ := e
    rw [Finset.mem_sdiff] at he
    obtain ⟨he0, hnd⟩ := he
    unfold Plan.badPt0 at he0
    rw [Finset.mem_filter] at he0
    obtain ⟨-, hpw, H, hj, hH⟩ := he0
    obtain ⟨b, t, hmix, hvs, a, q, hbad⟩ := id hj
    have hpa : p ∈ D.alive H := by
      unfold Dag.alive; exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hH⟩
    have hdead : D.deadSets I 2 H ≠ ∅ := by
      refine Finset.ne_empty_of_mem (a := {w, u a}) ?_
      unfold Dag.deadSets
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, Finset.card_le_two, ?_⟩
      by_contra hne
      obtain ⟨x, l, hxl, hx, hl⟩ := h5 N I D J r u hstd b t H w a q hmix hvs hbad
        (testInput I {w, u a})
        (fun x hx => by
          unfold testInput; rw [inp_castAdd]
          simp only [decide_eq_false_iff_not, Finset.mem_filter, Finset.mem_univ, true_and]
          exact fun hh => hh (u a) (by simp) hx)
        (by
          unfold testInput; rw [inp_castAdd]
          simp only [decide_eq_true_eq, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_insert, Finset.mem_singleton]
          rintro l (rfl | rfl)
          · exact hbad.1
          · exact hbad.2.1)
        (by unfold testInput; rw [inp_natAdd]; simp) (by simpa using hne)
      unfold testInput at hx hl
      rw [inp_castAdd] at hx
      rw [inp_natAdd] at hl
      simp only [decide_eq_true_eq, Finset.mem_filter, Finset.mem_univ, true_and] at hx hl
      exact hx l hl hxl
    have hc : (D.alive H ∩ ptsOn I w).card ≤ 2 := by
      by_contra hc
      apply hnd
      unfold Plan.drop2 Rich.rich
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hpw, H, hmix.2.2.le, hdead, hpa,
        by change 3 ≤ (D.alive H ∩ ptsOn I w).card; omega⟩
    have hHlt : H < N + N + D.size := by
      by_contra hlt
      have := hmix.2.2
      rw [Dag.deg, if_neg (by omega), List.getElem?_eq_none (by unfold Dag.size at hlt; omega)]
        at this
      exact absurd this zero_ne_one
    rw [Finset.mem_biUnion]
    refine ⟨(H, w), ?_, ?_⟩
    · unfold Plan.ujobs
      exact Finset.mem_filter.2 ⟨Finset.mem_product.2
        ⟨Finset.mem_range.2 hHlt, Finset.mem_univ _⟩, hj⟩
    · simp only [F]
      rw [if_pos hc, Finset.mem_product, Finset.mem_inter]
      refine ⟨⟨hpa, ?_⟩, Finset.mem_singleton_self _⟩
      unfold ptsOn; exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hpw⟩
  calc _ ≤ ((Plan.ujobs I D r u).biUnion F).card := Finset.card_le_card hsub
    _ ≤ (Plan.ujobs I D r u).card * 2 := Finset.card_biUnion_le_card_mul _ _ _ hF
    _ = _ := mul_comm _ _
theorem t07c : Plan.CardT07c := t07c_of Unsafe.t05b
theorem t07b : Plan.CardT07b := t07b_of Unsafe.t05b
end Lower0
end PEqualNP.Outside.L_meta_1321
open PEqualNP.Outside.L_meta_1321 in
theorem PEqualNP.Outside.L_meta_1321 : ∀ (N Jn : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (Ckt : PEqualNP.CircuitLowerBounds.Circuit) (fg : Fin Jn → ℕ) (Wl : Fin Jn → Finset (Fin N)), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 Ckt → (∀ jd : Fin Jn, (Ckt.lineDegrees (N + N) (Finset.Ico N (N + N))).getD (fg jd) 0 ≤ 2) → (∀ (jb : Fin Jn) (zz : Fin (N + N) → Bool), (∃ uz ∈ Wl jb, ∀ pz : Fin N, I pz uz → zz (Fin.castAdd N pz) = false) → (Ckt.wires (List.ofFn zz)).getD (fg jb) false = true → ∃ (pa lb : Fin N), I pa lb ∧ zz (Fin.castAdd N pa) = true ∧ zz (Fin.natAdd N lb) = true) → (Finset.univ.filter (fun e2 : Fin N × Fin N => I e2.1 e2.2 ∧ ∃ jc : Fin Jn, (∃ uc ∈ Wl jc, ¬ I e2.1 uc) ∧ (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fg jc) false = true)).card ≤ 192 * (Ckt.size + Jn) + 8 * N :=
  Plan.assembly Honest.cardT04 Unsafe.t05a Unsafe.t05b Unsafe.t05c Splice.t06b SafeWrap.t06c Lower0.t07b Lower0.t07c Splice.t10 AlphaWrap.t12
