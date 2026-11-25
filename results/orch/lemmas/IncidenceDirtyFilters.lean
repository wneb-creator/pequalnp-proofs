import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583_aux.DirtyFilters

open PEqualNP.CircuitLowerBounds

theorem getD_le {w w' : List Bool} (h : List.Forall₂ (fun a b => a ≤ b) w w') (i : ℕ) :
    w.getD i false ≤ w'.getD i false := by
  induction h generalizing i with
  | nil => simp
  | cons hab _ ih =>
    cases i with
    | zero => simpa using hab
    | succ i => simpa using ih i

theorem bool_le {a b : Bool} : a ≤ b ↔ (a = true → b = true) := by
  cases a <;> cases b <;> decide

theorem gate_le (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) {w w' : List Bool}
    (h : List.Forall₂ (fun a b => a ≤ b) w w') :
    g.op.eval (g.inputs.map fun i => w.getD i false) ≤
      g.op.eval (g.inputs.map fun i => w'.getD i false) := by
  rw [bool_le]
  rcases hg with hg | hg
  · rw [hg]
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
    intro hx x hx'
    obtain ⟨i, hi, rfl⟩ := hx'
    exact bool_le.mp (getD_le h i) (hx _ ⟨i, hi, rfl⟩)
  · rw [hg]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨x, ⟨i, hi, rfl⟩, hx⟩
    exact ⟨_, ⟨i, hi, rfl⟩, bool_le.mp (getD_le h i) hx⟩

theorem fold_le (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ w w' : List Bool, List.Forall₂ (fun a b => a ≤ b) w w' →
      List.Forall₂ (fun a b => a ≤ b)
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w)
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w') := by
  induction gs with
  | nil => intro w w' h; simpa using h
  | cons g gs ih =>
    intro w w' h
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    exact List.rel_append h (List.Forall₂.cons (gate_le g (hgs g List.mem_cons_self) h) List.Forall₂.nil)

theorem gateVal_mono {n : ℕ} (C : Circuit) (hC : PEqualNP.EdgeOwnership.AndOrOnly C) (j : ℕ)
    (x y : Fin n → Bool) (hxy : ∀ i, x i ≤ y i) :
    PEqualNP.EdgeOwnership.gateVal n C j x ≤ PEqualNP.EdgeOwnership.gateVal n C j y := by
  have h0 : List.Forall₂ (fun a b => a ≤ b) (List.ofFn x) (List.ofFn y) := by
    rw [List.forall₂_iff_get]
    refine ⟨by simp only [List.length_ofFn], fun i h1 h2 => ?_⟩
    simp only [List.get_eq_getElem, List.getElem_ofFn]
    exact hxy _
  exact getD_le (fold_le C.gates hC _ _ h0) (n + j)

open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.SplitCount
  PEqualNP.MetaComplexity.NestedCover

lemma pair_graph_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) : graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, pairInput]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    rcases ha with rfl | rfl <;>
      rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro huv
    exact ⟨u, v, huv, by simp, by simp⟩

lemma singleton_wmax_adj {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : AndOrOnly C) (g : ℕ) (u w : Fin n)
    (hu : u ∈ singletonSet n C g) (hw : w ∈ wmax G C g) : G.Adj u w := by
  have hs : gateVal n C g (unitInput u) = true := (Finset.mem_filter.mp hu).2
  have hmono := gateVal_mono C hC g (unitInput u) (pairInput u w) (by
    intro i
    rw [bool_le]
    intro hi
    have he : i = u := by simpa only [unitInput, decide_eq_true_eq] using hi
    subst i
    simp [pairInput])
  have hg : gateVal n C g (pairInput u w) = true := bool_le.mp hmono hs
  apply (pair_graph_iff G u w).mp
  exact (Finset.mem_filter.mp hw).2 (pairInput u w) hg (by simp [pairInput])

lemma two_singletons_one_filter {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : NoFourCycle G) (C : Circuit) (hC : AndOrOnly C)
    (g : ℕ) (hlarge : 2 ≤ (singletonSet n C g).card) : (wmax G C g).card ≤ 1 := by
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hlarge
  apply le_trans (Finset.card_le_card ?_) (hG u v huv)
  intro w hw
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    singleton_wmax_adj G C hC g u w hu hw,
    singleton_wmax_adj G C hC g v w hv hw⟩

lemma opposite_singletons_no_filter {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (side : Fin n → Bool)
    (bip : ∀ a b, G.Adj a b → side a ≠ side b)
    (C : Circuit) (hC : AndOrOnly C) (g : ℕ) (u v : Fin n)
    (hu : u ∈ singletonSet n C g) (hv : v ∈ singletonSet n C g)
    (huv : side u ≠ side v) : wmax G C g = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  have h1 := bip u w (singleton_wmax_adj G C hC g u w hu hw)
  have h2 := bip v w (singleton_wmax_adj G C hC g v w hv hw)
  cases e1 : side u <;> cases e2 : side v <;> cases e3 : side w <;>
    simp_all

end PEqualNP.Outside.L_meta_2583_aux.DirtyFilters
