import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1031.P5Exchange

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

lemma common_center {V : Type*} (G : SimpleGraph V)
    (h4 : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    {a b c z : V} (hac : a ≠ c) (hab : G.Adj a b) (hbc : G.Adj b c)
    (hza : G.Adj z a) (hzc : G.Adj z c) : z = b :=
  ((h4 a b c z hab hbc hzc.symm hza).resolve_left hac).symm

lemma prefix_sharing_constraints {V : Type*} (G : SimpleGraph V)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (h4 : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    {a b c d e : V} (hac : a ≠ c) (hce : c ≠ e) (hbd : b ≠ d)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hde : G.Adj d e) :
    (∀ z, G.Adj z b → G.Adj z d → z = c) ∧
      (∀ z, ¬ (G.Adj z b ∧ G.Adj z c)) ∧
      (∀ z, ¬ (G.Adj z b ∧ G.Adj z c ∧ G.Adj z e)) ∧
      (∀ z, ¬ (G.Adj z a ∧ G.Adj z c ∧ G.Adj z e)) ∧
      (∀ z, ¬ (G.Adj z a ∧ G.Adj z c ∧ G.Adj z d)) := by
  refine ⟨fun z hzb hzd => common_center G h4 hbd hbc hcd hzb hzd, ?_, ?_, ?_, ?_⟩
  · rintro z ⟨hzb, hzc⟩
    exact htri z b c hzb hbc hzc.symm
  · rintro z ⟨hzb, hzc, _⟩
    exact htri z b c hzb hbc hzc.symm
  · rintro z ⟨hza, hzc, hze⟩
    have hzb := common_center G h4 hac hab hbc hza hzc
    have hzd := common_center G h4 hce hcd hde hzc hze
    exact hbd (hzb.symm.trans hzd)
  · rintro z ⟨_, hzc, hzd⟩
    exact htri z c d hzc hcd hzd.symm

abbrev pathFive : SimpleGraph (Fin 5) := edgeGraph 5 [(0, 1), (1, 2), (2, 3), (3, 4)]

def oldCore : Circuit :=
  ⟨[⟨.or, [1, 3]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [6, 4]⟩,
    ⟨.or, [0, 4]⟩, ⟨.or, [8, 2]⟩, ⟨.or, [0, 3]⟩,
    ⟨.or, [10, 2]⟩, ⟨.and, [5, 7]⟩, ⟨.and, [9, 11]⟩,
    ⟨.and, [12, 13]⟩], 14⟩

def newCore : Circuit :=
  ⟨[⟨.or, [1, 3]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [0, 3]⟩,
    ⟨.or, [0, 2]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [2, 4]⟩,
    ⟨.and, [3, 10]⟩, ⟨.or, [9, 11]⟩], 12⟩

lemma oldCore_correct : circuitFun 5 oldCore = graphFun pathFive ∅ := by
  funext x
  revert x
  decide

lemma newCore_correct : circuitFun 5 newCore = graphFun pathFive ∅ := by
  funext x
  revert x
  decide

lemma oldCore_two_junk : PEqualNP.TopForm.junk pathFive oldCore = {7, 8} := by decide

lemma oldCore_top : PEqualNP.TopForm.TopForm pathFive oldCore := by decide

lemma newCore_preserves_shared_ports : ∀ x : Fin 5 → Bool,
    (oldCore.wires (List.ofFn x)).getD 5 false = (newCore.wires (List.ofFn x)).getD 5 false ∧
    (oldCore.wires (List.ofFn x)).getD 8 false = (newCore.wires (List.ofFn x)).getD 6 false ∧
    (oldCore.wires (List.ofFn x)).getD 10 false = (newCore.wires (List.ofFn x)).getD 7 false ∧
    oldCore.eval (List.ofFn x) = newCore.eval (List.ofFn x) := by
  decide

lemma newCore_legal : PEqualNP.TopForm.IsAO2 5 newCore := by decide

lemma newCore_nonempty_star_owners : ∀ j < newCore.gates.length,
    (gateAt newCore j).op = GateOp.and → ∃ c : Fin 5,
      (∃ u v : Fin 5, pathFive.Adj u v ∧ Owns 5 newCore j u v) ∧
      ∀ u v : Fin 5, pathFive.Adj u v → Owns 5 newCore j u v → u = c ∨ v = c := by
  intro j hj hop
  have hj8 : j < 8 := hj
  interval_cases j <;> norm_num [newCore, gateAt] at hop
  all_goals decide

lemma newCore_size_drop : newCore.size + 2 = oldCore.size := rfl

end PEqualNP.Outside.L_meta_1031.P5Exchange

namespace PEqualNP.Outside.L_meta_1031.P5Context

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_1031.P5Exchange

def allowed (w : ℕ) : Prop := w < 5 ∨ w = 5 ∨ w = 8 ∨ w = 10 ∨ w = 14 ∨ 15 ≤ w

def rename (w : ℕ) : ℕ :=
  if w < 5 then w else if w = 5 then 5 else if w = 8 then 6 else
    if w = 10 then 7 else if w = 14 then 12 else w - 2

def renameGate (g : Gate) : Gate := ⟨g.op, g.inputs.map rename⟩

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]) w

lemma rename_lt (w k : ℕ) (h : w < 15 + k) : rename w < 13 + k := by
  unfold rename
  split_ifs <;> omega

lemma rename_last (k : ℕ) : rename (15 + k) = 13 + k := by
  simp only [rename]
  split_ifs <;> omega

lemma rename_gt (w k : ℕ) (h : 15 + k < w) : 13 + k < rename w := by
  unfold rename
  split_ifs <;> omega

lemma append_relation (wo wn : List Bool) (k : ℕ) (v : Bool)
    (ho : wo.length = 15 + k) (hn : wn.length = 13 + k)
    (hr : ∀ w, allowed w → wo.getD w false = wn.getD (rename w) false) :
    ∀ w, allowed w → (wo ++ [v]).getD w false = (wn ++ [v]).getD (rename w) false := by
  intro w hw
  by_cases hlt : w < 15 + k
  · rw [List.getD_append _ _ _ _ (by omega),
      List.getD_append _ _ _ _ (by have := rename_lt w k hlt; omega)]
    exact hr w hw
  · by_cases he : w = 15 + k
    · subst w
      rw [rename_last, ← ho, ← hn]
      simp
    · have hw' : 15 + k < w := by omega
      have hw'' := rename_gt w k hw'
      rw [List.getD_eq_default _ _ (by simp only [List.length_append, List.length_singleton]; omega),
        List.getD_eq_default _ _ (by simp only [List.length_append, List.length_singleton]; omega)]

lemma run_relation (gs : List Gate)
    (hgs : ∀ g ∈ gs, ∀ w ∈ g.inputs, allowed w)
    (wo wn : List Bool) (k : ℕ) (ho : wo.length = 15 + k) (hn : wn.length = 13 + k)
    (hr : ∀ w, allowed w → wo.getD w false = wn.getD (rename w) false) :
    ∀ w, allowed w → (run gs wo).getD w false =
      (run (gs.map renameGate) wn).getD (rename w) false := by
  induction gs generalizing wo wn k with
  | nil => exact hr
  | cons g gs ih =>
    have hv : g.op.eval (g.inputs.map fun i => wo.getD i false) =
        (renameGate g).op.eval ((renameGate g).inputs.map fun i => wn.getD i false) := by
      change g.op.eval _ = g.op.eval _
      apply congrArg g.op.eval
      simp only [renameGate, List.map_map, Function.comp_def]
      apply List.map_congr_left
      intro w hw
      exact hr w (hgs g (by simp) w hw)
    change ∀ w, allowed w →
      (run gs (wo ++ [g.op.eval (g.inputs.map fun i => wo.getD i false)])).getD w false =
      (run (gs.map renameGate)
        (wn ++ [(renameGate g).op.eval ((renameGate g).inputs.map fun i => wn.getD i false)])).getD (rename w) false
    rw [← hv]
    apply ih (fun h hh => hgs h (List.mem_cons_of_mem _ hh)) _ _ (k + 1)
    · simp [ho]; omega
    · simp [hn]; omega
    · exact append_relation wo wn k _ ho hn hr

lemma core_relation (x : Fin 5 → Bool) : ∀ w, allowed w →
    (oldCore.wires (List.ofFn x)).getD w false =
      (newCore.wires (List.ofFn x)).getD (rename w) false := by
  have ho : (oldCore.wires (List.ofFn x)).length = 15 := by revert x; decide
  have hn : (newCore.wires (List.ofFn x)).length = 13 := by revert x; decide
  intro w hw
  by_cases hlt : w < 15
  · have hfinite : ∀ x : Fin 5 → Bool, ∀ w : Fin 15, allowed w.val →
        (oldCore.wires (List.ofFn x)).getD w.val false =
          (newCore.wires (List.ofFn x)).getD (rename w.val) false := by
      unfold allowed
      decide
    exact hfinite x ⟨w, hlt⟩ hw
  · have hren : rename w = w - 2 := by
      unfold rename
      split_ifs <;> omega
    rw [List.getD_eq_default _ _ (by omega), hren, List.getD_eq_default _ _ (by omega)]

lemma substitute_in_context (post : List Gate) (out : ℕ)
    (hpost : ∀ g ∈ post, ∀ w ∈ g.inputs, allowed w) (hout : allowed out) :
    ∀ x : Fin 5 → Bool,
      (⟨oldCore.gates ++ post, out⟩ : Circuit).eval (List.ofFn x) =
        (⟨newCore.gates ++ post.map renameGate, rename out⟩ : Circuit).eval (List.ofFn x) := by
  intro x
  have ho : (oldCore.wires (List.ofFn x)).length = 15 + 0 := by revert x; decide
  have hn : (newCore.wires (List.ofFn x)).length = 13 + 0 := by revert x; decide
  have h := run_relation post hpost _ _ 0 ho hn (core_relation x) out hout
  simpa only [Circuit.eval, Circuit.wires, List.foldl_append, run] using h

lemma substitute_size (post : List Gate) (out : ℕ) :
    (⟨newCore.gates ++ post.map renameGate, rename out⟩ : Circuit).size + 2 =
      (⟨oldCore.gates ++ post, out⟩ : Circuit).size := by
  simp [Circuit.size, oldCore, newCore]

lemma substitute_monotone (post : List Gate) (out : ℕ)
    (hmono : PEqualNP.MetaComplexity.Monotone2 ⟨oldCore.gates ++ post, out⟩) :
    PEqualNP.MetaComplexity.Monotone2
      ⟨newCore.gates ++ post.map renameGate, rename out⟩ := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · have hm : PEqualNP.MetaComplexity.Monotone2 newCore := by
      simp [PEqualNP.MetaComplexity.Monotone2, newCore]
    exact hm g hg
  · obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hg
    obtain ⟨hop, hlen⟩ := hmono h (List.mem_append_right _ hh)
    exact ⟨hop, by simpa [renameGate] using hlen⟩

lemma no_minimal_context (post : List Gate) (out : ℕ)
    (hpost : ∀ g ∈ post, ∀ w ∈ g.inputs, allowed w) (hout : allowed out) :
    ¬ PEqualNP.MetaComplexity.IsMinimalMonoCircuit 5 ⟨oldCore.gates ++ post, out⟩ := by
  intro h
  have heq : PEqualNP.MetaComplexity.circuitFun 5
        ⟨newCore.gates ++ post.map renameGate, rename out⟩ =
      PEqualNP.MetaComplexity.circuitFun 5 ⟨oldCore.gates ++ post, out⟩ := by
    funext x
    exact (substitute_in_context post out hpost hout x).symm
  have hle := h.2 _ (substitute_monotone post out h.1) heq
  have hdrop := substitute_size post out
  omega

end PEqualNP.Outside.L_meta_1031.P5Context
