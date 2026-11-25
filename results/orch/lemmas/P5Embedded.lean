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

namespace PEqualNP.Outside.L_meta_1031.P5Embedded

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_1031.P5Exchange

def embed (B : ℕ) (ρ : Fin 5 → ℕ) (w : ℕ) : ℕ :=
  if h : w < 5 then ρ ⟨w, h⟩ else B + (w - 5)

def embedGate (B : ℕ) (ρ : Fin 5 → ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (embed B ρ)⟩

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]) w

lemma embed_lt (B k : ℕ) (ρ : Fin 5 → ℕ) (hρ : ∀ i, ρ i < B)
    (w : ℕ) (hw : w < 5 + k) : embed B ρ w < B + k := by
  unfold embed
  split_ifs with h
  · have := hρ ⟨w, h⟩
    omega
  · omega

lemma embed_last (B k : ℕ) (ρ : Fin 5 → ℕ) : embed B ρ (5 + k) = B + k := by
  simp [embed]

lemma embed_gt (B k : ℕ) (ρ : Fin 5 → ℕ) (w : ℕ) (hw : 5 + k < w) :
    B + k < embed B ρ w := by
  unfold embed
  split_ifs <;> omega

lemma append_relation (B k : ℕ) (ρ : Fin 5 → ℕ) (hρ : ∀ i, ρ i < B)
    (wo wn : List Bool) (v : Bool) (ho : wo.length = 5 + k) (hn : wn.length = B + k)
    (hr : ∀ w, wo.getD w false = wn.getD (embed B ρ w) false) :
    ∀ w, (wo ++ [v]).getD w false = (wn ++ [v]).getD (embed B ρ w) false := by
  intro w
  by_cases hlt : w < 5 + k
  · rw [List.getD_append _ _ _ _ (by omega),
      List.getD_append _ _ _ _ (by have := embed_lt B k ρ hρ w hlt; omega)]
    exact hr w
  · by_cases he : w = 5 + k
    · subst w
      rw [embed_last, ← ho, ← hn]
      simp
    · have hw' : 5 + k < w := by omega
      have hw'' := embed_gt B k ρ w hw'
      rw [List.getD_eq_default _ _ (by simp only [List.length_append, List.length_singleton]; omega),
        List.getD_eq_default _ _ (by simp only [List.length_append, List.length_singleton]; omega)]

lemma run_relation (gs : List Gate) (B : ℕ) (ρ : Fin 5 → ℕ) (hρ : ∀ i, ρ i < B)
    (wo wn : List Bool) (k : ℕ) (ho : wo.length = 5 + k) (hn : wn.length = B + k)
    (hr : ∀ w, wo.getD w false = wn.getD (embed B ρ w) false) :
    ∀ w, (run gs wo).getD w false =
      (run (gs.map (embedGate B ρ)) wn).getD (embed B ρ w) false := by
  induction gs generalizing wo wn k with
  | nil => exact hr
  | cons g gs ih =>
    have hv : g.op.eval (g.inputs.map fun i => wo.getD i false) =
        (embedGate B ρ g).op.eval ((embedGate B ρ g).inputs.map fun i => wn.getD i false) := by
      change g.op.eval _ = g.op.eval _
      apply congrArg g.op.eval
      simp only [embedGate, List.map_map, Function.comp_def]
      exact List.map_congr_left (fun w _ => hr w)
    change ∀ w,
      (run gs (wo ++ [g.op.eval (g.inputs.map fun i => wo.getD i false)])).getD w false =
      (run (gs.map (embedGate B ρ))
        (wn ++ [(embedGate B ρ g).op.eval ((embedGate B ρ g).inputs.map fun i => wn.getD i false)])).getD (embed B ρ w) false
    rw [← hv]
    apply ih _ _ (k + 1)
    · simp [ho]; omega
    · simp [hn]; omega
    · exact append_relation B k ρ hρ wo wn _ ho hn hr

lemma input_relation (base : List Bool) (ρ : Fin 5 → ℕ) (hρ : ∀ i, ρ i < base.length) :
    ∀ w, (List.ofFn (fun i : Fin 5 => base.getD (ρ i) false)).getD w false =
      base.getD (embed base.length ρ w) false := by
  intro w
  by_cases hw : w < 5
  · simp only [embed, dif_pos hw, List.getD_eq_getElem?_getD,
      List.getElem?_ofFn, hw, dite_true, Option.getD_some]
  · have hge : (List.ofFn (fun i : Fin 5 => base.getD (ρ i) false)).length ≤ w := by
      simp
      omega
    rw [List.getD_eq_default _ _ hge]
    symm
    apply List.getD_eq_default
    simp only [embed, dif_neg hw]
    omega

lemma embedded_relation (gs : List Gate) (base : List Bool) (ρ : Fin 5 → ℕ)
    (hρ : ∀ i, ρ i < base.length) (w : ℕ) :
    (run gs (List.ofFn (fun i : Fin 5 => base.getD (ρ i) false))).getD w false =
      (run (gs.map (embedGate base.length ρ)) base).getD (embed base.length ρ w) false := by
  exact run_relation gs base.length ρ hρ _ _ 0 (by simp) (by simp)
    (input_relation base ρ hρ) w

lemma arbitrary_prefix_exchange (base : List Bool) (ρ : Fin 5 → ℕ)
    (hρ : ∀ i, ρ i < base.length) :
    let old := run (oldCore.gates.map (embedGate base.length ρ)) base
    let new := run (newCore.gates.map (embedGate base.length ρ)) base
    old.getD base.length false = new.getD base.length false ∧
    old.getD (base.length + 3) false = new.getD (base.length + 1) false ∧
    old.getD (base.length + 5) false = new.getD (base.length + 2) false ∧
    old.getD (base.length + 9) false = new.getD (base.length + 7) false := by
  dsimp only
  have h := newCore_preserves_shared_ports (fun i => base.getD (ρ i) false)
  have oldAt := embedded_relation oldCore.gates base ρ hρ
  have newAt := embedded_relation newCore.gates base ρ hρ
  have h5 := oldAt 5
  have h8 := oldAt 8
  have h10 := oldAt 10
  have h14 := oldAt 14
  have h5' := newAt 5
  have h6' := newAt 6
  have h7' := newAt 7
  have h12' := newAt 12
  simp only [embed, Nat.lt_irrefl, ↓reduceDIte, Nat.reduceLT, Nat.reduceSub,
    Nat.add_zero] at h5 h8 h10 h14 h5' h6' h7' h12'
  change _ ∧ _ ∧ _ ∧
    (oldCore.wires _).getD 14 false = (newCore.wires _).getD 12 false at h
  change (run oldCore.gates _).getD 5 false = (run newCore.gates _).getD 5 false ∧
    (run oldCore.gates _).getD 8 false = (run newCore.gates _).getD 6 false ∧
    (run oldCore.gates _).getD 10 false = (run newCore.gates _).getD 7 false ∧
    (run oldCore.gates _).getD 14 false = (run newCore.gates _).getD 12 false at h
  exact ⟨h5.symm.trans (h.1.trans h5'), h8.symm.trans (h.2.1.trans h6'),
    h10.symm.trans (h.2.2.1.trans h7'), h14.symm.trans (h.2.2.2.trans h12')⟩

end PEqualNP.Outside.L_meta_1031.P5Embedded
