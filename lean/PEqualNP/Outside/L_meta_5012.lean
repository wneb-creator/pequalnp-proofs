import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5012

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

end PEqualNP.Outside.L_meta_5012

namespace PEqualNP.Outside.L_meta_5012.OneOr

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

end PEqualNP.Outside.L_meta_5012.OneOr

namespace PEqualNP.Outside.L_meta_5012.Trace

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)

end PEqualNP.Outside.L_meta_5012.Trace

namespace PEqualNP.Outside.L_meta_5012.Small

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

end PEqualNP.Outside.L_meta_5012.Small

namespace PEqualNP.Outside.L_meta_5012.Count

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.Outside.L_meta_5012.OneOr

end PEqualNP.Outside.L_meta_5012.Count

namespace PEqualNP.Outside.L_meta_5012.Small

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

end PEqualNP.Outside.L_meta_5012.Small

namespace PEqualNP.Outside.L_meta_5012.Twin

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

namespace Merge

end Merge

namespace Restriction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

def ov (gs : List Gate) (x : List Bool) (o : Option ℕ) : Bool :=
  match o with
  | none => false
  | some w => (run gs x).getD w false

end Restriction

end PEqualNP.Outside.L_meta_5012.Twin

namespace PEqualNP.Outside.L_meta_5012.Singleton

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

end PEqualNP.Outside.L_meta_5012.Singleton

namespace PEqualNP.Outside.L_meta_5012.Overlap

open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

def rawOr {n : ℕ} (A : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∃ a ∈ A, x a = true)

def product {n : ℕ} (A B : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  rawOr A x && rawOr B x

def CleanMutual {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B C D : Finset (Fin n)) : Prop :=
  ∀ x, (product A B x && product C D x) = true → graphFun G ∅ x = true

lemma graphFun_true {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → Bool) : graphFun G ∅ x = true ↔
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
  simp [graphFun]

lemma graphFun_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) : graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  rw [graphFun_true]
  simp only [pairInput, decide_eq_true_eq]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro huv
    exact ⟨u, v, huv, Or.inl rfl, Or.inr rfl⟩

lemma rawOr_true {n : ℕ} {A : Finset (Fin n)} {x : Fin n → Bool}
    {a : Fin n} (ha : a ∈ A) (hx : x a = true) : rawOr A x = true :=
  decide_eq_true ⟨a, ha, hx⟩

lemma product_overlap_true {n : ℕ} {A B : Finset (Fin n)} {x : Fin n → Bool}
    {a : Fin n} (ha : a ∈ A ∩ B) (hx : x a = true) : product A B x = true := by
  simp only [product, rawOr_true (Finset.mem_inter.mp ha).1 hx,
    rawOr_true (Finset.mem_inter.mp ha).2 hx, Bool.and_self]

lemma cleanMutual_adj_overlaps {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (A B C D : Finset (Fin n))
    (hclean : CleanMutual G A B C D) {u v : Fin n}
    (hu : u ∈ A ∩ B) (hv : v ∈ C ∩ D) : G.Adj u v := by
  apply (graphFun_pair G u v).1
  apply hclean
  have hp := product_overlap_true hu (x := pairInput u v) (by simp [pairInput])
  have hq := product_overlap_true hv (x := pairInput u v) (by simp [pairInput])
  simp [hp, hq]

lemma cleanMutual_small_overlap {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (A B C D : Finset (Fin n)) (hG : NoFourCycle G)
    (hclean : CleanMutual G A B C D) : (A ∩ B).card ≤ 1 ∨ (C ∩ D).card ≤ 1 := by
  by_cases hAB : (A ∩ B).card ≤ 1
  · exact Or.inl hAB
  · right
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < (A ∩ B).card)
    have hsub : C ∩ D ⊆ Finset.univ.filter (fun w => G.Adj a w ∧ G.Adj b w) := by
      intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨cleanMutual_adj_overlaps G A B C D hclean ha hw,
        cleanMutual_adj_overlaps G A B C D hclean hb hw⟩
    exact (Finset.card_le_card hsub).trans (hG a b hab)

end PEqualNP.Outside.L_meta_5012.Overlap

namespace PEqualNP.Outside.L_meta_5012.CriticalEdge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

lemma run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

lemma getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

lemma run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

lemma run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

lemma run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)

def u (n : ℕ) (A : ℕ → Bool) (a b : ℕ → ℕ) (Del : Finset ℕ) (L : ℕ → List ℕ) (x : List Bool)
    (w : ℕ) : Bool :=
  if w < n then x.getD w false
  else if w - n ∈ Del then false
  else if A (w - n) = true then
    ((if _h : a (w - n) < w then u n A a b Del L x (a (w - n)) else false) ||
      (L (w - n)).any (fun t => x.getD t false)) &&
    (if _h : b (w - n) < w then u n A a b Del L x (b (w - n)) else false)
  else
    (if _h : a (w - n) < w then u n A a b Del L x (a (w - n)) else false) ||
    (if _h : b (w - n) < w then u n A a b Del L x (b (w - n)) else false)
termination_by w

section WireLemmas

variable {n : ℕ} {A : ℕ → Bool} {a b : ℕ → ℕ} {Del : Finset ℕ} {L : ℕ → List ℕ} {x : List Bool}

lemma u_in {w : ℕ} (h : w < n) : u n A a b Del L x w = x.getD w false := by
  rw [u, if_pos h]

lemma u_del {j : ℕ} (h : j ∈ Del) : u n A a b Del L x (n + j) = false := by
  rw [u, if_neg (by omega), Nat.add_sub_cancel_left, if_pos h]

lemma u_and {j : ℕ} (h : j ∉ Del) (hA : A j = true) (ha : a j < n + j) (hb : b j < n + j) :
    u n A a b Del L x (n + j) = ((u n A a b Del L x (a j) ||
      (L j).any (fun t => x.getD t false)) && u n A a b Del L x (b j)) := by
  rw [u, if_neg (by omega), Nat.add_sub_cancel_left, if_neg h, if_pos hA, dif_pos ha, dif_pos hb]

lemma u_or {j : ℕ} (h : j ∉ Del) (hA : A j = false) (ha : a j < n + j) (hb : b j < n + j) :
    u n A a b Del L x (n + j) = (u n A a b Del L x (a j) || u n A a b Del L x (b j)) := by
  rw [u, if_neg (by omega), Nat.add_sub_cancel_left, if_neg h, if_neg (by simp [hA]), dif_pos ha,
    dif_pos hb]

end WireLemmas

def Ok (n : ℕ) (gs : List Gate) : Prop :=
  ∀ j (hj : j < gs.length), ∃ o s t, gs[j] = ⟨o, [s, t]⟩ ∧ (o = GateOp.and ∨ o = GateOp.or) ∧
    s < n + j ∧ t < n + j

lemma ok_snoc {n : ℕ} {gs : List Gate} (h : Ok n gs) {o : GateOp} {s t : ℕ}
    (ho : o = GateOp.and ∨ o = GateOp.or) (hs : s < n + gs.length) (ht : t < n + gs.length) :
    Ok n (gs ++ [⟨o, [s, t]⟩]) := by
  intro j hj
  by_cases hlt : j < gs.length
  · rw [List.getElem_append_left hlt]; exact h j hlt
  · have : j = gs.length := by simp at hj; omega
    subst this
    exact ⟨o, s, t, by simp, ho, hs, ht⟩

open Classical in
noncomputable def dc (n : ℕ) (F : (Fin n → Bool) → Bool) (gs : List Gate) : ℕ :=
  ((Finset.range gs.length).filter fun i => (gs.getD i ⟨GateOp.or, []⟩).op = GateOp.and ∧
    ∃ x : Fin n → Bool, (run gs (List.ofFn x)).getD (n + i) false = true ∧ F x = false).card

open Classical in
lemma dc_snoc (n : ℕ) (F : (Fin n → Bool) → Bool) (gs : List Gate) (g : Gate) :
    dc n F (gs ++ [g]) ≤ dc n F gs + if g.op = GateOp.and ∧
      ∃ x : Fin n → Bool, (run (gs ++ [g]) (List.ofFn x)).getD (n + gs.length) false = true ∧
        F x = false then 1 else 0 := by
  unfold dc
  rw [List.length_append, List.length_singleton, Finset.range_add_one, Finset.filter_insert]
  have e : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
    simp [List.getD_eq_getElem?_getD]
  rw [e]
  have h1 : ((Finset.range gs.length).filter fun i =>
      ((gs ++ [g]).getD i ⟨GateOp.or, []⟩).op = GateOp.and ∧ ∃ x : Fin n → Bool,
        (run (gs ++ [g]) (List.ofFn x)).getD (n + i) false = true ∧ F x = false) =
      (Finset.range gs.length).filter fun i =>
      (gs.getD i ⟨GateOp.or, []⟩).op = GateOp.and ∧ ∃ x : Fin n → Bool,
        (run gs (List.ofFn x)).getD (n + i) false = true ∧ F x = false := by
    refine Finset.filter_congr fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    rw [getD_ltz _ _ _ _ hi']
    refine and_congr_right fun _ => exists_congr fun x => ?_
    rw [run_prefix gs [g] _ _ (by simp; omega)]
  rw [h1]
  split_ifs with h
  · exact (Finset.card_insert_le _ _)
  · simp

def ov (gs : List Gate) (x : List Bool) (o : Option ℕ) : Bool :=
  match o with
  | none => false
  | some w => (run gs x).getD w false

lemma ov_ext (gs hs : List Gate) (x : List Bool) (o : Option ℕ)
    (h : ∀ w, o = some w → w < x.length + gs.length) : ov (gs ++ hs) x o = ov gs x o := by
  cases o with
  | none => rfl
  | some w => exact run_prefix gs hs x w (h w rfl)

lemma ov_new (gs : List Gate) (n : ℕ) (x : List Bool) (hx : x.length = n) (o : GateOp) (s t : ℕ)
    (hs : s < n + gs.length) (ht : t < n + gs.length) :
    ov (gs ++ [⟨o, [s, t]⟩]) x (some (n + gs.length)) =
      o.eval [(run gs x).getD s false, (run gs x).getD t false] := by
  unfold ov
  simp only
  rw [run_snoc]
  have : n + gs.length = (run gs x).length := by rw [run_length, hx]
  rw [this, getD_at]
  rfl

lemma chain (n : ℕ) (F : (Fin n → Bool) → Bool) : ∀ (l : List ℕ), (∀ t ∈ l, t < n) →
    ∀ (gs : List Gate), Ok n gs → ∀ o : Option ℕ, (∀ w, o = some w → w < n + gs.length) →
    ∃ (hs : List Gate) (o' : Option ℕ), Ok n (gs ++ hs) ∧ hs.length ≤ l.length ∧
      dc n F (gs ++ hs) ≤ dc n F gs ∧ (∀ w, o' = some w → w < n + (gs ++ hs).length) ∧
      ∀ x : Fin n → Bool, ov (gs ++ hs) (List.ofFn x) o' =
        (ov gs (List.ofFn x) o || l.any (fun t => (List.ofFn x).getD t false)) := by
  intro l
  induction l with
  | nil =>
    intro _ gs hgs o ho
    exact ⟨[], o, by simpa using hgs, by simp, by simp, by simpa using ho, by simp⟩
  | cons t l ih =>
    intro hl gs hgs o ho
    have ht : t < n := hl t (by simp)
    have hl' : ∀ t ∈ l, t < n := fun s hs => hl s (by simp [hs])
    cases o with
    | none =>
      obtain ⟨hs, o', h1, h2, h3, h4, h5⟩ := ih hl' gs hgs (some t) (by
        intro w hw; cases hw; omega)
      refine ⟨hs, o', h1, by simp; omega, h3, h4, fun x => ?_⟩
      rw [h5 x]
      have : ov gs (List.ofFn x) (some t) = (List.ofFn x).getD t false :=
        run_input _ _ _ (by simpa using ht)
      rw [this]; simp [ov]
    | some w =>
      have hw := ho w rfl
      obtain ⟨hs, o', h1, h2, h3, h4, h5⟩ := ih hl' (gs ++ [⟨GateOp.or, [w, t]⟩])
        (ok_snoc hgs (Or.inr rfl) hw (by omega)) (some (n + gs.length)) (by
          intro w hw; cases hw; simp)
      refine ⟨⟨GateOp.or, [w, t]⟩ :: hs, o', by simpa using h1, by simp; omega, ?_,
        by simpa using h4, fun x => ?_⟩
      · have := dc_snoc n F gs ⟨GateOp.or, [w, t]⟩
        rw [if_neg (by simp)] at this
        have e : gs ++ ⟨GateOp.or, [w, t]⟩ :: hs = gs ++ [⟨GateOp.or, [w, t]⟩] ++ hs := by simp
        rw [e]; omega
      · have e : gs ++ ⟨GateOp.or, [w, t]⟩ :: hs = gs ++ [⟨GateOp.or, [w, t]⟩] ++ hs := by simp
        rw [e, h5 x, ov_new gs n _ (by simp) _ _ _ hw (by omega)]
        rw [run_input gs (List.ofFn x) t (by simpa using ht)]
        simp [ov, GateOp.eval, Bool.or_assoc]

open Classical in
lemma build (n : ℕ) (A : ℕ → Bool) (a b : ℕ → ℕ) (Del R : Finset ℕ) (L : ℕ → List ℕ)
    (F : (Fin n → Bool) → Bool) (hL : ∀ j, ∀ t ∈ L j, t < n)
    (hR : ∀ j ∈ R, A j = false ∧ j ∉ Del ∧ ∃ d ∈ Del, d < j ∧ (a j = n + d ∨ b j = n + d)) :
    ∀ p, (∀ j < p, a j < n + j ∧ b j < n + j) →
    ∃ (gs : List Gate) (m : ℕ → Option ℕ), Ok n gs ∧
      (∀ w < n + p, (∀ w', m w = some w' → w' < n + gs.length) ∧
        ∀ x : Fin n → Bool, ov gs (List.ofFn x) (m w) = u n A a b Del L (List.ofFn x) w) ∧
      (∀ d ∈ Del, d < p → m (n + d) = none) ∧
      gs.length + ((Finset.range p).filter (· ∈ Del)).card +
        ((Finset.range p).filter (· ∈ R)).card ≤ p + ∑ j ∈ Finset.range p, (L j).length ∧
      dc n F gs ≤ ((Finset.range p).filter fun j => A j = true ∧ j ∉ Del ∧
        ∃ x : Fin n → Bool, u n A a b Del L (List.ofFn x) (n + j) = true ∧ F x = false).card := by
  intro p
  induction p with
  | zero =>
    intro _
    refine ⟨[], fun w => some w, by intro j hj; simp at hj, ?_, by simp, by simp, by simp [dc]⟩
    intro w hw
    refine ⟨by intro w' h; cases h; simpa using hw, fun x => ?_⟩
    rw [u_in (by omega)]; rfl
  | succ p ih =>
    intro hab
    obtain ⟨gs, m, hok, hm, hd, hc, hj⟩ := ih fun j hj => hab j (by omega)
    obtain ⟨hap, hbp⟩ := hab p (by omega)
    suffices hh : ∃ (hs : List Gate) (o : Option ℕ), Ok n (gs ++ hs) ∧
        (∀ w, o = some w → w < n + (gs ++ hs).length) ∧ (p ∈ Del → o = none) ∧
        (∀ x : Fin n → Bool, ov (gs ++ hs) (List.ofFn x) o =
          u n A a b Del L (List.ofFn x) (n + p)) ∧
        hs.length + (if p ∈ Del then 1 else 0) + (if p ∈ R then 1 else 0) ≤ 1 + (L p).length ∧
        dc n F (gs ++ hs) ≤ dc n F gs + if A p = true ∧ p ∉ Del ∧ ∃ x : Fin n → Bool,
          u n A a b Del L (List.ofFn x) (n + p) = true ∧ F x = false then 1 else 0 by
      obtain ⟨hs, o, h1, h2, h3, h4, h5, h6⟩ := hh
      refine ⟨gs ++ hs, Function.update m (n + p) o, h1, ?_, ?_, ?_, ?_⟩
      · intro w hw
        by_cases hwp : w = n + p
        · subst hwp; rw [Function.update_self]; exact ⟨h2, h4⟩
        · rw [Function.update_of_ne hwp]
          obtain ⟨q1, q2⟩ := hm w (by omega)
          refine ⟨fun w' hw' => by have := q1 w' hw'; simp; omega, fun x => ?_⟩
          rw [ov_ext gs hs _ _ (by simpa using q1), q2]
      · intro d hdd hdp
        by_cases hdp' : d = p
        · subst hdp'; rw [Function.update_self]; exact h3 hdd
        · rw [Function.update_of_ne (by omega)]; exact hd d hdd (by omega)
      · rw [Finset.range_add_one, Finset.filter_insert, Finset.filter_insert,
          Finset.sum_insert (by simp), List.length_append]
        split_ifs at h5 ⊢ with q1 q2 q2 <;>
          (try rw [Finset.card_insert_of_notMem (by simp)]) <;>
          (try rw [Finset.card_insert_of_notMem (by simp)]) <;> omega
      · rw [Finset.range_add_one, Finset.filter_insert]
        split_ifs at h6 ⊢ with q1
        · rw [Finset.card_insert_of_notMem (by simp)]; omega
        · omega
    by_cases hpd : p ∈ Del
    · have hpR : p ∉ R := fun h => (hR p h).2.1 hpd
      refine ⟨[], none, by simpa using hok, by simp, fun _ => rfl, fun x => ?_, ?_, by simp⟩
      · rw [u_del hpd]; rfl
      · rw [if_pos hpd, if_neg hpR]; simp
    obtain ⟨a1, a2⟩ := hm (a p) hap
    obtain ⟨b1, b2⟩ := hm (b p) hbp
    cases hA : A p with
    | false =>
      have hu := fun x : Fin n → Bool => u_or (L := L) (x := List.ofFn x) hpd hA hap hbp
      rcases ha0 : m (a p) with _ | s
      · refine ⟨[], m (b p), by simpa using hok, by simpa using b1, fun h => absurd h hpd,
          fun x => ?_, ?_, by simp⟩
        · rw [hu x, ← a2 x, ← b2 x, ha0]; simp [ov]
        · rw [if_neg hpd]; split_ifs <;> simp
      rcases hb0 : m (b p) with _ | t
      · refine ⟨[], m (a p), by simpa using hok, by simpa using a1, fun h => absurd h hpd,
          fun x => ?_, ?_, by simp⟩
        · rw [hu x, ← a2 x, ← b2 x, hb0]; simp [ov]
        · rw [if_neg hpd]; split_ifs <;> simp
      have hpR : p ∉ R := by
        intro h
        obtain ⟨_, _, d, hd1, hd2, hd3⟩ := hR p h
        have := hd d hd1 hd2
        rcases hd3 with h | h
        · rw [h, this] at ha0; cases ha0
        · rw [h, this] at hb0; cases hb0
      have hs := a1 s ha0
      have ht := b1 t hb0
      refine ⟨[⟨GateOp.or, [s, t]⟩], some (n + gs.length), ok_snoc hok (Or.inr rfl) hs ht,
        by intro w hw; cases hw; simp, fun h => absurd h hpd, fun x => ?_, ?_, ?_⟩
      · rw [ov_new gs n _ (by simp) _ _ _ hs ht, hu x, ← a2 x, ← b2 x, ha0, hb0]
        simp [ov, GateOp.eval]
      · rw [if_neg hpd, if_neg hpR]; simp
      · have := dc_snoc n F gs ⟨GateOp.or, [s, t]⟩
        rw [if_neg (by simp)] at this
        omega
    | true =>
      have hu := fun x : Fin n → Bool => u_and (L := L) (x := List.ofFn x) hpd hA hap hbp
      have hpR : p ∉ R := fun h => by rw [(hR p h).1] at hA; cases hA
      obtain ⟨hs, o', c1, c2, c3, c4, c5⟩ := chain n F (L p) (hL p) gs hok (m (a p)) a1
      rcases ho : o' with _ | s
      · refine ⟨hs, none, c1, by simp, fun _ => rfl, fun x => ?_, ?_, by omega⟩
        · have := c5 x
          rw [ho, a2 x] at this
          rw [hu x, ← this]; simp [ov]
        · rw [if_neg hpd, if_neg hpR]; omega
      rcases hb0 : m (b p) with _ | t
      · refine ⟨hs, none, c1, by simp, fun _ => rfl, fun x => ?_, ?_, by omega⟩
        · have := b2 x
          rw [hb0] at this
          rw [hu x, ← this]; simp [ov]
        · rw [if_neg hpd, if_neg hpR]; omega
      have hs' := c4 s ho
      have ht : t < n + (gs ++ hs).length := by have := b1 t hb0; simp; omega
      have hval : ∀ x : Fin n → Bool, ov (gs ++ hs ++ [⟨GateOp.and, [s, t]⟩]) (List.ofFn x)
          (some (n + (gs ++ hs).length)) = u n A a b Del L (List.ofFn x) (n + p) := by
        intro x
        rw [ov_new (gs ++ hs) n _ (by simp) _ _ _ hs' ht, hu x, ← a2 x, ← b2 x, ← c5 x, ho, hb0,
          ← ov_ext gs hs (List.ofFn x) (some t) (by intro w hw; cases hw; simpa using b1 t hb0)]
        simp [ov, GateOp.eval]
      refine ⟨hs ++ [⟨GateOp.and, [s, t]⟩], some (n + (gs ++ hs).length), ?_, ?_,
        fun h => absurd h hpd, fun x => ?_, ?_, ?_⟩
      · rw [← List.append_assoc]; exact ok_snoc c1 (Or.inl rfl) hs' ht
      · intro w hw; cases hw; simp
      · rw [← List.append_assoc]; exact hval x
      · rw [if_neg hpd, if_neg hpR]; simp; omega
      · rw [← List.append_assoc]
        have := dc_snoc n F (gs ++ hs) ⟨GateOp.and, [s, t]⟩
        have e : ((⟨GateOp.and, [s, t]⟩ : Gate).op = GateOp.and ∧ ∃ x : Fin n → Bool,
            (run (gs ++ hs ++ [⟨GateOp.and, [s, t]⟩]) (List.ofFn x)).getD
              (n + (gs ++ hs).length) false = true ∧ F x = false) ↔
            (true = true ∧ p ∉ Del ∧ ∃ x : Fin n → Bool,
              u n A a b Del L (List.ofFn x) (n + p) = true ∧ F x = false) := by
          refine ⟨fun h => ⟨rfl, hpd, ?_⟩, fun h => ⟨rfl, ?_⟩⟩
          · obtain ⟨x, h1, h2⟩ := h.2
            exact ⟨x, by rw [← hval x]; exact h1, h2⟩
          · obtain ⟨x, h1, h2⟩ := h.2.2
            exact ⟨x, by rw [← hval x] at h1; exact h1, h2⟩
        rw [if_congr e rfl rfl] at this
        omega

lemma gf {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ p q, G.Adj p q ∧ x p = true ∧ x q = true := by
  simp [graphFun]

lemma gD {n : ℕ} (x : Fin n → Bool) (p : Fin n) : (List.ofFn x).getD p.val false = x p := by
  simp [List.getD_eq_getElem?_getD]

lemma u_mono {n N : ℕ} {A : ℕ → Bool} {a b : ℕ → ℕ} {Del : Finset ℕ} {L : ℕ → List ℕ}
    (hab : ∀ j < N, a j < n + j ∧ b j < n + j) (x y : List Bool)
    (h : ∀ t, x.getD t false = true → y.getD t false = true) :
    ∀ w < n + N, u n A a b Del L x w = true → u n A a b Del L y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hx
    by_cases h9 : w < n
    · rw [u_in h9] at hx ⊢; exact h _ hx
    obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    obtain ⟨ha, hb⟩ := hab j (by omega)
    by_cases hd : j ∈ Del
    · rw [u_del hd] at hx; cases hx
    have ia := ih (a j) ha (by omega)
    have ib := ih (b j) hb (by omega)
    cases hA : A j with
    | true =>
      rw [u_and hd hA ha hb, Bool.and_eq_true, Bool.or_eq_true] at hx ⊢
      refine ⟨?_, ib hx.2⟩
      rcases hx.1 with h1 | h1
      · exact Or.inl (ia h1)
      · right
        rw [List.any_eq_true] at h1 ⊢
        obtain ⟨t, h2, h3⟩ := h1
        exact ⟨t, h2, h t h3⟩
    | false =>
      rw [u_or hd hA ha hb, Bool.or_eq_true] at hx ⊢
      rcases hx with h1 | h1
      · exact Or.inl (ia h1)
      · exact Or.inr (ib h1)

lemma gate2 {n : ℕ} {C : Circuit} (h : TopForm.IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    C.gates[j] = gateAt C j ∧ (gateAt C j).inputs = [TopForm.opnd C j 0, TopForm.opnd C j 1] ∧
    TopForm.opnd C j 0 < n + j ∧ TopForm.opnd C j 1 < n + j ∧
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) := by
  have e : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
  have hm : gateAt C j ∈ C.gates := by rw [e]; exact List.getElem_mem hj
  have hl := h.2.2 _ hm
  obtain ⟨s, t, hst⟩ := List.length_eq_two.1 hl
  have hb := h.2.1 j hj
  rw [hst] at hb
  have e0 : TopForm.opnd C j 0 = s := by unfold TopForm.opnd; rw [hst]; rfl
  have e1 : TopForm.opnd C j 1 = t := by unfold TopForm.opnd; rw [hst]; rfl
  refine ⟨e.symm, by rw [hst, e0, e1], by rw [e0]; exact hb s (by simp),
    by rw [e1]; exact hb t (by simp), h.1 _ hm⟩

lemma gDv {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (List.ofFn x).getD w false = x ⟨w, hw⟩ := gD x ⟨w, hw⟩

lemma ok_ao {n : ℕ} {gs : List Gate} {w : ℕ} (hok : Ok n gs) : TopForm.IsAO2 n ⟨gs, w⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hq
    obtain ⟨o', s', t', h1, h2, _⟩ := hok i hi
    rw [h1]; exact h2
  · intro j hj i hi
    obtain ⟨o', s', t', h1, h2, h3, h4⟩ := hok j hj
    have e1 : gateAt ⟨gs, w⟩ j = gs[j] := List.getD_eq_getElem _ _ hj
    rw [e1, h1] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> assumption
  · intro q hq
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hq
    obtain ⟨o', s', t', h1, h2, _⟩ := hok i hi
    rw [h1]; rfl

open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

def isAnd (C : Circuit) (j : ℕ) : Bool :=
  match (gateAt C j).op with
  | .and => true
  | _ => false

def val (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (run C.gates (List.ofFn x)).getD w false

def cutVal (n : ℕ) (C : Circuit) (Del : Finset ℕ) (x : Fin n → Bool) (w : ℕ) : Bool :=
  u n (isAnd C) (fun j => opnd C j 0) (fun j => opnd C j 1) Del (fun _ => []) (List.ofFn x) w

lemma val_in {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val n C x w = (List.ofFn x).getD w false := by
  exact run_input C.gates (List.ofFn x) w (by simpa using hw)

lemma val_rec {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (x : Fin n → Bool) (j : ℕ)
    (hj : j < C.gates.length) :
    val n C x (n + j) = if isAnd C j = true then
      val n C x (opnd C j 0) && val n C x (opnd C j 1)
    else val n C x (opnd C j 0) || val n C x (opnd C j 1) := by
  obtain ⟨heq, hin, ha, hb, hop⟩ := gate2 hC hj
  have hr := run_gate C.gates (List.ofFn x) j hj
  rw [List.length_ofFn, heq, hin] at hr
  rcases hop with hop | hop
  · simp only [val, hr, hop, List.map_cons, List.map_nil, if_pos ha, if_pos hb]
    simp [isAnd, hop, GateOp.eval]
  · simp only [val, hr, hop, List.map_cons, List.map_nil, if_pos ha, if_pos hb]
    simp [isAnd, hop, GateOp.eval]

lemma cutVal_le {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (Del : Finset ℕ)
    (x : Fin n → Bool) :
    ∀ w < n + C.gates.length, cutVal n C Del x w = true → val n C x w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw h
    by_cases hin : w < n
    · simpa only [cutVal, u_in hin, val_in C x w hin] using h
    obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    have hj : j < C.gates.length := by omega
    obtain ⟨_, _, ha, hb, _⟩ := gate2 hC hj
    by_cases hd : j ∈ Del
    · simp only [cutVal, u_del hd] at h
      cases h
    rw [val_rec C hC x j hj]
    cases hA : isAnd C j with
    | false =>
      simp only [hA, Bool.false_eq_true, ↓reduceIte]
      rw [cutVal, u_or hd hA ha hb, Bool.or_eq_true] at h
      rcases h with h | h
      · rw [Bool.or_eq_true]; exact Or.inl (ih _ ha (by omega) h)
      · rw [Bool.or_eq_true]; exact Or.inr (ih _ hb (by omega) h)
    | true =>
      simp only [hA, ↓reduceIte]
      rw [cutVal, u_and hd hA ha hb] at h
      simp only [List.any_nil, Bool.or_false, Bool.and_eq_true] at h
      rw [Bool.and_eq_true]; exact ⟨ih _ ha (by omega) h.1, ih _ hb (by omega) h.2⟩

lemma cutVal_mono {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (Del : Finset ℕ)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true)
    (w : ℕ) (hw : w < n + C.gates.length) :
    cutVal n C Del x w = true → cutVal n C Del y w = true := by
  have hab : ∀ j < C.gates.length, opnd C j 0 < n + j ∧ opnd C j 1 < n + j := by
    intro j hj
    exact ⟨(gate2 hC hj).2.2.1, (gate2 hC hj).2.2.2.1⟩
  have hget : ∀ t, (List.ofFn x).getD t false = true → (List.ofFn y).getD t false = true := by
    intro t ht
    by_cases ht' : t < n
    · rw [gDv y t ht']
      exact hxy ⟨t, ht'⟩ (by simpa only [gDv x t ht'] using ht)
    · have : (List.ofFn x).getD t false = false :=
        List.getD_eq_default _ _ (by simp; omega)
      rw [this] at ht
      cases ht
  exact u_mono hab (List.ofFn x) (List.ofFn y) hget w hw

lemma val_out {n : ℕ} (C : Circuit) (x : Fin n → Bool) :
    val n C x C.output = circuitFun n C x := rfl

lemma output_lt {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hF : circuitFun n C = graphFun G ∅) (hE : G.edgeFinset.Nonempty) :
    C.output < n + C.gates.length := by
  have hE' : ∃ p q, G.Adj p q := by
    obtain ⟨e, he⟩ := hE
    induction e using Sym2.ind with
    | _ p q => exact ⟨p, q, by simpa using he⟩
  obtain ⟨p, q, hpq⟩ := hE'
  have htrue : val n C (fun _ => true) C.output = true := by
    rw [val_out, hF]
    exact (gf G _).mpr ⟨p, q, hpq, rfl, rfl⟩
  by_contra h
  have hfalse : val n C (fun _ => true) C.output = false :=
    List.getD_eq_default _ _ (by rw [run_length, List.length_ofFn]; omega)
  rw [hfalse] at htrue
  cases htrue

lemma compile_cut {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (j : ℕ)
    (hj : j < C.gates.length) (hout : C.output < n + C.gates.length) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size < C.size ∧
      ∀ x : Fin n → Bool, circuitFun n D x = cutVal n C {j} x C.output := by
  obtain ⟨gs, m, hok, hm, _, hsize, _⟩ := build n (isAnd C)
    (fun k => opnd C k 0) (fun k => opnd C k 1) {j} ∅ (fun _ => [])
    (fun _ => false) (by simp) (by simp) C.gates.length
    (fun k hk => ⟨(gate2 hC hk).2.2.1, (gate2 hC hk).2.2.2.1⟩)
  have hcard : ((Finset.range C.gates.length).filter (· ∈ ({j} : Finset ℕ))).card = 1 := by
    have : (Finset.range C.gates.length).filter (· ∈ ({j} : Finset ℕ)) = {j} := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      omega
    rw [this]
    simp
  simp only [hcard, Finset.notMem_empty, Finset.filter_false, Finset.card_empty,
    Nat.add_zero, List.length_nil, Finset.sum_const_zero] at hsize
  rcases hm C.output hout with ⟨hbound, heq⟩
  cases ho : m C.output with
  | none =>
    refine ⟨⟨gs, n + gs.length⟩, ok_ao hok, by simp only [Circuit.size]; omega, ?_⟩
    intro x
    have hfalse : (run gs (List.ofFn x)).getD (n + gs.length) false = false :=
      List.getD_eq_default _ _ (by rw [run_length, List.length_ofFn])
    change (run gs (List.ofFn x)).getD (n + gs.length) false = _
    rw [hfalse]
    have hh := heq x
    simpa only [ho, ov, cutVal] using hh
  | some w =>
    refine ⟨⟨gs, w⟩, ok_ao hok, by simp only [Circuit.size]; omega, ?_⟩
    intro x
    change (run gs (List.ofFn x)).getD w false = _
    have hh := heq x
    simpa only [ho, ov, cutVal] using hh

lemma least_gate_critical {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hE : G.edgeFinset.Nonempty) (j : ℕ)
    (hj : j < C.gates.length) :
    ∃ p q : Fin n, G.Adj p q ∧ cutVal n C {j} (pairInput p q) C.output = false := by
  have hout := output_lt G C hL.2.1 hE
  by_contra h
  push Not at h
  have hF : ∀ x : Fin n → Bool, cutVal n C {j} x C.output = graphFun G ∅ x := by
    intro x
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hx
      have hval := cutVal_le C hL.1 {j} x C.output hout hx
      rwa [val_out, hL.2.1] at hval
    · intro hx
      obtain ⟨p, q, hpq, hp, hq⟩ := (gf G x).mp hx
      have hedge : cutVal n C {j} (pairInput p q) C.output = true := by
        cases ht : cutVal n C {j} (pairInput p q) C.output
        · exact (h p q hpq ht).elim
        · rfl
      apply cutVal_mono C hL.1 {j} (pairInput p q) x ?_ C.output hout hedge
      intro i hi
      have : i = p ∨ i = q := by simpa [pairInput] using hi
      rcases this with rfl | rfl <;> assumption
  obtain ⟨D, hAO, hsize, heq⟩ := compile_cut C hL.1 j hj hout
  have hDF : circuitFun n D = graphFun G ∅ := funext fun x => (heq x).trans (hF x)
  have hmin := hL.2.2 D hAO hDF
  omega

lemma least_nonempty_of_gate {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (j : ℕ) (hj : j < C.gates.length) :
    G.edgeFinset.Nonempty := by
  by_contra hempty
  have hempty : G.edgeFinset = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
  have hadj : ∀ p q : Fin n, ¬ G.Adj p q := by
    intro p q hpq
    have he : s(p, q) ∈ G.edgeFinset := by simpa using hpq
    rw [hempty] at he
    exact Finset.notMem_empty _ he
  let D : Circuit := ⟨[], n⟩
  have hAO : IsAO2 n D := by
    simp [IsAO2, AndOrOnly, ReadsBack, D]
  have hF : circuitFun n D = graphFun G ∅ := by
    funext x
    have hfalse : graphFun G ∅ x = false := by
      cases hx : graphFun G ∅ x with
      | false => rfl
      | true =>
        obtain ⟨p, q, hpq, _, _⟩ := (gf G x).mp hx
        exact (hadj p q hpq).elim
    rw [hfalse]
    simp [circuitFun, D, Circuit.eval, Circuit.wires, List.getD_eq_getElem?_getD]
  have hsize := hL.2.2 D hAO hF
  simp only [Circuit.size, D, List.length_nil] at hsize
  omega

end PEqualNP.Outside.L_meta_5012.CriticalEdge

namespace PEqualNP.Outside.L_meta_5012.CriticalEdge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

end PEqualNP.Outside.L_meta_5012.CriticalEdge

namespace PEqualNP.Outside.L_meta_5012.Diamond

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm
  PEqualNP.CleanedNonEdge

end PEqualNP.Outside.L_meta_5012.Diamond

namespace PEqualNP.Outside.L_meta_5012.Absorption

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma gateVal_eq_val (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j) := rfl

lemma binary_eval {n : ℕ} (C : Circuit) (j a b : ℕ) (o : GateOp)
    (hj : j < C.gates.length) (hgate : gateAt C j = ⟨o, [a, b]⟩)
    (ha : a < n + j) (hb : b < n + j) (x : Fin n → Bool) :
    val C (List.ofFn x) (n + j) = o.eval [val C (List.ofFn x) a, val C (List.ofFn x) b] := by
  rw [val_gate (n := n) (by simp) hj, hgate]
  simp [ha, hb]

lemma mem_junk_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (j : ℕ) : j ∈ junk G C ↔
      j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧
        ∃ x : Fin n → Bool, gateVal n C j x = true ∧ graphFun G ∅ x = false := by
  unfold junk gatesWhere
  rw [Finset.mem_filter, Finset.mem_range]
  simp only [IsDirtyAnd, IsDirty]
  tauto

end PEqualNP.Outside.L_meta_5012.Absorption

namespace PEqualNP.Outside.L_meta_5012.Absorption

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

end PEqualNP.Outside.L_meta_5012.Absorption

namespace PEqualNP.Outside.L_meta_5012

namespace Lift

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Core PEqualNP.ReadTwo

lemma foldl_wires_len (gs : List Gate) (acc : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc).length =
      acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_wires_getD_lt (gs : List Gate) (acc : List Bool) (i : ℕ) (hi : i < acc.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) acc).getD i false =
      acc.getD i false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]).length := by
      simp only [List.length_append, List.length_singleton]; omega
    rw [ih _ hlt]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_wires_getD_gate (gs : List Gate) (acc : List Bool) (j : ℕ) (hj : j < gs.length)
    (hback : ∀ k ∈ gs[j].inputs, k < acc.length + j) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) acc).getD
        (acc.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun k =>
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun m => w.getD m false)]) acc).getD
          k false) := by
  induction gs generalizing acc j with
  | nil => cases hj
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [Nat.add_zero, List.foldl_cons, List.getElem_cons_zero] at hback ⊢
      set acc' := acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]
      have hlen : acc.length < acc'.length := by
        simp only [acc', List.length_append, List.length_singleton]; omega
      rw [foldl_wires_getD_lt gs acc' acc.length hlen]
      have hlhs : acc'.getD acc.length false = g.op.eval (g.inputs.map fun k => acc.getD k false) := by
        simp only [acc', List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
          Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
      rw [hlhs]
      congr 1
      apply List.map_congr_left
      intro k hk
      have hka : k < acc.length := hback k hk
      have hka' : k < acc'.length := by omega
      rw [foldl_wires_getD_lt gs acc' k hka']
      simp only [acc', List.getD_eq_getElem?_getD, List.getElem?_append_left hka]
    | succ j' =>
      simp only [List.foldl_cons, List.getElem_cons_succ]
      set acc' := acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]
      have hlen' : acc'.length = acc.length + 1 := by
        simp only [acc', List.length_append, List.length_singleton]
      have hj' : j' < gs.length := by simp only [List.length_cons] at hj; omega
      have hidx : acc.length + (j' + 1) = acc'.length + j' := by omega
      rw [hidx]
      apply ih acc' j' hj'
      intro k hk
      have hbk := hback k (by simpa using hk)
      omega

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length :=
  foldl_wires_len C.gates x

lemma wval_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    wval C x i = x ⟨i, hi⟩ := by
  unfold wval Circuit.wires
  have hlt : i < (List.ofFn x).length := by simp [hi]
  rw [foldl_wires_getD_lt C.gates (List.ofFn x) i hlt]
  simp [List.getD_eq_getElem?_getD, hi]

lemma gateVal_eq_wval {n : ℕ} (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    gateVal n C j x = wval C x (n + j) := rfl

lemma wval_ge_len {n : ℕ} (C : Circuit) (x : Fin n → Bool) {w : ℕ} (hw : n + C.gates.length ≤ w) :
    wval C x w = false := by
  unfold wval
  rw [List.getD_eq_getElem?_getD]
  have hlen : (C.wires (List.ofFn x)).length = n + C.gates.length := by
    rw [wires_length, List.length_ofFn]
  rw [List.getElem?_eq_none (by omega)]
  rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  unfold gateAt
  simp [List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma gate_inputs_eq {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
  have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 _ (gateAt_mem hj)
  unfold opnd
  match h : (gateAt C j).inputs with
  | [a, b] => simp
  | [] => rw [h] at hlen; simp at hlen
  | [_] => rw [h] at hlen; simp at hlen
  | _ :: _ :: _ :: _ => rw [h] at hlen; simp at hlen

lemma opnd_mem {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b ∈ (gateAt C j).inputs := by
  rw [gate_inputs_eq hAO hj]
  fin_cases b <;> simp

lemma opnd_lt {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b < n + j :=
  hAO.2.1 j hj _ (opnd_mem hAO hj b)

lemma wval_gate_eval {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) :
    wval C x (n + j) = (gateAt C j).op.eval [wval C x (opnd C j 0), wval C x (opnd C j 1)] := by
  unfold wval Circuit.wires
  have hlen : (List.ofFn x).length = n := List.length_ofFn
  have hback : ∀ k ∈ C.gates[j].inputs, k < (List.ofFn x).length + j := by
    intro k hk; rw [hlen, ← gateAt_eq hj] at *; exact hAO.2.1 j hj k hk
  have h := foldl_wires_getD_gate C.gates (List.ofFn x) j hj hback
  rw [hlen] at h
  rw [h, ← gateAt_eq hj, gate_inputs_eq hAO hj]
  simp

lemma wval_gate_or {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) :
    wval C x (n + j) = (wval C x (opnd C j 0) || wval C x (opnd C j 1)) := by
  rw [wval_gate_eval hAO x hj, hop]; simp [GateOp.eval]

lemma foldl_cones_len (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) :
    (gs.foldl (coneStep n) acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, coneStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_cones_getD_lt (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) (i : ℕ) (hi : i < acc.length) :
    (gs.foldl (coneStep n) acc).getD i [] = acc.getD i [] := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (coneStep n acc g).length := by
      simp only [coneStep, List.length_append, List.length_singleton]; omega
    rw [ih _ hlt]
    simp only [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma cones_length (n : ℕ) (C : Circuit) : (cones n C).length = C.gates.length := by
  unfold cones; rw [foldl_cones_len]; simp

lemma foldl_cones_getD_gate (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl (coneStep n) acc).getD (acc.length + j) [] =
      (gs[j].inputs.filter (fun w => decide (n ≤ w ∧ w < n + (acc.length + j)))).flatMap
        (fun w => (w - n) :: (gs.foldl (coneStep n) acc).getD (w - n) []) := by
  induction gs generalizing acc j with
  | nil => cases hj
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [Nat.add_zero, List.foldl_cons, List.getElem_cons_zero]
      set acc' := coneStep n acc g
      have hlen : acc.length < acc'.length := by
        simp only [acc', coneStep, List.length_append, List.length_singleton]; omega
      rw [foldl_cones_getD_lt n gs acc' acc.length hlen]
      have hlhs : acc'.getD acc.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + acc.length))).flatMap
            (fun w => (w - n) :: acc.getD (w - n) []) := by
        simp only [acc', coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
          Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
      rw [hlhs]
      apply List.flatMap_congr
      intro w hw
      simp only [List.mem_filter, decide_eq_true_eq] at hw
      have hwn : w - n < acc.length := by omega
      have hwn' : w - n < acc'.length := by omega
      rw [foldl_cones_getD_lt n gs acc' (w - n) hwn']
      simp only [acc', coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hwn]
    | succ j' =>
      simp only [List.foldl_cons, List.getElem_cons_succ]
      set acc' := coneStep n acc g
      have hlen' : acc'.length = acc.length + 1 := by
        simp only [acc', coneStep, List.length_append, List.length_singleton]
      have hj' : j' < gs.length := by simp only [List.length_cons] at hj; omega
      have hidx : acc.length + (j' + 1) = acc'.length + j' := by omega
      rw [hidx]
      exact ih acc' j' hj'

lemma inCone_lt_len {n : ℕ} {C : Circuit} {i j : ℕ} (h : InCone n C i j) : j < C.gates.length := by
  by_contra hge
  unfold InCone at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [cones_length]; omega)] at h
  simp at h

lemma inCone_iff {n : ℕ} {C : Circuit} {i j : ℕ} (hj : j < C.gates.length) :
    InCone n C i j ↔
      ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ w < n + j ∧ (i = w - n ∨ InCone n C i (w - n)) := by
  unfold InCone cones
  have h := foldl_cones_getD_gate n C.gates [] j hj
  simp only [List.length_nil, Nat.zero_add] at h
  rw [h, ← gateAt_eq hj]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw1, hw2, hw3⟩, hw4⟩; exact ⟨w, hw1, hw2, hw3, hw4⟩
  · rintro ⟨w, hw1, hw2, hw3, hw4⟩; exact ⟨w, ⟨hw1, hw2, hw3⟩, hw4⟩

lemma inCone_trans {n : ℕ} {C : Circuit} {i j k : ℕ} (h1 : InCone n C i j) (h2 : InCone n C j k) :
    InCone n C i k := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    have hk := inCone_lt_len h2
    rw [inCone_iff hk] at h2 ⊢
    rcases h2 with ⟨w, hw, hnw, hwnk, rfl | hsub⟩
    · exact ⟨w, hw, hnw, hwnk, Or.inr h1⟩
    · exact ⟨w, hw, hnw, hwnk, Or.inr (ih (w - n) (by omega) hsub)⟩

end Lift

namespace Patch

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Core PEqualNP.ReadTwo

open Lift

def patch (C : Circuit) (j : ℕ) (g : Gate) : Circuit := ⟨C.gates.set j g, C.output⟩

lemma patch_length (C : Circuit) (j : ℕ) (g : Gate) :
    (patch C j g).gates.length = C.gates.length := by
  simp [patch]

lemma gateAt_patch_ne (C : Circuit) (j k : ℕ) (g : Gate) (hne : j ≠ k) :
    gateAt (patch C j g) k = gateAt C k := by
  simp [patch, gateAt, List.getD_eq_getElem?_getD, List.getElem?_set_ne hne]

lemma gateAt_patch_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) (g : Gate) :
    gateAt (patch C j g) j = g := by
  simp [patch, gateAt, List.getD_eq_getElem?_getD, hj]

lemma patch_isAO2 {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (j : ℕ) (g : Gate)
    (hOp : g.op = GateOp.and ∨ g.op = GateOp.or) (hLen : g.inputs.length = 2)
    (hBack : ∀ w ∈ g.inputs, w < n + j) : IsAO2 n (patch C j g) := by
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    change k ∈ C.gates.set j g at hk
    rcases List.mem_or_eq_of_mem_set hk with hk | rfl
    · exact hAO.1 k hk
    · exact hOp
  · intro k hk w hw
    have hkC : k < C.gates.length := by simpa only [patch_length] using hk
    by_cases hkj : k = j
    · subst k
      rw [gateAt_patch_eq hkC] at hw
      exact hBack w hw
    · rw [gateAt_patch_ne C j k g (Ne.symm hkj)] at hw
      exact hAO.2.1 k hkC w hw
  · intro k hk
    change k ∈ C.gates.set j g at hk
    rcases List.mem_or_eq_of_mem_set hk with hk | rfl
    · exact hAO.2.2 k hk
    · exact hLen

lemma patch_gateVal_eq_of_not_inCone {n : ℕ} {C : Circuit} {j : ℕ} {g : Gate}
    (hAO : IsAO2 n C) (hAO' : IsAO2 n (patch C j g)) (k : ℕ)
    (hne : j ≠ k) (hCone : ¬ InCone n C j k) (x : Fin n → Bool) :
    gateVal n (patch C j g) k x = gateVal n C k x := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    by_cases hk : k < C.gates.length
    · have hk' : k < (patch C j g).gates.length := by simpa only [patch_length] using hk
      have hgate := gateAt_patch_ne C j k g hne
      have hopnd (b : Fin 2) : opnd (patch C j g) k b = opnd C k b := by
        unfold opnd
        rw [hgate]
      have hval (b : Fin 2) : wval (patch C j g) x (opnd C k b) =
          wval C x (opnd C k b) := by
        by_cases hw : opnd C k b < n
        · rw [wval_input _ _ _ hw, wval_input _ _ _ hw]
        · have hw' : n ≤ opnd C k b := by omega
          have hlt := opnd_lt hAO hk b
          have hsub_ne : j ≠ opnd C k b - n := by
            intro he
            apply hCone
            exact (inCone_iff hk).mpr ⟨opnd C k b, opnd_mem hAO hk b, hw', hlt, Or.inl he⟩
          have hsub_cone : ¬ InCone n C j (opnd C k b - n) := by
            intro he
            apply hCone
            exact (inCone_iff hk).mpr ⟨opnd C k b, opnd_mem hAO hk b, hw', hlt, Or.inr he⟩
          have hv := ih (opnd C k b - n) (by omega) hsub_ne hsub_cone
          rw [gateVal_eq_wval, gateVal_eq_wval, Nat.add_sub_of_le hw'] at hv
          exact hv
      rw [gateVal_eq_wval, gateVal_eq_wval, wval_gate_eval hAO' x hk',
        wval_gate_eval hAO x hk, hgate, hopnd 0, hopnd 1, hval 0, hval 1]
    · rw [gateVal_eq_wval, gateVal_eq_wval, wval_ge_len _ _ (by rw [patch_length]; omega),
        wval_ge_len _ _ (by omega)]

lemma patch_size (C : Circuit) (j : ℕ) (g : Gate) : (patch C j g).size = C.size := by
  simp [Circuit.size, patch_length]

lemma patch_isLeastAO {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} {j : ℕ} {g : Gate} (hL : IsLeastAO G C)
    (hAO' : IsAO2 n (patch C j g)) (hF' : circuitFun n (patch C j g) = graphFun G ∅) :
    IsLeastAO G (patch C j g) := by
  refine ⟨hAO', hF', ?_⟩
  intro D hD hDF
  rw [patch_size]
  exact hL.2.2 D hD hDF

lemma patch_junk_mem_iff_of_not_inCone {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} {j : ℕ} {g : Gate} (hAO : IsAO2 n C) (hAO' : IsAO2 n (patch C j g))
    {k : ℕ} (hne : j ≠ k) (hCone : ¬ InCone n C j k) :
    k ∈ junk G (patch C j g) ↔ k ∈ junk G C := by
  change (k ∈ (Finset.range (patch C j g).gates.length).filter (fun i => IsDirtyAnd n G (patch C j g) i)) ↔
    k ∈ (Finset.range C.gates.length).filter (fun i => IsDirtyAnd n G C i)
  rw [Finset.mem_filter, Finset.mem_filter]
  simp only [Finset.mem_range, IsDirtyAnd, IsDirty, patch_length,
    gateAt_patch_ne C j k g hne, patch_gateVal_eq_of_not_inCone hAO hAO' k hne hCone]

end Patch

namespace IndependentDescent

open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

def product {n : ℕ} (P Q : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∃ p ∈ P, x p = true) && decide (∃ q ∈ Q, x q = true)

def Safe {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P Q : Finset (Fin n)) (w : Fin n) : Prop :=
  ∀ x : Fin n → Bool, product P Q x = true → x w = true → graphFun G ∅ x = true

lemma product_true {n : ℕ} (P Q : Finset (Fin n)) (x : Fin n → Bool) :
    product P Q x = true ↔ (∃ p ∈ P, x p = true) ∧ ∃ q ∈ Q, x q = true := by
  simp [product]

lemma wmax_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : PEqualNP.CircuitLowerBounds.Circuit) (g : ℕ) (P Q : Finset (Fin n))
    (heval : ∀ x : Fin n → Bool, gateVal n C g x = product P Q x) (w : Fin n) :
    w ∈ wmax G C g ↔ Safe G P Q w := by
  simp only [wmax, Finset.mem_filter, Finset.mem_univ, true_and, Safe]
  simp_rw [heval]

lemma graph_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, pairInput]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro h
    exact ⟨u, v, h, Or.inl rfl, Or.inr rfl⟩

end IndependentDescent

namespace Cases

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Core

lemma edge_nonempty_of_junk_nonempty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hJ : (junk G C).Nonempty) :
    G.edgeFinset.Nonempty := by
  by_contra hE
  have hnone : ∀ u v : Fin n, ¬ G.Adj u v := by
    intro u v huv
    exact hE ⟨s(u,v), by simpa using huv⟩
  let D : Circuit := ⟨[], n⟩
  have hD : IsAO2 n D := by simp [IsAO2, AndOrOnly, ReadsBack, D]
  have hDF : circuitFun n D = graphFun G ∅ := by
    funext x
    simp [circuitFun, Circuit.eval, Circuit.wires, D, graphFun, hnone]
  have hsize := hL.2.2 D hD hDF
  obtain ⟨j, hj⟩ := hJ
  have hjlt : j < C.gates.length := by
    exact Finset.mem_range.mp (Finset.mem_filter.mp hj).1
  simp only [Circuit.size, D, List.length_nil] at hsize
  omega

end Cases

namespace CleanReplacement

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
  PEqualNP.CleanedNonEdge PEqualNP.TopForm

def gateBit (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def stepWire (w : List Bool) (g : Gate) : List Bool := w ++ [gateBit w g]

def WiresLE (w z : List Bool) : Prop :=
  w.length = z.length ∧ ∀ i, w.getD i false = true → z.getD i false = true

def IsMonoGate (g : Gate) : Prop := g.op = GateOp.and ∨ g.op = GateOp.or

lemma monoGate_of_mem {C : Circuit} (hC : Monotone2 C) {g : Gate} (hg : g ∈ C.gates) :
    IsMonoGate g := by
  simpa [IsMonoGate] using (hC g hg).1

lemma bit_mono {w z : List Bool} (h : WiresLE w z) {g : Gate} (hg : IsMonoGate g)
    (hw : gateBit w g = true) : gateBit z g = true := by
  rcases hg with hop | hop
  · simp only [gateBit, hop, GateOp.eval, List.all_map, List.all_eq_true,
      Function.comp_apply, id_eq] at hw ⊢
    exact fun i hi => h.2 i (hw i hi)
  · simp only [gateBit, hop, GateOp.eval, List.any_map, List.any_eq_true,
      Function.comp_apply, id_eq] at hw ⊢
    obtain ⟨i, hi, hv⟩ := hw
    exact ⟨i, hi, h.2 i hv⟩

lemma append_mono {w z : List Bool} {a b : Bool} (h : WiresLE w z)
    (hab : a = true → b = true) : WiresLE (w ++ [a]) (z ++ [b]) := by
  refine ⟨by simp [h.1], ?_⟩
  intro i hi
  rw [List.getD_eq_getElem?_getD] at hi ⊢
  by_cases hlt : i < w.length
  · rw [List.getElem?_append_left hlt] at hi
    rw [List.getElem?_append_left (by rwa [← h.1])]
    simpa only [List.getD_eq_getElem?_getD] using h.2 i
      (by simpa only [List.getD_eq_getElem?_getD] using hi)
  · rw [List.getElem?_append_right (Nat.le_of_not_gt hlt)] at hi
    rw [List.getElem?_append_right (by rw [← h.1]; omega), ← h.1]
    cases hd : i - w.length with
    | zero =>
      simp only [hd, List.getElem?_cons_zero, Option.getD_some] at hi ⊢
      exact hab hi
    | succ k => simp [hd] at hi

lemma fold_mono (gs : List Gate) (hg : ∀ g ∈ gs, IsMonoGate g)
    {w z : List Bool} (h : WiresLE w z) :
    WiresLE (gs.foldl stepWire w) (gs.foldl stepWire z) := by
  induction gs generalizing w z with
  | nil => exact h
  | cons g gs ih =>
    exact ih (fun k hk => hg k (List.mem_cons_of_mem _ hk))
      (append_mono h (bit_mono h (hg g (by simp))))

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma fold_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (stepWire w g) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma ofFn_getD {n : ℕ} (x : Fin n → Bool) (u : Fin n) :
    (List.ofFn x).getD u.val false = x u := by
  simp [List.getD_eq_getElem?_getD]

lemma ofFn_mono {n : ℕ} {x y : Fin n → Bool} (h : ∀ u, x u = true → y u = true) :
    WiresLE (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp, ?_⟩
  intro i hi
  by_cases hlt : i < n
  · rw [ofFn_getD y ⟨i, hlt⟩]
    exact h ⟨i, hlt⟩ (by simpa only [ofFn_getD x ⟨i, hlt⟩] using hi)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hlt)] at hi
    cases hi

def patch (C : Circuit) (j : ℕ) (g : Gate) : Circuit := ⟨C.gates.set j g, C.output⟩

def earlierWires (C : Circuit) (j : ℕ) (w : List Bool) : List Bool :=
  (C.gates.take j).foldl stepWire w

def off : Gate := ⟨GateOp.or, []⟩

def edgeGate {n : ℕ} (u v : Fin n) : Gate := ⟨GateOp.and, [u.val, v.val]⟩

lemma off_bit (w : List Bool) : gateBit w off = false := rfl

lemma edge_bit {n : ℕ} (C : Circuit) (j : ℕ) (x : Fin n → Bool) (u v : Fin n) :
    gateBit (earlierWires C j (List.ofFn x)) (edgeGate u v) = (x u && x v) := by
  simp only [gateBit, edgeGate, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
    List.all_nil, id_eq, Bool.and_true]
  unfold earlierWires
  rw [fold_getD_lt _ _ _ (by simp), fold_getD_lt _ _ _ (by simp),
    ofFn_getD, ofFn_getD]

lemma wires_patch {C : Circuit} {j : ℕ} (hj : j < C.gates.length) (g : Gate) (w : List Bool) :
    (patch C j g).wires w = (C.gates.drop (j + 1)).foldl stepWire (stepWire (earlierWires C j w) g) := by
  change (C.gates.set j g).foldl stepWire w = _
  rw [List.set_eq_take_append_cons_drop, ite_eq_left hj, List.foldl_append, List.foldl_cons]
  rfl

lemma original_patch {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    patch C j C.gates[j] = C := by
  cases C with
  | mk gates output =>
    change Circuit.mk (gates.set j gates[j]) output = Circuit.mk gates output
    congr 1
    exact List.set_getElem_self hj

lemma patch_mono {C : Circuit} (hC : Monotone2 C) {j : ℕ} (hj : j < C.gates.length)
    (g h : Gate) (w : List Bool)
    (hbit : gateBit (earlierWires C j w) g = true → gateBit (earlierWires C j w) h = true) :
    WiresLE ((patch C j g).wires w) ((patch C j h).wires w) := by
  rw [wires_patch hj, wires_patch hj]
  apply fold_mono _ (fun k hk => monoGate_of_mem hC (List.mem_of_mem_drop hk))
  exact append_mono ⟨rfl, fun _ h => h⟩ hbit

lemma patch_bit {n : ℕ} {C : Circuit} {j : ℕ} (hj : j < C.gates.length)
    (g : Gate) (x : Fin n → Bool) :
    gateVal n (patch C j g) j x = gateBit (earlierWires C j (List.ofFn x)) g := by
  have hlen : (earlierWires C j (List.ofFn x)).length = n + j := by
    unfold earlierWires
    rw [fold_length]
    simp [Nat.min_eq_left (Nat.le_of_lt hj)]
  unfold gateVal
  rw [wires_patch hj, fold_getD_lt _ _ _ (by simp [stepWire, hlen]), ← hlen]
  simp [stepWire, List.getD_eq_getElem?_getD]

lemma gateAt_patch_ne (C : Circuit) (j k : ℕ) (g : Gate) (hne : j ≠ k) :
    gateAt (patch C j g) k = gateAt C k := by
  simp [patch, gateAt, List.getD_eq_getElem?_getD, List.getElem?_set_ne hne]

lemma graph_true {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
  simp [graphFun]

lemma pair_le {n : ℕ} {x : Fin n → Bool} {u v : Fin n}
    (hu : x u = true) (hv : x v = true) (k : Fin n) :
    pairInput u v k = true → x k = true := by
  simp only [pairInput, decide_eq_true_eq]
  rintro (rfl | rfl)
  · exact hu
  · exact hv

lemma circuit_mono {n : ℕ} {C : Circuit} (hC : Monotone2 C) {x y : Fin n → Bool}
    (hxy : ∀ u, x u = true → y u = true) :
    circuitFun n C x = true → circuitFun n C y = true :=
  (fold_mono C.gates (fun _ hg => monoGate_of_mem hC hg) (ofFn_mono hxy)).2 C.output

lemma mem_junk {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {j : ℕ} :
    j ∈ junk G C ↔ j < C.gates.length ∧ IsDirtyAnd n G C j := by
  unfold junk gatesWhere
  rw [Finset.mem_filter, Finset.mem_range]

lemma ao2_mono {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) : Monotone2 C := by
  intro g hg
  exact ⟨by simpa using hAO.1 g hg, Nat.le_of_eq (hAO.2.2 g hg)⟩

lemma no_clean_independent_replacement {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hL : IsLeastAO G C)
    (hOne : ∀ D : Circuit, IsLeastAO G D → (junk G D).card ≠ 1)
    {j k : ℕ} (hne : j ≠ k) (hJ : junk G C = {j,k})
    (hCone : ¬ InCone n C j k) (R : Gate)
    (hOp : R.op = GateOp.and ∨ R.op = GateOp.or)
    (hLen : R.inputs.length = 2) (hBack : ∀ w ∈ R.inputs, w < n + j)
    (hClean : ∀ x : Fin n → Bool, graphFun G ∅ x = false →
      gateBit (earlierWires C j (List.ofFn x)) R = false)
    (hCover : ∀ u v : Fin n, G.Adj u v →
      circuitFun n (patch C j off) (pairInput u v) = false →
      gateBit (earlierWires C j (List.ofFn (pairInput u v))) R = true) : False := by
  have hjmem : j ∈ junk G C := by rw [hJ]; simp
  have hkmem : k ∈ junk G C := by rw [hJ]; simp
  have hj : j < C.gates.length := (mem_junk.mp hjmem).1
  have hmono : Monotone2 C := ao2_mono hL.1
  let D := patch C j R
  have hDAO : IsAO2 n D := Patch.patch_isAO2 hL.1 j R hOp hLen hBack
  have hDM : Monotone2 D := ao2_mono hDAO
  have hnegative (x : Fin n → Bool) (hf : graphFun G ∅ x = false) :
      WiresLE (D.wires (List.ofFn x)) (C.wires (List.ofFn x)) := by
    have h := patch_mono hmono hj R C.gates[j] (List.ofFn x)
      (by intro hh; rw [hClean x hf] at hh; cases hh)
    rwa [original_patch hj] at h
  have hEdges (u v : Fin n) (huv : G.Adj u v) :
      circuitFun n D (pairInput u v) = true := by
    have hF : circuitFun n C (pairInput u v) = true := by
      rw [hL.2.1]
      exact (graph_true G _).mpr ⟨u,v,huv,by simp [pairInput],by simp [pairInput]⟩
    cases hCut : circuitFun n (patch C j off) (pairInput u v) with
    | false =>
      have h := patch_mono hmono hj C.gates[j] R (List.ofFn (pairInput u v))
        (fun _ => hCover u v huv hCut)
      rw [original_patch hj] at h
      exact h.2 C.output hF
    | true =>
      exact (patch_mono hmono hj off R (List.ofFn (pairInput u v))
        (by intro hh; simp [off_bit] at hh)).2 C.output hCut
  have hDF : circuitFun n D = graphFun G ∅ := by
    funext x
    cases hf : graphFun G ∅ x with
    | false =>
      cases hd : circuitFun n D x with
      | false => rfl
      | true =>
        have hh : circuitFun n C x = true := (hnegative x hf).2 C.output hd
        rw [hL.2.1,hf] at hh
        cases hh
    | true =>
      obtain ⟨u,v,huv,hu,hv⟩ := (graph_true G x).mp hf
      exact circuit_mono hDM (pair_le hu hv) (hEdges u v huv)
  have hNoJ : j ∉ junk G D := by
    intro hmem
    obtain ⟨_,_,_,x,hx,hf⟩ := mem_junk.mp hmem
    change gateVal n (patch C j R) j x = true at hx
    rw [patch_bit hj, hClean x hf] at hx
    cases hx
  have hSub : junk G D ⊆ junk G C := by
    intro a ha
    have hja : j ≠ a := by intro he; exact hNoJ (he.symm ▸ ha)
    obtain ⟨haLen,haAnd,_,x,hx,hf⟩ := mem_junk.mp ha
    have haC : a < C.gates.length := by simpa [D,patch] using haLen
    have haOp : (gateAt C a).op = GateOp.and := by
      change (gateAt (patch C j R) a).op = GateOp.and at haAnd
      rwa [gateAt_patch_ne C j a R hja] at haAnd
    exact mem_junk.mpr ⟨haC,haOp,haC,x,(hnegative x hf).2 (n+a) hx,hf⟩
  have hkD : k ∈ junk G D :=
    (Patch.patch_junk_mem_iff_of_not_inCone hL.1 hDAO hne hCone).mpr hkmem
  have hJD : junk G D = {k} := by
    apply Finset.ext
    intro a
    constructor
    · intro ha
      have hao := hSub ha
      rw [hJ] at hao
      simp only [Finset.mem_insert,Finset.mem_singleton] at hao ⊢
      rcases hao with rfl | he
      · exact (hNoJ ha).elim
      · exact he
    · intro ha
      have he := Finset.mem_singleton.mp ha
      exact he ▸ hkD
  have hDL : IsLeastAO G D := Patch.patch_isLeastAO hL hDAO hDF
  exact hOne D hDL (by rw [hJD]; simp)

end CleanReplacement

namespace FlagReduction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo

open CleanReplacement IndependentDescent

lemma earlier_wire_eq {n : ℕ} (C : Circuit) (j : ℕ) (hj : j ≤ C.gates.length)
    (x : Fin n → Bool) {w : ℕ} (hw : w < n + j) :
    (earlierWires C j (List.ofFn x)).getD w false = wval C x w := by
  have hlen : (earlierWires C j (List.ofFn x)).length = n + j := by
    unfold earlierWires
    rw [fold_length]
    simp [Nat.min_eq_left hj]
  have hsplit : C.wires (List.ofFn x) =
      (C.gates.drop j).foldl stepWire (earlierWires C j (List.ofFn x)) := by
    change C.gates.foldl stepWire _ = _
    conv_lhs => rw [← List.take_append_drop j C.gates, List.foldl_append]
    rfl
  unfold wval
  rw [hsplit, fold_getD_lt _ _ _ (by omega)]

lemma star_gate_bit {n : ℕ} (C : Circuit) (j : ℕ) (hj : j ≤ C.gates.length)
    (z : Fin n) (w : ℕ) (hw : w < n + j) (x : Fin n → Bool) :
    gateBit (earlierWires C j (List.ofFn x)) ⟨GateOp.and,[z.val,w]⟩ =
      (x z && wval C x w) := by
  simp only [gateBit, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
    List.all_nil, id_eq, Bool.and_true]
  rw [earlier_wire_eq C j hj x (by have := z.isLt; omega),
    earlier_wire_eq C j hj x hw, Lift.wval_input C x z.val z.isLt]

end FlagReduction

namespace RawOperands

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq_foldl, foldl_stepWire_length, List.length_ofFn]

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

def W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then W n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, foldl_stepWire_length, hpre_len]
  have hCj : W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + k) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append]
    exact (foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact getD_ge_length w0 i (by omega)

lemma W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    W n C x u = x ⟨u, hu⟩ := by
  simp only [W]
  rw [wires_eq_foldl, foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]

open PEqualNP.CleanedNonEdge in
lemma orFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

open PEqualNP.CleanedNonEdge in
lemma orStep_mem_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) (x : ℕ) :
    x ∈ (orStep n cs g).getD cs.length [] ↔ x = cs.length ∨ (g.op = GateOp.or ∧
      ∃ w ∈ g.inputs, n ≤ w ∧ w < n + cs.length ∧ x ∈ cs.getD (w - n) []) := by
  by_cases h : g.op = GateOp.or
  · simp only [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl, h,
      ↓reduceIte, true_and, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some,
      List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro (h1 | ⟨w, ⟨hw, hn, hlt⟩, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, hw, hn, hlt, hx⟩
    · rintro (h1 | ⟨w, hw, hn, hlt, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, ⟨hw, hn, hlt⟩, hx⟩
  · simp [orStep, List.getD_eq_getElem?_getD, h]

open PEqualNP.CleanedNonEdge in
lemma orStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (orStep n cs g).getD m [] = cs.getD m [] := by
  simp [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

open PEqualNP.CleanedNonEdge in
lemma orFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (orStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (orStep n cs g) (by simp [orStep]; omega)]
    exact orStep_getD_lt n cs g k hk

open PEqualNP.CleanedNonEdge in
lemma orSets_mem_iff (n : ℕ) (C : Circuit) (k x : ℕ) (hk : k < C.gates.length) :
    x ∈ (orSets n C).getD k [] ↔ x = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧ x ∈ (orSets n C).getD (w - n) []) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : orSets n C = post.foldl (orStep n) (orStep n (pre.foldl (orStep n) []) gk) := by
    simp only [orSets]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (orStep n) []).length = k := by
    rw [orFold_length]; simp [hpre_len]
  have hl1 : (orStep n (pre.foldl (orStep n) []) gk).length = k + 1 := by
    simp [orStep, hl0]
  have h1 : (orSets n C).getD k [] = (orStep n (pre.foldl (orStep n) []) gk).getD k [] := by
    rw [hc, orFold_getD_lt n post _ k (by omega)]
  have h2 : ∀ m, m < k → (orSets n C).getD m [] = (pre.foldl (orStep n) []).getD m [] := by
    intro m hm
    rw [hc, orFold_getD_lt n post _ m (by omega)]
    exact orStep_getD_lt n _ gk m (by omega)
  have h3 := orStep_mem_last n (pre.foldl (orStep n) []) gk x
  rw [hl0] at h3
  rw [h1, h3]
  constructor
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [h2 (w - n) (by omega)]; exact hx⟩
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [← h2 (w - n) (by omega)]; exact hx⟩

lemma W_or (n : ℕ) (C : Circuit) (x : Fin n → Bool) (r : ℕ) (hr : r < C.gates.length)
    (hop : (gateAt C r).op = GateOp.or) (i : ℕ) (hi : i ∈ (gateAt C r).inputs)
    (hlt : i < n + r) (hv : W n C x i = true) : W n C x (n + r) = true := by
  rw [W_gate n C x r hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  exact ⟨i, hi, by rw [ite_eq_left hlt]; exact hv⟩

open PEqualNP.CleanedNonEdge in
lemma reach_val (n : ℕ) (C : Circuit) (x : Fin n → Bool) (g : ℕ)
    (hv : W n C x (n + g) = true) :
    ∀ k, k < C.gates.length → g ∈ (orSets n C).getD k [] → W n C x (n + k) = true := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk hmem
    rcases (orSets_mem_iff n C k g hk).mp hmem with h | ⟨hop, w, hw, hn, hlt, hx⟩
    · rw [← h]; exact hv
    · have h3 := ih (w - n) (by omega) (by omega) hx
      have e : n + (w - n) = w := by omega
      rw [e] at h3
      exact W_or n C x k hk hop w hw hlt h3

open PEqualNP.CleanedNonEdge in
lemma reach_up (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w g : ℕ)
    (h : OrReaches n C w g) (hv : W n C x (n + g) = true) : W n C x w = true := by
  obtain ⟨hn, hmem⟩ := h
  by_cases hk : w - n < C.gates.length
  · have h3 := reach_val n C x g hv (w - n) hk hmem
    have e : n + (w - n) = w := by omega
    rw [e] at h3
    exact h3
  · exfalso
    have hlen : (orSets n C).length = C.gates.length := by
      unfold orSets; rw [orFold_length]; simp
    have hge : (orSets n C).length ≤ w - n := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge] at hmem
    simp at hmem

lemma mem_filter_gen {α : Type} (p : α → Prop) (d : DecidablePred p) (s : Finset α) (a : α)
    (h : a ∈ @Finset.filter α p d s) : p a :=
  ((@Finset.mem_filter α p d s a).mp h).2

lemma side_val (n : ℕ) (C : Circuit) (x : Fin n → Bool) (j : ℕ) (b : Fin 2) (i : Fin n)
    (hi : i ∈ PEqualNP.TopForm.side (n := n) C j b) (hx : x i = true) :
    W n C x (PEqualNP.TopForm.opnd C j b) = true := by
  unfold PEqualNP.TopForm.side PEqualNP.TopForm.orIn at hi
  have hi2 := mem_filter_gen _ _ _ _ hi
  rcases hi2 with h | ⟨k, hk, hreach, hop, hin⟩
  · rw [← h, W_input n C x i.val i.isLt]; exact hx
  · have hk1 : W n C x (n + k) = true := by
      apply W_or n C x k hk hop i.val hin (by have := i.isLt; omega)
      rw [W_input n C x i.val i.isLt]; exact hx
    exact reach_up n C x _ k hreach hk1

open PEqualNP.EdgeOwnership in
lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

open PEqualNP.EdgeOwnership in
lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

open PEqualNP.EdgeOwnership in
lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

lemma gateAt_mem' (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq C j hj]; exact List.getElem_mem hj

open PEqualNP.EdgeOwnership in
lemma inCone_lt (n : ℕ) (C : Circuit) : ∀ j i, InCone n C i j → i < j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro i h
    obtain ⟨_, k, hk, _, h3⟩ := (inCone_iff n C i j).mp h
    rcases h3 with h3 | h3
    · omega
    · have := ih k hk i h3; omega

open PEqualNP.CleanedNonEdge in
lemma orReach_trans (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (w : ℕ) (hw : w ∈ (gateAt C k).inputs)
    (hlt : w < n + k) (g : ℕ) (h : OrReaches n C w g) : OrReaches n C (n + k) g := by
  obtain ⟨hn, hmem⟩ := h
  refine ⟨by omega, ?_⟩
  have e : n + k - n = k := by omega
  rw [e]
  exact (orSets_mem_iff n C k g hk).mpr (Or.inr ⟨hop, w, hw, hn, hlt, hmem⟩)

open PEqualNP.CleanedNonEdge in
lemma orReach_self (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    OrReaches n C (n + k) k := by
  refine ⟨by omega, ?_⟩
  have e : n + k - n = k := by omega
  rw [e]
  exact (orSets_mem_iff n C k k hk).mpr (Or.inl rfl)

lemma orIn_mem (n : ℕ) (C : Circuit) (w : ℕ) (i : Fin n) :
    i ∈ PEqualNP.TopForm.orIn n C w ↔ ((i : ℕ) = w ∨ ∃ k < C.gates.length,
      PEqualNP.CleanedNonEdge.OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧
        (i : ℕ) ∈ (gateAt C k).inputs) := by
  unfold PEqualNP.TopForm.orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

open PEqualNP.CleanedNonEdge in
lemma down (n : ℕ) (C : Circuit) (x : Fin n → Bool)
    (hAO : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) :
    ∀ w, W n C x w = true → (∃ i : Fin n, i ∈ PEqualNP.TopForm.orIn n C w ∧ x i = true) ∨
      ∃ k, k < C.gates.length ∧ OrReaches n C w k ∧ (gateAt C k).op = GateOp.and ∧
        W n C x (n + k) = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hwn : w < n
    · left
      refine ⟨⟨w, hwn⟩, (orIn_mem n C w _).mpr (Or.inl rfl), ?_⟩
      rw [← W_input n C x w hwn]; exact hv
    · by_cases hk : w - n < C.gates.length
      · have hw : w = n + (w - n) := by omega
        set k := w - n with hkdef
        rcases hAO k hk with hop | hop
        · right
          refine ⟨k, hk, ?_, hop, ?_⟩
          · rw [hw]; exact orReach_self n C k hk
          · rw [← hw]; exact hv
        · have hv2 := hv
          rw [hw, W_gate n C x k hk, hop] at hv2
          simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at hv2
          obtain ⟨i, hi, hiv⟩ := hv2
          split_ifs at hiv with hlt
          rcases ih i (by omega) hiv with ⟨j, hj, hxj⟩ | ⟨k', hk', hr, hop', hv'⟩
          · left
            refine ⟨j, ?_, hxj⟩
            rw [orIn_mem] at hj ⊢
            right
            rcases hj with hj | ⟨k'', hk'', hr, hop'', hin⟩
            · refine ⟨k, hk, ?_, hop, ?_⟩
              · rw [hw]; exact orReach_self n C k hk
              · rw [hj]; exact hi
            · refine ⟨k'', hk'', ?_, hop'', hin⟩
              rw [hw]; exact orReach_trans n C k hk hop i hi hlt k'' hr
          · right
            refine ⟨k', hk', ?_, hop', hv'⟩
            rw [hw]; exact orReach_trans n C k hk hop i hi hlt k' hr
      · exfalso
        have hl := wires_length n C x
        have : W n C x w = false := getD_ge_length _ w (by omega)
        rw [this] at hv; exact Bool.false_ne_true hv

open PEqualNP.EdgeOwnership in
lemma orSets_cone (n : ℕ) (C : Circuit) : ∀ m, m < C.gates.length → ∀ k,
    k ∈ (PEqualNP.CleanedNonEdge.orSets n C).getD m [] → k = m ∨ InCone n C k m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm k hk
    rcases (orSets_mem_iff n C m k hm).mp hk with h | ⟨_, w, hw, hn, hlt, hx⟩
    · exact Or.inl h
    · right
      have h2 := ih (w - n) (by omega) (by omega) k hx
      have e : n + (w - n) = w := by omega
      exact (inCone_iff n C k m).mpr ⟨hm, w - n, by omega, by rw [e]; exact hw, h2⟩

open PEqualNP.EdgeOwnership in
lemma reach_cone (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (o : ℕ)
    (ho : o ∈ (gateAt C j).inputs) (hlt : o < n + j) (k : ℕ)
    (h : PEqualNP.CleanedNonEdge.OrReaches n C o k) : InCone n C k j := by
  obtain ⟨hn, hmem⟩ := h
  have h2 := orSets_cone n C (o - n) (by omega) k hmem
  have e : n + (o - n) = o := by omega
  exact (inCone_iff n C k j).mpr ⟨hj, o - n, by omega, by rw [e]; exact ho, h2⟩

open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

lemma junk_data {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (j : ℕ) (hj : j ∈ junk G C) :
    j < C.gates.length ∧ (gateAt C j).op = GateOp.and := by
  obtain ⟨hjl, hja, _⟩ := Finset.mem_filter.mp hj
  exact ⟨Finset.mem_range.mp hjl, hja⟩

lemma operand_mem {n : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b ∈ (gateAt C j).inputs := by
  have hlen := hAO.2.2 _ (gateAt_mem' C j hj)
  unfold opnd
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  exact List.getElem_mem _

lemma raw_operand_of_no_junk_cone {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C)
    (j : ℕ) (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and)
    (hno : ∀ k ∈ junk G C, ¬ InCone n C k j) (b : Fin 2) (x : Fin n → Bool) :
    PEqualNP.ReadTwo.wval C x (opnd C j b) =
      decide (∃ u ∈ side (n := n) C j b, x u = true) := by
  have hm := operand_mem C hAO j hj b
  have hlt := hAO.2.1 j hj _ hm
  have hi : W n C x (opnd C j b) = true ↔
      ∃ u ∈ side (n := n) C j b, x u = true := by
    constructor
    · intro hv
      have hops : ∀ k < C.gates.length,
          (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or :=
        fun k hk => hAO.1 _ (gateAt_mem' C k hk)
      rcases down n C x hops _ hv with hraw | ⟨k, hk, hr, hop, _⟩
      · exact hraw
      · have hc := reach_cone n C j hj _ hm hlt k hr
        have hnb : ¬ BelowF G C k := fun hb => hTop k hk j hj hop hb hand hc
        have hd : ∃ y : Fin n → Bool, gateVal n C k y = true ∧ graphFun G ∅ y = false := by
          by_contra hn
          apply hnb
          intro y hy
          by_contra hf
          exact hn ⟨y, hy, Bool.eq_false_iff.mpr hf⟩
        have hkj : k ∈ junk G C :=
          Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hop, hk, hd⟩
        exact (hno k hkj hc).elim
    · rintro ⟨u, hu, hxu⟩
      exact side_val n C x j b u hu hxu
  change W n C x (opnd C j b) = _
  by_cases hv : W n C x (opnd C j b) = true
  · simp [hv, hi.mp hv]
  · have hn : ¬ ∃ u ∈ side (n := n) C j b, x u = true := fun h => hv (hi.mpr h)
    simp [Bool.eq_false_iff.mpr hv, hn]

lemma independent_no_junk_ancestors {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g h : ℕ) (hJ : junk G C = {g, h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (j : ℕ) (hj : j = g ∨ j = h) :
    ∀ k ∈ junk G C, ¬ InCone n C k j := by
  intro k hk hc
  have hkm : k = g ∨ k = h := by simpa [hJ] using hk
  rcases hj with rfl | rfl <;> rcases hkm with rfl | rfl
  · have := inCone_lt n C _ _ hc
    omega
  · exact hhg hc
  · exact hgh hc
  · have := inCone_lt n C _ _ hc
    omega

lemma independent_operand {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C)
    (g h : ℕ) (hJ : junk G C = {g, h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (j : ℕ) (hj : j = g ∨ j = h) (b : Fin 2) (x : Fin n → Bool) :
    PEqualNP.ReadTwo.wval C x (opnd C j b) =
      decide (∃ u ∈ side (n := n) C j b, x u = true) := by
  have hjm : j ∈ junk G C := by simpa [hJ] using hj
  obtain ⟨hjl, hja⟩ := junk_data G C j hjm
  exact raw_operand_of_no_junk_cone G C hAO hTop j hjl hja
    (independent_no_junk_ancestors G C g h hJ hgh hhg j hj) b x

lemma and_gate_eq {n : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and)
    (x : Fin n → Bool) :
    gateVal n C j x =
      (PEqualNP.ReadTwo.wval C x (opnd C j 0) && PEqualNP.ReadTwo.wval C x (opnd C j 1)) := by
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem' C j hj))
  have ham : a ∈ (gateAt C j).inputs := by simp [hab]
  have hbm : b ∈ (gateAt C j).inputs := by simp [hab]
  have hba := hAO.2.1 j hj a ham
  have hbb := hAO.2.1 j hj b hbm
  change W n C x (n + j) = _
  rw [W_gate n C x j hj, hand, hab]
  simp [GateOp.eval, opnd, hab, hba, hbb, W, PEqualNP.ReadTwo.wval]

lemma independent_product {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C)
    (g h : ℕ) (hJ : junk G C = {g, h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (j : ℕ) (hj : j = g ∨ j = h) (x : Fin n → Bool) :
    gateVal n C j x =
      (decide (∃ u ∈ side (n := n) C j 0, x u = true) &&
        decide (∃ u ∈ side (n := n) C j 1, x u = true)) := by
  have hjm : j ∈ junk G C := by simpa [hJ] using hj
  obtain ⟨hjl, hja⟩ := junk_data G C j hjm
  rw [and_gate_eq C hAO j hjl hja x,
    independent_operand G C hAO hTop g h hJ hgh hhg j hj 0 x,
    independent_operand G C hAO hTop g h hJ hgh hhg j hj 1 x]

end RawOperands

namespace Critical.Base

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [ite_eq_right hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [ite_eq_left hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h'; exact ⟨hlt, h'⟩
    · rw [ite_eq_right hlt] at h'; cases h'
  · intro h i hi
    rw [ite_eq_left (h i hi).1]; exact (h i hi).2

lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma gateVal_eq_val (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j) := rfl

def OrStep (n : ℕ) (C : Circuit) (w w' : ℕ) : Prop :=
  ∃ k, k < C.gates.length ∧ w = n + k ∧ (gateAt C k).op = GateOp.or ∧
    w' ∈ (gateAt C k).inputs ∧ w' < n + k

lemma orStep_up {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') (hv : val C x w' = true) :
    val C x w = true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head hstep _ ih =>
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (val_or hx hk hop).mpr ⟨_, hin, hlt, ih⟩

lemma or_trace {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) :
    ∀ w : ℕ, val C x w = true →
      ∃ w', Relation.ReflTransGen (OrStep n C) w w' ∧ val C x w' = true ∧
        (w' < n ∨ ∃ h, h < C.gates.length ∧ w' = n + h ∧ (gateAt C h).op ≠ GateOp.or) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · exact ⟨w, Relation.ReflTransGen.refl, hv, Or.inl hw⟩
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [val_ge hx hlen] at hv; cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        by_cases hop : (gateAt C k).op = GateOp.or
        · obtain ⟨i, hin, hlt, hi⟩ := (val_or hx hk hop).mp hv
          obtain ⟨w', hr, hv', hw'⟩ := ih i hlt hi
          exact ⟨w', Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hin, hlt⟩ hr, hv', hw'⟩
        · exact ⟨n + k, Relation.ReflTransGen.refl, hv, Or.inr ⟨k, hk, rfl, hop⟩⟩

lemma pairInput_left {n : ℕ} (u v : Fin n) : pairInput u v u = true := by
  simp [pairInput]

lemma pairInput_right {n : ℕ} (u v : Fin n) : pairInput u v v = true := by
  simp [pairInput]

lemma pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
  simp [pairInput]

lemma graphFun_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, pairInput_true]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro h
    exact ⟨u, v, h, Or.inl rfl, Or.inr rfl⟩

lemma operand_trace {n : ℕ} {C : Circuit} (u v : Fin n) (p : ℕ)
    (hv : val C (List.ofFn (pairInput u v)) p = true) :
    (∃ t : Fin n, (t = u ∨ t = v) ∧ Relation.ReflTransGen (OrStep n C) p t.val) ∨
    (∃ h, h < C.gates.length ∧ (gateAt C h).op ≠ GateOp.or ∧
      Relation.ReflTransGen (OrStep n C) p (n + h) ∧
      val C (List.ofFn (pairInput u v)) (n + h) = true) := by
  obtain ⟨w', hr, hv', hw'⟩ := or_trace (n := n) (C := C) (x := List.ofFn (pairInput u v))
    (by simp) p hv
  rcases hw' with hlt | ⟨h, hh, rfl, hop⟩
  · left
    refine ⟨⟨w', hlt⟩, ?_, hr⟩
    have h1 := val_ofFn C (pairInput u v) ⟨w', hlt⟩
    rw [show (⟨w', hlt⟩ : Fin n).val = w' from rfl, hv'] at h1
    exact (pairInput_true u v _).mp h1.symm
  · right
    exact ⟨h, hh, hop, hr, hv'⟩

lemma reach_var_val {n : ℕ} {C : Circuit} (x : Fin n → Bool) (p : ℕ) (t : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p t.val) (ht : x t = true) :
    val C (List.ofFn x) p = true :=
  orStep_up (n := n) (by simp) hr (by rw [val_ofFn]; exact ht)

lemma edge_trace {n : ℕ} (G : SimpleGraph (Fin n)) {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hF : ∀ u v : Fin n, F (pairInput u v) = true → G.Adj u v)
    (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x)
    (u v : Fin n) (huv : F (pairInput u v) = true) :
    ∃ a, a < C.gates.length ∧ (gateAt C a).op ≠ GateOp.or ∧
      Relation.ReflTransGen (OrStep n C) C.output (n + a) ∧
      val C (List.ofFn (pairInput u v)) (n + a) = true := by
  rcases operand_trace (C := C) u v C.output (by rw [hout]; exact huv) with
    ⟨t, _, hr⟩ | h
  · exfalso
    have h1 := reach_var_val (pairInput t t) _ t hr (pairInput_left t t)
    rw [hout] at h1
    exact G.irrefl (hF t t h1)
  · exact h

lemma below_of_reach {n : ℕ} {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x) (a : ℕ)
    (hr : Relation.ReflTransGen (OrStep n C) C.output (n + a)) (x : Fin n → Bool)
    (hv : val C (List.ofFn x) (n + a) = true) : F x = true := by
  rw [← hout]
  exact orStep_up (n := n) (by simp) hr hv

lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

lemma orStep_le {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') : w' ≤ w := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact le_rfl
  | head hstep _ ih =>
    obtain ⟨k, _, rfl, _, _, hlt⟩ := hstep
    omega

lemma orStep_cone {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') :
    ∀ k h', w = n + k → w' = n + h' → h' = k ∨ InCone n C h' k := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => intro k h' h1 h2; left; omega
  | @head a c hstep hrest ih =>
    intro k h' h1 h2
    obtain ⟨k0, hk0, e, _, hin, hlt⟩ := hstep
    have hk : k0 = k := by omega
    subst hk
    have hle := orStep_le hrest
    obtain ⟨k1, hk1⟩ : ∃ k1, c = n + k1 := ⟨c - n, by omega⟩
    subst hk1
    right
    rw [inCone_iff]
    exact ⟨hk0, k1, by omega, hin, ih k1 h' rfl h2⟩

lemma operand_cone {n : ℕ} {C : Circuit} {a p h : ℕ} (ha : a < C.gates.length)
    (hin : p ∈ (gateAt C a).inputs) (hp : p < n + a)
    (hr : Relation.ReflTransGen (OrStep n C) p (n + h)) : InCone n C h a := by
  have hle := orStep_le hr
  obtain ⟨k1, rfl⟩ : ∃ k1, p = n + k1 := ⟨p - n, by omega⟩
  rw [inCone_iff]
  exact ⟨ha, k1, by omega, hin, orStep_cone hr k1 h rfl rfl⟩

lemma orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (orStep n (gs.foldl (orStep n) []) g).getD k [] =
          (gs.foldl (orStep n) []).getD k [] := by
      intro k hk
      simp only [orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
        simp only [orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold OrReaches orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

lemma reach_orReaches {n : ℕ} {C : Circuit} {w w2 : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w2) :
    ∀ g, w2 = n + g → g < C.gates.length → OrReaches n C w g := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro g h1 hg
    subst h1
    exact (orReaches_iff n C g g).mpr ⟨hg, Or.inl rfl⟩
  | @head a c hstep hrest ih =>
    intro g h1 hg
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (orReaches_iff n C k g).mpr ⟨hk, Or.inr ⟨hop, c, hin, hlt, ih g h1 hg⟩⟩

lemma orReaches_reach {n : ℕ} {C : Circuit} (g : ℕ) :
    ∀ w, OrReaches n C w g →
      Relation.ReflTransGen (OrStep n C) w (n + g) ∧ g < C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    have hnw : n ≤ w := h.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp h
    rcases h3 with rfl | ⟨hop, i, hi, hlt, hr⟩
    · exact ⟨Relation.ReflTransGen.refl, hk⟩
    · obtain ⟨hr2, hg⟩ := ih i hlt hr
      exact ⟨Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hi, hlt⟩ hr2, hg⟩

lemma mem_orIn_reach {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hu : u ∈ PEqualNP.TopForm.orIn n C p) :
    Relation.ReflTransGen (OrStep n C) p u.val := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  rcases hu with h | ⟨k, hk, hr, hop, hin⟩
  · rw [h]
  · exact (orReaches_reach k p hr).1.tail ⟨k, hk, rfl, hop, hin, by omega⟩

lemma reach_mem_orIn {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p u.val) :
    u ∈ PEqualNP.TopForm.orIn n C p := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases Relation.ReflTransGen.cases_tail hr with h | ⟨c, hpc, hstep⟩
  · exact Or.inl h
  · obtain ⟨k, hk, rfl, hop, hin, _⟩ := hstep
    exact Or.inr ⟨k, hk, reach_orReaches hpc k rfl hk, hop, hin⟩

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

lemma topData {a : ℕ} (ha : a ∈ tops G C) :
    a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧ BelowF G C a := by
  simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using ha

lemma junkData {a : ℕ} (ha : a ∈ junk G C) :
    a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧
      ∃ x : Fin n → Bool, gateVal n C a x = true ∧ graphFun G ∅ x = false := by
  rcases Finset.mem_filter.mp ha with ⟨hr, hop, hal, hd⟩
  exact ⟨hal, hop, hd⟩

lemma binaryInputs (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) :
    ∃ p q, (gateAt C a).inputs = [p, q] :=
  List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem ha))

lemma opndMem (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
    opnd C a b ∈ (gateAt C a).inputs := by
  obtain ⟨p, q, hpq⟩ := binaryInputs hAO ha
  fin_cases b <;> simp [opnd, hpq]

lemma opndBound (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
    opnd C a b < n + a :=
  hAO.2.1 a ha _ (opndMem hAO ha b)

lemma andValBoth (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and) (x : Fin n → Bool) :
    gateVal n C a x = true ↔
      val C (List.ofFn x) (opnd C a 0) = true ∧
      val C (List.ofFn x) (opnd C a 1) = true := by
  rw [gateVal_eq_val, val_and (n := n) (by simp) ha hop]
  constructor
  · intro h
    exact ⟨(h _ (opndMem hAO ha 0)).2, (h _ (opndMem hAO ha 1)).2⟩
  · intro h i hi
    refine ⟨hAO.2.1 a ha i hi, ?_⟩
    obtain ⟨p, q, hpq⟩ := binaryInputs hAO ha
    rcases List.mem_cons.mp (hpq ▸ hi) with rfl | hq
    · simpa [opnd, hpq] using h.1
    · have e : i = q := List.mem_singleton.mp hq
      subst i
      simpa [opnd, hpq] using h.2

lemma andValOperands (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and) (x : Fin n → Bool) :
    gateVal n C a x = true ↔ ∀ b : Fin 2, val C (List.ofFn x) (opnd C a b) = true := by
  rw [andValBoth hAO ha hop]
  constructor
  · intro h b
    fin_cases b
    · exact h.1
    · exact h.2
  · intro h
    exact ⟨h 0, h 1⟩

lemma operandReachCone (hAO : IsAO2 n C) {a h : ℕ} (ha : a < C.gates.length)
    {b : Fin 2} (hr : OrReaches n C (opnd C a b) h) :
    InCone n C h a :=
  operand_cone ha (opndMem hAO ha b) (opndBound hAO ha b)
    (orReaches_reach h _ hr).1

lemma operandOrAndJunk (hAO : IsAO2 n C) (hT : TopForm G C) {a h : ℕ}
    (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and)
    {b : Fin 2} (hr : OrReaches n C (opnd C a b) h)
    (hh : (gateAt C h).op = GateOp.and) : h ∈ junk G C := by
  have hlen := (orReaches_reach h _ hr).2
  have hnb : ¬ BelowF G C h :=
    fun hb => hT h hlen a ha hh hb hop (operandReachCone hAO ha hr)
  have hdirty : ∃ x : Fin n → Bool, gateVal n C h x = true ∧ graphFun G ∅ x = false := by
    by_contra hne
    apply hnb
    intro x hx
    by_contra hf
    exact hne ⟨x, hx, Bool.eq_false_iff.mpr hf⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlen, hh, hlen, hdirty⟩

lemma reachVal {w h : ℕ} {x : Fin n → Bool} (hr : OrReaches n C w h)
    (hh : gateVal n C h x = true) : val C (List.ofFn x) w = true :=
  orStep_up (n := n) (by simp) (orReaches_reach h _ hr).1 hh

lemma eitherOperand (b c : Fin 2) : c = b ∨ c = 1 - b := by
  fin_cases b <;> fin_cases c <;> decide

lemma oppositeSideWmax (hAO : IsAO2 n C) {a j : ℕ} (ha : a ∈ tops G C) {b : Fin 2}
    (hr : OrReaches n C (opnd C a b) j) :
    side (n := n) C a (1 - b) ⊆ wmax G C j := by
  intro t ht
  obtain ⟨hal, hao, hab⟩ := topData ha
  simp only [wmax, Finset.mem_filter, Finset.mem_univ, true_and]
  intro x hj hx
  apply hab x
  apply (andValOperands hAO hal hao x).mpr
  intro c
  rcases eitherOperand b c with rfl | rfl
  · exact reachVal hr hj
  · exact reach_var_val x _ t (mem_orIn_reach t ht) hx

lemma orInTrans {w z : ℕ} (hr : Relation.ReflTransGen (OrStep n C) w z) :
    orIn n C z ⊆ orIn n C w :=
  fun x hx => reach_mem_orIn x (hr.trans (mem_orIn_reach x hx))

lemma inputsAsOpnd (hAO : IsAO2 n C) {m z : ℕ} (hm : m < C.gates.length)
    (hz : z ∈ (gateAt C m).inputs) : ∃ b : Fin 2, z = opnd C m b := by
  obtain ⟨p, q, hpq⟩ := binaryInputs hAO hm
  rcases List.mem_cons.mp (hpq ▸ hz) with rfl | hq
  · exact ⟨0, by simp [opnd, hpq]⟩
  · have e : z = q := List.mem_singleton.mp hq
    exact ⟨1, by simpa [opnd, hpq] using e⟩

lemma sideVal {a : ℕ} {b : Fin 2} {x : Fin n → Bool} {t : Fin n}
    (ht : t ∈ side (n := n) C a b) (hx : x t = true) :
    val C (List.ofFn x) (opnd C a b) = true :=
  reach_var_val x _ t (mem_orIn_reach t ht) hx

lemma andFromInputs (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and) {x : Fin n → Bool}
    {u v : Fin n} (hu : u ∈ side (n := n) C a 0) (hv : v ∈ side (n := n) C a 1)
    (xu : x u = true) (xv : x v = true) : gateVal n C a x = true :=
  (andValBoth hAO ha hop x).mpr ⟨sideVal hu xu, sideVal hv xv⟩

lemma topAdj (hAO : IsAO2 n C) {a : ℕ} (ha : a ∈ tops G C)
    {u v : Fin n} (hu : u ∈ side (n := n) C a 0) (hv : v ∈ side (n := n) C a 1) :
    G.Adj u v := by
  obtain ⟨hl, ho, hb⟩ := topData ha
  exact (graphFun_pair G u v).mp
    (hb _ (andFromInputs hAO hl ho hu hv (pairInput_left u v) (pairInput_right u v)))

lemma operandSupport (hAO : IsAO2 n C) (hT : TopForm G C) {a : ℕ}
    (ha : a < C.gates.length) (ho : (gateAt C a).op = GateOp.and) {b : Fin 2}
    {u v : Fin n} (h : val C (List.ofFn (pairInput u v)) (opnd C a b) = true) :
    (∃ t ∈ side (n := n) C a b, t = u ∨ t = v) ∨
      ∃ j ∈ junk G C, OrReaches n C (opnd C a b) j ∧
        gateVal n C j (pairInput u v) = true := by
  rcases operand_trace (C := C) u v _ h with ⟨t, ht, hr⟩ | ⟨j, hj, hn, hr, hv⟩
  · exact .inl ⟨t, reach_mem_orIn t hr, ht⟩
  · have hr' := reach_orReaches hr j rfl hj
    exact .inr ⟨j, operandOrAndJunk hAO hT ha ho hr'
      ((hAO.1 _ (gateAt_mem hj)).resolve_right hn), hr', hv⟩

lemma memJunkPair {j k a : ℕ} (hs : junk G C = {j,k}) (ha : a ∈ junk G C) :
    a = j ∨ a = k := by
  simpa only [hs, Finset.mem_insert, Finset.mem_singleton] using ha

end Critical.Base

namespace Critical.Patch

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Core PEqualNP.ReadTwo

lemma foldl_wires_len (gs : List Gate) (acc : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc).length =
      acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_wires_getD_lt (gs : List Gate) (acc : List Bool) (i : ℕ) (hi : i < acc.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) acc).getD i false =
      acc.getD i false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]).length := by
      simp only [List.length_append, List.length_singleton]; omega
    rw [ih _ hlt]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_wires_getD_gate (gs : List Gate) (acc : List Bool) (j : ℕ) (hj : j < gs.length)
    (hback : ∀ k ∈ gs[j].inputs, k < acc.length + j) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) acc).getD
        (acc.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun k =>
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun m => w.getD m false)]) acc).getD
          k false) := by
  induction gs generalizing acc j with
  | nil => cases hj
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [Nat.add_zero, List.foldl_cons, List.getElem_cons_zero] at hback ⊢
      set acc' := acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]
      have hlen : acc.length < acc'.length := by
        simp only [acc', List.length_append, List.length_singleton]; omega
      rw [foldl_wires_getD_lt gs acc' acc.length hlen]
      have hlhs : acc'.getD acc.length false = g.op.eval (g.inputs.map fun k => acc.getD k false) := by
        simp only [acc', List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
          Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
      rw [hlhs]
      congr 1
      apply List.map_congr_left
      intro k hk
      have hka : k < acc.length := hback k hk
      have hka' : k < acc'.length := by omega
      rw [foldl_wires_getD_lt gs acc' k hka']
      simp only [acc', List.getD_eq_getElem?_getD, List.getElem?_append_left hka]
    | succ j' =>
      simp only [List.foldl_cons, List.getElem_cons_succ]
      set acc' := acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]
      have hlen' : acc'.length = acc.length + 1 := by
        simp only [acc', List.length_append, List.length_singleton]
      have hj' : j' < gs.length := by simp only [List.length_cons] at hj; omega
      have hidx : acc.length + (j' + 1) = acc'.length + j' := by omega
      rw [hidx]
      apply ih acc' j' hj'
      intro k hk
      have hbk := hback k (by simpa using hk)
      omega

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length :=
  foldl_wires_len C.gates x

lemma wval_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    wval C x i = x ⟨i, hi⟩ := by
  unfold wval Circuit.wires
  have hlt : i < (List.ofFn x).length := by simp [hi]
  rw [foldl_wires_getD_lt C.gates (List.ofFn x) i hlt]
  simp [List.getD_eq_getElem?_getD, hi]

lemma gateVal_eq_wval {n : ℕ} (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    gateVal n C j x = wval C x (n + j) := rfl

lemma wval_ge_len {n : ℕ} (C : Circuit) (x : Fin n → Bool) {w : ℕ} (hw : n + C.gates.length ≤ w) :
    wval C x w = false := by
  unfold wval
  rw [List.getD_eq_getElem?_getD]
  have hlen : (C.wires (List.ofFn x)).length = n + C.gates.length := by
    rw [wires_length, List.length_ofFn]
  rw [List.getElem?_eq_none (by omega)]
  rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  unfold gateAt
  simp [List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma gate_inputs_eq {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
  have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 _ (gateAt_mem hj)
  unfold opnd
  match h : (gateAt C j).inputs with
  | [a, b] => simp
  | [] => rw [h] at hlen; simp at hlen
  | [_] => rw [h] at hlen; simp at hlen
  | _ :: _ :: _ :: _ => rw [h] at hlen; simp at hlen

lemma opnd_mem {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b ∈ (gateAt C j).inputs := by
  rw [gate_inputs_eq hAO hj]
  fin_cases b <;> simp

lemma opnd_lt {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b < n + j :=
  hAO.2.1 j hj _ (opnd_mem hAO hj b)

lemma wval_gate_eval {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) :
    wval C x (n + j) = (gateAt C j).op.eval [wval C x (opnd C j 0), wval C x (opnd C j 1)] := by
  unfold wval Circuit.wires
  have hlen : (List.ofFn x).length = n := List.length_ofFn
  have hback : ∀ k ∈ C.gates[j].inputs, k < (List.ofFn x).length + j := by
    intro k hk; rw [hlen, ← gateAt_eq hj] at *; exact hAO.2.1 j hj k hk
  have h := foldl_wires_getD_gate C.gates (List.ofFn x) j hj hback
  rw [hlen] at h
  rw [h, ← gateAt_eq hj, gate_inputs_eq hAO hj]
  simp

lemma foldl_cones_getD_lt (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) (i : ℕ) (hi : i < acc.length) :
    (gs.foldl (coneStep n) acc).getD i [] = acc.getD i [] := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (coneStep n acc g).length := by
      simp only [coneStep, List.length_append, List.length_singleton]; omega
    rw [ih _ hlt]
    simp only [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_cones_getD_gate (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl (coneStep n) acc).getD (acc.length + j) [] =
      (gs[j].inputs.filter (fun w => decide (n ≤ w ∧ w < n + (acc.length + j)))).flatMap
        (fun w => (w - n) :: (gs.foldl (coneStep n) acc).getD (w - n) []) := by
  induction gs generalizing acc j with
  | nil => cases hj
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [Nat.add_zero, List.foldl_cons, List.getElem_cons_zero]
      set acc' := coneStep n acc g
      have hlen : acc.length < acc'.length := by
        simp only [acc', coneStep, List.length_append, List.length_singleton]; omega
      rw [foldl_cones_getD_lt n gs acc' acc.length hlen]
      have hlhs : acc'.getD acc.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + acc.length))).flatMap
            (fun w => (w - n) :: acc.getD (w - n) []) := by
        simp only [acc', coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
          Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
      rw [hlhs]
      apply List.flatMap_congr
      intro w hw
      simp only [List.mem_filter, decide_eq_true_eq] at hw
      have hwn : w - n < acc.length := by omega
      have hwn' : w - n < acc'.length := by omega
      rw [foldl_cones_getD_lt n gs acc' (w - n) hwn']
      simp only [acc', coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hwn]
    | succ j' =>
      simp only [List.foldl_cons, List.getElem_cons_succ]
      set acc' := coneStep n acc g
      have hlen' : acc'.length = acc.length + 1 := by
        simp only [acc', coneStep, List.length_append, List.length_singleton]
      have hj' : j' < gs.length := by simp only [List.length_cons] at hj; omega
      have hidx : acc.length + (j' + 1) = acc'.length + j' := by omega
      rw [hidx]
      exact ih acc' j' hj'

lemma inCone_iff {n : ℕ} {C : Circuit} {i j : ℕ} (hj : j < C.gates.length) :
    InCone n C i j ↔
      ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ w < n + j ∧ (i = w - n ∨ InCone n C i (w - n)) := by
  unfold InCone cones
  have h := foldl_cones_getD_gate n C.gates [] j hj
  simp only [List.length_nil, Nat.zero_add] at h
  rw [h, ← gateAt_eq hj]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw1, hw2, hw3⟩, hw4⟩; exact ⟨w, hw1, hw2, hw3, hw4⟩
  · rintro ⟨w, hw1, hw2, hw3, hw4⟩; exact ⟨w, ⟨hw1, hw2, hw3⟩, hw4⟩

def patch (C : Circuit) (j : ℕ) (g : Gate) : Circuit := ⟨C.gates.set j g, C.output⟩

lemma patch_length (C : Circuit) (j : ℕ) (g : Gate) :
    (patch C j g).gates.length = C.gates.length := by
  simp [patch]

lemma gateAt_patch_ne (C : Circuit) (j k : ℕ) (g : Gate) (hne : j ≠ k) :
    gateAt (patch C j g) k = gateAt C k := by
  simp [patch, gateAt, List.getD_eq_getElem?_getD, List.getElem?_set_ne hne]

lemma patch_wval_gate_eval {n : ℕ} {C : Circuit} {j : ℕ} {g : Gate}
    (hAO : IsAO2 n C) (x : Fin n → Bool) {k : ℕ} (hk : k < C.gates.length)
    (hne : j ≠ k) :
    wval (patch C j g) x (n + k) = (gateAt C k).op.eval
      [wval (patch C j g) x (opnd C k 0), wval (patch C j g) x (opnd C k 1)] := by
  have hk' : k < (patch C j g).gates.length := by simpa only [patch_length] using hk
  have hgate := gateAt_patch_ne C j k g hne
  have hlen : (List.ofFn x).length = n := List.length_ofFn
  have hback : ∀ w ∈ (patch C j g).gates[k].inputs, w < (List.ofFn x).length + k := by
    intro w hw
    rw [← gateAt_eq hk', hgate] at hw
    rw [hlen]
    exact hAO.2.1 k hk w hw
  have heval := foldl_wires_getD_gate (patch C j g).gates (List.ofFn x) k hk' hback
  rw [hlen, ← gateAt_eq hk', hgate, gate_inputs_eq hAO hk] at heval
  simpa only [wval, Circuit.wires, List.map_cons, List.map_nil] using heval

lemma patch_gateVal_eq_of_not_inCone {n : ℕ} {C : Circuit} {j : ℕ} {g : Gate}
    (hAO : IsAO2 n C) (k : ℕ) (hne : j ≠ k) (hCone : ¬ InCone n C j k)
    (x : Fin n → Bool) : gateVal n (patch C j g) k x = gateVal n C k x := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    by_cases hk : k < C.gates.length
    · have hval (b : Fin 2) : wval (patch C j g) x (opnd C k b) =
          wval C x (opnd C k b) := by
        by_cases hw : opnd C k b < n
        · rw [wval_input _ _ _ hw, wval_input _ _ _ hw]
        · have hw' : n ≤ opnd C k b := by omega
          have hlt := opnd_lt hAO hk b
          have hsub_ne : j ≠ opnd C k b - n := by
            intro he
            apply hCone
            exact (inCone_iff hk).mpr ⟨opnd C k b, opnd_mem hAO hk b, hw', hlt, Or.inl he⟩
          have hsub_cone : ¬ InCone n C j (opnd C k b - n) := by
            intro he
            apply hCone
            exact (inCone_iff hk).mpr ⟨opnd C k b, opnd_mem hAO hk b, hw', hlt, Or.inr he⟩
          have hv := ih (opnd C k b - n) (by omega) hsub_ne hsub_cone
          rw [gateVal_eq_wval, gateVal_eq_wval, Nat.add_sub_of_le hw'] at hv
          exact hv
      rw [gateVal_eq_wval, gateVal_eq_wval, patch_wval_gate_eval hAO x hk hne,
        wval_gate_eval hAO x hk, hval 0, hval 1]
    · rw [gateVal_eq_wval, gateVal_eq_wval, wval_ge_len _ _ (by rw [patch_length]; omega),
        wval_ge_len _ _ (by omega)]

end Critical.Patch

namespace Critical

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

def offPatch (C : Circuit) (h : ℕ) : Circuit := ⟨C.gates.set h ⟨GateOp.or, []⟩, C.output⟩

lemma offPatch_length (C : Circuit) (h : ℕ) : (offPatch C h).gates.length = C.gates.length := by
  simp [offPatch]

lemma gateAt_offPatch_ne (C : Circuit) (h k : ℕ) (hne : h ≠ k) :
    gateAt (offPatch C h) k = gateAt C k := by
  simp [offPatch, gateAt, List.getD_eq_getElem?_getD, List.getElem?_set_ne hne]

lemma orStep_offPatch {n : ℕ} {C : Circuit} {h w w' : ℕ}
    (hAnd : (gateAt C h).op = GateOp.and) (hs : Base.OrStep n C w w') :
    Base.OrStep n (offPatch C h) w w' := by
  obtain ⟨k, hk, rfl, hOr, hi, hb⟩ := hs
  have hne : h ≠ k := by
    intro he
    rw [← he, hAnd] at hOr
    cases hOr
  refine ⟨k, by simpa only [offPatch_length] using hk, rfl, ?_, ?_, hb⟩
  · simpa only [gateAt_offPatch_ne C h k hne] using hOr
  · simpa only [gateAt_offPatch_ne C h k hne] using hi

lemma orPath_offPatch {n : ℕ} {C : Circuit} {h w w' : ℕ}
    (hAnd : (gateAt C h).op = GateOp.and)
    (hs : Relation.ReflTransGen (Base.OrStep n C) w w') :
    Relation.ReflTransGen (Base.OrStep n (offPatch C h)) w w' := by
  induction hs using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | head hs _ ih => exact Relation.ReflTransGen.head (orStep_offPatch hAnd hs) ih

lemma offPatch_difference_trace {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {h : ℕ} (hAnd : (gateAt C h).op = GateOp.and) (x : Fin n → Bool) :
    ∀ w, Base.val C (List.ofFn x) w = true → Base.val (offPatch C h) (List.ofFn x) w = false →
    ∃ j, j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧ OrReaches n C w j ∧
      gateVal n C j x = true ∧ gateVal n (offPatch C h) j x = false := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hw'
    by_cases hwInput : w < n
    · rw [Base.val_input (n := n) (by simp) hwInput] at hw hw'
      rw [hw] at hw'
      cases hw'
    · by_cases hwLarge : n + C.gates.length ≤ w
      · rw [Base.val_ge (n := n) (by simp) hwLarge] at hw
        cases hw
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        by_cases hOr : (gateAt C k).op = GateOp.or
        · have hne : h ≠ k := by
            intro he
            rw [← he, hAnd] at hOr
            cases hOr
          obtain ⟨v, hvMem, hvLt, hv⟩ := (Base.val_or (n := n) (by simp) hk hOr).mp hw
          have hv' : Base.val (offPatch C h) (List.ofFn x) v = false := by
            cases hv' : Base.val (offPatch C h) (List.ofFn x) v
            · rfl
            · have hk' : k < (offPatch C h).gates.length := by simpa only [offPatch_length] using hk
              have hOr' : (gateAt (offPatch C h) k).op = GateOp.or := by
                simpa only [gateAt_offPatch_ne C h k hne] using hOr
              have hMem' : v ∈ (gateAt (offPatch C h) k).inputs := by
                simpa only [gateAt_offPatch_ne C h k hne] using hvMem
              have ht := (Base.val_or (n := n) (by simp) hk' hOr').mpr ⟨v, hMem', hvLt, hv'⟩
              rw [hw'] at ht
              cases ht
          obtain ⟨j, hj, hjAnd, hReach, hjv, hjv'⟩ := ih v hvLt hv hv'
          refine ⟨j, hj, hjAnd, ?_, hjv, hjv'⟩
          exact (Base.orReaches_iff n C k j).mpr ⟨hk, Or.inr ⟨hOr, v, hvMem, hvLt, hReach⟩⟩
        · have hAndK : (gateAt C k).op = GateOp.and := (hAO.1 _ (Base.gateAt_mem hk)).resolve_right hOr
          exact ⟨k, hk, hAndK, (Base.orReaches_iff n C k k).mpr ⟨hk, Or.inl rfl⟩, hw, hw'⟩

lemma critical_edge_useful {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (hF : circuitFun n C = graphFun G ∅)
    (hT : TopForm G C) {g h : ℕ} (hJ : junk G C = {g, h}) (hne : g ≠ h)
    (hIndependent : ¬ InCone n C h g)
    (hNoCommon : ∀ a ∈ tops G C, ∀ b : Fin 2,
      OrReaches n C (opnd C a b) h → ¬ OrReaches n C (opnd C a (1 - b)) g)
    (u v : Fin n) (hAdj : G.Adj u v)
    (hLost : circuitFun n (offPatch C h) (pairInput u v) = false) :
    gateVal n C h (pairInput u v) = true ∧ (u ∈ wmax G C h ∨ v ∈ wmax G C h) := by
  have hhJ : h ∈ junk G C := by rw [hJ]; simp
  obtain ⟨hhLen, hhAnd, hx, hhx, hFx⟩ := Base.junkData hhJ
  have hout (x : Fin n → Bool) : Base.val C (List.ofFn x) C.output = graphFun G ∅ x :=
    congrFun hF x
  obtain ⟨a, haLen, haNotOr, haPath, haVal⟩ :=
    Base.edge_trace G (graphFun G ∅) (fun x y hxy => (Base.graphFun_pair G x y).mp hxy)
      hout u v ((Base.graphFun_pair G u v).mpr hAdj)
  have haAnd : (gateAt C a).op = GateOp.and :=
    (hAO.1 _ (Base.gateAt_mem haLen)).resolve_right haNotOr
  have haBelow : BelowF G C a := fun x hv =>
    Base.below_of_reach (graphFun G ∅) hout a haPath x hv
  have haTop : a ∈ tops G C := by
    simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using
      And.intro haLen (And.intro haAnd haBelow)
  have hha : h ≠ a := by
    intro he
    subst a
    have ht := haBelow hx hhx
    rw [hFx] at ht
    cases ht
  have haOff : gateVal n (offPatch C h) a (pairInput u v) = false := by
    cases hc : gateVal n (offPatch C h) a (pairInput u v)
    · rfl
    · have ho := Base.orStep_up (n := n) (by simp) (orPath_offPatch hhAnd haPath) hc
      change circuitFun n (offPatch C h) (pairInput u v) = true at ho
      rw [hLost] at ho
      cases ho
  have hEval : gateVal n (offPatch C h) a (pairInput u v) =
      (Base.val (offPatch C h) (List.ofFn (pairInput u v)) (opnd C a 0) &&
       Base.val (offPatch C h) (List.ofFn (pairInput u v)) (opnd C a 1)) := by
    have he := Patch.patch_wval_gate_eval (j := h) (g := ⟨GateOp.or, []⟩) hAO (pairInput u v) haLen hha
    change gateVal n (offPatch C h) a (pairInput u v) = (gateAt C a).op.eval
      [Base.val (offPatch C h) (List.ofFn (pairInput u v)) (opnd C a 0),
       Base.val (offPatch C h) (List.ofFn (pairInput u v)) (opnd C a 1)] at he
    simpa only [haAnd, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true] using he
  obtain ⟨b, hbOff⟩ : ∃ b : Fin 2,
      Base.val (offPatch C h) (List.ofFn (pairInput u v)) (opnd C a b) = false := by
    by_cases h0 : Base.val (offPatch C h) (List.ofFn (pairInput u v)) (opnd C a 0) = false
    · exact ⟨0, h0⟩
    · have h0t := Bool.eq_true_of_not_eq_false h0
      refine ⟨1, ?_⟩
      rw [haOff, h0t, Bool.true_and] at hEval
      exact hEval.symm
  have hbVal := ((Base.andValOperands hAO haLen haAnd (pairInput u v)).mp haVal) b
  obtain ⟨j, hjLen, hjAnd, hjReach, hjVal, hjOff⟩ :=
    offPatch_difference_trace hAO hhAnd (pairInput u v) (opnd C a b) hbVal hbOff
  have hjJ := Base.operandOrAndJunk hAO hT haLen haAnd hjReach hjAnd
  have hjh : j = h := by
    rcases Base.memJunkPair hJ hjJ with hjg | hjh
    · subst j
      have he := Patch.patch_gateVal_eq_of_not_inCone (j := h) (g := ⟨GateOp.or, []⟩)
        hAO g (Ne.symm hne) hIndependent (pairInput u v)
      change gateVal n (offPatch C h) g (pairInput u v) = gateVal n C g (pairInput u v) at he
      rw [he, hjVal] at hjOff
      cases hjOff
    · exact hjh
  subst j
  refine ⟨hjVal, ?_⟩
  have hoVal := ((Base.andValOperands hAO haLen haAnd (pairInput u v)).mp haVal) (1 - b)
  rcases Base.operandSupport hAO hT haLen haAnd hoVal with ⟨t, ht, htu⟩ | ⟨k, hkJ, hkReach, _⟩
  · have htw := Base.oppositeSideWmax hAO haTop hjReach ht
    rcases htu with rfl | rfl
    · exact Or.inl htw
    · exact Or.inr htw
  · rcases Base.memJunkPair hJ hkJ with hkg | hkh
    · subst k
      exact False.elim (hNoCommon a haTop b hjReach hkReach)
    · subst k
      have ht : gateVal n C a hx = true := by
        apply (Base.andValOperands hAO haLen haAnd hx).mpr
        intro c
        rcases Base.eitherOperand b c with rfl | rfl
        · exact Base.reachVal hjReach hhx
        · exact Base.reachVal hkReach hhx
      have hf := haBelow hx ht
      rw [hFx] at hf
      cases hf

end Critical

end PEqualNP.Outside.L_meta_5012

namespace PEqualNP.Outside.L_meta_5012.OverlapCase

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo

open IndependentDescent CleanReplacement

lemma safe_adj_overlap {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P Q : Finset (Fin n)) {z a : Fin n} (hz : Safe G P Q z) (ha : a ∈ P ∩ Q) :
    G.Adj z a := by
  apply (graph_pair G z a).mp
  apply hz
  · exact (product_true P Q _).mpr
      ⟨⟨a, (Finset.mem_inter.mp ha).1, by simp [pairInput]⟩,
        a, (Finset.mem_inter.mp ha).2, by simp [pairInput]⟩
  · simp [pairInput]

lemma safe_unique_of_overlap {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P Q : Finset (Fin n)) (h4 : NoFourCycle G) (hPQ : 2 ≤ (P ∩ Q).card)
    {z w : Fin n} (hz : Safe G P Q z) (hw : Safe G P Q w) : z = w := by
  by_contra hne
  have hsub : P ∩ Q ⊆ Finset.univ.filter fun a => G.Adj z a ∧ G.Adj w a := by
    intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      safe_adj_overlap G P Q hz ha, safe_adj_overlap G P Q hw ha⟩
  have hc := (Finset.card_le_card hsub).trans (h4 z w hne)
  omega

lemma no_independent_overlap_filter_inside {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hL : IsLeastAO G C)
    (hOne : ∀ D : Circuit, IsLeastAO G D → (junk G D).card ≠ 1)
    (hT : TopForm G C) {j k : ℕ} (hne : j ≠ k) (hJ : junk G C = {j,k})
    (hjk : ¬ InCone n C j k) (hkj : ¬ InCone n C k j)
    (hNoCommon : ∀ a ∈ tops G C, ∀ b : Fin 2,
      OrReaches n C (opnd C a b) j → ¬ OrReaches n C (opnd C a (1-b)) k)
    (h4 : NoFourCycle G)
    (hOverlap : 2 ≤ ((side (n := n) C j 0) ∩ (side (n := n) C j 1)).card)
    {z : Fin n} (hzW : z ∈ wmax G C j)
    (hzIn : z ∈ (side (n := n) C j 0) ∪ (side (n := n) C j 1)) : False := by
  let P := side (n := n) C j 0
  let Q := side (n := n) C j 1
  have hjmem : j ∈ junk G C := by rw [hJ]; simp
  have hj : j < C.gates.length := (mem_junk.mp hjmem).1
  have hOpnd (b : Fin 2) : opnd C j b < n + j := Lift.opnd_lt hL.1 hj b
  have hRaw (b : Fin 2) (x : Fin n → Bool) :
      wval C x (opnd C j b) = decide (∃ p ∈ side (n := n) C j b, x p = true) :=
    RawOperands.independent_operand G C hL.1 hT j k hJ hjk hkj j (Or.inl rfl) b x
  have heval (x : Fin n → Bool) : gateVal n C j x = product P Q x :=
    RawOperands.independent_product G C hL.1 hT j k hJ hjk hkj j (Or.inl rfl) x
  have hzSafe : Safe G P Q z := (wmax_iff G C j P Q heval z).mp hzW
  have hUnique (w : Fin n) (hw : Safe G P Q w) : w = z :=
    safe_unique_of_overlap G P Q h4 hOverlap hw hzSafe
  have hCritical (u v : Fin n) (huv : G.Adj u v)
      (hLost : circuitFun n (patch C j off) (pairInput u v) = false) :
      product P Q (pairInput u v) = true ∧ pairInput u v z = true := by
    have hJ' : junk G C = {k,j} := by rw [hJ, Finset.pair_comm]
    obtain ⟨hjv, hFilter⟩ := Critical.critical_edge_useful hL.1 hL.2.1 hT hJ'
      (Ne.symm hne) hjk hNoCommon u v huv hLost
    refine ⟨(heval _).symm.trans hjv, ?_⟩
    rcases hFilter with hu | hv
    · have huEq := hUnique u ((wmax_iff G C j P Q heval u).mp hu)
      simp [pairInput, ← huEq]
    · have hvEq := hUnique v ((wmax_iff G C j P Q heval v).mp hv)
      simp [pairInput, ← hvEq]
  have hReplace (b : Fin 2)
      (hClean : ∀ x : Fin n → Bool, graphFun G ∅ x = false →
        (x z && wval C x (opnd C j b)) = false)
      (hCover : ∀ u v : Fin n, G.Adj u v →
        circuitFun n (patch C j off) (pairInput u v) = false →
        (pairInput u v z && wval C (pairInput u v) (opnd C j b)) = true) : False := by
    apply no_clean_independent_replacement G C hL hOne hne hJ hjk
      ⟨GateOp.and, [z.val, opnd C j b]⟩ (Or.inl rfl) rfl
    · intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · have := z.isLt; omega
      · exact hOpnd b
    · intro x hf
      rw [FlagReduction.star_gate_bit C j (Nat.le_of_lt hj) z _ (hOpnd b) x]
      exact hClean x hf
    · intro u v huv hLost
      rw [FlagReduction.star_gate_bit C j (Nat.le_of_lt hj) z _ (hOpnd b) _]
      exact hCover u v huv hLost
  rcases Finset.mem_union.mp hzIn with hzP | hzQ
  · apply hReplace 1
    · intro x hf
      rw [hRaw 1 x]
      apply Bool.eq_false_iff.mpr
      intro ht
      simp only [Bool.and_eq_true] at ht
      obtain ⟨hxz, hxQ⟩ := ht
      have hQ : ∃ q ∈ Q, x q = true := of_decide_eq_true hxQ
      have hp : product P Q x = true :=
        (product_true P Q x).mpr ⟨⟨z, hzP, hxz⟩, hQ⟩
      have hg := hzSafe x hp hxz
      rw [hf] at hg
      cases hg
    · intro u v huv hLost
      obtain ⟨hp, hxz⟩ := hCritical u v huv hLost
      rw [hRaw 1 _, hxz, Bool.true_and]
      exact decide_eq_true ((product_true P Q _).mp hp).2
  · apply hReplace 0
    · intro x hf
      rw [hRaw 0 x]
      apply Bool.eq_false_iff.mpr
      intro ht
      simp only [Bool.and_eq_true] at ht
      obtain ⟨hxz, hxP⟩ := ht
      have hP : ∃ p ∈ P, x p = true := of_decide_eq_true hxP
      have hp : product P Q x = true :=
        (product_true P Q x).mpr ⟨hP, z, hzQ, hxz⟩
      have hg := hzSafe x hp hxz
      rw [hf] at hg
      cases hg
    · intro u v huv hLost
      obtain ⟨hp, hxz⟩ := hCritical u v huv hLost
      rw [hRaw 0 _, hxz, Bool.true_and]
      exact decide_eq_true ((product_true P Q _).mp hp).1

lemma independent_apart_wmax_nonempty {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hL : IsLeastAO G C)
    (hOne : ∀ D : Circuit, IsLeastAO G D → (junk G D).card ≠ 1)
    (hT : TopForm G C) {j k : ℕ} (hne : j ≠ k) (hJ : junk G C = {j,k})
    (hjk : ¬ InCone n C j k)
    (hNoCommon : ∀ a ∈ tops G C, ∀ b : Fin 2,
      OrReaches n C (opnd C a b) j → ¬ OrReaches n C (opnd C a (1-b)) k) :
    (wmax G C j).Nonempty := by
  by_contra hn
  have hjmem : j ∈ junk G C := by rw [hJ]; simp
  obtain ⟨e, he⟩ := Cases.edge_nonempty_of_junk_nonempty G C hL ⟨j, hjmem⟩
  obtain ⟨u, v, huv⟩ : ∃ u v : Fin n, G.Adj u v := by
    revert he
    refine Sym2.inductionOn e ?_
    intro u v he
    exact ⟨u, v, by simpa using he⟩
  apply no_clean_independent_replacement G C hL hOne hne hJ hjk
    (edgeGate u v) (Or.inl rfl) rfl
  · intro w hw
    simp only [edgeGate, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl <;> omega
  · intro x hf
    rw [edge_bit]
    apply Bool.eq_false_iff.mpr
    intro ht
    simp only [Bool.and_eq_true] at ht
    obtain ⟨hu, hv⟩ := ht
    have hg := (graph_true G x).mpr ⟨u, v, huv, hu, hv⟩
    rw [hf] at hg
    cases hg
  · intro a b hab hLost
    have hJ' : junk G C = {k,j} := by rw [hJ, Finset.pair_comm]
    obtain ⟨_, ha | hb⟩ := Critical.critical_edge_useful hL.1 hL.2.1 hT hJ'
      (Ne.symm hne) hjk hNoCommon a b hab hLost
    · exact (hn ⟨a, ha⟩).elim
    · exact (hn ⟨b, hb⟩).elim

lemma independent_overlap_unique_outside {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hL : IsLeastAO G C)
    (hOne : ∀ D : Circuit, IsLeastAO G D → (junk G D).card ≠ 1)
    (hT : TopForm G C) {j k : ℕ} (hne : j ≠ k) (hJ : junk G C = {j,k})
    (hjk : ¬ InCone n C j k) (hkj : ¬ InCone n C k j)
    (hNoCommon : ∀ a ∈ tops G C, ∀ b : Fin 2,
      OrReaches n C (opnd C a b) j → ¬ OrReaches n C (opnd C a (1-b)) k)
    (h4 : NoFourCycle G)
    (hOverlap : 2 ≤ ((side (n := n) C j 0) ∩ (side (n := n) C j 1)).card) :
    ∃ z : Fin n, wmax G C j = {z} ∧
      z ∉ (side (n := n) C j 0) ∪ (side (n := n) C j 1) := by
  obtain ⟨z, hz⟩ := independent_apart_wmax_nonempty G C hL hOne hT hne hJ hjk hNoCommon
  have heval (x : Fin n → Bool) : gateVal n C j x =
      product (side (n := n) C j 0) (side (n := n) C j 1) x :=
    RawOperands.independent_product G C hL.1 hT j k hJ hjk hkj j (Or.inl rfl) x
  refine ⟨z, ?_, ?_⟩
  · apply Finset.ext
    intro w
    constructor
    · intro hw
      apply Finset.mem_singleton.mpr
      exact safe_unique_of_overlap G _ _ h4 hOverlap
        ((wmax_iff G C j _ _ heval w).mp hw) ((wmax_iff G C j _ _ heval z).mp hz)
    · intro hw
      have he := Finset.mem_singleton.mp hw
      exact he ▸ hz
  · intro hzIn
    exact no_independent_overlap_filter_inside G C hL hOne hT hne hJ hjk hkj
      hNoCommon h4 hOverlap hz hzIn

end PEqualNP.Outside.L_meta_5012.OverlapCase

namespace PEqualNP.Outside.L_meta_5012.OverlapCase

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo

open IndependentDescent CleanReplacement

lemma product_pair_overlap_of_outside {n : ℕ} (P Q : Finset (Fin n))
    {z v : Fin n} (hzOut : z ∉ P ∪ Q)
    (hp : product P Q (pairInput z v) = true) : v ∈ P ∩ Q := by
  obtain ⟨⟨p, hp, hxp⟩, q, hq, hxq⟩ := (product_true P Q _).mp hp
  simp only [pairInput, decide_eq_true_eq] at hxp hxq
  have hpv : p = v := hxp.resolve_left
    (fun he => hzOut (Finset.mem_union.mpr (Or.inl (he ▸ hp))))
  have hqv : q = v := hxq.resolve_left
    (fun he => hzOut (Finset.mem_union.mpr (Or.inr (he ▸ hq))))
  exact Finset.mem_inter.mpr ⟨hpv ▸ hp, hqv ▸ hq⟩

end PEqualNP.Outside.L_meta_5012.OverlapCase

namespace PEqualNP.Outside.L_meta_5012.OverlapCase

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo

open IndependentDescent CleanReplacement

lemma no_independent_unique_filter_neighbor_factor {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C)
    (hOne : ∀ D : Circuit, IsLeastAO G D → (junk G D).card ≠ 1)
    (hT : TopForm G C) {j k : ℕ} (hne : j ≠ k) (hJ : junk G C = {j,k})
    (hjk : ¬ InCone n C j k) (hkj : ¬ InCone n C k j)
    (hNoCommon : ∀ a ∈ tops G C, ∀ b : Fin 2,
      OrReaches n C (opnd C a b) j → ¬ OrReaches n C (opnd C a (1-b)) k)
    {z : Fin n} (hW : wmax G C j = {z}) (b : Fin 2)
    (hNeighbors : ∀ v ∈ side (n := n) C j b, G.Adj z v) : False := by
  have hjmem : j ∈ junk G C := by rw [hJ]; simp
  have hj : j < C.gates.length := (mem_junk.mp hjmem).1
  have hjAnd : (gateAt C j).op = GateOp.and := (RawOperands.junk_data G C j hjmem).2
  have hOpnd : opnd C j b < n + j := Lift.opnd_lt hL.1 hj b
  have hRaw (x : Fin n → Bool) : wval C x (opnd C j b) =
      decide (∃ v ∈ side (n := n) C j b, x v = true) :=
    RawOperands.independent_operand G C hL.1 hT j k hJ hjk hkj j (Or.inl rfl) b x
  apply no_clean_independent_replacement G C hL hOne hne hJ hjk
    ⟨GateOp.and, [z.val, opnd C j b]⟩ (Or.inl rfl) rfl
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · have := z.isLt; omega
    · exact hOpnd
  · intro x hf
    rw [FlagReduction.star_gate_bit C j (Nat.le_of_lt hj) z _ hOpnd x, hRaw x]
    apply Bool.eq_false_iff.mpr
    intro hh
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hh
    obtain ⟨hxz, v, hv, hxv⟩ := hh
    have hg := (graph_true G x).mpr ⟨z, v, hNeighbors v hv, hxz, hxv⟩
    rw [hf] at hg
    cases hg
  · intro u v huv hLost
    have hJ' : junk G C = {k,j} := by rw [hJ, Finset.pair_comm]
    obtain ⟨hjv, hFilter⟩ := Critical.critical_edge_useful hL.1 hL.2.1 hT hJ'
      (Ne.symm hne) hjk hNoCommon u v huv hLost
    have hzv : pairInput u v z = true := by
      rcases hFilter with hu | hv
      · have hueq : u = z := by simpa [hW] using hu
        simp [pairInput, ← hueq]
      · have hveq : v = z := by simpa [hW] using hv
        simp [pairInput, ← hveq]
    have hOperand : wval C (pairInput u v) (opnd C j b) = true :=
      ((Critical.Base.andValOperands hL.1 hj hjAnd _).mp hjv) b
    rw [FlagReduction.star_gate_bit C j (Nat.le_of_lt hj) z _ hOpnd _, hzv,
      hOperand, Bool.true_and]

end PEqualNP.Outside.L_meta_5012.OverlapCase

namespace PEqualNP.Outside.L_meta_5012.SharedFilter

open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

open PEqualNP.Outside.L_meta_5012.Overlap

end PEqualNP.Outside.L_meta_5012.SharedFilter

namespace PEqualNP.Outside.L_meta_5012.OverlapCase

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo

open IndependentDescent CleanReplacement

end PEqualNP.Outside.L_meta_5012.OverlapCase

namespace PEqualNP.Outside.L_meta_5012.OverlapCase

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo

open IndependentDescent CleanReplacement

end PEqualNP.Outside.L_meta_5012.OverlapCase

namespace PEqualNP.Outside.L_meta_5012.WireAbsorption

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

open Absorption

end PEqualNP.Outside.L_meta_5012.WireAbsorption

namespace PEqualNP.Outside.L_meta_5012.SharedFilter

open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

open PEqualNP.Outside.L_meta_5012.Overlap

end PEqualNP.Outside.L_meta_5012.SharedFilter

namespace PEqualNP.Outside.L_meta_5012.OrRewrite

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

open Absorption

end PEqualNP.Outside.L_meta_5012.OrRewrite

namespace PEqualNP.Outside.L_meta_5012.SymmetricAbsorption

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

open Absorption

end PEqualNP.Outside.L_meta_5012.SymmetricAbsorption

namespace PEqualNP.Outside.L_meta_5012.Trace

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

end PEqualNP.Outside.L_meta_5012.Trace

namespace PEqualNP.Outside.L_meta_5012.Frontier

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma gate_op_cases {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := by
  exact hAO.1 _ (Trace.gateAt_mem hj)

lemma read_index_lt {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {i j : ℕ} (hj : j < C.gates.length)
    (hread : n + i ∈ (gateAt C j).inputs) : i < j := by
  have h := hAO.2.1 j hj (n + i) hread
  omega

lemma cutVal_rec {n : ℕ} (C : Circuit) (hAO : IsAO2 n C) (j k : ℕ)
    (hk : k < C.gates.length) (hkj : k ≠ j) (x : Fin n → Bool) :
    CriticalEdge.cutVal n C {j} x (n + k) =
      if CriticalEdge.isAnd C k = true then
        (CriticalEdge.cutVal n C {j} x (opnd C k 0) && CriticalEdge.cutVal n C {j} x (opnd C k 1))
      else
        (CriticalEdge.cutVal n C {j} x (opnd C k 0) || CriticalEdge.cutVal n C {j} x (opnd C k 1)) := by
  obtain ⟨_, _, ha, hb, _⟩ := CriticalEdge.gate2 hAO hk
  have hnot : k ∉ ({j} : Finset ℕ) := by simpa using hkj
  cases hA : CriticalEdge.isAnd C k with
  | false =>
    rw [CriticalEdge.cutVal, CriticalEdge.u_or hnot hA ha hb]
    rfl
  | true =>
    rw [CriticalEdge.cutVal, CriticalEdge.u_and hnot hA ha hb]
    simp [CriticalEdge.cutVal]

lemma cutVal_unread {n : ℕ} (C : Circuit) (hAO : IsAO2 n C) (j : ℕ)
    (hread : ∀ k < C.gates.length, n + j ∉ (gateAt C k).inputs)
    (x : Fin n → Bool) :
    ∀ w < n + C.gates.length, w ≠ n + j →
      CriticalEdge.cutVal n C {j} x w = CriticalEdge.val n C x w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hwj
    by_cases hwn : w < n
    · rw [CriticalEdge.cutVal, CriticalEdge.u_in hwn, CriticalEdge.val_in C x w hwn]
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < C.gates.length := by omega
      obtain ⟨_, hin, ha, hb, _⟩ := CriticalEdge.gate2 hAO hk
      have han : opnd C k 0 ≠ n + j := by
        intro he
        apply hread k hk
        rw [hin, ← he]
        simp
      have hbn : opnd C k 1 ≠ n + j := by
        intro he
        apply hread k hk
        rw [hin, ← he]
        simp
      rw [cutVal_rec C hAO j k hk (by omega) x, CriticalEdge.val_rec C hAO x k hk,
        ih _ ha (by omega) han, ih _ hb (by omega) hbn]

lemma least_live {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (j : ℕ) (hj : j < C.gates.length) :
    C.output = n + j ∨ ∃ k < C.gates.length, n + j ∈ (gateAt C k).inputs := by
  classical
  by_contra hn
  push Not at hn
  obtain ⟨hout, hread⟩ := hn
  have hE := CriticalEdge.least_nonempty_of_gate G C hL j hj
  obtain ⟨p, q, hpq, hcut⟩ := CriticalEdge.least_gate_critical G C hL hE j hj
  have hbound := CriticalEdge.output_lt G C hL.2.1 hE
  rw [cutVal_unread C hL.1 j hread (pairInput p q) C.output hbound hout,
    CriticalEdge.val_out, hL.2.1] at hcut
  have htrue : graphFun G ∅ (pairInput p q) = true :=
    (CriticalEdge.gf G _).2 ⟨p, q, hpq, by simp [pairInput], by simp [pairInput]⟩
  rw [htrue] at hcut
  cases hcut

end PEqualNP.Outside.L_meta_5012.Frontier

namespace PEqualNP.Outside.L_meta_5012.BoundaryFilters

open PEqualNP.TopForm

open PEqualNP.Outside.L_meta_5012.Overlap

end PEqualNP.Outside.L_meta_5012.BoundaryFilters

namespace PEqualNP.Outside.L_meta_5012.OverlapCase

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo

lemma ao2_wire_all_true {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) :
    ∀ u < n + C.gates.length, wval C (fun _ : Fin n => true) u = true := by
  intro u
  induction u using Nat.strong_induction_on with
  | ind u ih =>
    intro hu
    by_cases hun : u < n
    · rw [Lift.wval_input C (fun _ => true) u hun]
    · obtain ⟨j, rfl⟩ : ∃ j, u = n + j := ⟨u - n, by omega⟩
      have hj : j < C.gates.length := by omega
      have h0 := Lift.opnd_lt hAO hj 0
      have h1 := Lift.opnd_lt hAO hj 1
      have hv0 := ih (opnd C j 0) h0 (by omega)
      have hv1 := ih (opnd C j 1) h1 (by omega)
      rw [Lift.wval_gate_eval hAO _ hj, hv0, hv1]
      rcases hAO.1 _ (Lift.gateAt_mem hj) with hop | hop <;> rw [hop] <;> rfl

lemma top_raw_boundary_dichotomy {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C) (hTF : TopForm G C)
    {j k : ℕ} (hJ : junk G C = {j,k}) {w : Fin n} (hW : wmax G C j = {w})
    (h4 : NoFourCycle G) (I T : Finset (Fin n))
    (hOverlap : 2 ≤ (T ∩ I).card) (hIw : ∀ i ∈ I, G.Adj w i)
    {a : ℕ} (ha : a ∈ tops G C) (b : Fin 2)
    (hTside : T ⊆ side (n := n) C a b) :
    (∀ t ∈ T, G.Adj w t) ∨ T ⊆ wmax G C k := by
  obtain ⟨haLen, haAnd, _⟩ := Critical.Base.topData ha
  have hOpBound := Lift.opnd_lt hAO haLen (1-b)
  have hOpTrue : RawOperands.W n C (fun _ : Fin n => true) (opnd C a (1-b)) = true :=
    ao2_wire_all_true hAO _ (by omega)
  have hFlip : 1 - (1 - b) = b := by fin_cases b <;> decide
  have hTopAdj (t r : Fin n) (ht : t ∈ side (n := n) C a b)
      (hr : r ∈ side (n := n) C a (1-b)) : G.Adj t r := by
    fin_cases b
    · exact Critical.Base.topAdj hAO ha ht hr
    · exact (Critical.Base.topAdj hAO ha hr ht).symm
  rcases RawOperands.down n C (fun _ : Fin n => true)
      (fun l hl => hAO.1 _ (RawOperands.gateAt_mem' C l hl)) _ hOpTrue with
    ⟨r, hr, _⟩ | ⟨l, hl, hReach, hlAnd, _⟩
  · left
    have hrw : r = w := by
      by_contra hne
      have hSub : T ∩ I ⊆ Finset.univ.filter fun t => G.Adj r t ∧ G.Adj w t := by
        intro t ht
        obtain ⟨htT, htI⟩ := Finset.mem_inter.mp ht
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (hTopAdj t r (hTside htT) hr).symm, hIw t htI⟩
      have hCard := (Finset.card_le_card hSub).trans (h4 r w hne)
      omega
    intro t ht
    rw [← hrw]
    exact (hTopAdj t r (hTside ht) hr).symm
  · have hlJ : l ∈ junk G C :=
      Critical.Base.operandOrAndJunk hAO hTF haLen haAnd hReach hlAnd
    have hAll : T ⊆ wmax G C l := by
      have hOpp := Critical.Base.oppositeSideWmax hAO ha hReach
      rw [hFlip] at hOpp
      exact hTside.trans hOpp
    rcases Critical.Base.memJunkPair hJ hlJ with rfl | rfl
    · have hSub : T ∩ I ⊆ ({w} : Finset (Fin n)) := by
        intro t ht
        rw [← hW]
        exact hAll (Finset.mem_inter.mp ht).1
      have hCard := Finset.card_le_card hSub
      simp only [Finset.card_singleton] at hCard
      omega
    · exact Or.inr hAll

lemma top_raw_boundary_protected {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C) (hTF : TopForm G C)
    {j k : ℕ} (hJ : junk G C = {j,k})
    (hjk : ¬ InCone n C j k) (hkj : ¬ InCone n C k j)
    {w : Fin n} (hW : wmax G C j = {w}) (h4 : NoFourCycle G)
    (hKOverlap : ((side (n := n) C k 0) ∩ (side (n := n) C k 1)).Nonempty)
    (I T : Finset (Fin n)) (hIw : ∀ i ∈ I, G.Adj w i)
    {a : ℕ} (ha : a ∈ tops G C) (b : Fin 2)
    (hTside : T ⊆ side (n := n) C a b) :
    (∀ t ∈ T, G.Adj w t) ∨ (T ∩ I).card ≤ 1 := by
  by_cases hSmall : (T ∩ I).card ≤ 1
  · exact Or.inr hSmall
  · have hLarge : 2 ≤ (T ∩ I).card := by omega
    rcases top_raw_boundary_dichotomy G C hAO hTF hJ hW h4 I T hLarge hIw ha b hTside
        with hNeighbors | hFilter
    · exact Or.inl hNeighbors
    · left
      obtain ⟨z, hz⟩ := hKOverlap
      have heval (x : Fin n → Bool) : gateVal n C k x = IndependentDescent.product
          (side (n := n) C k 0) (side (n := n) C k 1) x :=
        RawOperands.independent_product G C hAO hTF j k hJ hjk hkj k (Or.inr rfl) x
      have hTz (t : Fin n) (ht : t ∈ T) : G.Adj t z :=
        safe_adj_overlap G _ _
          ((IndependentDescent.wmax_iff G C k _ _ heval t).mp (hFilter ht)) hz
      have hzw : z = w := by
        by_contra hne
        have hSub : T ∩ I ⊆ Finset.univ.filter fun t => G.Adj z t ∧ G.Adj w t := by
          intro t ht
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            (hTz t (Finset.mem_inter.mp ht).1).symm, hIw t (Finset.mem_inter.mp ht).2⟩
        have hCard := (Finset.card_le_card hSub).trans (h4 z w hne)
        omega
      intro t ht
      exact hzw ▸ (hTz t ht).symm

lemma output_raw_frontier_empty {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hF : circuitFun n C = graphFun G ∅) :
    orIn n C C.output = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  have hout : circuitFun n C (pairInput v v) = true :=
    Critical.Base.reach_var_val (pairInput v v) C.output v
      (Critical.Base.mem_orIn_reach v hv) (by simp [pairInput])
  rw [hF] at hout
  exact G.irrefl ((Critical.Base.graphFun_pair G v v).mp hout)

end PEqualNP.Outside.L_meta_5012.OverlapCase

namespace PEqualNP.Outside.L_meta_5012.Frontier

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

end PEqualNP.Outside.L_meta_5012.Frontier

namespace PEqualNP.Outside.L_meta_5012.PrivateMove

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

open Absorption

end PEqualNP.Outside.L_meta_5012.PrivateMove

namespace PEqualNP.Outside.L_meta_5012.AndSwap

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

open Absorption

end PEqualNP.Outside.L_meta_5012.AndSwap

namespace PEqualNP.Outside.L_meta_5012.PrivateMove

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

open Absorption

end PEqualNP.Outside.L_meta_5012.PrivateMove

namespace PEqualNP.Outside.L_meta_5012.Frontier

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

end PEqualNP.Outside.L_meta_5012.Frontier

namespace PEqualNP.Outside.L_meta_5012.OrFrontier

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma or_frontier_of_live {n : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (hlive : ∀ q < C.gates.length,
      C.output = n + q ∨ ∃ j < C.gates.length, n + q ∈ (gateAt C j).inputs)
    (q : ℕ) (hq : q < C.gates.length) :
    Relation.ReflTransGen (Critical.Base.OrStep n C) C.output (n + q) ∨
      ∃ (a : ℕ) (b : Fin 2), a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧
        Relation.ReflTransGen (Critical.Base.OrStep n C) (opnd C a b) (n + q) := by
  have aux : ∀ d q, C.gates.length - q = d → q < C.gates.length →
      Relation.ReflTransGen (Critical.Base.OrStep n C) C.output (n + q) ∨
        ∃ (a : ℕ) (b : Fin 2), a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧
          Relation.ReflTransGen (Critical.Base.OrStep n C) (opnd C a b) (n + q) := by
    intro d
    induction d using Nat.strong_induction_on with
    | ind d ih =>
      intro q hd hq
      rcases hlive q hq with hout | ⟨j, hj, hread⟩
      · exact Or.inl (by rw [hout])
      · have hqj := Frontier.read_index_lt hAO hj hread
        rcases Frontier.gate_op_cases hAO hj with hand | hor
        · obtain ⟨_, hin, _, _, _⟩ := CriticalEdge.gate2 hAO hj
          have hread' : n + q = opnd C j 0 ∨ n + q = opnd C j 1 := by
            rw [hin] at hread
            simpa using hread
          rcases hread' with he | he
          · exact Or.inr ⟨j, 0, hj, hand, by rw [← he]⟩
          · exact Or.inr ⟨j, 1, hj, hand, by rw [← he]⟩
        · have hstep : Critical.Base.OrStep n C (n + j) (n + q) :=
            ⟨j, hj, rfl, hor, hread, by omega⟩
          rcases ih (C.gates.length - j) (by omega) j rfl hj with hout | ⟨a, b, ha, hand, hp⟩
          · exact Or.inl (hout.tail hstep)
          · exact Or.inr ⟨a, b, ha, hand, hp.tail hstep⟩
  exact aux _ q rfl hq

lemma least_or_frontier {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (q : ℕ) (hq : q < C.gates.length) :
    Relation.ReflTransGen (Critical.Base.OrStep n C) C.output (n + q) ∨
      ∃ (a : ℕ) (b : Fin 2), a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧
        Relation.ReflTransGen (Critical.Base.OrStep n C) (opnd C a b) (n + q) :=
  or_frontier_of_live C hL.1 (Frontier.least_live G C hL) q hq

end PEqualNP.Outside.L_meta_5012.OrFrontier

namespace PEqualNP.Outside.L_meta_5012.OverlapCase

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo

open IndependentDescent CleanReplacement

lemma critical_overlap_cover {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C)
    (hF : circuitFun n C = graphFun G ∅) (hT : TopForm G C)
    {j k : ℕ} (hne : j ≠ k) (hJ : junk G C = {j,k})
    (hjk : ¬ InCone n C j k) (hkj : ¬ InCone n C k j)
    (hNoCommon : ∀ a ∈ tops G C, ∀ b : Fin 2,
      OrReaches n C (opnd C a b) j → ¬ OrReaches n C (opnd C a (1-b)) k)
    (z : Fin n) (hW : wmax G C j = {z})
    (hzOut : z ∉ side (n := n) C j 0 ∪ side (n := n) C j 1)
    (u v : Fin n) (huv : G.Adj u v)
    (hLost : circuitFun n (patch C j off) (pairInput u v) = false) :
    pairInput u v z = true ∧
      ∃ i ∈ side (n := n) C j 0 ∩ side (n := n) C j 1,
        pairInput u v i = true := by
  let P := side (n := n) C j 0
  let Q := side (n := n) C j 1
  have heval (x : Fin n → Bool) : gateVal n C j x = product P Q x :=
    RawOperands.independent_product G C hAO hT j k hJ hjk hkj j (Or.inl rfl) x
  have hJ' : junk G C = {k,j} := by rw [hJ, Finset.pair_comm]
  obtain ⟨hjv, hFilter⟩ := Critical.critical_edge_useful hAO hF hT hJ'
    (Ne.symm hne) hjk hNoCommon u v huv hLost
  have hp : product P Q (pairInput u v) = true := (heval _).symm.trans hjv
  rcases hFilter with hu | hv
  · have hueq : u = z := by simpa [hW] using hu
    subst u
    have hvI := product_pair_overlap_of_outside P Q hzOut hp
    exact ⟨by simp [pairInput], v, hvI, by simp [pairInput]⟩
  · have hveq : v = z := by simpa [hW] using hv
    subst v
    have hSwap : pairInput u z = pairInput z u := by
      funext a
      simp [pairInput, or_comm]
    rw [hSwap] at hp
    have huI := product_pair_overlap_of_outside P Q hzOut hp
    exact ⟨by simp [pairInput], u, huI, by simp [pairInput]⟩

end PEqualNP.Outside.L_meta_5012.OverlapCase

namespace PEqualNP.Outside.L_meta_5012.OverlapCase

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo

lemma both_large_overlap_no_opposite {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C) (hT : TopForm G C)
    {j k : ℕ} (hJ : junk G C = {j,k})
    (hjk : ¬ InCone n C j k) (hkj : ¬ InCone n C k j) (h4 : NoFourCycle G)
    (hLargeJ : 2 ≤ (side (n := n) C j 0 ∩ side (n := n) C j 1).card)
    (hLargeK : 2 ≤ (side (n := n) C k 0 ∩ side (n := n) C k 1).card) :
    ∀ a ∈ tops G C, ∀ b : Fin 2,
      OrReaches n C (opnd C a b) j → ¬ OrReaches n C (opnd C a (1-b)) k := by
  intro a ha b hjr hkr
  have hevalJ (x : Fin n → Bool) : gateVal n C j x =
      IndependentDescent.product (side (n := n) C j 0) (side (n := n) C j 1) x :=
    RawOperands.independent_product G C hAO hT j k hJ hjk hkj j (Or.inl rfl) x
  have hevalK (x : Fin n → Bool) : gateVal n C k x =
      IndependentDescent.product (side (n := n) C k 0) (side (n := n) C k 1) x :=
    RawOperands.independent_product G C hAO hT j k hJ hjk hkj k (Or.inr rfl) x
  have hClean : Overlap.CleanMutual G (side (n := n) C j 0) (side (n := n) C j 1)
      (side (n := n) C k 0) (side (n := n) C k 1) := by
    intro x hx
    have hv : Overlap.product (side (n := n) C j 0) (side (n := n) C j 1) x = true ∧
        Overlap.product (side (n := n) C k 0) (side (n := n) C k 1) x = true := by
      simpa only [Bool.and_eq_true] using hx
    have hjv : gateVal n C j x = true := by rw [hevalJ]; exact hv.1
    have hkv : gateVal n C k x = true := by rw [hevalK]; exact hv.2
    obtain ⟨haLen, haAnd, haBelow⟩ := Critical.Base.topData ha
    apply haBelow x
    apply (Critical.Base.andValOperands hAO haLen haAnd x).mpr
    intro c
    rcases Critical.Base.eitherOperand b c with rfl | rfl
    · exact Critical.Base.reachVal hjr hjv
    · exact Critical.Base.reachVal hkr hkv
  rcases Overlap.cleanMutual_small_overlap G _ _ _ _ h4 hClean with hSmall | hSmall <;>
    omega

end PEqualNP.Outside.L_meta_5012.OverlapCase

namespace PEqualNP.Outside.L_meta_5012.OrProjection

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm

open Absorption

def internal (n : ℕ) (J : Finset ℕ) (w : ℕ) : Prop := n ≤ w ∧ w - n ∈ J

def rewire (n : ℕ) (J : Finset ℕ) (proxy : ℕ → ℕ) (w : ℕ) : ℕ :=
  if n ≤ w ∧ w - n ∈ J then w else proxy w

def project (n : ℕ) (C : Circuit) (J : Finset ℕ) (proxy : ℕ → ℕ) : Circuit :=
  ⟨C.gates.mapIdx (fun j gate =>
    if j ∈ J then ⟨GateOp.or, gate.inputs.map (rewire n J proxy)⟩ else gate), C.output⟩

lemma project_length (n : ℕ) (C : Circuit) (J : Finset ℕ) (proxy : ℕ → ℕ) :
    (project n C J proxy).gates.length = C.gates.length := by simp [project]

lemma project_gate (n : ℕ) (C : Circuit) (J : Finset ℕ) (proxy : ℕ → ℕ)
    (j : ℕ) (hj : j < C.gates.length) :
    gateAt (project n C J proxy) j =
      if j ∈ J then ⟨GateOp.or, (gateAt C j).inputs.map (rewire n J proxy)⟩ else gateAt C j := by
  rw [gateAt_eq (by simpa only [project_length] using hj), gateAt_eq hj]
  simp [project]

lemma project_ao (n : ℕ) (C : Circuit) (J : Finset ℕ) (proxy : ℕ → ℕ)
    (hAO : IsAO2 n C)
    (hback : ∀ j ∈ J, ∀ w ∈ (gateAt C j).inputs, rewire n J proxy w < n + j) :
    IsAO2 n (project n C J proxy) := by
  have hdata : ∀ j < (project n C J proxy).gates.length,
      ((gateAt (project n C J proxy) j).op = GateOp.and ∨
        (gateAt (project n C J proxy) j).op = GateOp.or) ∧
      (gateAt (project n C J proxy) j).inputs.length = 2 ∧
      ∀ w ∈ (gateAt (project n C J proxy) j).inputs, w < n + j := by
    intro j hj
    have hjC : j < C.gates.length := by simpa only [project_length] using hj
    rw [project_gate n C J proxy j hjC]
    split_ifs with hjJ
    · refine ⟨Or.inr rfl, ?_, ?_⟩
      · simpa using hAO.2.2 _ (gateAt_mem hjC)
      · intro w hw
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
        exact hback j hjJ u hu
    · exact ⟨hAO.1 _ (gateAt_mem hjC), hAO.2.2 _ (gateAt_mem hjC), hAO.2.1 j hjC⟩
  refine ⟨?_, ?_, ?_⟩
  · intro gate hgate
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hgate
    have h := (hdata j hj).1
    rwa [gateAt_eq hj] at h
  · intro j hj w hw
    exact (hdata j hj).2.2 w hw
  · intro gate hgate
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hgate
    have h := (hdata j hj).2.1
    rwa [gateAt_eq hj] at h

lemma project_protected_values (n : ℕ) (C : Circuit) (J : Finset ℕ) (proxy : ℕ → ℕ)
    (hAO : IsAO2 n C) (E : Finset ℕ) (hdis : Disjoint E J)
    (hclosed : ∀ j ∈ E, ∀ w ∈ (gateAt C j).inputs, n ≤ w → w - n ∈ E)
    (x : Fin n → Bool) :
    ∀ j < C.gates.length, j ∈ E →
      val (project n C J proxy) (List.ofFn x) (n + j) = val C (List.ofFn x) (n + j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj hjE
    have hjJ : j ∉ J := fun hjJ => Finset.disjoint_left.mp hdis hjE hjJ
    have earlier : ∀ w ∈ (gateAt C j).inputs,
        val (project n C J proxy) (List.ofFn x) w = val C (List.ofFn x) w := by
      intro w hw
      by_cases hwn : w < n
      · rw [val_input (n := n) (by simp) hwn, val_input (n := n) (by simp) hwn]
      · have hwj := hAO.2.1 j hj w hw
        have hwrepr : w = n + (w - n) := by omega
        rw [hwrepr]
        exact ih (w - n) (by omega) (by omega) (hclosed j hjE w hw (by omega))
    rw [val_gate (n := n) (by simp) (by simpa only [project_length] using hj),
      val_gate (n := n) (by simp) hj, project_gate n C J proxy j hj, ite_eq_right hjJ]
    congr 1
    apply List.map_congr_left
    intro w hw
    have hwj := hAO.2.1 j hj w hw
    simp only [ite_eq_left hwj]
    exact earlier w hw

lemma project_protected_wire (n : ℕ) (C : Circuit) (J : Finset ℕ) (proxy : ℕ → ℕ)
    (hAO : IsAO2 n C) (E : Finset ℕ) (hdis : Disjoint E J)
    (hclosed : ∀ j ∈ E, ∀ w ∈ (gateAt C j).inputs, n ≤ w → w - n ∈ E)
    (x : Fin n → Bool) (w : ℕ) (hwE : n ≤ w → w - n ∈ E) :
    val (project n C J proxy) (List.ofFn x) w = val C (List.ofFn x) w := by
  by_cases hwn : w < n
  · rw [val_input (n := n) (by simp) hwn, val_input (n := n) (by simp) hwn]
  by_cases hwC : w < n + C.gates.length
  · have hwrepr : w = n + (w - n) := by omega
    rw [hwrepr]
    exact project_protected_values n C J proxy hAO E hdis hclosed x (w-n) (by omega) (hwE (by omega))
  · rw [val_ge (n := n) (by simp) (by rw [project_length]; omega),
      val_ge (n := n) (by simp) (by omega)]

def support (n : ℕ) (C : Circuit) (J : Finset ℕ) (boundary : ℕ → Finset (Fin n))
    (w : ℕ) : Finset (Fin n) :=
  if n ≤ w ∧ w - n ∈ J then
    (gateAt C (w-n)).inputs.foldr
      (fun u S => (if _hu : u < w then support n C J boundary u else ∅) ∪ S) ∅
  else boundary w
termination_by w

def rawOr {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∃ a ∈ S, x a = true)

lemma rawOr_union {n : ℕ} (A B : Finset (Fin n)) (x : Fin n → Bool) :
    rawOr (A ∪ B) x = (rawOr A x || rawOr B x) := by
  simp [rawOr, Finset.mem_union, or_and_right, exists_or]

lemma support_outside (n : ℕ) (C : Circuit) (J : Finset ℕ) (boundary : ℕ → Finset (Fin n))
    (w : ℕ) (hw : ¬ internal n J w) : support n C J boundary w = boundary w := by
  change ¬ (n ≤ w ∧ w - n ∈ J) at hw
  rw [support, ite_eq_right hw]

lemma support_gate (n : ℕ) (C : Circuit) (J : Finset ℕ) (boundary : ℕ → Finset (Fin n))
    (j a b : ℕ) (hj : j ∈ J) (hinputs : (gateAt C j).inputs = [a,b])
    (ha : a < n+j) (hb : b < n+j) :
    support n C J boundary (n+j) =
      support n C J boundary a ∪ support n C J boundary b := by
  rw [support]
  simp only [Nat.le_add_right, Nat.add_sub_cancel_left, hj, and_self, ite_true, hinputs,
    List.foldr_cons, List.foldr_nil, dite_eq_left ha, dite_eq_left hb, Finset.union_empty]

lemma support_subset (n : ℕ) (C : Circuit) (J : Finset ℕ) (boundary : ℕ → Finset (Fin n))
    (hAO : IsAO2 n C) (hreal : ∀ j ∈ J, j < C.gates.length)
    (N : Finset (Fin n)) (hboundary : ∀ w, boundary w ⊆ N) :
    ∀ w, support n C J boundary w ⊆ N := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw : internal n J w
    · have hj : w-n ∈ J := hw.2
      have hjr := hreal (w-n) hj
      have hwrep : w = n+(w-n) := by have := hw.1; omega
      obtain ⟨a,b,hab⟩ := List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem hjr))
      have ha : a < w := by
        have h := hAO.2.1 (w-n) hjr a (by rw [hab]; simp)
        omega
      have hb : b < w := by
        have h := hAO.2.1 (w-n) hjr b (by rw [hab]; simp)
        omega
      have hgate := support_gate n C J boundary (w-n) a b hj hab (by omega) (by omega)
      rw [← hwrep] at hgate
      rw [hgate]
      exact Finset.union_subset (ih a ha) (ih b hb)
    · rw [support_outside n C J boundary w hw]
      exact hboundary w

lemma support_covers (n : ℕ) (C : Circuit) (J : Finset ℕ) (boundary S : ℕ → Finset (Fin n))
    (hAO : IsAO2 n C) (hreal : ∀ j ∈ J, j < C.gates.length)
    (I : Finset (Fin n))
    (hboundary : ∀ w, S w ∩ I ⊆ boundary w)
    (hS : ∀ j ∈ J, ∀ a b, (gateAt C j).inputs = [a,b] → S (n+j) = S a ∪ S b) :
    ∀ w, S w ∩ I ⊆ support n C J boundary w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw : internal n J w
    · have hj : w-n ∈ J := hw.2
      have hjr := hreal (w-n) hj
      have hwrep : w = n+(w-n) := by have := hw.1; omega
      obtain ⟨a,b,hab⟩ := List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem hjr))
      have ha : a < w := by
        have h := hAO.2.1 (w-n) hjr a (by rw [hab]; simp)
        omega
      have hb : b < w := by
        have h := hAO.2.1 (w-n) hjr b (by rw [hab]; simp)
        omega
      have hgate := support_gate n C J boundary (w-n) a b hj hab (by omega) (by omega)
      have hSgate := hS (w-n) hj a b hab
      rw [← hwrep] at hgate hSgate
      rw [hgate, hSgate]
      intro v hv
      have hvI := (Finset.mem_inter.mp hv).2
      rcases Finset.mem_union.mp (Finset.mem_inter.mp hv).1 with hva | hvb
      · exact Finset.mem_union_left _ (ih a ha (Finset.mem_inter.mpr ⟨hva,hvI⟩))
      · exact Finset.mem_union_right _ (ih b hb (Finset.mem_inter.mpr ⟨hvb,hvI⟩))
    · rw [support_outside n C J boundary w hw]
      exact hboundary w

lemma project_internal_values (n : ℕ) (C : Circuit) (J : Finset ℕ) (proxy : ℕ → ℕ)
    (boundary : ℕ → Finset (Fin n)) (hAO : IsAO2 n C)
    (hreal : ∀ j ∈ J, j < C.gates.length)
    (hback : ∀ j ∈ J, ∀ w ∈ (gateAt C j).inputs, rewire n J proxy w < n + j)
    (hBoundary : ∀ j ∈ J, ∀ w ∈ (gateAt C j).inputs, ¬ internal n J w →
      ∀ x : Fin n → Bool,
        val (project n C J proxy) (List.ofFn x) (proxy w) = rawOr (boundary w) x)
    (x : Fin n → Bool) :
    ∀ j ∈ J, val (project n C J proxy) (List.ofFn x) (n+j) =
      rawOr (support n C J boundary (n+j)) x := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj
    have hjr := hreal j hj
    obtain ⟨a,b,hab⟩ := List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem hjr))
    have ha := hAO.2.1 j hjr a (by rw [hab]; simp)
    have hb := hAO.2.1 j hjr b (by rw [hab]; simp)
    have hgate : gateAt (project n C J proxy) j =
        ⟨GateOp.or, [rewire n J proxy a, rewire n J proxy b]⟩ := by
      rw [project_gate n C J proxy j hjr, ite_eq_left hj, hab]
      rfl
    have hinput (w : ℕ) (hw : w ∈ (gateAt C j).inputs) :
        val (project n C J proxy) (List.ofFn x) (rewire n J proxy w) =
          rawOr (support n C J boundary w) x := by
      by_cases hwI : internal n J w
      · have hwn := hwI.1
        have hwj := hAO.2.1 j hjr w hw
        have hwrep : w = n+(w-n) := by omega
        have hcond : n ≤ w ∧ w - n ∈ J := hwI
        rw [rewire, ite_eq_left hcond, hwrep]
        exact ih (w-n) (by omega) hwI.2
      · have hcond : ¬ (n ≤ w ∧ w - n ∈ J) := hwI
        rw [rewire, ite_eq_right hcond, support_outside n C J boundary w hwI]
        exact hBoundary j hj w hw hwI x
    rw [binary_eval _ j _ _ GateOp.or (by simpa only [project_length] using hjr) hgate
      (hback j hj a (by rw [hab]; simp)) (hback j hj b (by rw [hab]; simp)),
      hinput a (by rw [hab]; simp), hinput b (by rw [hab]; simp),
      support_gate n C J boundary j a b hj hab ha hb, rawOr_union]
    simp [GateOp.eval]

lemma binary_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (a b c d : Bool) (hac : a = true → c = true) (hbd : b = true → d = true) :
    op.eval [a,b] = true → op.eval [c,d] = true := by
  rcases hop with rfl | rfl <;> cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [GateOp.eval]

lemma private_patch_mono (n : ℕ) (C D E : Circuit) (J : Finset ℕ) (g : ℕ)
    (hAO : IsAO2 n C) (hDlen : D.gates.length = C.gates.length)
    (hElen : E.gates.length = C.gates.length)
    (hDsame : ∀ j < C.gates.length, j ∉ J → j ≠ g → gateAt D j = gateAt C j)
    (hEsame : ∀ j < C.gates.length, j ∉ J → j ≠ g → gateAt E j = gateAt C j)
    (hprivate : ∀ i ∈ J, ∀ j < C.gates.length,
      n+i ∈ (gateAt C j).inputs → j ∈ J ∨ j = g)
    (x : Fin n → Bool)
    (hg : val D (List.ofFn x) (n+g) = true → val E (List.ofFn x) (n+g) = true) :
    ∀ j < C.gates.length, j ∉ J →
      val D (List.ofFn x) (n+j) = true → val E (List.ofFn x) (n+j) = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj hjJ
    by_cases hjg : j = g
    · subst j; exact hg
    obtain ⟨a,b,hab⟩ := List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem hj))
    have hshape : gateAt C j = ⟨(gateAt C j).op,[a,b]⟩ := by rw [← hab]
    have ha := hAO.2.1 j hj a (by rw [hab]; simp)
    have hb := hAO.2.1 j hj b (by rw [hab]; simp)
    have hinput (w : ℕ) (hw : w ∈ (gateAt C j).inputs) :
        val D (List.ofFn x) w = true → val E (List.ofFn x) w = true := by
      by_cases hwn : w < n
      · rw [val_input (n := n) (by simp) hwn, val_input (n := n) (by simp) hwn]
        exact id
      · have hwj := hAO.2.1 j hj w hw
        have hwrep : w = n+(w-n) := by omega
        have hwJ : w-n ∉ J := by
          intro hmem
          have hread : n+(w-n) ∈ (gateAt C j).inputs := by rwa [← hwrep]
          rcases hprivate (w-n) hmem j hj hread with hJ | hG
          · exact hjJ hJ
          · exact hjg hG
        rw [hwrep]
        exact ih (w-n) (by omega) (by omega) hwJ
    rw [binary_eval D j a b _ (by omega) ((hDsame j hj hjJ hjg).trans hshape) ha hb,
      binary_eval E j a b _ (by omega) ((hEsame j hj hjJ hjg).trans hshape) ha hb]
    exact binary_mono _ (hAO.1 _ (gateAt_mem hj)) _ _ _ _
      (hinput a (by rw [hab]; simp)) (hinput b (by rw [hab]; simp))

lemma private_patch_wire_mono (n : ℕ) (C D E : Circuit) (J : Finset ℕ) (g : ℕ)
    (hAO : IsAO2 n C) (hDlen : D.gates.length = C.gates.length)
    (hElen : E.gates.length = C.gates.length)
    (hDsame : ∀ j < C.gates.length, j ∉ J → j ≠ g → gateAt D j = gateAt C j)
    (hEsame : ∀ j < C.gates.length, j ∉ J → j ≠ g → gateAt E j = gateAt C j)
    (hprivate : ∀ i ∈ J, ∀ j < C.gates.length,
      n+i ∈ (gateAt C j).inputs → j ∈ J ∨ j = g)
    (x : Fin n → Bool)
    (hg : val D (List.ofFn x) (n+g) = true → val E (List.ofFn x) (n+g) = true)
    (w : ℕ) (hw : ¬ internal n J w) :
    val D (List.ofFn x) w = true → val E (List.ofFn x) w = true := by
  by_cases hwn : w < n
  · rw [val_input (n := n) (by simp) hwn, val_input (n := n) (by simp) hwn]
    exact id
  by_cases hwC : w < n+C.gates.length
  · have hwrep : w = n+(w-n) := by omega
    have hwJ : w-n ∉ J := fun hJ => hw ⟨by omega,hJ⟩
    rw [hwrep]
    exact private_patch_mono n C D E J g hAO hDlen hElen hDsame hEsame hprivate x hg
      (w-n) (by omega) hwJ
  · rw [val_ge (n := n) (by simp) (by omega), val_ge (n := n) (by simp) (by omega)]
    exact id

def finish (n : ℕ) (C : Circuit) (J : Finset ℕ) (proxy : ℕ → ℕ)
    (g center root : ℕ) : Circuit :=
  ⟨(project n C J proxy).gates.set g ⟨GateOp.and,[center,root]⟩, C.output⟩

lemma finish_length (n : ℕ) (C : Circuit) (J : Finset ℕ) (proxy : ℕ → ℕ)
    (g center root : ℕ) :
    (finish n C J proxy g center root).gates.length = C.gates.length := by
  simp [finish, project_length]

lemma finish_size (n : ℕ) (C : Circuit) (J : Finset ℕ) (proxy : ℕ → ℕ)
    (g center root : ℕ) : (finish n C J proxy g center root).size = C.size := by
  exact finish_length n C J proxy g center root

lemma finish_gate (n : ℕ) (C : Circuit) (J : Finset ℕ) (proxy : ℕ → ℕ)
    (g center root j : ℕ) (hj : j < C.gates.length) :
    gateAt (finish n C J proxy g center root) j =
      if j = g then ⟨GateOp.and,[center,root]⟩ else gateAt (project n C J proxy) j := by
  rw [gateAt_eq (by simpa only [finish_length] using hj),
    gateAt_eq (by simpa only [project_length] using hj)]
  simp [finish, List.getElem_set, eq_comm]

lemma finish_same (n : ℕ) (C : Circuit) (J : Finset ℕ) (proxy : ℕ → ℕ)
    (g center root j : ℕ) (hj : j < C.gates.length) (hjJ : j ∉ J) (hjg : j ≠ g) :
    gateAt (finish n C J proxy g center root) j = gateAt C j := by
  rw [finish_gate n C J proxy g center root j hj, ite_eq_right hjg,
    project_gate n C J proxy j hj, ite_eq_right hjJ]

lemma finish_ao (n : ℕ) (C : Circuit) (J : Finset ℕ) (proxy : ℕ → ℕ)
    (g center root : ℕ) (hAO : IsAO2 n C)
    (hback : ∀ j ∈ J, ∀ w ∈ (gateAt C j).inputs, rewire n J proxy w < n+j)
    (hcenter : center < n+g) (hroot : root < n+g) :
    IsAO2 n (finish n C J proxy g center root) := by
  have hP := project_ao n C J proxy hAO hback
  have hdata : ∀ j < (finish n C J proxy g center root).gates.length,
      ((gateAt (finish n C J proxy g center root) j).op = GateOp.and ∨
        (gateAt (finish n C J proxy g center root) j).op = GateOp.or) ∧
      (gateAt (finish n C J proxy g center root) j).inputs.length = 2 ∧
      ∀ w ∈ (gateAt (finish n C J proxy g center root) j).inputs, w < n+j := by
    intro j hj
    have hjC : j < C.gates.length := by simpa only [finish_length] using hj
    rw [finish_gate n C J proxy g center root j hjC]
    split_ifs with hjg
    · subst j
      refine ⟨Or.inl rfl,rfl,?_⟩
      intro w hw
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with rfl | rfl
      · exact hcenter
      · exact hroot
    · have hjP : j < (project n C J proxy).gates.length := by simpa only [project_length] using hjC
      exact ⟨hP.1 _ (gateAt_mem hjP), hP.2.2 _ (gateAt_mem hjP), hP.2.1 j hjP⟩
  refine ⟨?_,?_,?_⟩
  · intro gate hgate
    obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hgate
    have h := (hdata j hj).1
    rwa [gateAt_eq hj] at h
  · intro j hj w hw
    exact (hdata j hj).2.2 w hw
  · intro gate hgate
    obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hgate
    have h := (hdata j hj).2.1
    rwa [gateAt_eq hj] at h

lemma same_before_values (n : ℕ) (C D : Circuit) (cut : ℕ)
    (hAO : IsAO2 n C) (hlen : D.gates.length = C.gates.length)
    (hsame : ∀ j < C.gates.length, j < cut → gateAt D j = gateAt C j)
    (x : Fin n → Bool) : ∀ j < C.gates.length, j < cut →
      val D (List.ofFn x) (n+j) = val C (List.ofFn x) (n+j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj hjcut
    have earlier (w : ℕ) (hw : w ∈ (gateAt C j).inputs) :
        val D (List.ofFn x) w = val C (List.ofFn x) w := by
      by_cases hwn : w < n
      · rw [val_input (n := n) (by simp) hwn, val_input (n := n) (by simp) hwn]
      · have hwj := hAO.2.1 j hj w hw
        have hwrep : w = n+(w-n) := by omega
        rw [hwrep]
        exact ih (w-n) (by omega) (by omega) (by omega)
    rw [val_gate (n := n) (by simp) (by omega), val_gate (n := n) (by simp) hj,
      hsame j hj hjcut]
    congr 1
    apply List.map_congr_left
    intro w hw
    have hwj := hAO.2.1 j hj w hw
    simp only [ite_eq_left hwj]
    exact earlier w hw

lemma same_before_wire (n : ℕ) (C D : Circuit) (cut : ℕ)
    (hAO : IsAO2 n C) (hlen : D.gates.length = C.gates.length)
    (hsame : ∀ j < C.gates.length, j < cut → gateAt D j = gateAt C j)
    (x : Fin n → Bool) (w : ℕ) (hw : w < n+cut) :
    val D (List.ofFn x) w = val C (List.ofFn x) w := by
  by_cases hwn : w < n
  · rw [val_input (n := n) (by simp) hwn, val_input (n := n) (by simp) hwn]
  by_cases hwC : w < n+C.gates.length
  · have hwrep : w = n+(w-n) := by omega
    rw [hwrep]
    exact same_before_values n C D cut hAO hlen hsame x (w-n) (by omega) (by omega)
  · rw [val_ge (n := n) (by simp) (by omega), val_ge (n := n) (by simp) (by omega)]

lemma finish_before_wire (n : ℕ) (C : Circuit) (J : Finset ℕ) (proxy : ℕ → ℕ)
    (g center root : ℕ) (hAO : IsAO2 n C)
    (hback : ∀ j ∈ J, ∀ w ∈ (gateAt C j).inputs, rewire n J proxy w < n+j)
    (x : Fin n → Bool) (w : ℕ) (hw : w < n+g) :
    val (finish n C J proxy g center root) (List.ofFn x) w =
      val (project n C J proxy) (List.ofFn x) w := by
  apply same_before_wire n (project n C J proxy) (finish n C J proxy g center root) g
    (project_ao n C J proxy hAO hback)
    (by rw [finish_length, project_length]) _ x w hw
  intro j hj hjg
  have hjC : j < C.gates.length := by simpa only [project_length] using hj
  rw [finish_gate n C J proxy g center root j hjC, ite_eq_right (Nat.ne_of_lt hjg)]

lemma finish_g_value (n : ℕ) (C : Circuit) (J : Finset ℕ) (proxy : ℕ → ℕ)
    (boundary : ℕ → Finset (Fin n)) (g r : ℕ) (center : Fin n)
    (hAO : IsAO2 n C) (hreal : ∀ j ∈ J, j < C.gates.length)
    (hback : ∀ j ∈ J, ∀ w ∈ (gateAt C j).inputs, rewire n J proxy w < n+j)
    (hBoundary : ∀ j ∈ J, ∀ w ∈ (gateAt C j).inputs, ¬ internal n J w →
      ∀ x : Fin n → Bool,
        val (project n C J proxy) (List.ofFn x) (proxy w) = rawOr (boundary w) x)
    (hg : g < C.gates.length) (hr : r ∈ J) (hrg : r < g) (x : Fin n → Bool) :
    gateVal n (finish n C J proxy g center.val (n+r)) g x =
      (x center && rawOr (support n C J boundary (n+r)) x) := by
  have hgate : gateAt (finish n C J proxy g center.val (n+r)) g =
      ⟨GateOp.and,[center.val,n+r]⟩ := by
    rw [finish_gate n C J proxy g center.val (n+r) g hg, ite_eq_left rfl]
  rw [gateVal_eq_val,
    binary_eval _ g center.val (n+r) GateOp.and (by simpa only [finish_length] using hg)
      hgate (by have := center.isLt; omega) (by omega),
    val_ofFn _ x center,
    finish_before_wire n C J proxy g center.val (n+r) hAO hback x (n+r) (by omega),
    project_internal_values n C J proxy boundary hAO hreal hback hBoundary x r hr]
  simp [GateOp.eval]

lemma project_boundary_from_protected (n : ℕ) (C : Circuit) (J E : Finset ℕ)
    (proxy : ℕ → ℕ) (boundary : ℕ → Finset (Fin n))
    (hAO : IsAO2 n C) (hdis : Disjoint E J)
    (hclosed : ∀ j ∈ E, ∀ w ∈ (gateAt C j).inputs, n ≤ w → w-n ∈ E)
    (hproxy : ∀ j ∈ J, ∀ w ∈ (gateAt C j).inputs, ¬ internal n J w →
      n ≤ proxy w → proxy w-n ∈ E)
    (hBoundary : ∀ j ∈ J, ∀ w ∈ (gateAt C j).inputs, ¬ internal n J w →
      ∀ x : Fin n → Bool, val C (List.ofFn x) (proxy w) = rawOr (boundary w) x) :
    ∀ j ∈ J, ∀ w ∈ (gateAt C j).inputs, ¬ internal n J w →
      ∀ x : Fin n → Bool,
        val (project n C J proxy) (List.ofFn x) (proxy w) = rawOr (boundary w) x := by
  intro j hj w hw hwI x
  rw [project_protected_wire n C J proxy hAO E hdis hclosed x (proxy w) (hproxy j hj w hw hwI)]
  exact hBoundary j hj w hw hwI x

def cut (C : Circuit) (g : ℕ) : Circuit :=
  ⟨C.gates.set g ⟨GateOp.or,[]⟩,C.output⟩

lemma cut_length (C : Circuit) (g : ℕ) : (cut C g).gates.length = C.gates.length := by
  simp [cut]

lemma cut_gate (C : Circuit) (g j : ℕ) (hj : j < C.gates.length) :
    gateAt (cut C g) j = if j = g then ⟨GateOp.or,[]⟩ else gateAt C j := by
  rw [gateAt_eq (by simpa only [cut_length] using hj), gateAt_eq hj]
  simp [cut,List.getElem_set,eq_comm]

lemma cut_g_false (n : ℕ) (C : Circuit) (g : ℕ) (hg : g < C.gates.length)
    (x : Fin n → Bool) : val (cut C g) (List.ofFn x) (n+g) = false := by
  rw [val_gate (n := n) (by simp) (by simpa only [cut_length] using hg),
    cut_gate C g g hg, ite_eq_left rfl]
  rfl

lemma wire_input_mono (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (x y : Fin n → Bool) (hxy : ∀ v, x v = true → y v = true) :
    ∀ j < C.gates.length,
      val C (List.ofFn x) (n+j) = true → val C (List.ofFn y) (n+j) = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj
    obtain ⟨a,b,hab⟩ := List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem hj))
    have hshape : gateAt C j = ⟨(gateAt C j).op,[a,b]⟩ := by rw [←hab]
    have ha := hAO.2.1 j hj a (by rw [hab]; simp)
    have hb := hAO.2.1 j hj b (by rw [hab]; simp)
    have hi (w : ℕ) (hw : w < n+j) :
        val C (List.ofFn x) w = true → val C (List.ofFn y) w = true := by
      by_cases hwn : w < n
      · have heq : w = (⟨w,hwn⟩ : Fin n).val := rfl
        rw [heq, val_ofFn C x ⟨w,hwn⟩, val_ofFn C y ⟨w,hwn⟩]
        exact hxy ⟨w,hwn⟩
      · have hwrep : w = n+(w-n) := by omega
        rw [hwrep]
        exact ih (w-n) (by omega) (by omega)
    rw [binary_eval C j a b _ hj hshape ha hb, binary_eval C j a b _ hj hshape ha hb]
    exact binary_mono _ (hAO.1 _ (gateAt_mem hj)) _ _ _ _ (hi a ha) (hi b hb)

lemma circuit_input_mono (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (x y : Fin n → Bool) (hxy : ∀ v, x v = true → y v = true) :
    circuitFun n C x = true → circuitFun n C y = true := by
  change val C (List.ofFn x) C.output = true → val C (List.ofFn y) C.output = true
  by_cases hwn : C.output < n
  · have heq : C.output = (⟨C.output,hwn⟩ : Fin n).val := rfl
    rw [heq, val_ofFn C x ⟨C.output,hwn⟩, val_ofFn C y ⟨C.output,hwn⟩]
    exact hxy ⟨C.output,hwn⟩
  by_cases hwC : C.output < n+C.gates.length
  · have hwrep : C.output = n+(C.output-n) := by omega
    rw [hwrep]
    exact wire_input_mono n C hAO x y hxy (C.output-n) (by omega)
  · rw [val_ge (n := n) (by simp) (by omega)]
    simp

lemma computes_of_edges {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D : Circuit) (hD : IsAO2 n D)
    (hnegative : ∀ x, graphFun G ∅ x = false → circuitFun n D x = false)
    (hedge : ∀ u v, G.Adj u v → circuitFun n D (pairInput u v) = true) :
    circuitFun n D = graphFun G ∅ := by
  funext x
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hDx
    by_contra hF
    have hfalse : graphFun G ∅ x = false := by cases h : graphFun G ∅ x <;> simp_all
    rw [hnegative x hfalse] at hDx
    cases hDx
  · intro hF
    have hpair : ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
      simpa [graphFun] using hF
    obtain ⟨u,v,huv,hu,hv⟩ := hpair
    apply circuit_input_mono n D hD (pairInput u v) x _ (hedge u v huv)
    intro a ha
    have ha' : a = u ∨ a = v := by simpa [pairInput] using ha
    rcases ha' with rfl | rfl
    · exact hu
    · exact hv

lemma private_patch_computes {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C D : Circuit) (J : Finset ℕ) (g : ℕ)
    (hAO : IsAO2 n C) (hD : IsAO2 n D) (hDlen : D.gates.length = C.gates.length)
    (hg : g < C.gates.length) (hDout : D.output = C.output)
    (hDsame : ∀ j < C.gates.length, j ∉ J → j ≠ g → gateAt D j = gateAt C j)
    (hprivate : ∀ i ∈ J, ∀ j < C.gates.length,
      n+i ∈ (gateAt C j).inputs → j ∈ J ∨ j = g)
    (hout : ¬ internal n J C.output) (hCF : circuitFun n C = graphFun G ∅)
    (hclean : ∀ x, gateVal n D g x = true → graphFun G ∅ x = true)
    (hcritical : ∀ u v, G.Adj u v → circuitFun n (cut C g) (pairInput u v) = false →
      gateVal n D g (pairInput u v) = true) :
    circuitFun n D = graphFun G ∅ := by
  apply computes_of_edges G D hD
  · intro x hF
    by_contra hDx
    have hDt : circuitFun n D x = true := by cases h : circuitFun n D x <;> simp_all
    have hG : val D (List.ofFn x) (n+g) = true → val C (List.ofFn x) (n+g) = true := by
      intro h
      have hc := hclean x h
      rw [hF] at hc
      cases hc
    have hmono := private_patch_wire_mono n C D C J g hAO hDlen rfl hDsame
      (fun _ _ _ _ => rfl) hprivate x hG C.output hout
    change val D (List.ofFn x) D.output = true at hDt
    rw [hDout] at hDt
    have hCt : circuitFun n C x = true := hmono hDt
    rw [hCF,hF] at hCt
    cases hCt
  · intro u v huv
    let x := pairInput u v
    have hCt : circuitFun n C x = true := by
      rw [hCF]
      simp only [graphFun, Bool.or_eq_true, decide_eq_true_eq]
      right
      exact ⟨u,v,huv,by simp [x,pairInput],by simp [x,pairInput]⟩
    change val D (List.ofFn x) D.output = true
    rw [hDout]
    by_cases hG : gateVal n D g x = true
    · apply private_patch_wire_mono n C C D J g hAO rfl hDlen
        (fun _ _ _ _ => rfl) hDsame hprivate x (fun _ => hG) C.output hout
      exact hCt
    · have hcut : circuitFun n (cut C g) x = true := by
        by_contra hcut
        have hcutf : circuitFun n (cut C g) x = false := by
          cases h : circuitFun n (cut C g) x <;> simp_all
        exact hG (hcritical u v huv hcutf)
      apply private_patch_wire_mono n C (cut C g) D J g hAO (cut_length C g) hDlen
        (fun j hj _ hjg => by rw [cut_gate C g j hj, ite_eq_right hjg])
        hDsame hprivate x _ C.output hout hcut
      intro hgtrue
      rw [cut_g_false n C g hg x] at hgtrue
      cases hgtrue

lemma private_patch_junk_subset {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C D : Circuit) (J : Finset ℕ) (g : ℕ)
    (hAO : IsAO2 n C) (hDlen : D.gates.length = C.gates.length)
    (hDsame : ∀ j < C.gates.length, j ∉ J → j ≠ g → gateAt D j = gateAt C j)
    (hDor : ∀ j ∈ J, (gateAt D j).op = GateOp.or)
    (hprivate : ∀ i ∈ J, ∀ j < C.gates.length,
      n+i ∈ (gateAt C j).inputs → j ∈ J ∨ j = g)
    (hclean : ∀ x, gateVal n D g x = true → graphFun G ∅ x = true) :
    junk G D ⊆ (junk G C).erase g := by
  intro j hjD
  obtain ⟨hj,hop,x,hjx,hF⟩ := (mem_junk_iff G D j).mp hjD
  have hjC : j < C.gates.length := by omega
  have hjJ : j ∉ J := by
    intro hjJ
    rw [hDor j hjJ] at hop
    cases hop
  have hjg : j ≠ g := by
    intro heq
    subst j
    have h := hclean x hjx
    rw [hF] at h
    cases h
  refine Finset.mem_erase.mpr ⟨hjg, (mem_junk_iff G C j).mpr ⟨hjC,?_,x,?_,hF⟩⟩
  · rw [← hDsame j hjC hjJ hjg]
    exact hop
  · apply private_patch_mono n C D C J g hAO hDlen rfl hDsame
      (fun _ _ _ _ => rfl) hprivate x _ j hjC hjJ hjx
    intro hgtrue
    have h := hclean x hgtrue
    rw [hF] at h
    cases h

lemma same_domain_values (n : ℕ) (C D : Circuit) (E : Finset ℕ)
    (hAO : IsAO2 n C) (hlen : D.gates.length = C.gates.length)
    (hsame : ∀ j < C.gates.length, j ∈ E → gateAt D j = gateAt C j)
    (hclosed : ∀ j ∈ E, ∀ w ∈ (gateAt C j).inputs, n ≤ w → w-n ∈ E)
    (x : Fin n → Bool) : ∀ j < C.gates.length, j ∈ E →
      val D (List.ofFn x) (n+j) = val C (List.ofFn x) (n+j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj hjE
    have earlier (w : ℕ) (hw : w ∈ (gateAt C j).inputs) :
        val D (List.ofFn x) w = val C (List.ofFn x) w := by
      by_cases hwn : w < n
      · rw [val_input (n := n) (by simp) hwn, val_input (n := n) (by simp) hwn]
      · have hwj := hAO.2.1 j hj w hw
        have hwrep : w = n+(w-n) := by omega
        rw [hwrep]
        exact ih (w-n) (by omega) (by omega) (hclosed j hjE w hw (by omega))
    rw [val_gate (n := n) (by simp) (by omega), val_gate (n := n) (by simp) hj,
      hsame j hj hjE]
    congr 1
    apply List.map_congr_left
    intro w hw
    have hwj := hAO.2.1 j hj w hw
    simp only [ite_eq_left hwj]
    exact earlier w hw

lemma same_domain_junk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C D : Circuit) (E : Finset ℕ) (hAO : IsAO2 n C)
    (hlen : D.gates.length = C.gates.length)
    (hsame : ∀ j < C.gates.length, j ∈ E → gateAt D j = gateAt C j)
    (hclosed : ∀ j ∈ E, ∀ w ∈ (gateAt C j).inputs, n ≤ w → w-n ∈ E)
    (j : ℕ) (hjE : j ∈ E) (hj : j ∈ junk G C) : j ∈ junk G D := by
  obtain ⟨hjr,hop,x,hjx,hF⟩ := (mem_junk_iff G C j).mp hj
  apply (mem_junk_iff G D j).mpr
  refine ⟨by omega,?_,x,?_,hF⟩
  · rw [hsame j hjr hjE]
    exact hop
  · change val D (List.ofFn x) (n+j) = true
    rw [same_domain_values n C D E hAO hlen hsame hclosed x j hjr hjE]
    exact hjx

lemma cleaning_contradiction {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C D : Circuit) (hL : IsLeastAO G C)
    (hOne : ∀ E : Circuit, IsLeastAO G E → (junk G E).card ≠ 1)
    (hTwo : (junk G C).card = 2) (g : ℕ) (hg : g ∈ junk G C)
    (hD : IsAO2 n D) (hsize : D.size = C.size) (hDF : circuitFun n D = graphFun G ∅)
    (hsub : junk G D ⊆ (junk G C).erase g) (hSurvive : (junk G D).Nonempty) : False := by
  have hcard : (junk G D).card = 1 := by
    have hle := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hg,hTwo] at hle
    have hpos := Finset.card_pos.mpr hSurvive
    omega
  have hDL : IsLeastAO G D := by
    refine ⟨hD,hDF,?_⟩
    intro E hE hEF
    rw [hsize]
    exact hL.2.2 E hE hEF
  exact hOne D hDL hcard

lemma projection_contradiction {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C)
    (hOne : ∀ D : Circuit, IsLeastAO G D → (junk G D).card ≠ 1)
    (hTwo : (junk G C).card = 2) (g h r : ℕ) (center : Fin n)
    (hgJ : g ∈ junk G C) (hhJ : h ∈ junk G C)
    (J E A : Finset ℕ) (proxy : ℕ → ℕ) (boundary S : ℕ → Finset (Fin n))
    (I : Finset (Fin n))
    (hbefore : ∀ j ∈ J, j < g) (hr : r ∈ J)
    (hback : ∀ j ∈ J, ∀ w ∈ (gateAt C j).inputs, rewire n J proxy w < n+j)
    (hEdis : Disjoint E J)
    (hEclosed : ∀ j ∈ E, ∀ w ∈ (gateAt C j).inputs, n ≤ w → w-n ∈ E)
    (hproxy : ∀ j ∈ J, ∀ w ∈ (gateAt C j).inputs, ¬ internal n J w →
      n ≤ proxy w → proxy w-n ∈ E)
    (hBoundary : ∀ j ∈ J, ∀ w ∈ (gateAt C j).inputs, ¬ internal n J w →
      ∀ x : Fin n → Bool, val C (List.ofFn x) (proxy w) = rawOr (boundary w) x)
    (hBoundaryClean : ∀ w, ∀ v ∈ boundary w, G.Adj center v)
    (hBoundaryCover : ∀ w, S w ∩ I ⊆ boundary w)
    (hS : ∀ j ∈ J, ∀ a b, (gateAt C j).inputs = [a,b] → S (n+j) = S a ∪ S b)
    (hIroot : I ⊆ S (n+r))
    (hprivate : ∀ i ∈ J, ∀ j < C.gates.length,
      n+i ∈ (gateAt C j).inputs → j ∈ J ∨ j = g)
    (hout : ¬ internal n J C.output)
    (hCritical : ∀ u v, G.Adj u v → circuitFun n (cut C g) (pairInput u v) = false →
      pairInput u v center = true ∧ ∃ i ∈ I, pairInput u v i = true)
    (hhA : h ∈ A)
    (hAclean : ∀ j ∈ A, j ∉ J ∧ j ≠ g)
    (hAclosed : ∀ j ∈ A, ∀ w ∈ (gateAt C j).inputs, n ≤ w → w-n ∈ A) : False := by
  let D := finish n C J proxy g center.val (n+r)
  have hg : g < C.gates.length := (mem_junk_iff G C g).mp hgJ |>.1
  have hreal : ∀ j ∈ J, j < C.gates.length := fun j hj => lt_trans (hbefore j hj) hg
  have hrg := hbefore r hr
  have hDlen : D.gates.length = C.gates.length := finish_length n C J proxy g center.val (n+r)
  have hDsize : D.size = C.size := finish_size n C J proxy g center.val (n+r)
  have hD : IsAO2 n D := finish_ao n C J proxy g center.val (n+r) hL.1 hback
    (by have := center.isLt; omega) (by omega)
  have hDsame : ∀ j < C.gates.length, j ∉ J → j ≠ g → gateAt D j = gateAt C j :=
    finish_same n C J proxy g center.val (n+r)
  have hBoundaryP := project_boundary_from_protected n C J E proxy boundary hL.1
    hEdis hEclosed hproxy hBoundary
  have hvalue (x : Fin n → Bool) : gateVal n D g x =
      (x center && rawOr (support n C J boundary (n+r)) x) :=
    finish_g_value n C J proxy boundary g r center hL.1 hreal hback hBoundaryP hg hr hrg x
  have hsubset : support n C J boundary (n+r) ⊆
      Finset.univ.filter (fun v => G.Adj center v) := by
    apply support_subset n C J boundary hL.1 hreal _ _ (n+r)
    intro w v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hBoundaryClean w v hv⟩
  have hcover : I ⊆ support n C J boundary (n+r) := by
    intro i hi
    exact support_covers n C J boundary S hL.1 hreal I hBoundaryCover hS (n+r)
      (Finset.mem_inter.mpr ⟨hIroot hi,hi⟩)
  have hclean : ∀ x, gateVal n D g x = true → graphFun G ∅ x = true := by
    intro x hx
    rw [hvalue x] at hx
    have hx' : x center = true ∧ ∃ v ∈ support n C J boundary (n+r), x v = true := by
      simpa [rawOr] using hx
    obtain ⟨hc,v,hv,hvx⟩ := hx'
    have hcv : G.Adj center v := (Finset.mem_filter.mp (hsubset hv)).2
    simp only [graphFun,Bool.or_eq_true,decide_eq_true_eq]
    exact Or.inr ⟨center,v,hcv,hc,hvx⟩
  have hcrit : ∀ u v, G.Adj u v → circuitFun n (cut C g) (pairInput u v) = false →
      gateVal n D g (pairInput u v) = true := by
    intro u v huv hcut
    obtain ⟨hc,i,hi,hix⟩ := hCritical u v huv hcut
    rw [hvalue]
    have hraw : rawOr (support n C J boundary (n+r)) (pairInput u v) = true :=
      decide_eq_true ⟨i,hcover hi,hix⟩
    simp [hc,hraw]
  have hDF : circuitFun n D = graphFun G ∅ := private_patch_computes G C D J g hL.1 hD
    hDlen hg rfl hDsame hprivate hout hL.2.1 hclean hcrit
  have hDor : ∀ j ∈ J, (gateAt D j).op = GateOp.or := by
    intro j hj
    have hjr := hreal j hj
    have hjg : j ≠ g := Nat.ne_of_lt (hbefore j hj)
    change (gateAt (finish n C J proxy g center.val (n+r)) j).op = _
    rw [finish_gate n C J proxy g center.val (n+r) j hjr, ite_eq_right hjg,
      project_gate n C J proxy j hjr, ite_eq_left hj]
  have hsub := private_patch_junk_subset G C D J g hL.1 hDlen hDsame hDor hprivate hclean
  have hsurv : h ∈ junk G D := same_domain_junk G C D A hL.1 hDlen
    (fun j hj hjA => hDsame j hj (hAclean j hjA).1 (hAclean j hjA).2) hAclosed h hhA hhJ
  exact cleaning_contradiction G C D hL hOne hTwo g hgJ hD hDsize hDF hsub ⟨h,hsurv⟩

end PEqualNP.Outside.L_meta_5012.OrProjection

namespace PEqualNP.Outside.L_meta_5012.OrProjection

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm

open Absorption

noncomputable def pickOr {n : ℕ} (T : Finset (Fin n)) (d : Fin n) : Fin n :=
  if h : T.Nonempty then Classical.choose h else d

lemma pickOr_mem {n : ℕ} (T : Finset (Fin n)) (d : Fin n) (h : T.Nonempty) :
    pickOr T d ∈ T := by
  simp only [pickOr,dite_eq_left h]
  exact Classical.choose_spec h

noncomputable def boundaryProxy {n : ℕ} (N I : Finset (Fin n)) (d : Fin n)
    (S : ℕ → Finset (Fin n)) (w : ℕ) : ℕ :=
  if S w ⊆ N then w else (pickOr (S w ∩ I) d).val

def boundarySupport {n : ℕ} (N I : Finset (Fin n)) (d : Fin n)
    (S : ℕ → Finset (Fin n)) (w : ℕ) : Finset (Fin n) :=
  if S w ⊆ N then S w else if (S w ∩ I).Nonempty then S w ∩ I else {d}

lemma boundaryProxy_eq_or_raw {n : ℕ} (N I : Finset (Fin n)) (d : Fin n)
    (S : ℕ → Finset (Fin n)) (w : ℕ) :
    boundaryProxy N I d S w = w ∨ boundaryProxy N I d S w < n := by
  by_cases h : S w ⊆ N
  · exact Or.inl (by simp [boundaryProxy,h])
  · right
    simp only [boundaryProxy,ite_eq_right h]
    exact (pickOr (S w ∩ I) d).isLt

lemma boundarySupport_subset {n : ℕ} (N I : Finset (Fin n)) (d : Fin n)
    (S : ℕ → Finset (Fin n)) (hI : I ⊆ N) (hd : d ∈ I) (w : ℕ) :
    boundarySupport N I d S w ⊆ N := by
  unfold boundarySupport
  split_ifs with hgood hnonempty
  · exact hgood
  · exact (Finset.inter_subset_right).trans hI
  · intro v hv
    have hvd : v = d := Finset.mem_singleton.mp hv
    subst v
    exact hI hd

lemma boundarySupport_covers {n : ℕ} (N I : Finset (Fin n)) (d : Fin n)
    (S : ℕ → Finset (Fin n)) (w : ℕ) :
    S w ∩ I ⊆ boundarySupport N I d S w := by
  unfold boundarySupport
  split_ifs with hgood hnonempty
  · exact Finset.inter_subset_left
  · exact Finset.Subset.refl _
  · intro v hv
    exact False.elim (hnonempty ⟨v,hv⟩)

lemma boundaryProxy_back {n : ℕ} (C : Circuit) (J : Finset ℕ)
    (N I : Finset (Fin n)) (d : Fin n) (S : ℕ → Finset (Fin n))
    (hAO : IsAO2 n C) (hreal : ∀ j ∈ J, j < C.gates.length) :
    ∀ j ∈ J, ∀ w ∈ (gateAt C j).inputs,
      rewire n J (boundaryProxy N I d S) w < n+j := by
  intro j hj w hw
  have hbound := hAO.2.1 j (hreal j hj) w hw
  unfold rewire
  split_ifs with hI
  · exact hbound
  · rcases boundaryProxy_eq_or_raw N I d S w with heq | hraw
    · rw [heq]
      exact hbound
    · omega

lemma boundaryProxy_protected {n : ℕ} (C : Circuit) (J E : Finset ℕ)
    (N I : Finset (Fin n)) (d : Fin n) (S : ℕ → Finset (Fin n))
    (hE : ∀ j ∈ J, ∀ w ∈ (gateAt C j).inputs, ¬ internal n J w → n ≤ w → w-n ∈ E) :
    ∀ j ∈ J, ∀ w ∈ (gateAt C j).inputs, ¬ internal n J w →
      n ≤ boundaryProxy N I d S w → boundaryProxy N I d S w-n ∈ E := by
  intro j hj w hw hwI hn
  rcases boundaryProxy_eq_or_raw N I d S w with heq | hraw
  · rw [heq] at hn ⊢
    exact hE j hj w hw hwI hn
  · omega

lemma boundaryProxy_value {n : ℕ} (C : Circuit)
    (N I : Finset (Fin n)) (d : Fin n) (S : ℕ → Finset (Fin n))
    (w : ℕ) (hprotected : S w ⊆ N ∨ (S w ∩ I).card ≤ 1)
    (hraw : ∀ x : Fin n → Bool, val C (List.ofFn x) w = rawOr (S w) x)
    (x : Fin n → Bool) :
    val C (List.ofFn x) (boundaryProxy N I d S w) =
      rawOr (boundarySupport N I d S w) x := by
  by_cases hgood : S w ⊆ N
  · simp only [boundaryProxy,boundarySupport,ite_eq_left hgood]
    exact hraw x
  · have hsmall : (S w ∩ I).card ≤ 1 := hprotected.resolve_left hgood
    simp only [boundaryProxy,boundarySupport,ite_eq_right hgood]
    by_cases hnonempty : (S w ∩ I).Nonempty
    · rw [ite_eq_left hnonempty, val_ofFn C x (pickOr (S w ∩ I) d)]
      have hpick := pickOr_mem (S w ∩ I) d hnonempty
      have heq : S w ∩ I = {pickOr (S w ∩ I) d} := by
        ext v
        simp only [Finset.mem_singleton]
        constructor
        · intro hv
          exact Finset.card_le_one.mp hsmall v hv _ hpick
        · intro hv
          simpa [hv] using hpick
      conv_rhs => rw [heq]
      simp [rawOr]
    · rw [ite_eq_right hnonempty]
      simp only [pickOr,dite_eq_right hnonempty]
      rw [val_ofFn C x d]
      simp [rawOr]

lemma projection_contradiction_of_boundaries {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hL : IsLeastAO G C)
    (hOne : ∀ D : Circuit, IsLeastAO G D → (junk G D).card ≠ 1)
    (hTwo : (junk G C).card = 2) (g h r : ℕ) (center d : Fin n)
    (hgJ : g ∈ junk G C) (hhJ : h ∈ junk G C)
    (J E A : Finset ℕ) (S : ℕ → Finset (Fin n)) (I : Finset (Fin n))
    (hd : d ∈ I) (hI : ∀ i ∈ I, G.Adj center i)
    (hbefore : ∀ j ∈ J, j < g) (hr : r ∈ J)
    (hEdis : Disjoint E J)
    (hEclosed : ∀ j ∈ E, ∀ w ∈ (gateAt C j).inputs, n ≤ w → w-n ∈ E)
    (hEboundary : ∀ j ∈ J, ∀ w ∈ (gateAt C j).inputs, ¬ internal n J w →
      n ≤ w → w-n ∈ E)
    (hBoundaryProtected : ∀ j ∈ J, ∀ w ∈ (gateAt C j).inputs, ¬ internal n J w →
      (∀ v ∈ S w, G.Adj center v) ∨ (S w ∩ I).card ≤ 1)
    (hBoundaryRaw : ∀ j ∈ J, ∀ w ∈ (gateAt C j).inputs, ¬ internal n J w →
      ∀ x : Fin n → Bool, val C (List.ofFn x) w = rawOr (S w) x)
    (hS : ∀ j ∈ J, ∀ a b, (gateAt C j).inputs = [a,b] → S (n+j) = S a ∪ S b)
    (hIroot : I ⊆ S (n+r))
    (hprivate : ∀ i ∈ J, ∀ j < C.gates.length,
      n+i ∈ (gateAt C j).inputs → j ∈ J ∨ j = g)
    (hout : ¬ internal n J C.output)
    (hCritical : ∀ u v, G.Adj u v → circuitFun n (cut C g) (pairInput u v) = false →
      pairInput u v center = true ∧ ∃ i ∈ I, pairInput u v i = true)
    (hhA : h ∈ A)
    (hAclean : ∀ j ∈ A, j ∉ J ∧ j ≠ g)
    (hAclosed : ∀ j ∈ A, ∀ w ∈ (gateAt C j).inputs, n ≤ w → w-n ∈ A) : False := by
  let N : Finset (Fin n) := Finset.univ.filter (fun v => G.Adj center v)
  let proxy := boundaryProxy N I d S
  let boundary := boundarySupport N I d S
  have hg : g < C.gates.length := (mem_junk_iff G C g).mp hgJ |>.1
  have hreal : ∀ j ∈ J, j < C.gates.length := fun j hj => lt_trans (hbefore j hj) hg
  have hIN : I ⊆ N := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hI i hi⟩
  apply projection_contradiction G C hL hOne hTwo g h r center hgJ hhJ J E A proxy boundary S I
    hbefore hr (boundaryProxy_back C J N I d S hL.1 hreal) hEdis hEclosed
    (boundaryProxy_protected C J E N I d S hEboundary) _ _
    (boundarySupport_covers N I d S) hS hIroot hprivate hout hCritical hhA hAclean hAclosed
  · intro j hj w hw hwI x
    apply boundaryProxy_value C N I d S w _ (hBoundaryRaw j hj w hw hwI) x
    rcases hBoundaryProtected j hj w hw hwI with hgood | hsmall
    · left
      intro v hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hgood v hv⟩
    · exact Or.inr hsmall
  · intro w v hv
    have hvN := boundarySupport_subset N I d S hIN hd w hv
    exact (Finset.mem_filter.mp hvN).2

end PEqualNP.Outside.L_meta_5012.OrProjection

namespace PEqualNP.Outside.L_meta_5012

namespace Colors

open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm
  PEqualNP.Outside.L_meta_5012.IndependentDescent

lemma safe_triple {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P Q : Finset (Fin n)) {w : Fin n} (hs : Safe G P Q w)
    {p q : Fin n} (hp : p ∈ P) (hq : q ∈ Q) :
    G.Adj p q ∨ G.Adj p w ∨ G.Adj q w := by
  let x : Fin n → Bool := fun v => decide (v = p ∨ v = q ∨ v = w)
  have hprod : product P Q x = true :=
    (product_true P Q x).mpr ⟨⟨p, hp, by simp [x]⟩, q, hq, by simp [x]⟩
  have hF := hs x hprod (by simp [x])
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, x] at hF
  obtain ⟨a, b, hab, ha, hb⟩ := hF
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  · exact (G.irrefl hab).elim
  · exact Or.inl hab
  · exact Or.inr (Or.inl hab)
  · exact Or.inl hab.symm
  · exact (G.irrefl hab).elim
  · exact Or.inr (Or.inr hab)
  · exact Or.inr (Or.inl hab.symm)
  · exact Or.inr (Or.inr hab.symm)
  · exact (G.irrefl hab).elim

lemma safe_bad_adjacent {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P Q : Finset (Fin n)) {w : Fin n} (hs : Safe G P Q w)
    {p q : Fin n} (hp : p ∈ P) (hq : q ∈ Q)
    (hpw : ¬ G.Adj p w) (hqw : ¬ G.Adj q w) : G.Adj p q := by
  rcases safe_triple G P Q hs hp hq with hpq | hpw' | hqw'
  · exact hpq
  · exact (hpw hpw').elim
  · exact (hqw hqw').elim

lemma bool_eq_of_common_ne {a b c : Bool} (ha : a ≠ c) (hb : b ≠ c) : a = b := by
  cases a <;> cases b <;> cases c <;> simp_all

lemma safe_bad_colors {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (P Q : Finset (Fin n)) {w p0 q0 : Fin n} (hs : Safe G P Q w)
    (hp0 : p0 ∈ P) (hq0 : q0 ∈ Q) (hpw : ¬ G.Adj p0 w) (hqw : ¬ G.Adj q0 w) :
    G.Adj p0 q0 ∧
      (∀ p ∈ P, ¬ G.Adj p w → s p = s p0) ∧
      (∀ q ∈ Q, ¬ G.Adj q w → s q = s q0) := by
  have hpq := safe_bad_adjacent G P Q hs hp0 hq0 hpw hqw
  refine ⟨hpq, ?_, ?_⟩
  · intro p hp hnp
    have hadj := safe_bad_adjacent G P Q hs hp hq0 hnp hqw
    exact bool_eq_of_common_ne (hbip p q0 hadj) (hbip p0 q0 hpq)
  · intro q hq hnq
    have hadj := safe_bad_adjacent G P Q hs hp0 hq hpw hnq
    exact bool_eq_of_common_ne (Ne.symm (hbip p0 q hadj)) (Ne.symm (hbip p0 q0 hpq))

lemma safe_oriented_bad_factors {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (P Q : Finset (Fin n)) {w p0 q0 : Fin n} (hs : Safe G P Q w)
    (hp0 : p0 ∈ P) (hq0 : q0 ∈ Q) (hpw : ¬ G.Adj p0 w) (hqw : ¬ G.Adj q0 w) :
    ((∀ p ∈ P, ¬ G.Adj p w → s p = s w) ∧ (∀ q ∈ Q, s q ≠ s w)) ∨
      ((∀ q ∈ Q, ¬ G.Adj q w → s q = s w) ∧ (∀ p ∈ P, s p ≠ s w)) := by
  obtain ⟨hpq, hP, hQ⟩ := safe_bad_colors G s hbip P Q hs hp0 hq0 hpw hqw
  have hpqColor := hbip p0 q0 hpq
  by_cases hpColor : s p0 = s w
  · left
    constructor
    · intro p hp hn
      exact (hP p hp hn).trans hpColor
    · intro q hq hqwColor
      have hnq : ¬ G.Adj q w := fun hadj => hbip q w hadj hqwColor
      have hqColor := hQ q hq hnq
      exact hpqColor (hpColor.trans (hqwColor.symm.trans hqColor))
  · right
    have hqColor : s q0 = s w :=
      bool_eq_of_common_ne (Ne.symm hpqColor) (Ne.symm hpColor)
    constructor
    · intro q hq hn
      exact (hQ q hq hn).trans hqColor
    · intro p hp hpwColor
      have hnp : ¬ G.Adj p w := fun hadj => hbip p w hadj hpwColor
      have hpColor' := hP p hp hnp
      exact hpqColor (hpColor'.symm.trans (hpwColor.trans hqColor.symm))

end Colors

namespace Sharing

open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm
  PEqualNP.Outside.L_meta_5012.IndependentDescent
  PEqualNP.Outside.L_meta_5012.Colors

lemma safe_swap {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P Q : Finset (Fin n)) {w : Fin n} (hs : Safe G P Q w) : Safe G Q P w := by
  intro x hx hxw
  apply hs x _ hxw
  simpa only [product, Bool.and_comm] using hx

lemma common_neighbor_unique {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (I : Finset (Fin n)) (hI : 2 ≤ I.card)
    {w z : Fin n} (hw : ∀ i ∈ I, G.Adj w i) (hz : ∀ i ∈ I, G.Adj z i) : z = w := by
  by_contra hne
  have hsub : I ⊆ Finset.univ.filter fun i => G.Adj z i ∧ G.Adj w i := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz i hi, hw i hi⟩
  have hc := (Finset.card_le_card hsub).trans (h4 z w hne)
  omega

lemma shared_mixed_forces_same_center {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G) (I T R S : Finset (Fin n)) (hI : 2 ≤ I.card)
    {w z p : Fin n} (hIw : ∀ i ∈ I, G.Adj w i) (hIT : I ⊆ T) (hTR : T ⊆ R)
    (hpT : p ∈ T) (hpColor : s p = s w) (hzColor : s z = s w)
    (hSafe : Safe G R S z) (hBad : ∃ q ∈ S, ¬ G.Adj q z) : z = w := by
  obtain ⟨q, hqS, hqBad⟩ := hBad
  have hpBad : ¬ G.Adj p z := by
    intro hpz
    exact hbip p z hpz (hpColor.trans hzColor.symm)
  have hpq := safe_bad_adjacent G R S hSafe (hTR hpT) hqS hpBad hqBad
  have hqColor : s q ≠ s w := by
    intro he
    exact hbip p q hpq (hpColor.trans he.symm)
  apply common_neighbor_unique G h4 I hI hIw
  intro i hi
  have hiColor : s i ≠ s w := Ne.symm (hbip w i (hIw i hi))
  have hiq : s i = s q := bool_eq_of_common_ne hiColor hqColor
  rcases safe_triple G R S hSafe (hTR (hIT hi)) hqS with hiqAdj | hizAdj | hqzAdj
  · exact False.elim (hbip i q hiqAdj hiq)
  · exact hizAdj.symm
  · exact False.elim (hqBad hqzAdj)

lemma shared_mono_forces_neighbors {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G) (I T R S : Finset (Fin n)) (hI : 2 ≤ I.card)
    {w z : Fin n} (hIw : ∀ i ∈ I, G.Adj w i) (hIT : I ⊆ T) (hTR : T ⊆ R)
    (hColor : ∀ t ∈ T, s t = s z) (hSafe : Safe G R S z)
    (hBad : ∃ q ∈ S, ¬ G.Adj q z) : ∀ t ∈ T, G.Adj w t := by
  obtain ⟨q, hqS, hqBad⟩ := hBad
  have hqt : ∀ t ∈ T, G.Adj q t := by
    intro t ht
    have htBad : ¬ G.Adj t z := fun htz => hbip t z htz (hColor t ht)
    exact (safe_bad_adjacent G R S hSafe (hTR ht) hqS htBad hqBad).symm
  have hqw : q = w := common_neighbor_unique G h4 I hI hIw (fun i hi => hqt i (hIT hi))
  simpa only [hqw] using hqt

lemma mixed_shared_subset_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G) (I T R S : Finset (Fin n)) {w z : Fin n}
    (hIw : ∀ i ∈ I, G.Adj w i) (hzColor : s z = s w) (hzw : z ≠ w)
    (hColor : ∀ t ∈ T, ¬ G.Adj t w → s t = s w)
    (hSafe : Safe G R S z) (hRBad : ∃ p ∈ R, ¬ G.Adj p z)
    (hSBad : ∃ q ∈ S, ¬ G.Adj q z) (hShared : T ⊆ R ∨ T ⊆ S) :
    (∀ t ∈ T, G.Adj w t) ∨ (T ∩ I).card ≤ 1 := by
  classical
  by_cases hGood : ∀ t ∈ T, G.Adj w t
  · exact Or.inl hGood
  · right
    by_contra hCard
    have hI : 2 ≤ (T ∩ I).card := by omega
    push Not at hGood
    obtain ⟨p, hpT, hpBad⟩ := hGood
    have hpBad' : ¬ G.Adj p w := fun hpw => hpBad hpw.symm
    have hpColor := hColor p hpT hpBad'
    have hIntw : ∀ i ∈ T ∩ I, G.Adj w i := fun i hi => hIw i (Finset.mem_inter.mp hi).2
    rcases hShared with hTR | hTS
    · exact hzw (shared_mixed_forces_same_center G s hbip h4 (T ∩ I) T R S hI
        hIntw Finset.inter_subset_left hTR hpT hpColor hzColor hSafe hSBad)
    · exact hzw (shared_mixed_forces_same_center G s hbip h4 (T ∩ I) T S R hI
        hIntw Finset.inter_subset_left hTS hpT hpColor hzColor (safe_swap G R S hSafe) hRBad)

lemma mono_shared_subset_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G) (I T R S : Finset (Fin n)) {w z : Fin n}
    (hIw : ∀ i ∈ I, G.Adj w i) (hzColor : s z ≠ s w)
    (hColor : ∀ t ∈ T, s t ≠ s w)
    (hSafe : Safe G R S z) (hRBad : ∃ p ∈ R, ¬ G.Adj p z)
    (hSBad : ∃ q ∈ S, ¬ G.Adj q z) (hShared : T ⊆ R ∨ T ⊆ S) :
    (∀ t ∈ T, G.Adj w t) ∨ (T ∩ I).card ≤ 1 := by
  classical
  by_cases hCard : (T ∩ I).card ≤ 1
  · exact Or.inr hCard
  · left
    have hI : 2 ≤ (T ∩ I).card := by omega
    have hColor' : ∀ t ∈ T, s t = s z := fun t ht => bool_eq_of_common_ne (hColor t ht) hzColor
    have hIntw : ∀ i ∈ T ∩ I, G.Adj w i := fun i hi => hIw i (Finset.mem_inter.mp hi).2
    rcases hShared with hTR | hTS
    · exact shared_mono_forces_neighbors G s hbip h4 (T ∩ I) T R S hI hIntw
        Finset.inter_subset_left hTR hColor' hSafe hSBad
    · exact shared_mono_forces_neighbors G s hbip h4 (T ∩ I) T S R hI hIntw
        Finset.inter_subset_left hTS hColor' (safe_swap G R S hSafe) hRBad

lemma distinct_safe_centers_protected_factor {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G) (P Q R S : Finset (Fin n)) {w z : Fin n}
    (hSafe : Safe G P Q w) (hSafe' : Safe G R S z) (hzw : z ≠ w)
    (hPBad : ∃ p ∈ P, ¬ G.Adj p w) (hQBad : ∃ q ∈ Q, ¬ G.Adj q w)
    (hRBad : ∃ p ∈ R, ¬ G.Adj p z) (hSBad : ∃ q ∈ S, ¬ G.Adj q z) :
    ∃ U : Finset (Fin n), (U = P ∨ U = Q) ∧ ∀ T ⊆ U, (T ⊆ R ∨ T ⊆ S) →
      (∀ t ∈ T, G.Adj w t) ∨ (T ∩ (P ∩ Q)).card ≤ 1 := by
  obtain ⟨p, hp, hpBad⟩ := hPBad
  obtain ⟨q, hq, hqBad⟩ := hQBad
  have hIw : ∀ i ∈ P ∩ Q, G.Adj w i :=
    fun _ hi => OverlapCase.safe_adj_overlap G P Q hSafe hi
  rcases safe_oriented_bad_factors G s hbip P Q hSafe hp hq hpBad hqBad with hPQ | hQP
  · by_cases hzColor : s z = s w
    · refine ⟨P, Or.inl rfl, ?_⟩
      intro T hTP hShared
      exact mixed_shared_subset_bound G s hbip h4 (P ∩ Q) T R S hIw hzColor hzw
        (fun t ht hBad => hPQ.1 t (hTP ht) hBad) hSafe' hRBad hSBad hShared
    · refine ⟨Q, Or.inr rfl, ?_⟩
      intro T hTQ hShared
      exact mono_shared_subset_bound G s hbip h4 (P ∩ Q) T R S hIw hzColor
        (fun t ht => hPQ.2 t (hTQ ht)) hSafe' hRBad hSBad hShared
  · by_cases hzColor : s z = s w
    · refine ⟨Q, Or.inr rfl, ?_⟩
      intro T hTQ hShared
      exact mixed_shared_subset_bound G s hbip h4 (P ∩ Q) T R S hIw hzColor hzw
        (fun t ht hBad => hQP.1 t (hTQ ht) hBad) hSafe' hRBad hSBad hShared
    · refine ⟨P, Or.inl rfl, ?_⟩
      intro T hTP hShared
      exact mono_shared_subset_bound G s hbip h4 (P ∩ Q) T R S hIw hzColor
        (fun t ht => hQP.2 t (hTP ht)) hSafe' hRBad hSBad hShared

end Sharing

end PEqualNP.Outside.L_meta_5012

namespace PEqualNP.Outside.L_meta_5012.PrivateRegion

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo

def overlap (n : ℕ) (C : Circuit) (g : ℕ) : Finset (Fin n) :=
  side (n := n) C g 0 ∩ side (n := n) C g 1

def Bad {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n)
    (I T : Finset (Fin n)) : Prop :=
  (¬ ∀ t ∈ T, G.Adj w t) ∧ 2 ≤ (T ∩ I).card

noncomputable def nodes {n : ℕ} (G : SimpleGraph (Fin n))
    (C : Circuit) (g : ℕ) (b : Fin 2) (w : Fin n) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter fun q =>
    (gateAt C q).op = GateOp.or ∧ OrReaches n C (opnd C g b) q ∧
      Bad G w (overlap n C g) (orIn n C (n+q))

lemma mem_nodes {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (g : ℕ) (b : Fin 2) (w : Fin n) (q : ℕ) :
    q ∈ nodes G C g b w ↔ q < C.gates.length ∧
      (gateAt C q).op = GateOp.or ∧ OrReaches n C (opnd C g b) q ∧
        Bad G w (overlap n C g) (orIn n C (n+q)) := by
  classical
  simp only [nodes, Finset.mem_filter, Finset.mem_range]

lemma bad_mono {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n)
    (I S T : Finset (Fin n)) (hST : S ⊆ T) (hBad : Bad G w I S) : Bad G w I T := by
  refine ⟨fun hGood => hBad.1 (fun t ht => hGood t (hST ht)), ?_⟩
  have hSub : S ∩ I ⊆ T ∩ I := by
    intro t ht
    exact Finset.mem_inter.mpr ⟨hST (Finset.mem_inter.mp ht).1, (Finset.mem_inter.mp ht).2⟩
  exact hBad.2.trans (Finset.card_le_card hSub)

lemma bad_excludes_protected {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n)
    (I T : Finset (Fin n)) (hBad : Bad G w I T)
    (hProtect : (∀ t ∈ T, G.Adj w t) ∨ (T ∩ I).card ≤ 1) : False := by
  rcases hProtect with hGood | hSmall
  · exact hBad.1 hGood
  · have := hBad.2
    omega

lemma nodes_before_junk {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (hAO : IsAO2 n C) {g : ℕ} (hg : g < C.gates.length) (b : Fin 2) (w : Fin n)
    {q : ℕ} (hq : q ∈ nodes G C g b w) : q < g := by
  have hr := ((mem_nodes G C g b w q).mp hq).2.2.1
  have hle := Critical.Base.orStep_le (Critical.Base.orReaches_reach q _ hr).1
  have hback := Lift.opnd_lt hAO hg b
  omega

lemma bad_terminal_is_chosen {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hTF : TopForm G C)
    {g h : ℕ} (hJ : junk G C = {g,h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (b : Fin 2) (w : Fin n) (hW : wmax G C g = {w}) (h4 : NoFourCycle G)
    (hOtherOverlap : (overlap n C h).Nonempty)
    (hIw : ∀ i ∈ overlap n C g, G.Adj w i)
    (hProtected : ∀ T ⊆ side (n := n) C g b,
      (T ⊆ side (n := n) C h 0 ∨ T ⊆ side (n := n) C h 1) →
      (∀ t ∈ T, G.Adj w t) ∨ (T ∩ overlap n C g).card ≤ 1)
    (T : Finset (Fin n)) (hT : T ⊆ side (n := n) C g b)
    (hBad : Bad G w (overlap n C g) T)
    {a : ℕ} (ha : a < C.gates.length) (haAnd : (gateAt C a).op = GateOp.and)
    (c : Fin 2) (hTa : T ⊆ side (n := n) C a c) : a = g ∧ c = b := by
  classical
  by_cases hag : a = g
  · subst a
    refine ⟨rfl, ?_⟩
    rcases Critical.Base.eitherOperand b c with hcb | hcb
    · exact hcb
    · exfalso
      apply hBad.1
      intro t ht
      apply hIw
      have ht0 := hT ht
      have ht1 := hTa ht
      rw [hcb] at ht1
      fin_cases b
      · exact Finset.mem_inter.mpr ⟨ht0, ht1⟩
      · exact Finset.mem_inter.mpr ⟨ht1, ht0⟩
  · by_cases hah : a = h
    · subst a
      have hShared : T ⊆ side (n := n) C h 0 ∨ T ⊆ side (n := n) C h 1 := by
        fin_cases c
        · exact Or.inl hTa
        · exact Or.inr hTa
      exact (bad_excludes_protected G w _ T hBad (hProtected T hT hShared)).elim
    · have hNotJ : a ∉ junk G C := by
        intro haJ
        exact (Critical.Base.memJunkPair hJ haJ).elim hag hah
      have hBelow : BelowF G C a := by
        intro x hx
        by_contra hf
        exact hNotJ (CleanReplacement.mem_junk.mpr
          ⟨ha, haAnd, ha, x, hx, Bool.eq_false_iff.mpr hf⟩)
      have haTop : a ∈ tops G C := by
        simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using
          And.intro ha (And.intro haAnd hBelow)
      have hProtect := OverlapCase.top_raw_boundary_protected G C hAO hTF hJ hgh hhg
        hW h4 hOtherOverlap (overlap n C g) T hIw haTop c hTa
      exact (bad_excludes_protected G w _ T hBad hProtect).elim

lemma private_readers {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hTF : TopForm G C)
    {g h : ℕ} (hJ : junk G C = {g,h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (b : Fin 2) (w : Fin n) (hW : wmax G C g = {w}) (h4 : NoFourCycle G)
    (hOtherOverlap : (overlap n C h).Nonempty)
    (hIw : ∀ i ∈ overlap n C g, G.Adj w i)
    (hProtected : ∀ T ⊆ side (n := n) C g b,
      (T ⊆ side (n := n) C h 0 ∨ T ⊆ side (n := n) C h 1) →
      (∀ t ∈ T, G.Adj w t) ∨ (T ∩ overlap n C g).card ≤ 1) :
    ∀ q ∈ nodes G C g b w, ∀ r < C.gates.length,
      n + q ∈ (gateAt C r).inputs → r ∈ nodes G C g b w ∨ r = g := by
  intro q hq r hr hread
  obtain ⟨hqLen, _, hqReach, hqBad⟩ := (mem_nodes G C g b w q).mp hq
  let T := orIn n C (n+q)
  have hT : T ⊆ side (n := n) C g b :=
    Critical.Base.orInTrans (Critical.Base.orReaches_reach q _ hqReach).1
  have hNoOutput (hp : Relation.ReflTransGen (Critical.Base.OrStep n C) C.output (n+q)) : False := by
    have hCard : 2 ≤ (T ∩ overlap n C g).card := hqBad.2
    obtain ⟨i, hi⟩ := Finset.card_pos.mp (by omega : 0 < (T ∩ overlap n C g).card)
    have hiOut := Critical.Base.orInTrans hp (Finset.mem_inter.mp hi).1
    rw [OverlapCase.output_raw_frontier_empty G C hL.2.1] at hiOut
    exact Finset.notMem_empty i hiOut
  rcases hL.1.1 _ (Lift.gateAt_mem hr) with hrAnd | hrOr
  · obtain ⟨c, hc⟩ := Critical.Base.inputsAsOpnd hL.1 hr hread
    have hTa : T ⊆ side (n := n) C r c := by
      change orIn n C (n+q) ⊆ orIn n C (opnd C r c)
      rw [← hc]
    exact Or.inr (bad_terminal_is_chosen G C hL.1 hTF hJ hgh hhg b w hW h4
      hOtherOverlap hIw hProtected T hT hqBad hr hrAnd c hTa).1
  · have hStep : Critical.Base.OrStep n C (n+r) (n+q) :=
      ⟨r, hr, rfl, hrOr, hread, hL.1.2.1 r hr _ hread⟩
    have hQR : T ⊆ orIn n C (n+r) :=
      Critical.Base.orInTrans (Relation.ReflTransGen.single hStep)
    have hrBad := bad_mono G w (overlap n C g) T _ hQR hqBad
    have hrReach : OrReaches n C (opnd C g b) r := by
      rcases OrFrontier.least_or_frontier G C hL r hr with hpOut | ⟨a, c, ha, haAnd, hp⟩
      · exact (hNoOutput (hpOut.tail hStep)).elim
      · have hTa : T ⊆ side (n := n) C a c := Critical.Base.orInTrans (hp.tail hStep)
        obtain ⟨hag, hcb⟩ := bad_terminal_is_chosen G C hL.1 hTF hJ hgh hhg b w hW h4
          hOtherOverlap hIw hProtected T hT hqBad ha haAnd c hTa
        subst a
        subst c
        exact Critical.Base.reach_orReaches hp r rfl hr
    exact Or.inl ((mem_nodes G C g b w r).mpr ⟨hr, hrOr, hrReach, hrBad⟩)

lemma or_of_operand_path {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hTF : TopForm G C)
    {g h : ℕ} (hJ : junk G C = {g,h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (b : Fin 2) {q : ℕ} (hq : q < C.gates.length)
    (hp : Relation.ReflTransGen (Critical.Base.OrStep n C) (opnd C g b) (n+q)) :
    (gateAt C q).op = GateOp.or := by
  rcases hAO.1 _ (Lift.gateAt_mem hq) with hAnd | hOr
  · have hgJ : g ∈ junk G C := by rw [hJ]; simp
    obtain ⟨hg, hgAnd⟩ := RawOperands.junk_data G C g hgJ
    have hReach := Critical.Base.reach_orReaches hp q rfl hq
    have hqJ := Critical.Base.operandOrAndJunk hAO hTF hg hgAnd hReach hAnd
    have hCone := Critical.Base.operandReachCone hAO hg hReach
    exact (RawOperands.independent_no_junk_ancestors G C g h hJ hgh hhg g
      (Or.inl rfl) q hqJ hCone).elim
  · exact hOr

lemma raw_of_operand_path {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hTF : TopForm G C)
    {g h : ℕ} (hJ : junk G C = {g,h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (b : Fin 2) (u : ℕ)
    (hp : Relation.ReflTransGen (Critical.Base.OrStep n C) (opnd C g b) u)
    (x : Fin n → Bool) :
    wval C x u = decide (∃ i ∈ orIn n C u, x i = true) := by
  have hForward : wval C x u = true → ∃ i ∈ orIn n C u, x i = true := by
    intro hu
    rcases RawOperands.down n C x (fun q hq => hAO.1 _ (Lift.gateAt_mem hq)) u hu with
      hRaw | ⟨q, hq, hReach, hAnd, _⟩
    · exact hRaw
    · have hOr := or_of_operand_path G C hAO hTF hJ hgh hhg b hq
        (hp.trans (Critical.Base.orReaches_reach q _ hReach).1)
      rw [hOr] at hAnd
      cases hAnd
  have hBackward : (∃ i ∈ orIn n C u, x i = true) → wval C x u = true := by
    rintro ⟨i, hi, hxi⟩
    exact Critical.Base.reach_var_val x u i (Critical.Base.mem_orIn_reach i hi) hxi
  by_cases hu : wval C x u = true
  · simp [hu, hForward hu]
  · have hn : ¬ ∃ i ∈ orIn n C u, x i = true := fun hh => hu (hBackward hh)
    simp [Bool.eq_false_iff.mpr hu, hn]

lemma input_raw_card {n : ℕ} (C : Circuit) (u : ℕ) (hu : u < n) :
    (orIn n C u).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi t ht
  have hiu : i.val = u := by
    rcases (RawOperands.orIn_mem n C u i).mp hi with hh | ⟨q, _, hReach, _, _⟩
    · exact hh
    · have := hReach.1
      omega
  have htu : t.val = u := by
    rcases (RawOperands.orIn_mem n C u t).mp ht with hh | ⟨q, _, hReach, _, _⟩
    · exact hh
    · have := hReach.1
      omega
  exact Fin.ext (hiu.trans htu.symm)

lemma node_input_path {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (hAO : IsAO2 n C) (g : ℕ) (b : Fin 2) (w : Fin n)
    {q u : ℕ} (hq : q ∈ nodes G C g b w) (hu : u ∈ (gateAt C q).inputs) :
    Relation.ReflTransGen (Critical.Base.OrStep n C) (opnd C g b) u := by
  obtain ⟨hqLen, hqOr, hqReach, _⟩ := (mem_nodes G C g b w q).mp hq
  exact ((Critical.Base.orReaches_reach q _ hqReach).1).tail
    ⟨q, hqLen, rfl, hqOr, hu, hAO.2.1 q hqLen u hu⟩

lemma boundary_protected {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hTF : TopForm G C)
    {g h : ℕ} (hJ : junk G C = {g,h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (b : Fin 2) (w : Fin n) {q u : ℕ}
    (hq : q ∈ nodes G C g b w) (hu : u ∈ (gateAt C q).inputs)
    (hExternal : ¬ (n ≤ u ∧ u - n ∈ nodes G C g b w)) :
    (∀ i ∈ orIn n C u, G.Adj w i) ∨ (orIn n C u ∩ overlap n C g).card ≤ 1 := by
  by_cases hun : u < n
  · exact Or.inr ((Finset.card_le_card Finset.inter_subset_left).trans (input_raw_card C u hun))
  · have hnu : n ≤ u := by omega
    have hqLen := ((mem_nodes G C g b w q).mp hq).1
    have hub := hAO.2.1 q hqLen u hu
    have huLen : u - n < C.gates.length := by omega
    have hRep : n + (u - n) = u := by omega
    have hp := node_input_path G C hAO g b w hq hu
    have huOr := or_of_operand_path G C hAO hTF hJ hgh hhg b huLen (by rwa [hRep])
    have huReach := Critical.Base.reach_orReaches hp (u-n) hRep.symm huLen
    by_cases hGood : ∀ i ∈ orIn n C u, G.Adj w i
    · exact Or.inl hGood
    · right
      by_contra hSmall
      have hBad : Bad G w (overlap n C g) (orIn n C (n+(u-n))) := by
        rw [hRep]
        exact ⟨hGood, by omega⟩
      exact hExternal ⟨hnu, (mem_nodes G C g b w (u-n)).mpr ⟨huLen, huOr, huReach, hBad⟩⟩

lemma root_mem_nodes {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hTF : TopForm G C)
    {g h : ℕ} (hJ : junk G C = {g,h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (b : Fin 2) (w : Fin n) (hI : 2 ≤ (overlap n C g).card)
    (hBad : ¬ ∀ t ∈ side (n := n) C g b, G.Adj w t) :
    ∃ q ∈ nodes G C g b w, opnd C g b = n + q := by
  have hgJ : g ∈ junk G C := by rw [hJ]; simp
  have hg := (RawOperands.junk_data G C g hgJ).1
  have hIu : overlap n C g ⊆ side (n := n) C g b := by
    fin_cases b
    · exact Finset.inter_subset_left
    · exact Finset.inter_subset_right
  have hCard : 2 ≤ (side (n := n) C g b).card := hI.trans (Finset.card_le_card hIu)
  have hun : n ≤ opnd C g b := by
    by_contra hn
    have hc := input_raw_card (n := n) C (opnd C g b) (by omega)
    change (side (n := n) C g b).card ≤ 1 at hc
    omega
  have hRep : opnd C g b = n + (opnd C g b - n) := by omega
  have huBack := Lift.opnd_lt hAO hg b
  have hq : opnd C g b - n < C.gates.length := by omega
  have hp : Relation.ReflTransGen (Critical.Base.OrStep n C)
      (opnd C g b) (n + (opnd C g b - n)) := by rw [← hRep]
  have hOr := or_of_operand_path G C hAO hTF hJ hgh hhg b hq hp
  have hReach := Critical.Base.reach_orReaches hp (opnd C g b - n) rfl hq
  have hBad' : Bad G w (overlap n C g) (orIn n C (n + (opnd C g b - n))) := by
    rw [← hRep]
    refine ⟨hBad, ?_⟩
    change 2 ≤ (side (n := n) C g b ∩ overlap n C g).card
    rw [Finset.inter_eq_right.mpr hIu]
    exact hI
  exact ⟨_, (mem_nodes G C g b w _).mpr ⟨hq, hOr, hReach, hBad'⟩, hRep⟩

end PEqualNP.Outside.L_meta_5012.PrivateRegion

namespace PEqualNP.Outside.L_meta_5012.PrivateRegion

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo

noncomputable def protectedNodes {n : ℕ} (G : SimpleGraph (Fin n))
    (C : Circuit) (g : ℕ) (b : Fin 2) (w : Fin n) : Finset ℕ :=
  Finset.range g \ nodes G C g b w

lemma mem_protectedNodes {n : ℕ} (G : SimpleGraph (Fin n))
    (C : Circuit) (g : ℕ) (b : Fin 2) (w : Fin n) (q : ℕ) :
    q ∈ protectedNodes G C g b w ↔ q < g ∧ q ∉ nodes G C g b w := by
  simp only [protectedNodes, Finset.mem_sdiff, Finset.mem_range]

lemma protected_disjoint {n : ℕ} (G : SimpleGraph (Fin n))
    (C : Circuit) (g : ℕ) (b : Fin 2) (w : Fin n) :
    Disjoint (protectedNodes G C g b w) (nodes G C g b w) := by
  exact Finset.disjoint_left.mpr fun q hq hqJ => ((mem_protectedNodes G C g b w q).mp hq).2 hqJ

lemma protected_closed_of_private {n : ℕ} (G : SimpleGraph (Fin n))
    (C : Circuit) (hAO : IsAO2 n C) (g : ℕ) (hg : g < C.gates.length)
    (b : Fin 2) (w : Fin n)
    (hPrivate : ∀ q ∈ nodes G C g b w, ∀ r < C.gates.length,
      n + q ∈ (gateAt C r).inputs → r ∈ nodes G C g b w ∨ r = g) :
    ∀ q ∈ protectedNodes G C g b w, ∀ u ∈ (gateAt C q).inputs,
      n ≤ u → u - n ∈ protectedNodes G C g b w := by
  intro q hq u hu hnu
  obtain ⟨hqg, hqNot⟩ := (mem_protectedNodes G C g b w q).mp hq
  have hqLen : q < C.gates.length := by omega
  have hub := hAO.2.1 q hqLen u hu
  apply (mem_protectedNodes G C g b w (u-n)).mpr
  refine ⟨by omega, ?_⟩
  intro huJ
  have hRep : n + (u-n) = u := by omega
  rcases hPrivate (u-n) huJ q hqLen (by rwa [hRep]) with hqJ | hqEq
  · exact hqNot hqJ
  · omega

lemma boundary_mem_protected {n : ℕ} (G : SimpleGraph (Fin n))
    (C : Circuit) (hAO : IsAO2 n C) (g : ℕ) (hg : g < C.gates.length)
    (b : Fin 2) (w : Fin n) {q u : ℕ}
    (hq : q ∈ nodes G C g b w) (hu : u ∈ (gateAt C q).inputs)
    (hExternal : ¬ (n ≤ u ∧ u - n ∈ nodes G C g b w)) (hnu : n ≤ u) :
    u - n ∈ protectedNodes G C g b w := by
  have hqLen := ((mem_nodes G C g b w q).mp hq).1
  have hqg := nodes_before_junk G C hAO hg b w hq
  have hub := hAO.2.1 q hqLen u hu
  exact (mem_protectedNodes G C g b w (u-n)).mpr
    ⟨by omega, fun huJ => hExternal ⟨hnu, huJ⟩⟩

lemma nodes_not_output {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hF : circuitFun n C = graphFun G ∅)
    (g : ℕ) (b : Fin 2) (w : Fin n) {q : ℕ} (hq : q ∈ nodes G C g b w) :
    C.output ≠ n + q := by
  intro hOut
  have hBad := ((mem_nodes G C g b w q).mp hq).2.2.2
  have hEmpty := OverlapCase.output_raw_frontier_empty G C hF
  rw [hOut] at hEmpty
  have hCard := hBad.2
  rw [hEmpty] at hCard
  simp at hCard

end PEqualNP.Outside.L_meta_5012.PrivateRegion

namespace PEqualNP.Outside.L_meta_5012.PrivateRegion

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo

lemma distinct_filters_choose_private_factor {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C)
    (hOne : ∀ D : Circuit, IsLeastAO G D → (junk G D).card ≠ 1)
    (hTF : TopForm G C) {g h : ℕ} (hne : g ≠ h) (hJ : junk G C = {g,h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (hNoCommon : ∀ a ∈ tops G C, ∀ b : Fin 2,
      OrReaches n C (opnd C a b) g → ¬ OrReaches n C (opnd C a (1-b)) h)
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G) (w z : Fin n)
    (hW : wmax G C g = {w}) (hZ : wmax G C h = {z}) (hzw : z ≠ w)
    (hI : 2 ≤ (overlap n C g).card) (hH : (overlap n C h).Nonempty) :
    ∃ b : Fin 2,
      (∃ q ∈ nodes G C g b w, opnd C g b = n + q) ∧
      (∀ q ∈ nodes G C g b w, ∀ r < C.gates.length,
        n + q ∈ (gateAt C r).inputs → r ∈ nodes G C g b w ∨ r = g) := by
  classical
  have hJ' : junk G C = {h,g} := by rw [hJ, Finset.pair_comm]
  have hNoCommon' : ∀ a ∈ tops G C, ∀ b : Fin 2,
      OrReaches n C (opnd C a b) h → ¬ OrReaches n C (opnd C a (1-b)) g := by
    intro a ha b hh hg
    have hFlip : 1 - (1 - b) = b := by fin_cases b <;> decide
    exact hNoCommon a ha (1-b) hg (by simpa only [hFlip] using hh)
  have hBadG (b : Fin 2) : ∃ p ∈ side (n := n) C g b, ¬ G.Adj p w := by
    by_contra hn
    push_neg at hn
    exact OverlapCase.no_independent_unique_filter_neighbor_factor G C hL hOne hTF hne hJ
      hgh hhg hNoCommon hW b (fun p hp => (hn p hp).symm)
  have hBadH (b : Fin 2) : ∃ p ∈ side (n := n) C h b, ¬ G.Adj p z := by
    by_contra hn
    push_neg at hn
    exact OverlapCase.no_independent_unique_filter_neighbor_factor G C hL hOne hTF
      (Ne.symm hne) hJ' hhg hgh hNoCommon' hZ b (fun p hp => (hn p hp).symm)
  have hEvalG (x : Fin n → Bool) : gateVal n C g x = IndependentDescent.product
      (side (n := n) C g 0) (side (n := n) C g 1) x :=
    RawOperands.independent_product G C hL.1 hTF g h hJ hgh hhg g (Or.inl rfl) x
  have hEvalH (x : Fin n → Bool) : gateVal n C h x = IndependentDescent.product
      (side (n := n) C h 0) (side (n := n) C h 1) x :=
    RawOperands.independent_product G C hL.1 hTF g h hJ hgh hhg h (Or.inr rfl) x
  have hSafeG := (IndependentDescent.wmax_iff G C g _ _ hEvalG w).mp (by rw [hW]; simp)
  have hSafeH := (IndependentDescent.wmax_iff G C h _ _ hEvalH z).mp (by rw [hZ]; simp)
  have hIw : ∀ i ∈ overlap n C g, G.Adj w i := fun i hi =>
    OverlapCase.safe_adj_overlap G _ _ hSafeG hi
  obtain ⟨U, hU, hProtect⟩ := Sharing.distinct_safe_centers_protected_factor G s hbip h4
    (side (n := n) C g 0) (side (n := n) C g 1)
    (side (n := n) C h 0) (side (n := n) C h 1) hSafeG hSafeH hzw
    (hBadG 0) (hBadG 1) (hBadH 0) (hBadH 1)
  have hFinish (b : Fin 2) (hUb : U = side (n := n) C g b) :
      (∃ q ∈ nodes G C g b w, opnd C g b = n + q) ∧
      (∀ q ∈ nodes G C g b w, ∀ r < C.gates.length,
        n + q ∈ (gateAt C r).inputs → r ∈ nodes G C g b w ∨ r = g) := by
    have hBad : ¬ ∀ t ∈ side (n := n) C g b, G.Adj w t := by
      intro hGood
      obtain ⟨t, ht, htBad⟩ := hBadG b
      exact htBad (hGood t ht).symm
    refine ⟨root_mem_nodes G C hL.1 hTF hJ hgh hhg b w hI hBad, ?_⟩
    apply private_readers G C hL hTF hJ hgh hhg b w hW h4 hH hIw
    intro T hT hShared
    exact hProtect T (by simpa only [hUb] using hT) hShared
  rcases hU with hU | hU
  · exact ⟨0, hFinish 0 hU⟩
  · exact ⟨1, hFinish 1 hU⟩

end PEqualNP.Outside.L_meta_5012.PrivateRegion

namespace PEqualNP.Outside.L_meta_5012.PrivateRegion

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo

noncomputable def independentProtected {n : ℕ} (G : SimpleGraph (Fin n))
    (C : Circuit) (g : ℕ) (b : Fin 2) (w : Fin n) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter fun q =>
    q ∉ nodes G C g b w ∧ q ≠ g ∧ ¬ InCone n C g q

lemma mem_independentProtected {n : ℕ} (G : SimpleGraph (Fin n))
    (C : Circuit) (g : ℕ) (b : Fin 2) (w : Fin n) (q : ℕ) :
    q ∈ independentProtected G C g b w ↔ q < C.gates.length ∧
      q ∉ nodes G C g b w ∧ q ≠ g ∧ ¬ InCone n C g q := by
  classical
  simp only [independentProtected, Finset.mem_filter, Finset.mem_range]

lemma independentProtected_closed {n : ℕ} (G : SimpleGraph (Fin n))
    (C : Circuit) (hAO : IsAO2 n C) (g : ℕ) (b : Fin 2) (w : Fin n)
    (hPrivate : ∀ q ∈ nodes G C g b w, ∀ r < C.gates.length,
      n + q ∈ (gateAt C r).inputs → r ∈ nodes G C g b w ∨ r = g) :
    ∀ q ∈ independentProtected G C g b w, ∀ u ∈ (gateAt C q).inputs,
      n ≤ u → u - n ∈ independentProtected G C g b w := by
  intro q hq u hu hnu
  obtain ⟨hqLen, hqNot, hqNe, hqCone⟩ := (mem_independentProtected G C g b w q).mp hq
  have hub := hAO.2.1 q hqLen u hu
  have hRep : n + (u-n) = u := by omega
  have hDirect : InCone n C (u-n) q :=
    (Lift.inCone_iff hqLen).mpr ⟨u, hu, hnu, hub, Or.inl rfl⟩
  apply (mem_independentProtected G C g b w (u-n)).mpr
  refine ⟨by omega, ?_, ?_, ?_⟩
  · intro huJ
    rcases hPrivate (u-n) huJ q hqLen (by rwa [hRep]) with hqJ | hqEq
    · exact hqNot hqJ
    · exact hqNe hqEq
  · intro he
    exact hqCone (he ▸ hDirect)
  · intro hCone
    exact hqCone (Lift.inCone_trans hCone hDirect)

lemma other_mem_independentProtected {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) {g h : ℕ} (hne : g ≠ h) (hJ : junk G C = {g,h})
    (hgh : ¬ InCone n C g h) (b : Fin 2) (w : Fin n) :
    h ∈ independentProtected G C g b w := by
  have hhJ : h ∈ junk G C := by rw [hJ]; simp
  obtain ⟨hh, hhAnd⟩ := RawOperands.junk_data G C h hhJ
  apply (mem_independentProtected G C g b w h).mpr
  refine ⟨hh, ?_, Ne.symm hne, hgh⟩
  intro hhNodes
  have hhOr := ((mem_nodes G C g b w h).mp hhNodes).2.1
  rw [hhAnd] at hhOr
  cases hhOr

end PEqualNP.Outside.L_meta_5012.PrivateRegion

namespace PEqualNP.Outside.L_meta_5012.PrivateRegion

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo

lemma nodes_support_union {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hTF : TopForm G C)
    {g h : ℕ} (hJ : junk G C = {g,h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (b : Fin 2) (w : Fin n) {q : ℕ} (hq : q ∈ nodes G C g b w)
    (a c : ℕ) (hInputs : (gateAt C q).inputs = [a,c]) :
    orIn n C (n+q) = orIn n C a ∪ orIn n C c := by
  obtain ⟨hqLen, hqOr, hqReach, _⟩ := (mem_nodes G C g b w q).mp hq
  have ha : a ∈ (gateAt C q).inputs := by rw [hInputs]; simp
  have hc : c ∈ (gateAt C q).inputs := by rw [hInputs]; simp
  have hp := (Critical.Base.orReaches_reach q _ hqReach).1
  have hpa := node_input_path G C hAO g b w hq ha
  have hpc := node_input_path G C hAO g b w hq hc
  apply Finset.ext
  intro i
  let x : Fin n → Bool := fun t => decide (t = i)
  have hRawQ := raw_of_operand_path G C hAO hTF hJ hgh hhg b (n+q) hp x
  have hRawA := raw_of_operand_path G C hAO hTF hJ hgh hhg b a hpa x
  have hRawC := raw_of_operand_path G C hAO hTF hJ hgh hhg b c hpc x
  have hEval := Lift.wval_gate_or hAO x hqLen hqOr
  have hOpA : opnd C q 0 = a := by simp [opnd, hInputs]
  have hOpC : opnd C q 1 = c := by simp [opnd, hInputs]
  rw [hOpA, hOpC, hRawQ, hRawA, hRawC] at hEval
  have hEq : decide (i ∈ orIn n C (n+q)) =
      (decide (i ∈ orIn n C a) || decide (i ∈ orIn n C c)) := by
    simpa [x] using hEval
  have hTrue : decide (i ∈ orIn n C (n+q)) = true ↔
      (decide (i ∈ orIn n C a) || decide (i ∈ orIn n C c)) = true := by rw [hEq]
  simpa only [decide_eq_true_eq, Bool.or_eq_true, Finset.mem_union] using hTrue

end PEqualNP.Outside.L_meta_5012.PrivateRegion

namespace PEqualNP.Outside.L_meta_5012.OverlapCase

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo

lemma independent_large_overlaps_distinct_filters_impossible {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C)
    (hOne : ∀ D : Circuit, IsLeastAO G D → (junk G D).card ≠ 1)
    (hT : TopForm G C) {g h : ℕ} (hne : g ≠ h) (hJ : junk G C = {g,h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G)
    (hLargeG : 2 ≤ (side (n := n) C g 0 ∩ side (n := n) C g 1).card)
    (hLargeH : 2 ≤ (side (n := n) C h 0 ∩ side (n := n) C h 1).card)
    (w z : Fin n) (hW : wmax G C g = {w}) (hZ : wmax G C h = {z})
    (hwz : w ≠ z) : False := by
  classical
  have hNoCommon := both_large_overlap_no_opposite G C hL.1 hT hJ hgh hhg h4 hLargeG hLargeH
  have hgJ : g ∈ junk G C := by rw [hJ]; simp
  have hhJ : h ∈ junk G C := by rw [hJ]; simp
  have hg := (RawOperands.junk_data G C g hgJ).1
  have hTwo : (junk G C).card = 2 := by simp [hJ,hne]
  have hH : (PrivateRegion.overlap n C h).Nonempty := by
    apply Finset.card_pos.mp
    change 0 < (side (n := n) C h 0 ∩ side (n := n) C h 1).card
    omega
  obtain ⟨b,⟨r,hr,hroot⟩,hprivate⟩ :=
    PrivateRegion.distinct_filters_choose_private_factor G C hL hOne hT hne hJ hgh hhg
      hNoCommon s hbip h4 w z hW hZ (Ne.symm hwz) hLargeG hH
  obtain ⟨d,hd⟩ : (PrivateRegion.overlap n C g).Nonempty := by
    apply Finset.card_pos.mp
    change 0 < (side (n := n) C g 0 ∩ side (n := n) C g 1).card
    omega
  have hWmem : w ∈ wmax G C g := by rw [hW]; simp
  have hwOut : w ∉ side (n := n) C g 0 ∪ side (n := n) C g 1 := by
    intro hin
    exact no_independent_overlap_filter_inside G C hL hOne hT hne hJ hgh hhg
      hNoCommon h4 hLargeG hWmem hin
  have hEval (x : Fin n → Bool) : gateVal n C g x = IndependentDescent.product
      (side (n := n) C g 0) (side (n := n) C g 1) x :=
    RawOperands.independent_product G C hL.1 hT g h hJ hgh hhg g (Or.inl rfl) x
  have hSafe := (IndependentDescent.wmax_iff G C g _ _ hEval w).mp hWmem
  have hIw : ∀ i ∈ PrivateRegion.overlap n C g, G.Adj w i := fun i hi =>
    safe_adj_overlap G _ _ hSafe hi
  have hIroot : PrivateRegion.overlap n C g ⊆ orIn n C (n+r) := by
    rw [← hroot]
    change PrivateRegion.overlap n C g ⊆ side (n := n) C g b
    fin_cases b
    · exact Finset.inter_subset_left
    · exact Finset.inter_subset_right
  apply OrProjection.projection_contradiction_of_boundaries G C hL hOne hTwo g h r w d
    hgJ hhJ (PrivateRegion.nodes G C g b w) (PrivateRegion.protectedNodes G C g b w)
    (PrivateRegion.independentProtected G C g b w) (orIn n C) (PrivateRegion.overlap n C g)
    hd hIw
    (fun j hj => PrivateRegion.nodes_before_junk G C hL.1 hg b w hj) hr
    (PrivateRegion.protected_disjoint G C g b w)
    (PrivateRegion.protected_closed_of_private G C hL.1 g hg b w hprivate)
    _ _ _ _ hIroot hprivate _ _
    (PrivateRegion.other_mem_independentProtected G C hne hJ hgh b w) _
    (PrivateRegion.independentProtected_closed G C hL.1 g b w hprivate)
  · intro j hj u hu huJ hnu
    exact PrivateRegion.boundary_mem_protected G C hL.1 g hg b w hj hu huJ hnu
  · intro j hj u hu huJ
    exact PrivateRegion.boundary_protected G C hL.1 hT hJ hgh hhg b w hj hu huJ
  · intro j hj u hu _ x
    exact PrivateRegion.raw_of_operand_path G C hL.1 hT hJ hgh hhg b u
      (PrivateRegion.node_input_path G C hL.1 g b w hj hu) x
  · intro j hj a c hinputs
    exact PrivateRegion.nodes_support_union G C hL.1 hT hJ hgh hhg b w hj a c hinputs
  · intro hOutput
    have hrep : C.output = n+(C.output-n) := by have := hOutput.1; omega
    exact PrivateRegion.nodes_not_output G C hL.2.1 g b w hOutput.2 hrep
  · intro u v huv hcut
    exact critical_overlap_cover G C hL.1 hL.2.1 hT hne hJ hgh hhg hNoCommon
      w hW hwOut u v huv hcut
  · intro j hj
    have hmem := (PrivateRegion.mem_independentProtected G C g b w j).mp hj
    exact ⟨hmem.2.1,hmem.2.2.1⟩

lemma independent_large_overlaps_same_filters {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C)
    (hOne : ∀ D : Circuit, IsLeastAO G D → (junk G D).card ≠ 1)
    (hT : TopForm G C) {g h : ℕ} (hne : g ≠ h) (hJ : junk G C = {g,h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G)
    (hLargeG : 2 ≤ (side (n := n) C g 0 ∩ side (n := n) C g 1).card)
    (hLargeH : 2 ≤ (side (n := n) C h 0 ∩ side (n := n) C h 1).card) :
    wmax G C g = wmax G C h := by
  have hNoCommon := both_large_overlap_no_opposite G C hL.1 hT hJ hgh hhg h4 hLargeG hLargeH
  have hJ' : junk G C = {h,g} := by rw [hJ,Finset.pair_comm]
  have hNoCommon' := both_large_overlap_no_opposite G C hL.1 hT hJ' hhg hgh h4 hLargeH hLargeG
  obtain ⟨w,hW,_⟩ := independent_overlap_unique_outside G C hL hOne hT hne hJ hgh hhg
    hNoCommon h4 hLargeG
  obtain ⟨z,hZ,_⟩ := independent_overlap_unique_outside G C hL hOne hT (Ne.symm hne) hJ' hhg hgh
    hNoCommon' h4 hLargeH
  by_cases hwz : w = z
  · rw [hW,hZ,hwz]
  · exact False.elim (independent_large_overlaps_distinct_filters_impossible G C hL hOne hT
      hne hJ hgh hhg s hbip h4 hLargeG hLargeH w z hW hZ hwz)

end PEqualNP.Outside.L_meta_5012.OverlapCase

namespace PEqualNP.Outside.L_meta_5012.H3

namespace Lift

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Core PEqualNP.ReadTwo

lemma foldl_wires_len (gs : List Gate) (acc : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc).length =
      acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_wires_getD_lt (gs : List Gate) (acc : List Bool) (i : ℕ) (hi : i < acc.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) acc).getD i false =
      acc.getD i false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]).length := by
      simp only [List.length_append, List.length_singleton]; omega
    rw [ih _ hlt]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_wires_getD_gate (gs : List Gate) (acc : List Bool) (j : ℕ) (hj : j < gs.length)
    (hback : ∀ k ∈ gs[j].inputs, k < acc.length + j) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) acc).getD
        (acc.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun k =>
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun m => w.getD m false)]) acc).getD
          k false) := by
  induction gs generalizing acc j with
  | nil => cases hj
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [Nat.add_zero, List.foldl_cons, List.getElem_cons_zero] at hback ⊢
      set acc' := acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]
      have hlen : acc.length < acc'.length := by
        simp only [acc', List.length_append, List.length_singleton]; omega
      rw [foldl_wires_getD_lt gs acc' acc.length hlen]
      have hlhs : acc'.getD acc.length false = g.op.eval (g.inputs.map fun k => acc.getD k false) := by
        simp only [acc', List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
          Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
      rw [hlhs]
      congr 1
      apply List.map_congr_left
      intro k hk
      have hka : k < acc.length := hback k hk
      have hka' : k < acc'.length := by omega
      rw [foldl_wires_getD_lt gs acc' k hka']
      simp only [acc', List.getD_eq_getElem?_getD, List.getElem?_append_left hka]
    | succ j' =>
      simp only [List.foldl_cons, List.getElem_cons_succ]
      set acc' := acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]
      have hlen' : acc'.length = acc.length + 1 := by
        simp only [acc', List.length_append, List.length_singleton]
      have hj' : j' < gs.length := by simp only [List.length_cons] at hj; omega
      have hidx : acc.length + (j' + 1) = acc'.length + j' := by omega
      rw [hidx]
      apply ih acc' j' hj'
      intro k hk
      have hbk := hback k (by simpa using hk)
      omega

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length :=
  foldl_wires_len C.gates x

lemma wval_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    wval C x i = x ⟨i, hi⟩ := by
  unfold wval Circuit.wires
  have hlt : i < (List.ofFn x).length := by simp [hi]
  rw [foldl_wires_getD_lt C.gates (List.ofFn x) i hlt]
  simp [List.getD_eq_getElem?_getD, hi]

lemma gateVal_eq_wval {n : ℕ} (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    gateVal n C j x = wval C x (n + j) := rfl

lemma wval_ge_len {n : ℕ} (C : Circuit) (x : Fin n → Bool) {w : ℕ} (hw : n + C.gates.length ≤ w) :
    wval C x w = false := by
  unfold wval
  rw [List.getD_eq_getElem?_getD]
  have hlen : (C.wires (List.ofFn x)).length = n + C.gates.length := by
    rw [wires_length, List.length_ofFn]
  rw [List.getElem?_eq_none (by omega)]
  rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  unfold gateAt
  simp [List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma gate_inputs_eq {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
  have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 _ (gateAt_mem hj)
  unfold opnd
  match h : (gateAt C j).inputs with
  | [a, b] => simp
  | [] => rw [h] at hlen; simp at hlen
  | [_] => rw [h] at hlen; simp at hlen
  | _ :: _ :: _ :: _ => rw [h] at hlen; simp at hlen

lemma opnd_mem {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b ∈ (gateAt C j).inputs := by
  rw [gate_inputs_eq hAO hj]
  fin_cases b <;> simp

lemma opnd_lt {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b < n + j :=
  hAO.2.1 j hj _ (opnd_mem hAO hj b)

lemma wval_gate_eval {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) :
    wval C x (n + j) = (gateAt C j).op.eval [wval C x (opnd C j 0), wval C x (opnd C j 1)] := by
  unfold wval Circuit.wires
  have hlen : (List.ofFn x).length = n := List.length_ofFn
  have hback : ∀ k ∈ C.gates[j].inputs, k < (List.ofFn x).length + j := by
    intro k hk; rw [hlen, ← gateAt_eq hj] at *; exact hAO.2.1 j hj k hk
  have h := foldl_wires_getD_gate C.gates (List.ofFn x) j hj hback
  rw [hlen] at h
  rw [h, ← gateAt_eq hj, gate_inputs_eq hAO hj]
  simp

lemma foldl_cones_len (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) :
    (gs.foldl (coneStep n) acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, coneStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_cones_getD_lt (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) (i : ℕ) (hi : i < acc.length) :
    (gs.foldl (coneStep n) acc).getD i [] = acc.getD i [] := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (coneStep n acc g).length := by
      simp only [coneStep, List.length_append, List.length_singleton]; omega
    rw [ih _ hlt]
    simp only [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma cones_length (n : ℕ) (C : Circuit) : (cones n C).length = C.gates.length := by
  unfold cones; rw [foldl_cones_len]; simp

lemma foldl_cones_getD_gate (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl (coneStep n) acc).getD (acc.length + j) [] =
      (gs[j].inputs.filter (fun w => decide (n ≤ w ∧ w < n + (acc.length + j)))).flatMap
        (fun w => (w - n) :: (gs.foldl (coneStep n) acc).getD (w - n) []) := by
  induction gs generalizing acc j with
  | nil => cases hj
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [Nat.add_zero, List.foldl_cons, List.getElem_cons_zero]
      set acc' := coneStep n acc g
      have hlen : acc.length < acc'.length := by
        simp only [acc', coneStep, List.length_append, List.length_singleton]; omega
      rw [foldl_cones_getD_lt n gs acc' acc.length hlen]
      have hlhs : acc'.getD acc.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + acc.length))).flatMap
            (fun w => (w - n) :: acc.getD (w - n) []) := by
        simp only [acc', coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
          Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
      rw [hlhs]
      apply List.flatMap_congr
      intro w hw
      simp only [List.mem_filter, decide_eq_true_eq] at hw
      have hwn : w - n < acc.length := by omega
      have hwn' : w - n < acc'.length := by omega
      rw [foldl_cones_getD_lt n gs acc' (w - n) hwn']
      simp only [acc', coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hwn]
    | succ j' =>
      simp only [List.foldl_cons, List.getElem_cons_succ]
      set acc' := coneStep n acc g
      have hlen' : acc'.length = acc.length + 1 := by
        simp only [acc', coneStep, List.length_append, List.length_singleton]
      have hj' : j' < gs.length := by simp only [List.length_cons] at hj; omega
      have hidx : acc.length + (j' + 1) = acc'.length + j' := by omega
      rw [hidx]
      exact ih acc' j' hj'

lemma inCone_lt_len {n : ℕ} {C : Circuit} {i j : ℕ} (h : InCone n C i j) : j < C.gates.length := by
  by_contra hge
  unfold InCone at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [cones_length]; omega)] at h
  simp at h

lemma inCone_iff {n : ℕ} {C : Circuit} {i j : ℕ} (hj : j < C.gates.length) :
    InCone n C i j ↔
      ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ w < n + j ∧ (i = w - n ∨ InCone n C i (w - n)) := by
  unfold InCone cones
  have h := foldl_cones_getD_gate n C.gates [] j hj
  simp only [List.length_nil, Nat.zero_add] at h
  rw [h, ← gateAt_eq hj]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw1, hw2, hw3⟩, hw4⟩; exact ⟨w, hw1, hw2, hw3, hw4⟩
  · rintro ⟨w, hw1, hw2, hw3, hw4⟩; exact ⟨w, ⟨hw1, hw2, hw3⟩, hw4⟩

lemma inCone_lt {n : ℕ} {C : Circuit} {i j : ℕ} : InCone n C i j → i < j := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro h
    have hj := inCone_lt_len h
    rw [inCone_iff hj] at h
    rcases h with ⟨w, _, hnw, hwnj, rfl | hsub⟩
    · omega
    · have := ih (w - n) (by omega) hsub; omega

lemma inCone_trans {n : ℕ} {C : Circuit} {i j k : ℕ} (h1 : InCone n C i j) (h2 : InCone n C j k) :
    InCone n C i k := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    have hk := inCone_lt_len h2
    rw [inCone_iff hk] at h2 ⊢
    rcases h2 with ⟨w, hw, hnw, hwnk, rfl | hsub⟩
    · exact ⟨w, hw, hnw, hwnk, Or.inr h1⟩
    · exact ⟨w, hw, hnw, hwnk, Or.inr (ih (w - n) (by omega) hsub)⟩

end Lift

namespace Patch

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Core PEqualNP.ReadTwo

open Lift

def patch (C : Circuit) (j : ℕ) (g : Gate) : Circuit := ⟨C.gates.set j g, C.output⟩

lemma patch_length (C : Circuit) (j : ℕ) (g : Gate) :
    (patch C j g).gates.length = C.gates.length := by
  simp [patch]

lemma gateAt_patch_ne (C : Circuit) (j k : ℕ) (g : Gate) (hne : j ≠ k) :
    gateAt (patch C j g) k = gateAt C k := by
  simp [patch, gateAt, List.getD_eq_getElem?_getD, List.getElem?_set_ne hne]

lemma gateAt_patch_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) (g : Gate) :
    gateAt (patch C j g) j = g := by
  simp [patch, gateAt, List.getD_eq_getElem?_getD, hj]

lemma patch_isAO2 {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (j : ℕ) (g : Gate)
    (hOp : g.op = GateOp.and ∨ g.op = GateOp.or) (hLen : g.inputs.length = 2)
    (hBack : ∀ w ∈ g.inputs, w < n + j) : IsAO2 n (patch C j g) := by
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    change k ∈ C.gates.set j g at hk
    rcases List.mem_or_eq_of_mem_set hk with hk | rfl
    · exact hAO.1 k hk
    · exact hOp
  · intro k hk w hw
    have hkC : k < C.gates.length := by simpa only [patch_length] using hk
    by_cases hkj : k = j
    · subst k
      rw [gateAt_patch_eq hkC] at hw
      exact hBack w hw
    · rw [gateAt_patch_ne C j k g (Ne.symm hkj)] at hw
      exact hAO.2.1 k hkC w hw
  · intro k hk
    change k ∈ C.gates.set j g at hk
    rcases List.mem_or_eq_of_mem_set hk with hk | rfl
    · exact hAO.2.2 k hk
    · exact hLen

lemma patch_gateVal_eq_of_not_inCone {n : ℕ} {C : Circuit} {j : ℕ} {g : Gate}
    (hAO : IsAO2 n C) (hAO' : IsAO2 n (patch C j g)) (k : ℕ)
    (hne : j ≠ k) (hCone : ¬ InCone n C j k) (x : Fin n → Bool) :
    gateVal n (patch C j g) k x = gateVal n C k x := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    by_cases hk : k < C.gates.length
    · have hk' : k < (patch C j g).gates.length := by simpa only [patch_length] using hk
      have hgate := gateAt_patch_ne C j k g hne
      have hopnd (b : Fin 2) : opnd (patch C j g) k b = opnd C k b := by
        unfold opnd
        rw [hgate]
      have hval (b : Fin 2) : wval (patch C j g) x (opnd C k b) =
          wval C x (opnd C k b) := by
        by_cases hw : opnd C k b < n
        · rw [wval_input _ _ _ hw, wval_input _ _ _ hw]
        · have hw' : n ≤ opnd C k b := by omega
          have hlt := opnd_lt hAO hk b
          have hsub_ne : j ≠ opnd C k b - n := by
            intro he
            apply hCone
            exact (inCone_iff hk).mpr ⟨opnd C k b, opnd_mem hAO hk b, hw', hlt, Or.inl he⟩
          have hsub_cone : ¬ InCone n C j (opnd C k b - n) := by
            intro he
            apply hCone
            exact (inCone_iff hk).mpr ⟨opnd C k b, opnd_mem hAO hk b, hw', hlt, Or.inr he⟩
          have hv := ih (opnd C k b - n) (by omega) hsub_ne hsub_cone
          rw [gateVal_eq_wval, gateVal_eq_wval, Nat.add_sub_of_le hw'] at hv
          exact hv
      rw [gateVal_eq_wval, gateVal_eq_wval, wval_gate_eval hAO' x hk',
        wval_gate_eval hAO x hk, hgate, hopnd 0, hopnd 1, hval 0, hval 1]
    · rw [gateVal_eq_wval, gateVal_eq_wval, wval_ge_len _ _ (by rw [patch_length]; omega),
        wval_ge_len _ _ (by omega)]

lemma patch_size (C : Circuit) (j : ℕ) (g : Gate) : (patch C j g).size = C.size := by
  simp [Circuit.size, patch_length]

lemma patch_isLeastAO {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} {j : ℕ} {g : Gate} (hL : IsLeastAO G C)
    (hAO' : IsAO2 n (patch C j g)) (hF' : circuitFun n (patch C j g) = graphFun G ∅) :
    IsLeastAO G (patch C j g) := by
  refine ⟨hAO', hF', ?_⟩
  intro D hD hDF
  rw [patch_size]
  exact hL.2.2 D hD hDF

lemma patch_junk_mem_iff_of_not_inCone {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} {j : ℕ} {g : Gate} (hAO : IsAO2 n C) (hAO' : IsAO2 n (patch C j g))
    {k : ℕ} (hne : j ≠ k) (hCone : ¬ InCone n C j k) :
    k ∈ junk G (patch C j g) ↔ k ∈ junk G C := by
  change (k ∈ (Finset.range (patch C j g).gates.length).filter (fun i => IsDirtyAnd n G (patch C j g) i)) ↔
    k ∈ (Finset.range C.gates.length).filter (fun i => IsDirtyAnd n G C i)
  rw [Finset.mem_filter, Finset.mem_filter]
  simp only [Finset.mem_range, IsDirtyAnd, IsDirty, patch_length,
    gateAt_patch_ne C j k g hne, patch_gateVal_eq_of_not_inCone hAO hAO' k hne hCone]

end Patch

namespace SoleReader

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Core PEqualNP.ReadTwo

open Lift

end SoleReader

namespace IndependentDescent

open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

def product {n : ℕ} (P Q : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∃ p ∈ P, x p = true) && decide (∃ q ∈ Q, x q = true)

def Safe {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P Q : Finset (Fin n)) (w : Fin n) : Prop :=
  ∀ x : Fin n → Bool, product P Q x = true → x w = true → graphFun G ∅ x = true

def Useful {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P Q : Finset (Fin n)) (u v : Fin n) : Prop :=
  G.Adj u v ∧ product P Q (pairInput u v) = true ∧
    (Safe G P Q u ∨ Safe G P Q v)

lemma product_true {n : ℕ} (P Q : Finset (Fin n)) (x : Fin n → Bool) :
    product P Q x = true ↔ (∃ p ∈ P, x p = true) ∧ ∃ q ∈ Q, x q = true := by
  simp [product]

lemma wmax_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : PEqualNP.CircuitLowerBounds.Circuit) (g : ℕ) (P Q : Finset (Fin n))
    (heval : ∀ x : Fin n → Bool, gateVal n C g x = product P Q x) (w : Fin n) :
    w ∈ wmax G C g ↔ Safe G P Q w := by
  simp only [wmax, Finset.mem_filter, Finset.mem_univ, true_and, Safe]
  simp_rw [heval]

lemma graph_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, pairInput]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro h
    exact ⟨u, v, h, Or.inl rfl, Or.inr rfl⟩

lemma safe_overlap_adjacent {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P Q : Finset (Fin n)) {w v : Fin n} (hw : Safe G P Q w) (hv : v ∈ P ∩ Q) :
    G.Adj w v := by
  obtain ⟨hvP, hvQ⟩ := Finset.mem_inter.mp hv
  apply (graph_pair G w v).mp
  apply hw
  · exact (product_true P Q _).mpr ⟨⟨v, hvP, by simp [pairInput]⟩,
      v, hvQ, by simp [pairInput]⟩
  · simp [pairInput]

end IndependentDescent

namespace IndependentObstruction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

open PEqualNP.TopForm

end IndependentObstruction

namespace Normalize

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

end Normalize

namespace Cases

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Core

end Cases

namespace CleanReplacement

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
  PEqualNP.CleanedNonEdge PEqualNP.TopForm

def gateBit (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def stepWire (w : List Bool) (g : Gate) : List Bool := w ++ [gateBit w g]

def WiresLE (w z : List Bool) : Prop :=
  w.length = z.length ∧ ∀ i, w.getD i false = true → z.getD i false = true

def IsMonoGate (g : Gate) : Prop := g.op = GateOp.and ∨ g.op = GateOp.or

lemma monoGate_of_mem {C : Circuit} (hC : Monotone2 C) {g : Gate} (hg : g ∈ C.gates) :
    IsMonoGate g := by
  simpa [IsMonoGate] using (hC g hg).1

lemma bit_mono {w z : List Bool} (h : WiresLE w z) {g : Gate} (hg : IsMonoGate g)
    (hw : gateBit w g = true) : gateBit z g = true := by
  rcases hg with hop | hop
  · simp only [gateBit, hop, GateOp.eval, List.all_map, List.all_eq_true,
      Function.comp_apply, id_eq] at hw ⊢
    exact fun i hi => h.2 i (hw i hi)
  · simp only [gateBit, hop, GateOp.eval, List.any_map, List.any_eq_true,
      Function.comp_apply, id_eq] at hw ⊢
    obtain ⟨i, hi, hv⟩ := hw
    exact ⟨i, hi, h.2 i hv⟩

lemma append_mono {w z : List Bool} {a b : Bool} (h : WiresLE w z)
    (hab : a = true → b = true) : WiresLE (w ++ [a]) (z ++ [b]) := by
  refine ⟨by simp [h.1], ?_⟩
  intro i hi
  rw [List.getD_eq_getElem?_getD] at hi ⊢
  by_cases hlt : i < w.length
  · rw [List.getElem?_append_left hlt] at hi
    rw [List.getElem?_append_left (by rwa [← h.1])]
    simpa only [List.getD_eq_getElem?_getD] using h.2 i
      (by simpa only [List.getD_eq_getElem?_getD] using hi)
  · rw [List.getElem?_append_right (Nat.le_of_not_gt hlt)] at hi
    rw [List.getElem?_append_right (by rw [← h.1]; omega), ← h.1]
    cases hd : i - w.length with
    | zero =>
      simp only [hd, List.getElem?_cons_zero, Option.getD_some] at hi ⊢
      exact hab hi
    | succ k => simp [hd] at hi

lemma fold_mono (gs : List Gate) (hg : ∀ g ∈ gs, IsMonoGate g)
    {w z : List Bool} (h : WiresLE w z) :
    WiresLE (gs.foldl stepWire w) (gs.foldl stepWire z) := by
  induction gs generalizing w z with
  | nil => exact h
  | cons g gs ih =>
    exact ih (fun k hk => hg k (List.mem_cons_of_mem _ hk))
      (append_mono h (bit_mono h (hg g (by simp))))

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma fold_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (stepWire w g) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma ofFn_getD {n : ℕ} (x : Fin n → Bool) (u : Fin n) :
    (List.ofFn x).getD u.val false = x u := by
  simp [List.getD_eq_getElem?_getD]

lemma ofFn_mono {n : ℕ} {x y : Fin n → Bool} (h : ∀ u, x u = true → y u = true) :
    WiresLE (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp, ?_⟩
  intro i hi
  by_cases hlt : i < n
  · rw [ofFn_getD y ⟨i, hlt⟩]
    exact h ⟨i, hlt⟩ (by simpa only [ofFn_getD x ⟨i, hlt⟩] using hi)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hlt)] at hi
    cases hi

def patch (C : Circuit) (j : ℕ) (g : Gate) : Circuit := ⟨C.gates.set j g, C.output⟩

def earlierWires (C : Circuit) (j : ℕ) (w : List Bool) : List Bool :=
  (C.gates.take j).foldl stepWire w

def off : Gate := ⟨GateOp.or, []⟩

lemma off_bit (w : List Bool) : gateBit w off = false := rfl

lemma wires_patch {C : Circuit} {j : ℕ} (hj : j < C.gates.length) (g : Gate) (w : List Bool) :
    (patch C j g).wires w = (C.gates.drop (j + 1)).foldl stepWire (stepWire (earlierWires C j w) g) := by
  change (C.gates.set j g).foldl stepWire w = _
  rw [List.set_eq_take_append_cons_drop, ite_eq_left hj, List.foldl_append, List.foldl_cons]
  rfl

lemma original_patch {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    patch C j C.gates[j] = C := by
  cases C with
  | mk gates output =>
    change Circuit.mk (gates.set j gates[j]) output = Circuit.mk gates output
    congr 1
    exact List.set_getElem_self hj

lemma patch_mono {C : Circuit} (hC : Monotone2 C) {j : ℕ} (hj : j < C.gates.length)
    (g h : Gate) (w : List Bool)
    (hbit : gateBit (earlierWires C j w) g = true → gateBit (earlierWires C j w) h = true) :
    WiresLE ((patch C j g).wires w) ((patch C j h).wires w) := by
  rw [wires_patch hj, wires_patch hj]
  apply fold_mono _ (fun k hk => monoGate_of_mem hC (List.mem_of_mem_drop hk))
  exact append_mono ⟨rfl, fun _ h => h⟩ hbit

lemma patch_bit {n : ℕ} {C : Circuit} {j : ℕ} (hj : j < C.gates.length)
    (g : Gate) (x : Fin n → Bool) :
    gateVal n (patch C j g) j x = gateBit (earlierWires C j (List.ofFn x)) g := by
  have hlen : (earlierWires C j (List.ofFn x)).length = n + j := by
    unfold earlierWires
    rw [fold_length]
    simp [Nat.min_eq_left (Nat.le_of_lt hj)]
  unfold gateVal
  rw [wires_patch hj, fold_getD_lt _ _ _ (by simp [stepWire, hlen]), ← hlen]
  simp [stepWire, List.getD_eq_getElem?_getD]

lemma gateAt_patch_ne (C : Circuit) (j k : ℕ) (g : Gate) (hne : j ≠ k) :
    gateAt (patch C j g) k = gateAt C k := by
  simp [patch, gateAt, List.getD_eq_getElem?_getD, List.getElem?_set_ne hne]

lemma graph_true {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
  simp [graphFun]

lemma pair_le {n : ℕ} {x : Fin n → Bool} {u v : Fin n}
    (hu : x u = true) (hv : x v = true) (k : Fin n) :
    pairInput u v k = true → x k = true := by
  simp only [pairInput, decide_eq_true_eq]
  rintro (rfl | rfl)
  · exact hu
  · exact hv

lemma circuit_mono {n : ℕ} {C : Circuit} (hC : Monotone2 C) {x y : Fin n → Bool}
    (hxy : ∀ u, x u = true → y u = true) :
    circuitFun n C x = true → circuitFun n C y = true :=
  (fold_mono C.gates (fun _ hg => monoGate_of_mem hC hg) (ofFn_mono hxy)).2 C.output

lemma mem_junk {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {j : ℕ} :
    j ∈ junk G C ↔ j < C.gates.length ∧ IsDirtyAnd n G C j := by
  unfold junk gatesWhere
  rw [Finset.mem_filter, Finset.mem_range]

lemma ao2_mono {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) : Monotone2 C := by
  intro g hg
  exact ⟨by simpa using hAO.1 g hg, Nat.le_of_eq (hAO.2.2 g hg)⟩

lemma no_clean_independent_replacement {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hL : IsLeastAO G C)
    (hOne : ∀ D : Circuit, IsLeastAO G D → (junk G D).card ≠ 1)
    {j k : ℕ} (hne : j ≠ k) (hJ : junk G C = {j,k})
    (hCone : ¬ InCone n C j k) (R : Gate)
    (hOp : R.op = GateOp.and ∨ R.op = GateOp.or)
    (hLen : R.inputs.length = 2) (hBack : ∀ w ∈ R.inputs, w < n + j)
    (hClean : ∀ x : Fin n → Bool, graphFun G ∅ x = false →
      gateBit (earlierWires C j (List.ofFn x)) R = false)
    (hCover : ∀ u v : Fin n, G.Adj u v →
      circuitFun n (patch C j off) (pairInput u v) = false →
      gateBit (earlierWires C j (List.ofFn (pairInput u v))) R = true) : False := by
  have hjmem : j ∈ junk G C := by rw [hJ]; simp
  have hkmem : k ∈ junk G C := by rw [hJ]; simp
  have hj : j < C.gates.length := (mem_junk.mp hjmem).1
  have hmono : Monotone2 C := ao2_mono hL.1
  let D := patch C j R
  have hDAO : IsAO2 n D := Patch.patch_isAO2 hL.1 j R hOp hLen hBack
  have hDM : Monotone2 D := ao2_mono hDAO
  have hnegative (x : Fin n → Bool) (hf : graphFun G ∅ x = false) :
      WiresLE (D.wires (List.ofFn x)) (C.wires (List.ofFn x)) := by
    have h := patch_mono hmono hj R C.gates[j] (List.ofFn x)
      (by intro hh; rw [hClean x hf] at hh; cases hh)
    rwa [original_patch hj] at h
  have hEdges (u v : Fin n) (huv : G.Adj u v) :
      circuitFun n D (pairInput u v) = true := by
    have hF : circuitFun n C (pairInput u v) = true := by
      rw [hL.2.1]
      exact (graph_true G _).mpr ⟨u,v,huv,by simp [pairInput],by simp [pairInput]⟩
    cases hCut : circuitFun n (patch C j off) (pairInput u v) with
    | false =>
      have h := patch_mono hmono hj C.gates[j] R (List.ofFn (pairInput u v))
        (fun _ => hCover u v huv hCut)
      rw [original_patch hj] at h
      exact h.2 C.output hF
    | true =>
      exact (patch_mono hmono hj off R (List.ofFn (pairInput u v))
        (by intro hh; simp [off_bit] at hh)).2 C.output hCut
  have hDF : circuitFun n D = graphFun G ∅ := by
    funext x
    cases hf : graphFun G ∅ x with
    | false =>
      cases hd : circuitFun n D x with
      | false => rfl
      | true =>
        have hh : circuitFun n C x = true := (hnegative x hf).2 C.output hd
        rw [hL.2.1,hf] at hh
        cases hh
    | true =>
      obtain ⟨u,v,huv,hu,hv⟩ := (graph_true G x).mp hf
      exact circuit_mono hDM (pair_le hu hv) (hEdges u v huv)
  have hNoJ : j ∉ junk G D := by
    intro hmem
    obtain ⟨_,_,_,x,hx,hf⟩ := mem_junk.mp hmem
    change gateVal n (patch C j R) j x = true at hx
    rw [patch_bit hj, hClean x hf] at hx
    cases hx
  have hSub : junk G D ⊆ junk G C := by
    intro a ha
    have hja : j ≠ a := by intro he; exact hNoJ (he.symm ▸ ha)
    obtain ⟨haLen,haAnd,_,x,hx,hf⟩ := mem_junk.mp ha
    have haC : a < C.gates.length := by simpa [D,patch] using haLen
    have haOp : (gateAt C a).op = GateOp.and := by
      change (gateAt (patch C j R) a).op = GateOp.and at haAnd
      rwa [gateAt_patch_ne C j a R hja] at haAnd
    exact mem_junk.mpr ⟨haC,haOp,haC,x,(hnegative x hf).2 (n+a) hx,hf⟩
  have hkD : k ∈ junk G D :=
    (Patch.patch_junk_mem_iff_of_not_inCone hL.1 hDAO hne hCone).mpr hkmem
  have hJD : junk G D = {k} := by
    apply Finset.ext
    intro a
    constructor
    · intro ha
      have hao := hSub ha
      rw [hJ] at hao
      simp only [Finset.mem_insert,Finset.mem_singleton] at hao ⊢
      rcases hao with rfl | he
      · exact (hNoJ ha).elim
      · exact he
    · intro ha
      have he := Finset.mem_singleton.mp ha
      exact he ▸ hkD
  have hDL : IsLeastAO G D := Patch.patch_isLeastAO hL hDAO hDF
  exact hOne D hDL (by rw [hJD]; simp)

end CleanReplacement

namespace FlagReduction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo

open CleanReplacement IndependentDescent

lemma earlier_wire_eq {n : ℕ} (C : Circuit) (j : ℕ) (hj : j ≤ C.gates.length)
    (x : Fin n → Bool) {w : ℕ} (hw : w < n + j) :
    (earlierWires C j (List.ofFn x)).getD w false = wval C x w := by
  have hlen : (earlierWires C j (List.ofFn x)).length = n + j := by
    unfold earlierWires
    rw [fold_length]
    simp [Nat.min_eq_left hj]
  have hsplit : C.wires (List.ofFn x) =
      (C.gates.drop j).foldl stepWire (earlierWires C j (List.ofFn x)) := by
    change C.gates.foldl stepWire _ = _
    conv_lhs => rw [← List.take_append_drop j C.gates, List.foldl_append]
    rfl
  unfold wval
  rw [hsplit, fold_getD_lt _ _ _ (by omega)]

lemma star_gate_bit {n : ℕ} (C : Circuit) (j : ℕ) (hj : j ≤ C.gates.length)
    (z : Fin n) (w : ℕ) (hw : w < n + j) (x : Fin n → Bool) :
    gateBit (earlierWires C j (List.ofFn x)) ⟨GateOp.and,[z.val,w]⟩ =
      (x z && wval C x w) := by
  simp only [gateBit, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
    List.all_nil, id_eq, Bool.and_true]
  rw [earlier_wire_eq C j hj x (by have := z.isLt; omega),
    earlier_wire_eq C j hj x hw, Lift.wval_input C x z.val z.isLt]

end FlagReduction

namespace RawOperands

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq_foldl, foldl_stepWire_length, List.length_ofFn]

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

def W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then W n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, foldl_stepWire_length, hpre_len]
  have hCj : W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + k) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append]
    exact (foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact getD_ge_length w0 i (by omega)

lemma W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    W n C x u = x ⟨u, hu⟩ := by
  simp only [W]
  rw [wires_eq_foldl, foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]

open PEqualNP.CleanedNonEdge in
lemma orFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

open PEqualNP.CleanedNonEdge in
lemma orStep_mem_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) (x : ℕ) :
    x ∈ (orStep n cs g).getD cs.length [] ↔ x = cs.length ∨ (g.op = GateOp.or ∧
      ∃ w ∈ g.inputs, n ≤ w ∧ w < n + cs.length ∧ x ∈ cs.getD (w - n) []) := by
  by_cases h : g.op = GateOp.or
  · simp only [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl, h,
      ↓reduceIte, true_and, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some,
      List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro (h1 | ⟨w, ⟨hw, hn, hlt⟩, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, hw, hn, hlt, hx⟩
    · rintro (h1 | ⟨w, hw, hn, hlt, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, ⟨hw, hn, hlt⟩, hx⟩
  · simp [orStep, List.getD_eq_getElem?_getD, h]

open PEqualNP.CleanedNonEdge in
lemma orStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (orStep n cs g).getD m [] = cs.getD m [] := by
  simp [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

open PEqualNP.CleanedNonEdge in
lemma orFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (orStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (orStep n cs g) (by simp [orStep]; omega)]
    exact orStep_getD_lt n cs g k hk

open PEqualNP.CleanedNonEdge in
lemma orSets_mem_iff (n : ℕ) (C : Circuit) (k x : ℕ) (hk : k < C.gates.length) :
    x ∈ (orSets n C).getD k [] ↔ x = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧ x ∈ (orSets n C).getD (w - n) []) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : orSets n C = post.foldl (orStep n) (orStep n (pre.foldl (orStep n) []) gk) := by
    simp only [orSets]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (orStep n) []).length = k := by
    rw [orFold_length]; simp [hpre_len]
  have hl1 : (orStep n (pre.foldl (orStep n) []) gk).length = k + 1 := by
    simp [orStep, hl0]
  have h1 : (orSets n C).getD k [] = (orStep n (pre.foldl (orStep n) []) gk).getD k [] := by
    rw [hc, orFold_getD_lt n post _ k (by omega)]
  have h2 : ∀ m, m < k → (orSets n C).getD m [] = (pre.foldl (orStep n) []).getD m [] := by
    intro m hm
    rw [hc, orFold_getD_lt n post _ m (by omega)]
    exact orStep_getD_lt n _ gk m (by omega)
  have h3 := orStep_mem_last n (pre.foldl (orStep n) []) gk x
  rw [hl0] at h3
  rw [h1, h3]
  constructor
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [h2 (w - n) (by omega)]; exact hx⟩
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [← h2 (w - n) (by omega)]; exact hx⟩

lemma W_or (n : ℕ) (C : Circuit) (x : Fin n → Bool) (r : ℕ) (hr : r < C.gates.length)
    (hop : (gateAt C r).op = GateOp.or) (i : ℕ) (hi : i ∈ (gateAt C r).inputs)
    (hlt : i < n + r) (hv : W n C x i = true) : W n C x (n + r) = true := by
  rw [W_gate n C x r hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  exact ⟨i, hi, by rw [ite_eq_left hlt]; exact hv⟩

open PEqualNP.CleanedNonEdge in
lemma reach_val (n : ℕ) (C : Circuit) (x : Fin n → Bool) (g : ℕ)
    (hv : W n C x (n + g) = true) :
    ∀ k, k < C.gates.length → g ∈ (orSets n C).getD k [] → W n C x (n + k) = true := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk hmem
    rcases (orSets_mem_iff n C k g hk).mp hmem with h | ⟨hop, w, hw, hn, hlt, hx⟩
    · rw [← h]; exact hv
    · have h3 := ih (w - n) (by omega) (by omega) hx
      have e : n + (w - n) = w := by omega
      rw [e] at h3
      exact W_or n C x k hk hop w hw hlt h3

open PEqualNP.CleanedNonEdge in
lemma reach_up (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w g : ℕ)
    (h : OrReaches n C w g) (hv : W n C x (n + g) = true) : W n C x w = true := by
  obtain ⟨hn, hmem⟩ := h
  by_cases hk : w - n < C.gates.length
  · have h3 := reach_val n C x g hv (w - n) hk hmem
    have e : n + (w - n) = w := by omega
    rw [e] at h3
    exact h3
  · exfalso
    have hlen : (orSets n C).length = C.gates.length := by
      unfold orSets; rw [orFold_length]; simp
    have hge : (orSets n C).length ≤ w - n := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge] at hmem
    simp at hmem

lemma mem_filter_gen {α : Type} (p : α → Prop) (d : DecidablePred p) (s : Finset α) (a : α)
    (h : a ∈ @Finset.filter α p d s) : p a :=
  ((@Finset.mem_filter α p d s a).mp h).2

lemma side_val (n : ℕ) (C : Circuit) (x : Fin n → Bool) (j : ℕ) (b : Fin 2) (i : Fin n)
    (hi : i ∈ PEqualNP.TopForm.side (n := n) C j b) (hx : x i = true) :
    W n C x (PEqualNP.TopForm.opnd C j b) = true := by
  unfold PEqualNP.TopForm.side PEqualNP.TopForm.orIn at hi
  have hi2 := mem_filter_gen _ _ _ _ hi
  rcases hi2 with h | ⟨k, hk, hreach, hop, hin⟩
  · rw [← h, W_input n C x i.val i.isLt]; exact hx
  · have hk1 : W n C x (n + k) = true := by
      apply W_or n C x k hk hop i.val hin (by have := i.isLt; omega)
      rw [W_input n C x i.val i.isLt]; exact hx
    exact reach_up n C x _ k hreach hk1

open PEqualNP.EdgeOwnership in
lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

open PEqualNP.EdgeOwnership in
lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

open PEqualNP.EdgeOwnership in
lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

lemma gateAt_mem' (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq C j hj]; exact List.getElem_mem hj

open PEqualNP.EdgeOwnership in
lemma inCone_lt (n : ℕ) (C : Circuit) : ∀ j i, InCone n C i j → i < j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro i h
    obtain ⟨_, k, hk, _, h3⟩ := (inCone_iff n C i j).mp h
    rcases h3 with h3 | h3
    · omega
    · have := ih k hk i h3; omega

open PEqualNP.CleanedNonEdge in
lemma orReach_trans (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (w : ℕ) (hw : w ∈ (gateAt C k).inputs)
    (hlt : w < n + k) (g : ℕ) (h : OrReaches n C w g) : OrReaches n C (n + k) g := by
  obtain ⟨hn, hmem⟩ := h
  refine ⟨by omega, ?_⟩
  have e : n + k - n = k := by omega
  rw [e]
  exact (orSets_mem_iff n C k g hk).mpr (Or.inr ⟨hop, w, hw, hn, hlt, hmem⟩)

open PEqualNP.CleanedNonEdge in
lemma orReach_self (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    OrReaches n C (n + k) k := by
  refine ⟨by omega, ?_⟩
  have e : n + k - n = k := by omega
  rw [e]
  exact (orSets_mem_iff n C k k hk).mpr (Or.inl rfl)

lemma orIn_mem (n : ℕ) (C : Circuit) (w : ℕ) (i : Fin n) :
    i ∈ PEqualNP.TopForm.orIn n C w ↔ ((i : ℕ) = w ∨ ∃ k < C.gates.length,
      PEqualNP.CleanedNonEdge.OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧
        (i : ℕ) ∈ (gateAt C k).inputs) := by
  unfold PEqualNP.TopForm.orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

open PEqualNP.CleanedNonEdge in
lemma down (n : ℕ) (C : Circuit) (x : Fin n → Bool)
    (hAO : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) :
    ∀ w, W n C x w = true → (∃ i : Fin n, i ∈ PEqualNP.TopForm.orIn n C w ∧ x i = true) ∨
      ∃ k, k < C.gates.length ∧ OrReaches n C w k ∧ (gateAt C k).op = GateOp.and ∧
        W n C x (n + k) = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hwn : w < n
    · left
      refine ⟨⟨w, hwn⟩, (orIn_mem n C w _).mpr (Or.inl rfl), ?_⟩
      rw [← W_input n C x w hwn]; exact hv
    · by_cases hk : w - n < C.gates.length
      · have hw : w = n + (w - n) := by omega
        set k := w - n with hkdef
        rcases hAO k hk with hop | hop
        · right
          refine ⟨k, hk, ?_, hop, ?_⟩
          · rw [hw]; exact orReach_self n C k hk
          · rw [← hw]; exact hv
        · have hv2 := hv
          rw [hw, W_gate n C x k hk, hop] at hv2
          simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at hv2
          obtain ⟨i, hi, hiv⟩ := hv2
          split_ifs at hiv with hlt
          rcases ih i (by omega) hiv with ⟨j, hj, hxj⟩ | ⟨k', hk', hr, hop', hv'⟩
          · left
            refine ⟨j, ?_, hxj⟩
            rw [orIn_mem] at hj ⊢
            right
            rcases hj with hj | ⟨k'', hk'', hr, hop'', hin⟩
            · refine ⟨k, hk, ?_, hop, ?_⟩
              · rw [hw]; exact orReach_self n C k hk
              · rw [hj]; exact hi
            · refine ⟨k'', hk'', ?_, hop'', hin⟩
              rw [hw]; exact orReach_trans n C k hk hop i hi hlt k'' hr
          · right
            refine ⟨k', hk', ?_, hop', hv'⟩
            rw [hw]; exact orReach_trans n C k hk hop i hi hlt k' hr
      · exfalso
        have hl := wires_length n C x
        have : W n C x w = false := getD_ge_length _ w (by omega)
        rw [this] at hv; exact Bool.false_ne_true hv

open PEqualNP.EdgeOwnership in
lemma orSets_cone (n : ℕ) (C : Circuit) : ∀ m, m < C.gates.length → ∀ k,
    k ∈ (PEqualNP.CleanedNonEdge.orSets n C).getD m [] → k = m ∨ InCone n C k m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm k hk
    rcases (orSets_mem_iff n C m k hm).mp hk with h | ⟨_, w, hw, hn, hlt, hx⟩
    · exact Or.inl h
    · right
      have h2 := ih (w - n) (by omega) (by omega) k hx
      have e : n + (w - n) = w := by omega
      exact (inCone_iff n C k m).mpr ⟨hm, w - n, by omega, by rw [e]; exact hw, h2⟩

open PEqualNP.EdgeOwnership in
lemma reach_cone (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (o : ℕ)
    (ho : o ∈ (gateAt C j).inputs) (hlt : o < n + j) (k : ℕ)
    (h : PEqualNP.CleanedNonEdge.OrReaches n C o k) : InCone n C k j := by
  obtain ⟨hn, hmem⟩ := h
  have h2 := orSets_cone n C (o - n) (by omega) k hmem
  have e : n + (o - n) = o := by omega
  exact (inCone_iff n C k j).mpr ⟨hj, o - n, by omega, by rw [e]; exact ho, h2⟩

open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

lemma junk_data {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (j : ℕ) (hj : j ∈ junk G C) :
    j < C.gates.length ∧ (gateAt C j).op = GateOp.and := by
  obtain ⟨hjl, hja, _⟩ := Finset.mem_filter.mp hj
  exact ⟨Finset.mem_range.mp hjl, hja⟩

lemma operand_mem {n : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b ∈ (gateAt C j).inputs := by
  have hlen := hAO.2.2 _ (gateAt_mem' C j hj)
  unfold opnd
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  exact List.getElem_mem _

lemma raw_operand_of_no_junk_cone {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C)
    (j : ℕ) (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and)
    (hno : ∀ k ∈ junk G C, ¬ InCone n C k j) (b : Fin 2) (x : Fin n → Bool) :
    PEqualNP.ReadTwo.wval C x (opnd C j b) =
      decide (∃ u ∈ side (n := n) C j b, x u = true) := by
  have hm := operand_mem C hAO j hj b
  have hlt := hAO.2.1 j hj _ hm
  have hi : W n C x (opnd C j b) = true ↔
      ∃ u ∈ side (n := n) C j b, x u = true := by
    constructor
    · intro hv
      have hops : ∀ k < C.gates.length,
          (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or :=
        fun k hk => hAO.1 _ (gateAt_mem' C k hk)
      rcases down n C x hops _ hv with hraw | ⟨k, hk, hr, hop, _⟩
      · exact hraw
      · have hc := reach_cone n C j hj _ hm hlt k hr
        have hnb : ¬ BelowF G C k := fun hb => hTop k hk j hj hop hb hand hc
        have hd : ∃ y : Fin n → Bool, gateVal n C k y = true ∧ graphFun G ∅ y = false := by
          by_contra hn
          apply hnb
          intro y hy
          by_contra hf
          exact hn ⟨y, hy, Bool.eq_false_iff.mpr hf⟩
        have hkj : k ∈ junk G C :=
          Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hop, hk, hd⟩
        exact (hno k hkj hc).elim
    · rintro ⟨u, hu, hxu⟩
      exact side_val n C x j b u hu hxu
  change W n C x (opnd C j b) = _
  by_cases hv : W n C x (opnd C j b) = true
  · simp [hv, hi.mp hv]
  · have hn : ¬ ∃ u ∈ side (n := n) C j b, x u = true := fun h => hv (hi.mpr h)
    simp [Bool.eq_false_iff.mpr hv, hn]

lemma independent_no_junk_ancestors {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g h : ℕ) (hJ : junk G C = {g, h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (j : ℕ) (hj : j = g ∨ j = h) :
    ∀ k ∈ junk G C, ¬ InCone n C k j := by
  intro k hk hc
  have hkm : k = g ∨ k = h := by simpa [hJ] using hk
  rcases hj with rfl | rfl <;> rcases hkm with rfl | rfl
  · have := inCone_lt n C _ _ hc
    omega
  · exact hhg hc
  · exact hgh hc
  · have := inCone_lt n C _ _ hc
    omega

lemma independent_operand {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C)
    (g h : ℕ) (hJ : junk G C = {g, h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (j : ℕ) (hj : j = g ∨ j = h) (b : Fin 2) (x : Fin n → Bool) :
    PEqualNP.ReadTwo.wval C x (opnd C j b) =
      decide (∃ u ∈ side (n := n) C j b, x u = true) := by
  have hjm : j ∈ junk G C := by simpa [hJ] using hj
  obtain ⟨hjl, hja⟩ := junk_data G C j hjm
  exact raw_operand_of_no_junk_cone G C hAO hTop j hjl hja
    (independent_no_junk_ancestors G C g h hJ hgh hhg j hj) b x

lemma and_gate_eq {n : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and)
    (x : Fin n → Bool) :
    gateVal n C j x =
      (PEqualNP.ReadTwo.wval C x (opnd C j 0) && PEqualNP.ReadTwo.wval C x (opnd C j 1)) := by
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem' C j hj))
  have ham : a ∈ (gateAt C j).inputs := by simp [hab]
  have hbm : b ∈ (gateAt C j).inputs := by simp [hab]
  have hba := hAO.2.1 j hj a ham
  have hbb := hAO.2.1 j hj b hbm
  change W n C x (n + j) = _
  rw [W_gate n C x j hj, hand, hab]
  simp [GateOp.eval, opnd, hab, hba, hbb, W, PEqualNP.ReadTwo.wval]

lemma independent_product {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C)
    (g h : ℕ) (hJ : junk G C = {g, h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (j : ℕ) (hj : j = g ∨ j = h) (x : Fin n → Bool) :
    gateVal n C j x =
      (decide (∃ u ∈ side (n := n) C j 0, x u = true) &&
        decide (∃ u ∈ side (n := n) C j 1, x u = true)) := by
  have hjm : j ∈ junk G C := by simpa [hJ] using hj
  obtain ⟨hjl, hja⟩ := junk_data G C j hjm
  rw [and_gate_eq C hAO j hjl hja x,
    independent_operand G C hAO hTop g h hJ hgh hhg j hj 0 x,
    independent_operand G C hAO hTop g h hJ hgh hhg j hj 1 x]

end RawOperands

namespace Critical.Base

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [ite_eq_right hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [ite_eq_left hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h'; exact ⟨hlt, h'⟩
    · rw [ite_eq_right hlt] at h'; cases h'
  · intro h i hi
    rw [ite_eq_left (h i hi).1]; exact (h i hi).2

lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma gateVal_eq_val (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j) := rfl

def OrStep (n : ℕ) (C : Circuit) (w w' : ℕ) : Prop :=
  ∃ k, k < C.gates.length ∧ w = n + k ∧ (gateAt C k).op = GateOp.or ∧
    w' ∈ (gateAt C k).inputs ∧ w' < n + k

lemma orStep_up {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') (hv : val C x w' = true) :
    val C x w = true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head hstep _ ih =>
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (val_or hx hk hop).mpr ⟨_, hin, hlt, ih⟩

lemma or_trace {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) :
    ∀ w : ℕ, val C x w = true →
      ∃ w', Relation.ReflTransGen (OrStep n C) w w' ∧ val C x w' = true ∧
        (w' < n ∨ ∃ h, h < C.gates.length ∧ w' = n + h ∧ (gateAt C h).op ≠ GateOp.or) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · exact ⟨w, Relation.ReflTransGen.refl, hv, Or.inl hw⟩
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [val_ge hx hlen] at hv; cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        by_cases hop : (gateAt C k).op = GateOp.or
        · obtain ⟨i, hin, hlt, hi⟩ := (val_or hx hk hop).mp hv
          obtain ⟨w', hr, hv', hw'⟩ := ih i hlt hi
          exact ⟨w', Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hin, hlt⟩ hr, hv', hw'⟩
        · exact ⟨n + k, Relation.ReflTransGen.refl, hv, Or.inr ⟨k, hk, rfl, hop⟩⟩

lemma pairInput_left {n : ℕ} (u v : Fin n) : pairInput u v u = true := by
  simp [pairInput]

lemma pairInput_right {n : ℕ} (u v : Fin n) : pairInput u v v = true := by
  simp [pairInput]

lemma pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
  simp [pairInput]

lemma graphFun_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, pairInput_true]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro h
    exact ⟨u, v, h, Or.inl rfl, Or.inr rfl⟩

lemma operand_trace {n : ℕ} {C : Circuit} (u v : Fin n) (p : ℕ)
    (hv : val C (List.ofFn (pairInput u v)) p = true) :
    (∃ t : Fin n, (t = u ∨ t = v) ∧ Relation.ReflTransGen (OrStep n C) p t.val) ∨
    (∃ h, h < C.gates.length ∧ (gateAt C h).op ≠ GateOp.or ∧
      Relation.ReflTransGen (OrStep n C) p (n + h) ∧
      val C (List.ofFn (pairInput u v)) (n + h) = true) := by
  obtain ⟨w', hr, hv', hw'⟩ := or_trace (n := n) (C := C) (x := List.ofFn (pairInput u v))
    (by simp) p hv
  rcases hw' with hlt | ⟨h, hh, rfl, hop⟩
  · left
    refine ⟨⟨w', hlt⟩, ?_, hr⟩
    have h1 := val_ofFn C (pairInput u v) ⟨w', hlt⟩
    rw [show (⟨w', hlt⟩ : Fin n).val = w' from rfl, hv'] at h1
    exact (pairInput_true u v _).mp h1.symm
  · right
    exact ⟨h, hh, hop, hr, hv'⟩

lemma reach_var_val {n : ℕ} {C : Circuit} (x : Fin n → Bool) (p : ℕ) (t : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p t.val) (ht : x t = true) :
    val C (List.ofFn x) p = true :=
  orStep_up (n := n) (by simp) hr (by rw [val_ofFn]; exact ht)

lemma edge_trace {n : ℕ} (G : SimpleGraph (Fin n)) {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hF : ∀ u v : Fin n, F (pairInput u v) = true → G.Adj u v)
    (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x)
    (u v : Fin n) (huv : F (pairInput u v) = true) :
    ∃ a, a < C.gates.length ∧ (gateAt C a).op ≠ GateOp.or ∧
      Relation.ReflTransGen (OrStep n C) C.output (n + a) ∧
      val C (List.ofFn (pairInput u v)) (n + a) = true := by
  rcases operand_trace (C := C) u v C.output (by rw [hout]; exact huv) with
    ⟨t, _, hr⟩ | h
  · exfalso
    have h1 := reach_var_val (pairInput t t) _ t hr (pairInput_left t t)
    rw [hout] at h1
    exact G.irrefl (hF t t h1)
  · exact h

lemma below_of_reach {n : ℕ} {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x) (a : ℕ)
    (hr : Relation.ReflTransGen (OrStep n C) C.output (n + a)) (x : Fin n → Bool)
    (hv : val C (List.ofFn x) (n + a) = true) : F x = true := by
  rw [← hout]
  exact orStep_up (n := n) (by simp) hr hv

lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

lemma orStep_le {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') : w' ≤ w := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact le_rfl
  | head hstep _ ih =>
    obtain ⟨k, _, rfl, _, _, hlt⟩ := hstep
    omega

lemma orStep_cone {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') :
    ∀ k h', w = n + k → w' = n + h' → h' = k ∨ InCone n C h' k := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => intro k h' h1 h2; left; omega
  | @head a c hstep hrest ih =>
    intro k h' h1 h2
    obtain ⟨k0, hk0, e, _, hin, hlt⟩ := hstep
    have hk : k0 = k := by omega
    subst hk
    have hle := orStep_le hrest
    obtain ⟨k1, hk1⟩ : ∃ k1, c = n + k1 := ⟨c - n, by omega⟩
    subst hk1
    right
    rw [inCone_iff]
    exact ⟨hk0, k1, by omega, hin, ih k1 h' rfl h2⟩

lemma operand_cone {n : ℕ} {C : Circuit} {a p h : ℕ} (ha : a < C.gates.length)
    (hin : p ∈ (gateAt C a).inputs) (hp : p < n + a)
    (hr : Relation.ReflTransGen (OrStep n C) p (n + h)) : InCone n C h a := by
  have hle := orStep_le hr
  obtain ⟨k1, rfl⟩ : ∃ k1, p = n + k1 := ⟨p - n, by omega⟩
  rw [inCone_iff]
  exact ⟨ha, k1, by omega, hin, orStep_cone hr k1 h rfl rfl⟩

lemma orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (orStep n (gs.foldl (orStep n) []) g).getD k [] =
          (gs.foldl (orStep n) []).getD k [] := by
      intro k hk
      simp only [orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
        simp only [orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold OrReaches orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

lemma reach_orReaches {n : ℕ} {C : Circuit} {w w2 : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w2) :
    ∀ g, w2 = n + g → g < C.gates.length → OrReaches n C w g := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro g h1 hg
    subst h1
    exact (orReaches_iff n C g g).mpr ⟨hg, Or.inl rfl⟩
  | @head a c hstep hrest ih =>
    intro g h1 hg
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (orReaches_iff n C k g).mpr ⟨hk, Or.inr ⟨hop, c, hin, hlt, ih g h1 hg⟩⟩

lemma orReaches_reach {n : ℕ} {C : Circuit} (g : ℕ) :
    ∀ w, OrReaches n C w g →
      Relation.ReflTransGen (OrStep n C) w (n + g) ∧ g < C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    have hnw : n ≤ w := h.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp h
    rcases h3 with rfl | ⟨hop, i, hi, hlt, hr⟩
    · exact ⟨Relation.ReflTransGen.refl, hk⟩
    · obtain ⟨hr2, hg⟩ := ih i hlt hr
      exact ⟨Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hi, hlt⟩ hr2, hg⟩

lemma mem_orIn_reach {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hu : u ∈ PEqualNP.TopForm.orIn n C p) :
    Relation.ReflTransGen (OrStep n C) p u.val := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  rcases hu with h | ⟨k, hk, hr, hop, hin⟩
  · rw [h]
  · exact (orReaches_reach k p hr).1.tail ⟨k, hk, rfl, hop, hin, by omega⟩

lemma reach_mem_orIn {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p u.val) :
    u ∈ PEqualNP.TopForm.orIn n C p := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases Relation.ReflTransGen.cases_tail hr with h | ⟨c, hpc, hstep⟩
  · exact Or.inl h
  · obtain ⟨k, hk, rfl, hop, hin, _⟩ := hstep
    exact Or.inr ⟨k, hk, reach_orReaches hpc k rfl hk, hop, hin⟩

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

lemma topData {a : ℕ} (ha : a ∈ tops G C) :
    a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧ BelowF G C a := by
  simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using ha

lemma junkData {a : ℕ} (ha : a ∈ junk G C) :
    a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧
      ∃ x : Fin n → Bool, gateVal n C a x = true ∧ graphFun G ∅ x = false := by
  rcases Finset.mem_filter.mp ha with ⟨hr, hop, hal, hd⟩
  exact ⟨hal, hop, hd⟩

lemma binaryInputs (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) :
    ∃ p q, (gateAt C a).inputs = [p, q] :=
  List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem ha))

lemma opndMem (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
    opnd C a b ∈ (gateAt C a).inputs := by
  obtain ⟨p, q, hpq⟩ := binaryInputs hAO ha
  fin_cases b <;> simp [opnd, hpq]

lemma opndBound (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
    opnd C a b < n + a :=
  hAO.2.1 a ha _ (opndMem hAO ha b)

lemma andValBoth (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and) (x : Fin n → Bool) :
    gateVal n C a x = true ↔
      val C (List.ofFn x) (opnd C a 0) = true ∧
      val C (List.ofFn x) (opnd C a 1) = true := by
  rw [gateVal_eq_val, val_and (n := n) (by simp) ha hop]
  constructor
  · intro h
    exact ⟨(h _ (opndMem hAO ha 0)).2, (h _ (opndMem hAO ha 1)).2⟩
  · intro h i hi
    refine ⟨hAO.2.1 a ha i hi, ?_⟩
    obtain ⟨p, q, hpq⟩ := binaryInputs hAO ha
    rcases List.mem_cons.mp (hpq ▸ hi) with rfl | hq
    · simpa [opnd, hpq] using h.1
    · have e : i = q := List.mem_singleton.mp hq
      subst i
      simpa [opnd, hpq] using h.2

lemma andValOperands (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and) (x : Fin n → Bool) :
    gateVal n C a x = true ↔ ∀ b : Fin 2, val C (List.ofFn x) (opnd C a b) = true := by
  rw [andValBoth hAO ha hop]
  constructor
  · intro h b
    fin_cases b
    · exact h.1
    · exact h.2
  · intro h
    exact ⟨h 0, h 1⟩

lemma operandReachCone (hAO : IsAO2 n C) {a h : ℕ} (ha : a < C.gates.length)
    {b : Fin 2} (hr : OrReaches n C (opnd C a b) h) :
    InCone n C h a :=
  operand_cone ha (opndMem hAO ha b) (opndBound hAO ha b)
    (orReaches_reach h _ hr).1

lemma operandOrAndJunk (hAO : IsAO2 n C) (hT : TopForm G C) {a h : ℕ}
    (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and)
    {b : Fin 2} (hr : OrReaches n C (opnd C a b) h)
    (hh : (gateAt C h).op = GateOp.and) : h ∈ junk G C := by
  have hlen := (orReaches_reach h _ hr).2
  have hnb : ¬ BelowF G C h :=
    fun hb => hT h hlen a ha hh hb hop (operandReachCone hAO ha hr)
  have hdirty : ∃ x : Fin n → Bool, gateVal n C h x = true ∧ graphFun G ∅ x = false := by
    by_contra hne
    apply hnb
    intro x hx
    by_contra hf
    exact hne ⟨x, hx, Bool.eq_false_iff.mpr hf⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlen, hh, hlen, hdirty⟩

lemma reachVal {w h : ℕ} {x : Fin n → Bool} (hr : OrReaches n C w h)
    (hh : gateVal n C h x = true) : val C (List.ofFn x) w = true :=
  orStep_up (n := n) (by simp) (orReaches_reach h _ hr).1 hh

lemma eitherOperand (b c : Fin 2) : c = b ∨ c = 1 - b := by
  fin_cases b <;> fin_cases c <;> decide

lemma oppositeSideWmax (hAO : IsAO2 n C) {a j : ℕ} (ha : a ∈ tops G C) {b : Fin 2}
    (hr : OrReaches n C (opnd C a b) j) :
    side (n := n) C a (1 - b) ⊆ wmax G C j := by
  intro t ht
  obtain ⟨hal, hao, hab⟩ := topData ha
  simp only [wmax, Finset.mem_filter, Finset.mem_univ, true_and]
  intro x hj hx
  apply hab x
  apply (andValOperands hAO hal hao x).mpr
  intro c
  rcases eitherOperand b c with rfl | rfl
  · exact reachVal hr hj
  · exact reach_var_val x _ t (mem_orIn_reach t ht) hx

lemma orInTrans {w z : ℕ} (hr : Relation.ReflTransGen (OrStep n C) w z) :
    orIn n C z ⊆ orIn n C w :=
  fun x hx => reach_mem_orIn x (hr.trans (mem_orIn_reach x hx))

lemma sideVal {a : ℕ} {b : Fin 2} {x : Fin n → Bool} {t : Fin n}
    (ht : t ∈ side (n := n) C a b) (hx : x t = true) :
    val C (List.ofFn x) (opnd C a b) = true :=
  reach_var_val x _ t (mem_orIn_reach t ht) hx

lemma andFromInputs (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and) {x : Fin n → Bool}
    {u v : Fin n} (hu : u ∈ side (n := n) C a 0) (hv : v ∈ side (n := n) C a 1)
    (xu : x u = true) (xv : x v = true) : gateVal n C a x = true :=
  (andValBoth hAO ha hop x).mpr ⟨sideVal hu xu, sideVal hv xv⟩

lemma topAdj (hAO : IsAO2 n C) {a : ℕ} (ha : a ∈ tops G C)
    {u v : Fin n} (hu : u ∈ side (n := n) C a 0) (hv : v ∈ side (n := n) C a 1) :
    G.Adj u v := by
  obtain ⟨hl, ho, hb⟩ := topData ha
  exact (graphFun_pair G u v).mp
    (hb _ (andFromInputs hAO hl ho hu hv (pairInput_left u v) (pairInput_right u v)))

lemma operandSupport (hAO : IsAO2 n C) (hT : TopForm G C) {a : ℕ}
    (ha : a < C.gates.length) (ho : (gateAt C a).op = GateOp.and) {b : Fin 2}
    {u v : Fin n} (h : val C (List.ofFn (pairInput u v)) (opnd C a b) = true) :
    (∃ t ∈ side (n := n) C a b, t = u ∨ t = v) ∨
      ∃ j ∈ junk G C, OrReaches n C (opnd C a b) j ∧
        gateVal n C j (pairInput u v) = true := by
  rcases operand_trace (C := C) u v _ h with ⟨t, ht, hr⟩ | ⟨j, hj, hn, hr, hv⟩
  · exact .inl ⟨t, reach_mem_orIn t hr, ht⟩
  · have hr' := reach_orReaches hr j rfl hj
    exact .inr ⟨j, operandOrAndJunk hAO hT ha ho hr'
      ((hAO.1 _ (gateAt_mem hj)).resolve_right hn), hr', hv⟩

lemma memJunkPair {j k a : ℕ} (hs : junk G C = {j,k}) (ha : a ∈ junk G C) :
    a = j ∨ a = k := by
  simpa only [hs, Finset.mem_insert, Finset.mem_singleton] using ha

end Critical.Base

namespace Critical.Patch

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Core PEqualNP.ReadTwo

lemma foldl_wires_len (gs : List Gate) (acc : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc).length =
      acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_wires_getD_lt (gs : List Gate) (acc : List Bool) (i : ℕ) (hi : i < acc.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) acc).getD i false =
      acc.getD i false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]).length := by
      simp only [List.length_append, List.length_singleton]; omega
    rw [ih _ hlt]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_wires_getD_gate (gs : List Gate) (acc : List Bool) (j : ℕ) (hj : j < gs.length)
    (hback : ∀ k ∈ gs[j].inputs, k < acc.length + j) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) acc).getD
        (acc.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun k =>
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun m => w.getD m false)]) acc).getD
          k false) := by
  induction gs generalizing acc j with
  | nil => cases hj
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [Nat.add_zero, List.foldl_cons, List.getElem_cons_zero] at hback ⊢
      set acc' := acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]
      have hlen : acc.length < acc'.length := by
        simp only [acc', List.length_append, List.length_singleton]; omega
      rw [foldl_wires_getD_lt gs acc' acc.length hlen]
      have hlhs : acc'.getD acc.length false = g.op.eval (g.inputs.map fun k => acc.getD k false) := by
        simp only [acc', List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
          Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
      rw [hlhs]
      congr 1
      apply List.map_congr_left
      intro k hk
      have hka : k < acc.length := hback k hk
      have hka' : k < acc'.length := by omega
      rw [foldl_wires_getD_lt gs acc' k hka']
      simp only [acc', List.getD_eq_getElem?_getD, List.getElem?_append_left hka]
    | succ j' =>
      simp only [List.foldl_cons, List.getElem_cons_succ]
      set acc' := acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]
      have hlen' : acc'.length = acc.length + 1 := by
        simp only [acc', List.length_append, List.length_singleton]
      have hj' : j' < gs.length := by simp only [List.length_cons] at hj; omega
      have hidx : acc.length + (j' + 1) = acc'.length + j' := by omega
      rw [hidx]
      apply ih acc' j' hj'
      intro k hk
      have hbk := hback k (by simpa using hk)
      omega

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length :=
  foldl_wires_len C.gates x

lemma wval_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    wval C x i = x ⟨i, hi⟩ := by
  unfold wval Circuit.wires
  have hlt : i < (List.ofFn x).length := by simp [hi]
  rw [foldl_wires_getD_lt C.gates (List.ofFn x) i hlt]
  simp [List.getD_eq_getElem?_getD, hi]

lemma gateVal_eq_wval {n : ℕ} (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    gateVal n C j x = wval C x (n + j) := rfl

lemma wval_ge_len {n : ℕ} (C : Circuit) (x : Fin n → Bool) {w : ℕ} (hw : n + C.gates.length ≤ w) :
    wval C x w = false := by
  unfold wval
  rw [List.getD_eq_getElem?_getD]
  have hlen : (C.wires (List.ofFn x)).length = n + C.gates.length := by
    rw [wires_length, List.length_ofFn]
  rw [List.getElem?_eq_none (by omega)]
  rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  unfold gateAt
  simp [List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma gate_inputs_eq {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
  have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 _ (gateAt_mem hj)
  unfold opnd
  match h : (gateAt C j).inputs with
  | [a, b] => simp
  | [] => rw [h] at hlen; simp at hlen
  | [_] => rw [h] at hlen; simp at hlen
  | _ :: _ :: _ :: _ => rw [h] at hlen; simp at hlen

lemma opnd_mem {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b ∈ (gateAt C j).inputs := by
  rw [gate_inputs_eq hAO hj]
  fin_cases b <;> simp

lemma opnd_lt {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b < n + j :=
  hAO.2.1 j hj _ (opnd_mem hAO hj b)

lemma wval_gate_eval {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) :
    wval C x (n + j) = (gateAt C j).op.eval [wval C x (opnd C j 0), wval C x (opnd C j 1)] := by
  unfold wval Circuit.wires
  have hlen : (List.ofFn x).length = n := List.length_ofFn
  have hback : ∀ k ∈ C.gates[j].inputs, k < (List.ofFn x).length + j := by
    intro k hk; rw [hlen, ← gateAt_eq hj] at *; exact hAO.2.1 j hj k hk
  have h := foldl_wires_getD_gate C.gates (List.ofFn x) j hj hback
  rw [hlen] at h
  rw [h, ← gateAt_eq hj, gate_inputs_eq hAO hj]
  simp

lemma foldl_cones_getD_lt (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) (i : ℕ) (hi : i < acc.length) :
    (gs.foldl (coneStep n) acc).getD i [] = acc.getD i [] := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (coneStep n acc g).length := by
      simp only [coneStep, List.length_append, List.length_singleton]; omega
    rw [ih _ hlt]
    simp only [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_cones_getD_gate (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl (coneStep n) acc).getD (acc.length + j) [] =
      (gs[j].inputs.filter (fun w => decide (n ≤ w ∧ w < n + (acc.length + j)))).flatMap
        (fun w => (w - n) :: (gs.foldl (coneStep n) acc).getD (w - n) []) := by
  induction gs generalizing acc j with
  | nil => cases hj
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [Nat.add_zero, List.foldl_cons, List.getElem_cons_zero]
      set acc' := coneStep n acc g
      have hlen : acc.length < acc'.length := by
        simp only [acc', coneStep, List.length_append, List.length_singleton]; omega
      rw [foldl_cones_getD_lt n gs acc' acc.length hlen]
      have hlhs : acc'.getD acc.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + acc.length))).flatMap
            (fun w => (w - n) :: acc.getD (w - n) []) := by
        simp only [acc', coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
          Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
      rw [hlhs]
      apply List.flatMap_congr
      intro w hw
      simp only [List.mem_filter, decide_eq_true_eq] at hw
      have hwn : w - n < acc.length := by omega
      have hwn' : w - n < acc'.length := by omega
      rw [foldl_cones_getD_lt n gs acc' (w - n) hwn']
      simp only [acc', coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hwn]
    | succ j' =>
      simp only [List.foldl_cons, List.getElem_cons_succ]
      set acc' := coneStep n acc g
      have hlen' : acc'.length = acc.length + 1 := by
        simp only [acc', coneStep, List.length_append, List.length_singleton]
      have hj' : j' < gs.length := by simp only [List.length_cons] at hj; omega
      have hidx : acc.length + (j' + 1) = acc'.length + j' := by omega
      rw [hidx]
      exact ih acc' j' hj'

lemma inCone_iff {n : ℕ} {C : Circuit} {i j : ℕ} (hj : j < C.gates.length) :
    InCone n C i j ↔
      ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ w < n + j ∧ (i = w - n ∨ InCone n C i (w - n)) := by
  unfold InCone cones
  have h := foldl_cones_getD_gate n C.gates [] j hj
  simp only [List.length_nil, Nat.zero_add] at h
  rw [h, ← gateAt_eq hj]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw1, hw2, hw3⟩, hw4⟩; exact ⟨w, hw1, hw2, hw3, hw4⟩
  · rintro ⟨w, hw1, hw2, hw3, hw4⟩; exact ⟨w, ⟨hw1, hw2, hw3⟩, hw4⟩

def patch (C : Circuit) (j : ℕ) (g : Gate) : Circuit := ⟨C.gates.set j g, C.output⟩

lemma patch_length (C : Circuit) (j : ℕ) (g : Gate) :
    (patch C j g).gates.length = C.gates.length := by
  simp [patch]

lemma gateAt_patch_ne (C : Circuit) (j k : ℕ) (g : Gate) (hne : j ≠ k) :
    gateAt (patch C j g) k = gateAt C k := by
  simp [patch, gateAt, List.getD_eq_getElem?_getD, List.getElem?_set_ne hne]

lemma patch_wval_gate_eval {n : ℕ} {C : Circuit} {j : ℕ} {g : Gate}
    (hAO : IsAO2 n C) (x : Fin n → Bool) {k : ℕ} (hk : k < C.gates.length)
    (hne : j ≠ k) :
    wval (patch C j g) x (n + k) = (gateAt C k).op.eval
      [wval (patch C j g) x (opnd C k 0), wval (patch C j g) x (opnd C k 1)] := by
  have hk' : k < (patch C j g).gates.length := by simpa only [patch_length] using hk
  have hgate := gateAt_patch_ne C j k g hne
  have hlen : (List.ofFn x).length = n := List.length_ofFn
  have hback : ∀ w ∈ (patch C j g).gates[k].inputs, w < (List.ofFn x).length + k := by
    intro w hw
    rw [← gateAt_eq hk', hgate] at hw
    rw [hlen]
    exact hAO.2.1 k hk w hw
  have heval := foldl_wires_getD_gate (patch C j g).gates (List.ofFn x) k hk' hback
  rw [hlen, ← gateAt_eq hk', hgate, gate_inputs_eq hAO hk] at heval
  simpa only [wval, Circuit.wires, List.map_cons, List.map_nil] using heval

lemma patch_gateVal_eq_of_not_inCone {n : ℕ} {C : Circuit} {j : ℕ} {g : Gate}
    (hAO : IsAO2 n C) (k : ℕ) (hne : j ≠ k) (hCone : ¬ InCone n C j k)
    (x : Fin n → Bool) : gateVal n (patch C j g) k x = gateVal n C k x := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    by_cases hk : k < C.gates.length
    · have hval (b : Fin 2) : wval (patch C j g) x (opnd C k b) =
          wval C x (opnd C k b) := by
        by_cases hw : opnd C k b < n
        · rw [wval_input _ _ _ hw, wval_input _ _ _ hw]
        · have hw' : n ≤ opnd C k b := by omega
          have hlt := opnd_lt hAO hk b
          have hsub_ne : j ≠ opnd C k b - n := by
            intro he
            apply hCone
            exact (inCone_iff hk).mpr ⟨opnd C k b, opnd_mem hAO hk b, hw', hlt, Or.inl he⟩
          have hsub_cone : ¬ InCone n C j (opnd C k b - n) := by
            intro he
            apply hCone
            exact (inCone_iff hk).mpr ⟨opnd C k b, opnd_mem hAO hk b, hw', hlt, Or.inr he⟩
          have hv := ih (opnd C k b - n) (by omega) hsub_ne hsub_cone
          rw [gateVal_eq_wval, gateVal_eq_wval, Nat.add_sub_of_le hw'] at hv
          exact hv
      rw [gateVal_eq_wval, gateVal_eq_wval, patch_wval_gate_eval hAO x hk hne,
        wval_gate_eval hAO x hk, hval 0, hval 1]
    · rw [gateVal_eq_wval, gateVal_eq_wval, wval_ge_len _ _ (by rw [patch_length]; omega),
        wval_ge_len _ _ (by omega)]

end Critical.Patch

namespace Critical

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

def offPatch (C : Circuit) (h : ℕ) : Circuit := ⟨C.gates.set h ⟨GateOp.or, []⟩, C.output⟩

lemma offPatch_length (C : Circuit) (h : ℕ) : (offPatch C h).gates.length = C.gates.length := by
  simp [offPatch]

lemma gateAt_offPatch_ne (C : Circuit) (h k : ℕ) (hne : h ≠ k) :
    gateAt (offPatch C h) k = gateAt C k := by
  simp [offPatch, gateAt, List.getD_eq_getElem?_getD, List.getElem?_set_ne hne]

lemma orStep_offPatch {n : ℕ} {C : Circuit} {h w w' : ℕ}
    (hAnd : (gateAt C h).op = GateOp.and) (hs : Base.OrStep n C w w') :
    Base.OrStep n (offPatch C h) w w' := by
  obtain ⟨k, hk, rfl, hOr, hi, hb⟩ := hs
  have hne : h ≠ k := by
    intro he
    rw [← he, hAnd] at hOr
    cases hOr
  refine ⟨k, by simpa only [offPatch_length] using hk, rfl, ?_, ?_, hb⟩
  · simpa only [gateAt_offPatch_ne C h k hne] using hOr
  · simpa only [gateAt_offPatch_ne C h k hne] using hi

lemma orPath_offPatch {n : ℕ} {C : Circuit} {h w w' : ℕ}
    (hAnd : (gateAt C h).op = GateOp.and)
    (hs : Relation.ReflTransGen (Base.OrStep n C) w w') :
    Relation.ReflTransGen (Base.OrStep n (offPatch C h)) w w' := by
  induction hs using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | head hs _ ih => exact Relation.ReflTransGen.head (orStep_offPatch hAnd hs) ih

lemma offPatch_difference_trace {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {h : ℕ} (hAnd : (gateAt C h).op = GateOp.and) (x : Fin n → Bool) :
    ∀ w, Base.val C (List.ofFn x) w = true → Base.val (offPatch C h) (List.ofFn x) w = false →
    ∃ j, j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧ OrReaches n C w j ∧
      gateVal n C j x = true ∧ gateVal n (offPatch C h) j x = false := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hw'
    by_cases hwInput : w < n
    · rw [Base.val_input (n := n) (by simp) hwInput] at hw hw'
      rw [hw] at hw'
      cases hw'
    · by_cases hwLarge : n + C.gates.length ≤ w
      · rw [Base.val_ge (n := n) (by simp) hwLarge] at hw
        cases hw
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        by_cases hOr : (gateAt C k).op = GateOp.or
        · have hne : h ≠ k := by
            intro he
            rw [← he, hAnd] at hOr
            cases hOr
          obtain ⟨v, hvMem, hvLt, hv⟩ := (Base.val_or (n := n) (by simp) hk hOr).mp hw
          have hv' : Base.val (offPatch C h) (List.ofFn x) v = false := by
            cases hv' : Base.val (offPatch C h) (List.ofFn x) v
            · rfl
            · have hk' : k < (offPatch C h).gates.length := by simpa only [offPatch_length] using hk
              have hOr' : (gateAt (offPatch C h) k).op = GateOp.or := by
                simpa only [gateAt_offPatch_ne C h k hne] using hOr
              have hMem' : v ∈ (gateAt (offPatch C h) k).inputs := by
                simpa only [gateAt_offPatch_ne C h k hne] using hvMem
              have ht := (Base.val_or (n := n) (by simp) hk' hOr').mpr ⟨v, hMem', hvLt, hv'⟩
              rw [hw'] at ht
              cases ht
          obtain ⟨j, hj, hjAnd, hReach, hjv, hjv'⟩ := ih v hvLt hv hv'
          refine ⟨j, hj, hjAnd, ?_, hjv, hjv'⟩
          exact (Base.orReaches_iff n C k j).mpr ⟨hk, Or.inr ⟨hOr, v, hvMem, hvLt, hReach⟩⟩
        · have hAndK : (gateAt C k).op = GateOp.and := (hAO.1 _ (Base.gateAt_mem hk)).resolve_right hOr
          exact ⟨k, hk, hAndK, (Base.orReaches_iff n C k k).mpr ⟨hk, Or.inl rfl⟩, hw, hw'⟩

lemma critical_edge_useful {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (hF : circuitFun n C = graphFun G ∅)
    (hT : TopForm G C) {g h : ℕ} (hJ : junk G C = {g, h}) (hne : g ≠ h)
    (hIndependent : ¬ InCone n C h g)
    (hNoCommon : ∀ a ∈ tops G C, ∀ b : Fin 2,
      OrReaches n C (opnd C a b) h → ¬ OrReaches n C (opnd C a (1 - b)) g)
    (u v : Fin n) (hAdj : G.Adj u v)
    (hLost : circuitFun n (offPatch C h) (pairInput u v) = false) :
    gateVal n C h (pairInput u v) = true ∧ (u ∈ wmax G C h ∨ v ∈ wmax G C h) := by
  have hhJ : h ∈ junk G C := by rw [hJ]; simp
  obtain ⟨hhLen, hhAnd, hx, hhx, hFx⟩ := Base.junkData hhJ
  have hout (x : Fin n → Bool) : Base.val C (List.ofFn x) C.output = graphFun G ∅ x :=
    congrFun hF x
  obtain ⟨a, haLen, haNotOr, haPath, haVal⟩ :=
    Base.edge_trace G (graphFun G ∅) (fun x y hxy => (Base.graphFun_pair G x y).mp hxy)
      hout u v ((Base.graphFun_pair G u v).mpr hAdj)
  have haAnd : (gateAt C a).op = GateOp.and :=
    (hAO.1 _ (Base.gateAt_mem haLen)).resolve_right haNotOr
  have haBelow : BelowF G C a := fun x hv =>
    Base.below_of_reach (graphFun G ∅) hout a haPath x hv
  have haTop : a ∈ tops G C := by
    simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using
      And.intro haLen (And.intro haAnd haBelow)
  have hha : h ≠ a := by
    intro he
    subst a
    have ht := haBelow hx hhx
    rw [hFx] at ht
    cases ht
  have haOff : gateVal n (offPatch C h) a (pairInput u v) = false := by
    cases hc : gateVal n (offPatch C h) a (pairInput u v)
    · rfl
    · have ho := Base.orStep_up (n := n) (by simp) (orPath_offPatch hhAnd haPath) hc
      change circuitFun n (offPatch C h) (pairInput u v) = true at ho
      rw [hLost] at ho
      cases ho
  have hEval : gateVal n (offPatch C h) a (pairInput u v) =
      (Base.val (offPatch C h) (List.ofFn (pairInput u v)) (opnd C a 0) &&
       Base.val (offPatch C h) (List.ofFn (pairInput u v)) (opnd C a 1)) := by
    have he := Patch.patch_wval_gate_eval (j := h) (g := ⟨GateOp.or, []⟩) hAO (pairInput u v) haLen hha
    change gateVal n (offPatch C h) a (pairInput u v) = (gateAt C a).op.eval
      [Base.val (offPatch C h) (List.ofFn (pairInput u v)) (opnd C a 0),
       Base.val (offPatch C h) (List.ofFn (pairInput u v)) (opnd C a 1)] at he
    simpa only [haAnd, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true] using he
  obtain ⟨b, hbOff⟩ : ∃ b : Fin 2,
      Base.val (offPatch C h) (List.ofFn (pairInput u v)) (opnd C a b) = false := by
    by_cases h0 : Base.val (offPatch C h) (List.ofFn (pairInput u v)) (opnd C a 0) = false
    · exact ⟨0, h0⟩
    · have h0t := Bool.eq_true_of_not_eq_false h0
      refine ⟨1, ?_⟩
      rw [haOff, h0t, Bool.true_and] at hEval
      exact hEval.symm
  have hbVal := ((Base.andValOperands hAO haLen haAnd (pairInput u v)).mp haVal) b
  obtain ⟨j, hjLen, hjAnd, hjReach, hjVal, hjOff⟩ :=
    offPatch_difference_trace hAO hhAnd (pairInput u v) (opnd C a b) hbVal hbOff
  have hjJ := Base.operandOrAndJunk hAO hT haLen haAnd hjReach hjAnd
  have hjh : j = h := by
    rcases Base.memJunkPair hJ hjJ with hjg | hjh
    · subst j
      have he := Patch.patch_gateVal_eq_of_not_inCone (j := h) (g := ⟨GateOp.or, []⟩)
        hAO g (Ne.symm hne) hIndependent (pairInput u v)
      change gateVal n (offPatch C h) g (pairInput u v) = gateVal n C g (pairInput u v) at he
      rw [he, hjVal] at hjOff
      cases hjOff
    · exact hjh
  subst j
  refine ⟨hjVal, ?_⟩
  have hoVal := ((Base.andValOperands hAO haLen haAnd (pairInput u v)).mp haVal) (1 - b)
  rcases Base.operandSupport hAO hT haLen haAnd hoVal with ⟨t, ht, htu⟩ | ⟨k, hkJ, hkReach, _⟩
  · have htw := Base.oppositeSideWmax hAO haTop hjReach ht
    rcases htu with rfl | rfl
    · exact Or.inl htw
    · exact Or.inr htw
  · rcases Base.memJunkPair hJ hkJ with hkg | hkh
    · subst k
      exact False.elim (hNoCommon a haTop b hjReach hkReach)
    · subst k
      have ht : gateVal n C a hx = true := by
        apply (Base.andValOperands hAO haLen haAnd hx).mpr
        intro c
        rcases Base.eitherOperand b c with rfl | rfl
        · exact Base.reachVal hjReach hhx
        · exact Base.reachVal hkReach hhx
      have hf := haBelow hx ht
      rw [hFx] at hf
      cases hf

end Critical

namespace ApartFlags

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo

end ApartFlags

namespace MixedPrivacy

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

open PEqualNP.TopForm

end MixedPrivacy

namespace FlagSafe

open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

open PEqualNP.Outside.L_meta_5012.H3.IndependentDescent

end FlagSafe

namespace Colors

open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm
  PEqualNP.Outside.L_meta_5012.H3.IndependentDescent

lemma safe_triple {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P Q : Finset (Fin n)) {w : Fin n} (hs : Safe G P Q w)
    {p q : Fin n} (hp : p ∈ P) (hq : q ∈ Q) :
    G.Adj p q ∨ G.Adj p w ∨ G.Adj q w := by
  let x : Fin n → Bool := fun v => decide (v = p ∨ v = q ∨ v = w)
  have hprod : product P Q x = true :=
    (product_true P Q x).mpr ⟨⟨p, hp, by simp [x]⟩, q, hq, by simp [x]⟩
  have hF := hs x hprod (by simp [x])
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, x] at hF
  obtain ⟨a, b, hab, ha, hb⟩ := hF
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  · exact (G.irrefl hab).elim
  · exact Or.inl hab
  · exact Or.inr (Or.inl hab)
  · exact Or.inl hab.symm
  · exact (G.irrefl hab).elim
  · exact Or.inr (Or.inr hab)
  · exact Or.inr (Or.inl hab.symm)
  · exact Or.inr (Or.inr hab.symm)
  · exact (G.irrefl hab).elim

lemma safe_bad_adjacent {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P Q : Finset (Fin n)) {w : Fin n} (hs : Safe G P Q w)
    {p q : Fin n} (hp : p ∈ P) (hq : q ∈ Q)
    (hpw : ¬ G.Adj p w) (hqw : ¬ G.Adj q w) : G.Adj p q := by
  rcases safe_triple G P Q hs hp hq with hpq | hpw' | hqw'
  · exact hpq
  · exact (hpw hpw').elim
  · exact (hqw hqw').elim

lemma bool_eq_of_common_ne {a b c : Bool} (ha : a ≠ c) (hb : b ≠ c) : a = b := by
  cases a <;> cases b <;> cases c <;> simp_all

lemma safe_bad_colors {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (P Q : Finset (Fin n)) {w p0 q0 : Fin n} (hs : Safe G P Q w)
    (hp0 : p0 ∈ P) (hq0 : q0 ∈ Q) (hpw : ¬ G.Adj p0 w) (hqw : ¬ G.Adj q0 w) :
    G.Adj p0 q0 ∧
      (∀ p ∈ P, ¬ G.Adj p w → s p = s p0) ∧
      (∀ q ∈ Q, ¬ G.Adj q w → s q = s q0) := by
  have hpq := safe_bad_adjacent G P Q hs hp0 hq0 hpw hqw
  refine ⟨hpq, ?_, ?_⟩
  · intro p hp hnp
    have hadj := safe_bad_adjacent G P Q hs hp hq0 hnp hqw
    exact bool_eq_of_common_ne (hbip p q0 hadj) (hbip p0 q0 hpq)
  · intro q hq hnq
    have hadj := safe_bad_adjacent G P Q hs hp0 hq hpw hnq
    exact bool_eq_of_common_ne (Ne.symm (hbip p0 q hadj)) (Ne.symm (hbip p0 q0 hpq))

lemma safe_oriented_bad_factors {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (P Q : Finset (Fin n)) {w p0 q0 : Fin n} (hs : Safe G P Q w)
    (hp0 : p0 ∈ P) (hq0 : q0 ∈ Q) (hpw : ¬ G.Adj p0 w) (hqw : ¬ G.Adj q0 w) :
    ((∀ p ∈ P, ¬ G.Adj p w → s p = s w) ∧ (∀ q ∈ Q, s q ≠ s w)) ∨
      ((∀ q ∈ Q, ¬ G.Adj q w → s q = s w) ∧ (∀ p ∈ P, s p ≠ s w)) := by
  obtain ⟨hpq, hP, hQ⟩ := safe_bad_colors G s hbip P Q hs hp0 hq0 hpw hqw
  have hpqColor := hbip p0 q0 hpq
  by_cases hpColor : s p0 = s w
  · left
    constructor
    · intro p hp hn
      exact (hP p hp hn).trans hpColor
    · intro q hq hqwColor
      have hnq : ¬ G.Adj q w := fun hadj => hbip q w hadj hqwColor
      have hqColor := hQ q hq hnq
      exact hpqColor (hpColor.trans (hqwColor.symm.trans hqColor))
  · right
    have hqColor : s q0 = s w :=
      bool_eq_of_common_ne (Ne.symm hpqColor) (Ne.symm hpColor)
    constructor
    · intro q hq hn
      exact (hQ q hq hn).trans hqColor
    · intro p hp hpwColor
      have hnp : ¬ G.Adj p w := fun hadj => hbip p w hadj hpwColor
      have hpColor' := hP p hp hnp
      exact hpqColor (hpColor'.symm.trans (hpwColor.trans hqColor.symm))

end Colors

namespace Sharing

open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm
  PEqualNP.Outside.L_meta_5012.H3.IndependentDescent
  PEqualNP.Outside.L_meta_5012.H3.Colors

end Sharing

namespace CleanReplacement

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

open PEqualNP.EdgeOwnership PEqualNP.TopForm

open PEqualNP.Outside.L_meta_5012.H3.Lift

open PEqualNP.Outside.L_meta_5012.H3.Patch

end CleanReplacement

namespace SingletonOverlap

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadTwo PEqualNP.CleanedNonEdge

open PEqualNP.Outside.L_meta_5012.H3.CleanReplacement

open PEqualNP.Outside.L_meta_5012.H3.IndependentDescent

end SingletonOverlap

namespace CommonCenterForm

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

end CommonCenterForm

namespace MixedClosure

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma val_all_true {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (w : ℕ) (hw : w < n + C.gates.length) :
    Critical.Base.val C (List.ofFn (fun _ : Fin n => true)) w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hwInput : w < n
    · rw [Critical.Base.val_input (n := n) (by simp) hwInput]
      simp [List.getD_eq_getElem?_getD, hwInput]
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < C.gates.length := by omega
      rcases hAO.1 _ (Critical.Base.gateAt_mem hk) with hAnd | hOr
      · apply (Critical.Base.val_and (n := n) (by simp) hk hAnd).mpr
        intro v hv
        have hvLt := hAO.2.1 k hk v hv
        exact ⟨hvLt, ih v hvLt (by omega)⟩
      · have hvLt := Critical.Base.opndBound hAO hk 0
        apply (Critical.Base.val_or (n := n) (by simp) hk hOr).mpr
        exact ⟨opnd C k 0, Critical.Base.opndMem hAO hk 0, hvLt, ih _ hvLt (by omega)⟩

lemma bool_eq_of_common_ne {a b c : Bool} (ha : a ≠ c) (hb : b ≠ c) : a = b := by
  cases a <;> cases b <;> cases c <;> simp_all

lemma top_side_same_color {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (hAO : IsAO2 n C) (hT : TopForm G C)
    (hW : ∀ j ∈ junk G C, (wmax G C j).card ≤ 1)
    {a : ℕ} (ha : a ∈ tops G C) (b : Fin 2) {u v : Fin n}
    (hu : u ∈ side (n := n) C a b) (hv : v ∈ side (n := n) C a b) : s u = s v := by
  obtain ⟨haLen, haAnd, _⟩ := Critical.Base.topData ha
  have hwLt := Critical.Base.opndBound hAO haLen (1 - b)
  have hwVal := val_all_true hAO (opnd C a (1 - b)) (by omega)
  obtain ⟨w, hPath, _, hwCase⟩ := Critical.Base.or_trace (n := n) (by simp) (opnd C a (1 - b)) hwVal
  rcases hwCase with hwInput | ⟨j, hj, rfl, hjNotOr⟩
  · let t : Fin n := ⟨w, hwInput⟩
    have ht : t ∈ side (n := n) C a (1 - b) := Critical.Base.reach_mem_orIn t hPath
    have hut : G.Adj u t := by
      fin_cases b
      · exact Critical.Base.topAdj hAO ha hu ht
      · exact (Critical.Base.topAdj hAO ha ht hu).symm
    have hvt : G.Adj v t := by
      fin_cases b
      · exact Critical.Base.topAdj hAO ha hv ht
      · exact (Critical.Base.topAdj hAO ha ht hv).symm
    exact bool_eq_of_common_ne (hbip u t hut) (hbip v t hvt)
  · have hjAnd := (hAO.1 _ (Critical.Base.gateAt_mem hj)).resolve_right hjNotOr
    have hjReach := Critical.Base.reach_orReaches hPath j rfl hj
    have hjJ := Critical.Base.operandOrAndJunk hAO hT haLen haAnd hjReach hjAnd
    have hSub := Critical.Base.oppositeSideWmax hAO ha hjReach
    have hFlip : (1 : Fin 2) - (1 - b) = b := by fin_cases b <;> decide
    rw [hFlip] at hSub
    have huv : u = v := Finset.card_le_one.mp (hW j hjJ) u (hSub hu) v (hSub hv)
    exact congrArg s huv

end MixedClosure

namespace MixedClosure

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma raw_nonempty_not_orReaches_output {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hF : circuitFun n C = graphFun G ∅) {k : ℕ}
    (hRaw : (orIn n C (n + k)).Nonempty) : ¬ OrReaches n C C.output k := by
  intro hReach
  obtain ⟨u, hu⟩ := hRaw
  have hPath := (Critical.Base.orReaches_reach k _ hReach).1.trans (Critical.Base.mem_orIn_reach u hu)
  have ht := Critical.Base.reach_var_val (pairInput u u) C.output u hPath (Critical.Base.pairInput_left u u)
  change circuitFun n C (pairInput u u) = true at ht
  rw [hF] at ht
  exact G.irrefl ((Critical.Base.graphFun_pair G u u).mp ht)

end MixedClosure

namespace TopFrontier

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo

end TopFrontier

namespace SameColor

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
  PEqualNP.Outside.L_meta_5012.H3.IndependentDescent

lemma bool_eq_of_common_ne {a b c : Bool} (ha : a ≠ c) (hb : b ≠ c) : a = b := by
  cases a <;> cases b <;> cases c <;> simp_all

lemma overlap_products_not_joint_below_same_color {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (P Q R S : Finset (Fin n)) {w z : Fin n} (hw : Safe G P Q w) (hz : Safe G R S z)
    (hP : (P ∩ Q).Nonempty) (hR : (R ∩ S).Nonempty) (hColor : s w = s z) :
    ¬ ∀ x : Fin n → Bool, product P Q x = true → product R S x = true → graphFun G ∅ x = true := by
  intro hJoint
  obtain ⟨i, hi⟩ := hP
  obtain ⟨j, hj⟩ := hR
  have hwi := safe_overlap_adjacent G P Q hw hi
  have hzj := safe_overlap_adjacent G R S hz hj
  have hiColor : s i ≠ s w := Ne.symm (hbip w i hwi)
  have hjColor : s j ≠ s w := by rw [hColor]; exact Ne.symm (hbip z j hzj)
  have hijColor := bool_eq_of_common_ne hiColor hjColor
  have hPi : product P Q (pairInput i j) = true := by
    obtain ⟨hiP, hiQ⟩ := Finset.mem_inter.mp hi
    exact (product_true P Q _).mpr ⟨⟨i, hiP, by simp [pairInput]⟩, i, hiQ, by simp [pairInput]⟩
  have hRj : product R S (pairInput i j) = true := by
    obtain ⟨hjR, hjS⟩ := Finset.mem_inter.mp hj
    exact (product_true R S _).mpr ⟨⟨j, hjR, by simp [pairInput]⟩, j, hjS, by simp [pairInput]⟩
  exact hbip i j ((graph_pair G i j).mp (hJoint _ hPi hRj)) hijColor

lemma no_opposite_top_same_color {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (hAO : IsAO2 n C) (P Q R S : Finset (Fin n)) {g h : ℕ}
    (hgEval : ∀ x : Fin n → Bool, gateVal n C g x = product P Q x)
    (hhEval : ∀ x : Fin n → Bool, gateVal n C h x = product R S x)
    {w z : Fin n} (hw : Safe G P Q w) (hz : Safe G R S z)
    (hP : (P ∩ Q).Nonempty) (hR : (R ∩ S).Nonempty) (hColor : s w = s z)
    {a : ℕ} (ha : a ∈ tops G C) (b : Fin 2)
    (hG : OrReaches n C (opnd C a b) g) : ¬ OrReaches n C (opnd C a (1 - b)) h := by
  intro hH
  obtain ⟨haLen, haAnd, haBelow⟩ := PEqualNP.Outside.L_meta_5012.H3.Critical.Base.topData ha
  apply overlap_products_not_joint_below_same_color G s hbip P Q R S hw hz hP hR hColor
  intro x hxg hxh
  apply haBelow x
  apply (PEqualNP.Outside.L_meta_5012.H3.Critical.Base.andValOperands hAO haLen haAnd x).mpr
  intro c
  rcases PEqualNP.Outside.L_meta_5012.H3.Critical.Base.eitherOperand b c with rfl | rfl
  · exact PEqualNP.Outside.L_meta_5012.H3.Critical.Base.reachVal hG (by rw [hgEval]; exact hxg)
  · exact PEqualNP.Outside.L_meta_5012.H3.Critical.Base.reachVal hH (by rw [hhEval]; exact hxh)

lemma useful_at_unique_outside_center {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P Q : Finset (Fin n)) {w : Fin n} (hwP : w ∉ P) (hwQ : w ∉ Q)
    (hUnique : ∀ z, Safe G P Q z → z = w) (u v : Fin n) (huv : Useful G P Q u v) :
    (u = w ∧ v ∈ P ∩ Q) ∨ (v = w ∧ u ∈ P ∩ Q) := by
  obtain ⟨_, hp, hu | hv⟩ := huv
  · have he := hUnique u hu
    subst u
    left
    refine ⟨rfl, ?_⟩
    obtain ⟨⟨p, hp, hpx⟩, q, hq, hqx⟩ := (product_true P Q _).mp hp
    simp only [pairInput, decide_eq_true_eq] at hpx hqx
    have hpv : p = v := hpx.resolve_left (fun he => hwP (he ▸ hp))
    have hqv : q = v := hqx.resolve_left (fun he => hwQ (he ▸ hq))
    exact Finset.mem_inter.mpr ⟨hpv ▸ hp, hqv ▸ hq⟩
  · have he := hUnique v hv
    subst v
    right
    refine ⟨rfl, ?_⟩
    obtain ⟨⟨p, hp, hpx⟩, q, hq, hqx⟩ := (product_true P Q _).mp hp
    simp only [pairInput, decide_eq_true_eq] at hpx hqx
    have hpu : p = u := hpx.resolve_right (fun he => hwP (he ▸ hp))
    have hqu : q = u := hqx.resolve_right (fun he => hwQ (he ▸ hq))
    exact Finset.mem_inter.mpr ⟨hpu ▸ hp, hqu ▸ hq⟩

end SameColor

namespace OverlapInside

open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

open PEqualNP.Outside.L_meta_5012.H3.IndependentDescent

end OverlapInside

namespace Rewrite

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Core PEqualNP.ReadTwo

lemma foldl_wires_len (gs : List Gate) (acc : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc).length =
      acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_wires_getD_lt (gs : List Gate) (acc : List Bool) (i : ℕ) (hi : i < acc.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) acc).getD i false =
      acc.getD i false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]).length := by
      simp only [List.length_append, List.length_singleton]; omega
    rw [ih _ hlt]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_wires_getD_gate (gs : List Gate) (acc : List Bool) (j : ℕ) (hj : j < gs.length)
    (hback : ∀ k ∈ gs[j].inputs, k < acc.length + j) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) acc).getD
        (acc.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun k =>
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun m => w.getD m false)]) acc).getD
          k false) := by
  induction gs generalizing acc j with
  | nil => cases hj
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [Nat.add_zero, List.foldl_cons, List.getElem_cons_zero] at hback ⊢
      set acc' := acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]
      have hlen : acc.length < acc'.length := by
        simp only [acc', List.length_append, List.length_singleton]; omega
      rw [foldl_wires_getD_lt gs acc' acc.length hlen]
      have hlhs : acc'.getD acc.length false = g.op.eval (g.inputs.map fun k => acc.getD k false) := by
        simp only [acc', List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
          Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
      rw [hlhs]
      congr 1
      apply List.map_congr_left
      intro k hk
      have hka : k < acc.length := hback k hk
      have hka' : k < acc'.length := by omega
      rw [foldl_wires_getD_lt gs acc' k hka']
      simp only [acc', List.getD_eq_getElem?_getD, List.getElem?_append_left hka]
    | succ j' =>
      simp only [List.foldl_cons, List.getElem_cons_succ]
      set acc' := acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]
      have hlen' : acc'.length = acc.length + 1 := by
        simp only [acc', List.length_append, List.length_singleton]
      have hj' : j' < gs.length := by simp only [List.length_cons] at hj; omega
      have hidx : acc.length + (j' + 1) = acc'.length + j' := by omega
      rw [hidx]
      apply ih acc' j' hj'
      intro k hk
      have hbk := hback k (by simpa using hk)
      omega

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length :=
  foldl_wires_len C.gates x

lemma wval_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    wval C x i = x ⟨i, hi⟩ := by
  unfold wval Circuit.wires
  have hlt : i < (List.ofFn x).length := by simp [hi]
  rw [foldl_wires_getD_lt C.gates (List.ofFn x) i hlt]
  simp [List.getD_eq_getElem?_getD, hi]

lemma wval_ge_len {n : ℕ} (C : Circuit) (x : Fin n → Bool) {w : ℕ} (hw : n + C.gates.length ≤ w) :
    wval C x w = false := by
  unfold wval
  rw [List.getD_eq_getElem?_getD]
  have hlen : (C.wires (List.ofFn x)).length = n + C.gates.length := by
    rw [wires_length, List.length_ofFn]
  rw [List.getElem?_eq_none (by omega)]
  rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  unfold gateAt
  simp [List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma gate_inputs_eq {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
  have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 _ (gateAt_mem hj)
  unfold opnd
  match h : (gateAt C j).inputs with
  | [a, b] => simp
  | [] => rw [h] at hlen; simp at hlen
  | [_] => rw [h] at hlen; simp at hlen
  | _ :: _ :: _ :: _ => rw [h] at hlen; simp at hlen

lemma opnd_mem {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b ∈ (gateAt C j).inputs := by
  rw [gate_inputs_eq hAO hj]
  fin_cases b <;> simp

lemma opnd_lt {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b < n + j :=
  hAO.2.1 j hj _ (opnd_mem hAO hj b)

lemma wval_gate_eval {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) :
    wval C x (n + j) = (gateAt C j).op.eval [wval C x (opnd C j 0), wval C x (opnd C j 1)] := by
  unfold wval Circuit.wires
  have hlen : (List.ofFn x).length = n := List.length_ofFn
  have hback : ∀ k ∈ C.gates[j].inputs, k < (List.ofFn x).length + j := by
    intro k hk; rw [hlen, ← gateAt_eq hj] at *; exact hAO.2.1 j hj k hk
  have h := foldl_wires_getD_gate C.gates (List.ofFn x) j hj hback
  rw [hlen] at h
  rw [h, ← gateAt_eq hj, gate_inputs_eq hAO hj]
  simp

lemma wval_gate_and {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) :
    wval C x (n + j) = (wval C x (opnd C j 0) && wval C x (opnd C j 1)) := by
  rw [wval_gate_eval hAO x hj, hop]; simp [GateOp.eval]

lemma wval_gate_or {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) :
    wval C x (n + j) = (wval C x (opnd C j 0) || wval C x (opnd C j 1)) := by
  rw [wval_gate_eval hAO x hj, hop]; simp [GateOp.eval]

def rewriteCircuit (C : Circuit) (f : ℕ → Gate → Gate) : Circuit :=
  ⟨C.gates.mapIdx f, C.output⟩

lemma rewrite_length (C : Circuit) (f : ℕ → Gate → Gate) :
    (rewriteCircuit C f).gates.length = C.gates.length := by
  simp [rewriteCircuit]

lemma rewrite_size (C : Circuit) (f : ℕ → Gate → Gate) :
    (rewriteCircuit C f).size = C.size := by
  simp only [Circuit.size, rewrite_length]

lemma gateAt_rewrite (C : Circuit) (f : ℕ → Gate → Gate) {k : ℕ}
    (hk : k < C.gates.length) : gateAt (rewriteCircuit C f) k = f k (gateAt C k) := by
  have hk' : k < (rewriteCircuit C f).gates.length := by simpa only [rewrite_length] using hk
  rw [gateAt_eq hk', gateAt_eq hk]
  simp only [rewriteCircuit, List.getElem_mapIdx]

lemma rewrite_isAO2 {n : ℕ} (C : Circuit) (f : ℕ → Gate → Gate)
    (hOp : ∀ k < C.gates.length,
      (f k (gateAt C k)).op = GateOp.and ∨ (f k (gateAt C k)).op = GateOp.or)
    (hLen : ∀ k < C.gates.length, (f k (gateAt C k)).inputs.length = 2)
    (hBack : ∀ k < C.gates.length, ∀ w ∈ (f k (gateAt C k)).inputs, w < n + k) :
    IsAO2 n (rewriteCircuit C f) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    change g ∈ C.gates.mapIdx f at hg
    obtain ⟨k, hk, he⟩ := List.exists_of_mem_mapIdx hg
    rw [← gateAt_eq hk] at he
    rw [← he]
    exact hOp k hk
  · intro k hk w hw
    have hkC : k < C.gates.length := by simpa only [rewrite_length] using hk
    rw [gateAt_rewrite C f hkC] at hw
    exact hBack k hkC w hw
  · intro g hg
    change g ∈ C.gates.mapIdx f at hg
    obtain ⟨k, hk, he⟩ := List.exists_of_mem_mapIdx hg
    rw [← gateAt_eq hk] at he
    rw [← he]
    exact hLen k hk

lemma rewrite_wval_gate_eval {n : ℕ} (C : Circuit) (f : ℕ → Gate → Gate)
    (x : Fin n → Bool) {k : ℕ} (hk : k < C.gates.length)
    (hBack : ∀ w ∈ (f k (gateAt C k)).inputs, w < n + k) :
    wval (rewriteCircuit C f) x (n + k) = (f k (gateAt C k)).op.eval
      ((f k (gateAt C k)).inputs.map fun w => wval (rewriteCircuit C f) x w) := by
  have hk' : k < (rewriteCircuit C f).gates.length := by simpa only [rewrite_length] using hk
  have hgate := gateAt_rewrite C f hk
  have hlen : (List.ofFn x).length = n := List.length_ofFn
  have hback : ∀ w ∈ (rewriteCircuit C f).gates[k].inputs, w < (List.ofFn x).length + k := by
    intro w hw
    rw [← gateAt_eq hk', hgate] at hw
    rw [hlen]
    exact hBack w hw
  have heval := foldl_wires_getD_gate (rewriteCircuit C f).gates (List.ofFn x) k hk' hback
  rw [hlen, ← gateAt_eq hk', hgate] at heval
  simpa only [wval, Circuit.wires] using heval

lemma rewrite_wval_gate_eval_pair {n : ℕ} (C : Circuit) (f : ℕ → Gate → Gate)
    (x : Fin n → Bool) {k p q : ℕ} (hk : k < C.gates.length)
    (hInputs : (f k (gateAt C k)).inputs = [p, q]) (hp : p < n + k) (hq : q < n + k) :
    wval (rewriteCircuit C f) x (n + k) = (f k (gateAt C k)).op.eval
      [wval (rewriteCircuit C f) x p, wval (rewriteCircuit C f) x q] := by
  have hBack : ∀ w ∈ (f k (gateAt C k)).inputs, w < n + k := by
    intro w hw
    rw [hInputs] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact hp
    · exact hq
  rw [rewrite_wval_gate_eval C f x hk hBack, hInputs]
  rfl

lemma rewrite_isLeastAO {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (f : ℕ → Gate → Gate) (hL : IsLeastAO G C)
    (hAO' : IsAO2 n (rewriteCircuit C f))
    (hF' : circuitFun n (rewriteCircuit C f) = graphFun G ∅) :
    IsLeastAO G (rewriteCircuit C f) := by
  refine ⟨hAO', hF', ?_⟩
  intro D hD hDF
  rw [rewrite_size]
  exact hL.2.2 D hD hDF

end Rewrite

namespace Projection

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo
  PEqualNP.Outside.L_meta_5012.H3.Rewrite

end Projection

namespace Projection

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo
  PEqualNP.Outside.L_meta_5012.H3.Rewrite

end Projection

namespace Projection

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo
  PEqualNP.Outside.L_meta_5012.H3.Rewrite

end Projection

namespace ProjectionSemantics

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.ReadTwo

open PEqualNP.Outside.L_meta_5012.H3.Rewrite

def supportValue {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∃ i ∈ S, x i = true)

lemma supportValue_union {n : ℕ} (A B : Finset (Fin n)) (x : Fin n → Bool) :
    supportValue (A ∪ B) x = (supportValue A x || supportValue B x) := by
  simp only [supportValue, Finset.mem_union]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, Bool.or_eq_true]
  aesop

lemma masked_value {n : ℕ} (D : Circuit) (supp : ℕ → Finset (Fin n))
    (Good : Finset (Fin n)) (x : Fin n → Bool) (w : ℕ)
    (hv : (supp w ∩ Good).Nonempty →
      wval D x w = supportValue (supp w ∩ Good) x) :
    (decide (supp w ∩ Good).Nonempty && wval D x w) =
      supportValue (supp w ∩ Good) x := by
  by_cases h : (supp w ∩ Good).Nonempty
  · simp only [h, decide_true, Bool.true_and, hv h]
  · have he : supp w ∩ Good = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [he, supportValue]

lemma projected_raw_semantics {n : ℕ} (C D : Circuit) (hAO : IsAO2 n C)
    (R : Finset ℕ) (supp : ℕ → Finset (Fin n)) (Good : Finset (Fin n))
    (hBound : ∀ k ∈ R, k < C.gates.length)
    (hInput : ∀ i : Fin n, supp i.val = {i})
    (hUnion : ∀ k ∈ R, supp (n + k) = supp (opnd C k 0) ∪ supp (opnd C k 1))
    (hClosed : ∀ k ∈ R, ∀ b : Fin 2,
      opnd C k b < n ∨ ∃ j ∈ R, opnd C k b = n + j)
    (hEval : ∀ k ∈ R, (supp (n + k) ∩ Good).Nonempty → ∀ x : Fin n → Bool,
      wval D x (n + k) =
        ((decide (supp (opnd C k 0) ∩ Good).Nonempty && wval D x (opnd C k 0)) ||
         (decide (supp (opnd C k 1) ∩ Good).Nonempty && wval D x (opnd C k 1))))
    {w : ℕ} (hw : w < n ∨ ∃ k ∈ R, w = n + k)
    (hGood : (supp w ∩ Good).Nonempty) (x : Fin n → Bool) :
    wval D x w = supportValue (supp w ∩ Good) x := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rcases hw with hw | ⟨k, hk, rfl⟩
    · let i : Fin n := ⟨w, hw⟩
      have hSupp : supp w = {i} := hInput i
      have hi : i ∈ Good := by
        obtain ⟨t, ht⟩ := hGood
        rw [hSupp, Finset.mem_inter, Finset.mem_singleton] at ht
        exact ht.1 ▸ ht.2
      rw [wval_input D x w hw, hSupp]
      have he : ({i} : Finset (Fin n)) ∩ Good = {i} := by
        exact Finset.inter_eq_left.mpr (Finset.singleton_subset_iff.mpr hi)
      rw [he]
      simp only [supportValue, Finset.mem_singleton, exists_eq_left]
      exact Bool.decide_coe _
    · rw [hEval k hk hGood x]
      have h0 : (supp (opnd C k 0) ∩ Good).Nonempty →
          wval D x (opnd C k 0) = supportValue (supp (opnd C k 0) ∩ Good) x := by
        intro hg
        exact ih _ (opnd_lt hAO (hBound k hk) 0) (hClosed k hk 0) hg
      have h1 : (supp (opnd C k 1) ∩ Good).Nonempty →
          wval D x (opnd C k 1) = supportValue (supp (opnd C k 1) ∩ Good) x := by
        intro hg
        exact ih _ (opnd_lt hAO (hBound k hk) 1) (hClosed k hk 1) hg
      rw [masked_value D supp Good x _ h0, masked_value D supp Good x _ h1,
        hUnion k hk, Finset.union_inter_distrib_right, supportValue_union]

end ProjectionSemantics

namespace ProjectionSemantics

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.ReadTwo

open PEqualNP.Outside.L_meta_5012.H3.Rewrite PEqualNP.Outside.L_meta_5012.H3.Projection

end ProjectionSemantics

namespace ProjectionSemantics

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.ReadTwo

open PEqualNP.Outside.L_meta_5012.H3.Rewrite PEqualNP.Outside.L_meta_5012.H3.Projection

end ProjectionSemantics

namespace ProjectionSemantics

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.ReadTwo

open PEqualNP.Outside.L_meta_5012.H3.Rewrite PEqualNP.Outside.L_meta_5012.H3.Projection

end ProjectionSemantics

namespace ProjectionTransfer

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.ReadTwo PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

open PEqualNP.Outside.L_meta_5012.H3.Critical

lemma preserve_or_path {n : ℕ} {C D : Circuit} (hLen : C.gates.length ≤ D.gates.length)
    {w z : ℕ}
    (hSame : ∀ k < C.gates.length, (gateAt C k).op = GateOp.or →
      OrReaches n C w k → gateAt D k = gateAt C k)
    (hr : Relation.ReflTransGen (Base.OrStep n C) w z) :
    Relation.ReflTransGen (Base.OrStep n D) w z := by
  induction hr with
  | refl => exact .refl
  | @tail b c hwb hbc ih =>
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hbc
    have he := hSame k hk hop (Base.reach_orReaches hwb k rfl hk)
    exact ih.tail ⟨k, by omega, rfl, by rw [he]; exact hop, by rw [he]; exact hin, hlt⟩

lemma preserve_all_edges {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C D : Circuit) (hAO : IsAO2 n C) (hD : IsAO2 n D)
    (hF : circuitFun n C = graphFun G ∅) (hT : TopForm G C)
    (hLen : C.gates.length ≤ D.gates.length) (hOut : D.output = C.output)
    (hTop : ∀ a ∈ tops G C, gateAt D a = gateAt C a)
    (hOrOut : ∀ k < C.gates.length, (gateAt C k).op = GateOp.or →
      OrReaches n C C.output k → gateAt D k = gateAt C k)
    (hOrTop : ∀ a ∈ tops G C, ∀ b : Fin 2, ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.or → OrReaches n C (opnd C a b) k →
      gateAt D k = gateAt C k)
    (hNoOpp : ∀ a ∈ tops G C, ∀ b : Fin 2, ∀ j ∈ junk G C, ∀ k ∈ junk G C,
      OrReaches n C (opnd C a b) j → ¬ OrReaches n C (opnd C a (1 - b)) k)
    (hUseful : ∀ j ∈ junk G C, ∀ u v : Fin n, G.Adj u v →
      gateVal n C j (pairInput u v) = true → (u ∈ wmax G C j ∨ v ∈ wmax G C j) →
      gateVal n D j (pairInput u v) = true)
    {u v : Fin n} (huv : G.Adj u v) : circuitFun n D (pairInput u v) = true := by
  have hout (x : Fin n → Bool) : Base.val C (List.ofFn x) C.output = graphFun G ∅ x :=
    congrFun hF x
  obtain ⟨a, hal, hao, hrOut, hat⟩ :=
    Base.edge_trace G (graphFun G ∅) (fun k l => (Base.graphFun_pair G k l).mp)
      hout u v ((Base.graphFun_pair G u v).mpr huv)
  have haAnd := (hAO.1 _ (Base.gateAt_mem hal)).resolve_right hao
  have haBelow : BelowF G C a := fun x hx =>
    Base.below_of_reach (graphFun G ∅) hout a hrOut x hx
  have ha : a ∈ tops G C := by
    simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using
      And.intro hal (And.intro haAnd haBelow)
  have hOldOperands := (Base.andValOperands hAO hal haAnd (pairInput u v)).mp hat
  have hNewOperands : ∀ b : Fin 2,
      Base.val D (List.ofFn (pairInput u v)) (opnd C a b) = true := by
    intro b
    rcases Base.operandSupport hAO hT hal haAnd (hOldOperands b) with
      ⟨t, ht, htu | htv⟩ | ⟨j, hj, hrj, hjv⟩
    · have hpath := preserve_or_path hLen (hOrTop a ha b) (Base.mem_orIn_reach t ht)
      exact Base.reach_var_val (pairInput u v) _ t hpath (htu ▸ Base.pairInput_left u v)
    · have hpath := preserve_or_path hLen (hOrTop a ha b) (Base.mem_orIn_reach t ht)
      exact Base.reach_var_val (pairInput u v) _ t hpath (htv ▸ Base.pairInput_right u v)
    · rcases Base.operandSupport hAO hT hal haAnd (hOldOperands (1 - b)) with
        ⟨t, ht, htu | htv⟩ | ⟨k, hk, hrk, _⟩
      · have hw : u ∈ wmax G C j := htu ▸ Base.oppositeSideWmax hAO ha hrj ht
        have hjD := hUseful j hj u v huv hjv (Or.inl hw)
        exact Base.orStep_up (n := n) (by simp)
          (preserve_or_path hLen (hOrTop a ha b) (Base.orReaches_reach j _ hrj).1) hjD
      · have hw : v ∈ wmax G C j := htv ▸ Base.oppositeSideWmax hAO ha hrj ht
        have hjD := hUseful j hj u v huv hjv (Or.inr hw)
        exact Base.orStep_up (n := n) (by simp)
          (preserve_or_path hLen (hOrTop a ha b) (Base.orReaches_reach j _ hrj).1) hjD
      · exact False.elim (hNoOpp a ha b j hj k hk hrj hrk)
  have haD : a < D.gates.length := by omega
  have haAndD : (gateAt D a).op = GateOp.and := by rw [hTop a ha]; exact haAnd
  have hOpnd (b : Fin 2) : opnd D a b = opnd C a b := by simp only [opnd, hTop a ha]
  have hatD : gateVal n D a (pairInput u v) = true :=
    (Base.andValOperands hD haD haAndD (pairInput u v)).mpr (by
      intro b; rw [hOpnd b]; exact hNewOperands b)
  change Base.val D (List.ofFn (pairInput u v)) D.output = true
  rw [hOut]
  exact Base.orStep_up (n := n) (by simp) (preserve_or_path hLen hOrOut hrOut) hatD

end ProjectionTransfer

namespace DuplicateOR

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Core PEqualNP.ReadTwo

lemma foldl_wires_len (gs : List Gate) (acc : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc).length =
      acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_wires_getD_lt (gs : List Gate) (acc : List Bool) (i : ℕ) (hi : i < acc.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) acc).getD i false =
      acc.getD i false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]).length := by
      simp only [List.length_append, List.length_singleton]; omega
    rw [ih _ hlt]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_wires_getD_gate (gs : List Gate) (acc : List Bool) (j : ℕ) (hj : j < gs.length)
    (hback : ∀ k ∈ gs[j].inputs, k < acc.length + j) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) acc).getD
        (acc.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun k =>
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun m => w.getD m false)]) acc).getD
          k false) := by
  induction gs generalizing acc j with
  | nil => cases hj
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [Nat.add_zero, List.foldl_cons, List.getElem_cons_zero] at hback ⊢
      set acc' := acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]
      have hlen : acc.length < acc'.length := by
        simp only [acc', List.length_append, List.length_singleton]; omega
      rw [foldl_wires_getD_lt gs acc' acc.length hlen]
      have hlhs : acc'.getD acc.length false = g.op.eval (g.inputs.map fun k => acc.getD k false) := by
        simp only [acc', List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
          Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
      rw [hlhs]
      congr 1
      apply List.map_congr_left
      intro k hk
      have hka : k < acc.length := hback k hk
      have hka' : k < acc'.length := by omega
      rw [foldl_wires_getD_lt gs acc' k hka']
      simp only [acc', List.getD_eq_getElem?_getD, List.getElem?_append_left hka]
    | succ j' =>
      simp only [List.foldl_cons, List.getElem_cons_succ]
      set acc' := acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]
      have hlen' : acc'.length = acc.length + 1 := by
        simp only [acc', List.length_append, List.length_singleton]
      have hj' : j' < gs.length := by simp only [List.length_cons] at hj; omega
      have hidx : acc.length + (j' + 1) = acc'.length + j' := by omega
      rw [hidx]
      apply ih acc' j' hj'
      intro k hk
      have hbk := hback k (by simpa using hk)
      omega

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length :=
  foldl_wires_len C.gates x

lemma wval_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    wval C x i = x ⟨i, hi⟩ := by
  unfold wval Circuit.wires
  have hlt : i < (List.ofFn x).length := by simp [hi]
  rw [foldl_wires_getD_lt C.gates (List.ofFn x) i hlt]
  simp [List.getD_eq_getElem?_getD, hi]

lemma wval_ge_len {n : ℕ} (C : Circuit) (x : Fin n → Bool) {w : ℕ} (hw : n + C.gates.length ≤ w) :
    wval C x w = false := by
  unfold wval
  rw [List.getD_eq_getElem?_getD]
  have hlen : (C.wires (List.ofFn x)).length = n + C.gates.length := by
    rw [wires_length, List.length_ofFn]
  rw [List.getElem?_eq_none (by omega)]
  rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  unfold gateAt
  simp [List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma gate_inputs_eq {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
  have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 _ (gateAt_mem hj)
  unfold opnd
  match h : (gateAt C j).inputs with
  | [a, b] => simp
  | [] => rw [h] at hlen; simp at hlen
  | [_] => rw [h] at hlen; simp at hlen
  | _ :: _ :: _ :: _ => rw [h] at hlen; simp at hlen

lemma opnd_mem {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b ∈ (gateAt C j).inputs := by
  rw [gate_inputs_eq hAO hj]
  fin_cases b <;> simp

lemma opnd_lt {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b < n + j :=
  hAO.2.1 j hj _ (opnd_mem hAO hj b)

lemma wval_gate_eval {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) :
    wval C x (n + j) = (gateAt C j).op.eval [wval C x (opnd C j 0), wval C x (opnd C j 1)] := by
  unfold wval Circuit.wires
  have hlen : (List.ofFn x).length = n := List.length_ofFn
  have hback : ∀ k ∈ C.gates[j].inputs, k < (List.ofFn x).length + j := by
    intro k hk; rw [hlen, ← gateAt_eq hj] at *; exact hAO.2.1 j hj k hk
  have h := foldl_wires_getD_gate C.gates (List.ofFn x) j hj hback
  rw [hlen] at h
  rw [h, ← gateAt_eq hj, gate_inputs_eq hAO hj]
  simp

lemma wval_gate_or {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) :
    wval C x (n + j) = (wval C x (opnd C j 0) || wval C x (opnd C j 1)) := by
  rw [wval_gate_eval hAO x hj, hop]; simp [GateOp.eval]

def delWire (n j r w : ℕ) : ℕ :=
  if w = n + j then r else if n + j < w then w - 1 else w

def delCircuit (n : ℕ) (C : Circuit) (j r : ℕ) : Circuit :=
  { gates := (C.gates.eraseIdx j).map (fun g => { g with inputs := g.inputs.map (delWire n j r) })
    output := delWire n j r C.output }

lemma delCircuit_len (n : ℕ) (C : Circuit) {j : ℕ} (hj : j < C.gates.length) (r : ℕ) :
    (delCircuit n C j r).gates.length = C.gates.length - 1 := by
  simp [delCircuit, List.length_eraseIdx, hj]

lemma delCircuit_gateAt_lt {n : ℕ} {C : Circuit} {j r i : ℕ}
    (hj : j < C.gates.length) (hi : i < j) :
    gateAt (delCircuit n C j r) i =
      { (gateAt C i) with inputs := (gateAt C i).inputs.map (delWire n j r) } := by
  have hi' : i < (delCircuit n C j r).gates.length := by rw [delCircuit_len n C hj r]; omega
  rw [gateAt_eq hi', gateAt_eq (by omega)]
  simp only [delCircuit, List.getElem_map]
  rw [List.getElem_eraseIdx_of_lt (by rw [List.length_eraseIdx, ite_eq_left hj]; omega) hi]

lemma delCircuit_gateAt_ge {n : ℕ} {C : Circuit} {j r i : ℕ}
    (hj : j < C.gates.length) (hji : j ≤ i) (hi : i < C.gates.length - 1) :
    gateAt (delCircuit n C j r) i =
      { (gateAt C (i + 1)) with inputs := (gateAt C (i + 1)).inputs.map (delWire n j r) } := by
  have hi' : i < (delCircuit n C j r).gates.length := by rw [delCircuit_len n C hj r]; omega
  rw [gateAt_eq hi', gateAt_eq (by omega)]
  simp only [delCircuit, List.getElem_map]
  rw [List.getElem_eraseIdx_of_ge (by rw [List.length_eraseIdx, ite_eq_left hj]; omega) hji]

lemma delCircuit_isAO2 {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j r : ℕ}
    (hj : j < C.gates.length) (hr : r < n + j) : IsAO2 n (delCircuit n C j r) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [delCircuit, List.mem_map] at hg
    rcases hg with ⟨g0, hg0, rfl⟩
    exact hAO.1 g0 (List.mem_of_mem_eraseIdx hg0)
  · intro i hi w hw
    rw [delCircuit_len n C hj r] at hi
    by_cases hij : i < j
    · rw [delCircuit_gateAt_lt hj hij] at hw
      simp only [List.mem_map] at hw
      rcases hw with ⟨u, hu, rfl⟩
      have hult : u < n + i := hAO.2.1 i (by omega) u hu
      unfold delWire
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      exact hult
    · rw [delCircuit_gateAt_ge hj (by omega) hi] at hw
      simp only [List.mem_map] at hw
      rcases hw with ⟨u, hu, rfl⟩
      have hult : u < n + (i + 1) := hAO.2.1 (i + 1) (by omega) u hu
      unfold delWire
      split_ifs <;> omega
  · intro g hg
    simp only [delCircuit, List.mem_map] at hg
    rcases hg with ⟨g0, hg0, rfl⟩
    simp only [List.length_map]
    exact hAO.2.2 g0 (List.mem_of_mem_eraseIdx hg0)

lemma delCircuit_opnd_lt {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j r i : ℕ}
    (hj : j < C.gates.length) (hi : i < j) (b : Fin 2) :
    opnd (delCircuit n C j r) i b = delWire n j r (opnd C i b) := by
  unfold opnd
  rw [delCircuit_gateAt_lt hj hi, gate_inputs_eq hAO (by omega)]
  fin_cases b <;> rfl

lemma delCircuit_opnd_ge {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j r i : ℕ}
    (hj : j < C.gates.length) (hji : j ≤ i) (hi : i < C.gates.length - 1) (b : Fin 2) :
    opnd (delCircuit n C j r) i b = delWire n j r (opnd C (i + 1) b) := by
  unfold opnd
  rw [delCircuit_gateAt_ge hj hji hi, gate_inputs_eq hAO (by omega)]
  fin_cases b <;> rfl

lemma delCircuit_wval_eq {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j r : ℕ} (hj : j < C.gates.length) (hr : r < n + j)
    (heq : wval C x r = wval C x (n + j)) :
    ∀ w < n + C.gates.length, wval (delCircuit n C j r) x (delWire n j r w) = wval C x w := by
  have hAO' := delCircuit_isAO2 hAO hj hr
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hwn : w < n
    · have hdw : delWire n j r w = w := by unfold delWire; rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      rw [hdw, wval_input _ x w hwn, wval_input _ x w hwn]
    · by_cases hwj : w = n + j
      · subst hwj
        have hdw : delWire n j r (n + j) = r := by unfold delWire; simp
        have hdr : delWire n j r r = r := by unfold delWire; rw [ite_eq_right (by omega), ite_eq_right (by omega)]
        have h1 := ih r hr (by omega)
        rw [hdr] at h1
        rw [hdw, h1, heq]
      · by_cases hlt : w < n + j
        · have hk : w - n < j := by omega
          have hdw : delWire n j r w = n + (w - n) := by
            unfold delWire; rw [ite_eq_right hwj, ite_eq_right (by omega)]; omega
          have hw_eq : w = n + (w - n) := by omega
          rw [hdw]
          conv_rhs => rw [hw_eq]
          have hk' : w - n < (delCircuit n C j r).gates.length := by rw [delCircuit_len n C hj r]; omega
          rw [wval_gate_eval hAO' x hk', wval_gate_eval hAO x (by omega)]
          have hg := delCircuit_gateAt_lt (n := n) (r := r) hj hk
          rw [delCircuit_opnd_lt hAO hj hk 0, delCircuit_opnd_lt hAO hj hk 1]
          have h0 := ih (opnd C (w - n) 0) (by have := opnd_lt hAO (by omega : w - n < C.gates.length) 0; omega) (by have := opnd_lt hAO (by omega : w - n < C.gates.length) 0; omega)
          have h1 := ih (opnd C (w - n) 1) (by have := opnd_lt hAO (by omega : w - n < C.gates.length) 1; omega) (by have := opnd_lt hAO (by omega : w - n < C.gates.length) 1; omega)
          rw [h0, h1, hg]
        · have hgt : n + j < w := by omega
          have hk : w - n - 1 < C.gates.length - 1 := by omega
          have hjk : j ≤ w - n - 1 := by omega
          have hdw : delWire n j r w = n + (w - n - 1) := by
            unfold delWire; rw [ite_eq_right hwj, ite_eq_left hgt]; omega
          have hw_eq : w = n + (w - n - 1 + 1) := by omega
          rw [hdw]
          conv_rhs => rw [hw_eq]
          have hk' : w - n - 1 < (delCircuit n C j r).gates.length := by rw [delCircuit_len n C hj r]; omega
          rw [wval_gate_eval hAO' x hk', wval_gate_eval hAO x (by omega)]
          have hg := delCircuit_gateAt_ge (n := n) (r := r) hj hjk hk
          rw [delCircuit_opnd_ge hAO hj hjk hk 0, delCircuit_opnd_ge hAO hj hjk hk 1]
          have h0 := ih (opnd C (w - n - 1 + 1) 0) (by have := opnd_lt hAO (by omega : w - n - 1 + 1 < C.gates.length) 0; omega) (by have := opnd_lt hAO (by omega : w - n - 1 + 1 < C.gates.length) 0; omega)
          have h1 := ih (opnd C (w - n - 1 + 1) 1) (by have := opnd_lt hAO (by omega : w - n - 1 + 1 < C.gates.length) 1; omega) (by have := opnd_lt hAO (by omega : w - n - 1 + 1 < C.gates.length) 1; omega)
          rw [h0, h1, hg]

lemma least_no_equiv_wire {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) {j r : ℕ}
    (hj : j < C.gates.length) (hr : r < n + j)
    (heq : ∀ x : Fin n → Bool, wval C x r = wval C x (n + j)) : False := by
  let D := delCircuit n C j r
  have hD := delCircuit_isAO2 hL.1 hj hr
  have hfun : circuitFun n D = graphFun G ∅ := by
    funext x
    rw [← congrFun hL.2.1 x]
    change wval (delCircuit n C j r) x (delWire n j r C.output) = wval C x C.output
    by_cases hout : C.output < n + C.gates.length
    · exact delCircuit_wval_eq hL.1 x hj hr (heq x) C.output hout
    · rw [wval_ge_len C x (by omega)]
      apply wval_ge_len
      rw [delCircuit_len n C hj r]
      unfold delWire
      rw [ite_eq_right (by omega), ite_eq_left (by omega)]
      omega
  have hsize := hL.2.2 D hD hfun
  simp only [Circuit.size, D, delCircuit_len n C hj r] at hsize
  omega

lemma least_no_duplicate_or {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) {j w : ℕ}
    (hj : j < C.gates.length) (hw : w < n + j)
    (hgate : gateAt C j = ⟨GateOp.or, [w,w]⟩) : False := by
  apply least_no_equiv_wire hL hj hw
  intro x
  rw [wval_gate_or hL.1 x hj (by rw [hgate])]
  simp [opnd,hgate]

end DuplicateOR

namespace ProjectionSemantics

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.ReadTwo PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

open PEqualNP.Outside.L_meta_5012.H3.Rewrite PEqualNP.Outside.L_meta_5012.H3.Projection
  PEqualNP.Outside.L_meta_5012.H3.ProjectionTransfer

end ProjectionSemantics

namespace RawSupport

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo

noncomputable def region (n : ℕ) (C : Circuit) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter fun k =>
    ∀ a, a = k ∨ InCone n C a k → (gateAt C a).op ≠ GateOp.and

lemma mem_region {n : ℕ} {C : Circuit} {k : ℕ} : k ∈ region n C ↔
    k < C.gates.length ∧ ∀ a, a = k ∨ InCone n C a k → (gateAt C a).op ≠ GateOp.and := by
  classical
  simp only [region,Finset.mem_filter,Finset.mem_range]

def Raw (n : ℕ) (C : Circuit) (w : ℕ) : Prop :=
  w < n ∨ ∃ k ∈ region n C, w = n+k

lemma orIn_input {n : ℕ} (C : Circuit) (u : Fin n) : orIn n C u.val = {u} := by
  apply Finset.ext
  intro v
  constructor
  · intro hv
    have hr := Critical.Base.mem_orIn_reach v hv
    rcases Relation.ReflTransGen.cases_head hr with he | ⟨w,hs,_⟩
    · exact Finset.mem_singleton.mpr (Fin.ext he.symm)
    · obtain ⟨k,_,he,_,_,_⟩ := hs
      have := u.isLt
      omega
  · intro hv
    have he := Finset.mem_singleton.mp hv
    subst v
    simp [orIn]

lemma orIn_or {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) (hOR : (gateAt C j).op = GateOp.or) :
    orIn n C (n+j) = orIn n C (opnd C j 0) ∪ orIn n C (opnd C j 1) := by
  apply Finset.ext
  intro v
  constructor
  · intro hv
    have hr := Critical.Base.mem_orIn_reach v hv
    rcases Relation.ReflTransGen.cases_head hr with he | ⟨w,hs,hr⟩
    · have := v.isLt
      omega
    · obtain ⟨k,hk,he,_,hin,hlt⟩ := hs
      have hkj : k=j := by omega
      subst k
      rw [Lift.gate_inputs_eq hAO hj] at hin
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hin
      rcases hin with hw | hw
      · exact Finset.mem_union_left _ (Critical.Base.reach_mem_orIn v (hw ▸ hr))
      · exact Finset.mem_union_right _ (Critical.Base.reach_mem_orIn v (hw ▸ hr))
  · intro hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact Critical.Base.reach_mem_orIn v (Relation.ReflTransGen.head
        ⟨j,hj,rfl,hOR,Lift.opnd_mem hAO hj 0,Lift.opnd_lt hAO hj 0⟩
        (Critical.Base.mem_orIn_reach v hv))
    · exact Critical.Base.reach_mem_orIn v (Relation.ReflTransGen.head
        ⟨j,hj,rfl,hOR,Lift.opnd_mem hAO hj 1,Lift.opnd_lt hAO hj 1⟩
        (Critical.Base.mem_orIn_reach v hv))

lemma region_or {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ}
    (hj : j ∈ region n C) : (gateAt C j).op = GateOp.or := by
  obtain ⟨hjl,hn⟩ := mem_region.mp hj
  exact (hAO.1 _ (Lift.gateAt_mem hjl)).resolve_left (hn j (Or.inl rfl))

lemma region_closed {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ}
    (hj : j ∈ region n C) (b : Fin 2) : Raw n C (opnd C j b) := by
  obtain ⟨hjl,hn⟩ := mem_region.mp hj
  by_cases hw : opnd C j b < n
  · exact Or.inl hw
  · obtain ⟨k,hk⟩ : ∃ k, opnd C j b = n+k := ⟨opnd C j b-n,by omega⟩
    have hkj : k < j := by have := Lift.opnd_lt hAO hjl b; omega
    have hcone : InCone n C k j := (Critical.Base.inCone_iff n C k j).mpr
      ⟨hjl,k,hkj,hk ▸ Lift.opnd_mem hAO hjl b,Or.inl rfl⟩
    refine Or.inr ⟨k,mem_region.mpr ⟨Nat.lt_trans hkj hjl,?_⟩,hk⟩
    intro a ha
    rcases ha with rfl | ha
    · exact hn _ (Or.inr hcone)
    · exact hn a (Or.inr (Lift.inCone_trans ha hcone))

lemma raw_support_nonempty {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) :
    ∀ w, Raw n C w → (orIn n C w).Nonempty := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    rcases hw with hi | ⟨j,hj,rfl⟩
    · have he := orIn_input C (⟨w,hi⟩ : Fin n)
      rw [he]
      exact Finset.singleton_nonempty _
    · have hjl := (mem_region.mp hj).1
      rw [orIn_or hAO hjl (region_or hAO hj)]
      obtain ⟨v,hv⟩ := ih (opnd C j 0) (Lift.opnd_lt hAO hjl 0) (region_closed hAO hj 0)
      exact ⟨v,Finset.mem_union_left _ hv⟩

lemma and_ancestor_junk {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hTop : TopForm G C) {a j : ℕ} (hj : j < C.gates.length)
    (hjAnd : (gateAt C j).op = GateOp.and) (haAnd : (gateAt C a).op = GateOp.and)
    (hCone : InCone n C a j) : a ∈ junk G C := by
  have ha : a < C.gates.length := Nat.lt_trans (Lift.inCone_lt hCone) hj
  have hnb : ¬ BelowF G C a := fun hb => hTop a ha j hj haAnd hb hjAnd hCone
  have hd : ∃ x : Fin n → Bool, gateVal n C a x = true ∧ graphFun G ∅ x = false := by
    by_contra hh
    apply hnb
    intro x hx
    by_contra hf
    exact hh ⟨x,hx,Bool.eq_false_iff.mpr hf⟩
  exact CleanReplacement.mem_junk.mpr ⟨ha,haAnd,ha,hd⟩

lemma independent_operand_raw {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (hTop : TopForm G C) {j k : ℕ}
    (hJ : junk G C = {j,k}) (hkj : ¬ InCone n C k j) (b : Fin 2) :
    Raw n C (opnd C j b) := by
  have hjmem : j ∈ junk G C := by rw [hJ]; simp
  have hj := (CleanReplacement.mem_junk.mp hjmem).1
  have hjAnd := (CleanReplacement.mem_junk.mp hjmem).2.1
  by_cases hw : opnd C j b < n
  · exact Or.inl hw
  · obtain ⟨r,hr⟩ : ∃ r, opnd C j b = n+r := ⟨opnd C j b-n,by omega⟩
    have hrj : r < j := by have := Lift.opnd_lt hAO hj b; omega
    have hCone : InCone n C r j := (Critical.Base.inCone_iff n C r j).mpr
      ⟨hj,r,hrj,hr ▸ Lift.opnd_mem hAO hj b,Or.inl rfl⟩
    refine Or.inr ⟨r,mem_region.mpr ⟨Nat.lt_trans hrj hj,?_⟩,hr⟩
    intro a ha haAnd
    have haj : InCone n C a j := by
      rcases ha with rfl | ha
      · exact hCone
      · exact Lift.inCone_trans ha hCone
    have ham := and_ancestor_junk hTop hj hjAnd haAnd haj
    rw [hJ] at ham
    rcases (show a=j ∨ a=k by simpa only [Finset.mem_insert,Finset.mem_singleton] using ham) with rfl | rfl
    · have := Lift.inCone_lt haj
      omega
    · exact hkj haj

end RawSupport

namespace CommonCenterProjection

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.ReadTwo PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

open PEqualNP.Outside.L_meta_5012.H3.Rewrite PEqualNP.Outside.L_meta_5012.H3.Projection
  PEqualNP.Outside.L_meta_5012.H3.ProjectionSemantics

end CommonCenterProjection

namespace VectorProjection

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo
  PEqualNP.Outside.L_meta_5012.H3.Rewrite

def keepGate (p q : ℕ) (hp hq : Bool) (old : Gate) : Gate :=
  if hp then (if hq then old else ⟨GateOp.or, [p, p]⟩)
  else (if hq then ⟨GateOp.or, [q, q]⟩ else old)

def projectGate (C : Circuit) (R B : Finset ℕ) (good : ℕ → Bool)
    (center : ℕ → ℕ) (root : ℕ → ℕ) (j : ℕ) (old : Gate) : Gate :=
  if j ∈ B then ⟨GateOp.and, [center j, root j]⟩
  else if j ∈ R then
    keepGate (opnd C j 0) (opnd C j 1) (good (opnd C j 0)) (good (opnd C j 1)) old
  else old

def projectCircuit (C : Circuit) (R B : Finset ℕ) (good : ℕ → Bool)
    (center : ℕ → ℕ) (root : ℕ → ℕ) : Circuit :=
  rewriteCircuit C (projectGate C R B good center root)

lemma keepGate_properties (n j p q : ℕ) (hp hq : Bool) (old : Gate)
    (hOldOp : old.op = GateOp.and ∨ old.op = GateOp.or) (hOldLen : old.inputs.length = 2)
    (hOldBack : ∀ w ∈ old.inputs, w < n + j) (hpLt : p < n + j) (hqLt : q < n + j) :
    ((keepGate p q hp hq old).op = GateOp.and ∨ (keepGate p q hp hq old).op = GateOp.or) ∧
      (keepGate p q hp hq old).inputs.length = 2 ∧
      ∀ w ∈ (keepGate p q hp hq old).inputs, w < n + j := by
  cases hp <;> cases hq <;> simp_all [keepGate]

lemma keepGate_eval (p q : ℕ) (hp hq : Bool) (old : Gate) (v : ℕ → Bool) :
    (keepGate p q hp hq old).op.eval ((keepGate p q hp hq old).inputs.map v) =
      if hp then (if hq then old.op.eval (old.inputs.map v) else v p)
      else (if hq then v q else old.op.eval (old.inputs.map v)) := by
  cases hp <;> cases hq <;> simp [keepGate, GateOp.eval]

lemma projectGate_properties {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (R B : Finset ℕ) (good : ℕ → Bool) (center : ℕ → ℕ) (root : ℕ → ℕ)
    (hBackB : ∀ j < C.gates.length, j ∈ B → center j < n + j ∧ root j < n + j)
    (j : ℕ) (hj : j < C.gates.length) :
    ((projectGate C R B good center root j (gateAt C j)).op = GateOp.and ∨
      (projectGate C R B good center root j (gateAt C j)).op = GateOp.or) ∧
      (projectGate C R B good center root j (gateAt C j)).inputs.length = 2 ∧
      ∀ w ∈ (projectGate C R B good center root j (gateAt C j)).inputs, w < n + j := by
  by_cases hjB : j ∈ B
  · simp only [projectGate, ite_eq_left hjB]
    refine ⟨by simp, by simp, ?_⟩
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact (hBackB j hj hjB).1
    · exact (hBackB j hj hjB).2
  · by_cases hjR : j ∈ R
    · simp only [projectGate, ite_eq_right hjB, ite_eq_left hjR]
      exact keepGate_properties n j _ _ _ _ _ (hAO.1 _ (gateAt_mem hj))
        (hAO.2.2 _ (gateAt_mem hj)) (hAO.2.1 j hj) (opnd_lt hAO hj 0) (opnd_lt hAO hj 1)
    · simp only [projectGate, ite_eq_right hjB, ite_eq_right hjR]
      exact ⟨hAO.1 _ (gateAt_mem hj), hAO.2.2 _ (gateAt_mem hj), hAO.2.1 j hj⟩

lemma project_isAO2 {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (R B : Finset ℕ) (good : ℕ → Bool) (center : ℕ → ℕ) (root : ℕ → ℕ)
    (hBackB : ∀ j < C.gates.length, j ∈ B → center j < n + j ∧ root j < n + j) :
    IsAO2 n (projectCircuit C R B good center root) := by
  apply rewrite_isAO2
  · intro j hj
    exact (projectGate_properties hAO R B good center root hBackB j hj).1
  · intro j hj
    exact (projectGate_properties hAO R B good center root hBackB j hj).2.1
  · intro j hj
    exact (projectGate_properties hAO R B good center root hBackB j hj).2.2

lemma project_or_eval {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (R B : Finset ℕ) (good : ℕ → Bool) (center : ℕ → ℕ) (root : ℕ → ℕ)
    (hBackB : ∀ j < C.gates.length, j ∈ B → center j < n + j ∧ root j < n + j)
    (x : Fin n → Bool) {j : ℕ} (hj : j < C.gates.length) (hjR : j ∈ R) (hjB : j ∉ B)
    (hOr : (gateAt C j).op = GateOp.or) :
    wval (projectCircuit C R B good center root) x (n + j) =
      if good (opnd C j 0) then
        (if good (opnd C j 1) then
          wval (projectCircuit C R B good center root) x (opnd C j 0) ||
            wval (projectCircuit C R B good center root) x (opnd C j 1)
        else wval (projectCircuit C R B good center root) x (opnd C j 0))
      else (if good (opnd C j 1) then
        wval (projectCircuit C R B good center root) x (opnd C j 1)
      else wval (projectCircuit C R B good center root) x (opnd C j 0) ||
        wval (projectCircuit C R B good center root) x (opnd C j 1)) := by
  have hBack := (projectGate_properties hAO R B good center root hBackB j hj).2.2
  rw [projectCircuit, rewrite_wval_gate_eval C _ x hj hBack]
  simp only [projectGate, ite_eq_right hjB, ite_eq_left hjR, keepGate_eval]
  rw [gate_inputs_eq hAO hj, hOr]
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
    id_eq, Bool.or_false]

lemma project_and_eval {n : ℕ} (C : Circuit) (R B : Finset ℕ) (good : ℕ → Bool)
    (center : ℕ → ℕ) (root : ℕ → ℕ) (x : Fin n → Bool) {j : ℕ}
    (hj : j < C.gates.length) (hjB : j ∈ B) (hc : center j < n + j) (hr : root j < n + j) :
    wval (projectCircuit C R B good center root) x (n + j) =
      (wval (projectCircuit C R B good center root) x (center j) &&
        wval (projectCircuit C R B good center root) x (root j)) := by
  have hInputs : (projectGate C R B good center root j (gateAt C j)).inputs = [center j, root j] := by
    simp only [projectGate, ite_eq_left hjB]
  have hOp : (projectGate C R B good center root j (gateAt C j)).op = GateOp.and := by
    simp only [projectGate, ite_eq_left hjB]
  have hv := rewrite_wval_gate_eval_pair C (projectGate C R B good center root) x hj hInputs hc hr
  rw [hOp] at hv
  simpa only [GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true, projectCircuit] using hv

lemma keepGate_eq_of_flags_eq (p q : ℕ) (hp hq : Bool) (old : Gate) (h : hp = hq) :
    keepGate p q hp hq old = old := by
  rw [h]
  cases hq <;> rfl

lemma projectGate_eq_of_not_B_not_R (C : Circuit) (R B : Finset ℕ) (good : ℕ → Bool)
    (center : ℕ → ℕ) (root : ℕ → ℕ) (j : ℕ) (old : Gate) (hjB : j ∉ B) (hjR : j ∉ R) :
    projectGate C R B good center root j old = old := by
  simp only [projectGate, ite_eq_right hjB, ite_eq_right hjR]

lemma projectGate_eq_of_not_B_flags_equal (C : Circuit) (R B : Finset ℕ) (good : ℕ → Bool)
    (center : ℕ → ℕ) (root : ℕ → ℕ) (j : ℕ) (old : Gate) (hjB : j ∉ B)
    (hEq : good (opnd C j 0) = good (opnd C j 1)) :
    projectGate C R B good center root j old = old := by
  by_cases hjR : j ∈ R
  · simp only [projectGate, ite_eq_right hjB, ite_eq_left hjR]
    exact keepGate_eq_of_flags_eq _ _ _ _ old hEq
  · exact projectGate_eq_of_not_B_not_R C R B good center root j old hjB hjR

lemma keepGate_eval_le_or (p q : ℕ) (hp hq : Bool) (old : Gate) (v : ℕ → Bool)
    (hOp : old.op = GateOp.or) (hInputs : old.inputs = [p, q]) :
    (keepGate p q hp hq old).op.eval ((keepGate p q hp hq old).inputs.map v) = true →
      (v p || v q) = true := by
  cases hp <;> cases hq <;> simp [keepGate, hOp, hInputs, GateOp.eval, Bool.or_eq_true] <;> aesop

end VectorProjection

namespace VectorProjection

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo
  PEqualNP.Outside.L_meta_5012.H3.Rewrite

lemma projectGate_eval_le_old {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (R B : Finset ℕ) (good : ℕ → Bool) (center : ℕ → ℕ) (root : ℕ → ℕ)
    (hOrR : ∀ j < C.gates.length, j ∈ R → (gateAt C j).op = GateOp.or)
    (j : ℕ) (hj : j < C.gates.length) (hjB : j ∉ B) (v : ℕ → Bool) :
    (projectGate C R B good center root j (gateAt C j)).op.eval
      ((projectGate C R B good center root j (gateAt C j)).inputs.map v) = true →
      (gateAt C j).op.eval ((gateAt C j).inputs.map v) = true := by
  intro hv
  by_cases hjR : j ∈ R
  · simp only [projectGate, ite_eq_right hjB, ite_eq_left hjR] at hv
    have hOr := hOrR j hj hjR
    have hVal := keepGate_eval_le_or _ _ _ _ _ v hOr (gate_inputs_eq hAO hj) hv
    rw [hOr, gate_inputs_eq hAO hj]
    simpa only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      id_eq, Bool.or_false] using hVal
  · rwa [projectGate_eq_of_not_B_not_R C R B good center root j (gateAt C j) hjB hjR] at hv

lemma project_wval_le_of_B_false {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (R B : Finset ℕ) (good : ℕ → Bool) (center : ℕ → ℕ) (root : ℕ → ℕ)
    (hBackB : ∀ j < C.gates.length, j ∈ B → center j < n + j ∧ root j < n + j)
    (hOrR : ∀ j < C.gates.length, j ∈ R → (gateAt C j).op = GateOp.or)
    (x : Fin n → Bool)
    (hBFalse : ∀ j < C.gates.length, j ∈ B →
      gateVal n (projectCircuit C R B good center root) j x = false)
    (w : ℕ) (hw : w < n + C.gates.length)
    (hv : wval (projectCircuit C R B good center root) x w = true) : wval C x w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hwInput : w < n
    · rw [wval_input _ _ _ hwInput] at hv ⊢
      exact hv
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < C.gates.length := by omega
      by_cases hjB : j ∈ B
      · have hf := hBFalse j hj hjB
        change wval (projectCircuit C R B good center root) x (n + j) = false at hf
        rw [hf] at hv
        cases hv
      · have hBack := (projectGate_properties hAO R B good center root hBackB j hj).2.2
        change wval (rewriteCircuit C (projectGate C R B good center root)) x (n + j) = true at hv
        rw [rewrite_wval_gate_eval C _ x hj hBack] at hv
        have hOld := projectGate_eval_le_old hAO R B good center root hOrR j hj hjB
          (wval (projectCircuit C R B good center root) x) hv
        have hChild (b : Fin 2)
            (hb : wval (projectCircuit C R B good center root) x (opnd C j b) = true) :
            wval C x (opnd C j b) = true := by
          have hlt := opnd_lt hAO hj b
          exact ih _ hlt (by omega) hb
        rw [wval_gate_eval hAO x hj]
        rcases hAO.1 _ (gateAt_mem hj) with hAnd | hOr
        · rw [hAnd, gate_inputs_eq hAO hj] at hOld
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
            id_eq, Bool.and_true, Bool.and_eq_true] at hOld
          rw [hAnd]
          simp only [GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true, Bool.and_eq_true]
          exact ⟨hChild 0 hOld.1, hChild 1 hOld.2⟩
        · rw [hOr, gate_inputs_eq hAO hj] at hOld
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
            id_eq, Bool.or_false, Bool.or_eq_true] at hOld
          rw [hOr]
          simp only [GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false, Bool.or_eq_true]
          rcases hOld with h0 | h1
          · exact Or.inl (hChild 0 h0)
          · exact Or.inr (hChild 1 h1)

lemma project_no_false_positive {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (hF : circuitFun n C = graphFun G ∅)
    (R B : Finset ℕ) (good : ℕ → Bool) (center : ℕ → ℕ) (root : ℕ → ℕ)
    (hBackB : ∀ j < C.gates.length, j ∈ B → center j < n + j ∧ root j < n + j)
    (hOrR : ∀ j < C.gates.length, j ∈ R → (gateAt C j).op = GateOp.or)
    (hBelowB : ∀ j < C.gates.length, j ∈ B → BelowF G (projectCircuit C R B good center root) j)
    (x : Fin n → Bool) (hx : circuitFun n (projectCircuit C R B good center root) x = true) :
    graphFun G ∅ x = true := by
  by_cases hFx : graphFun G ∅ x = true
  · exact hFx
  · exfalso
    apply hFx
    have hBFalse : ∀ j < C.gates.length, j ∈ B →
        gateVal n (projectCircuit C R B good center root) j x = false := by
      intro j hj hjB
      cases hjv : gateVal n (projectCircuit C R B good center root) j x
      · rfl
      · exact False.elim (hFx (hBelowB j hj hjB x hjv))
    have hv : wval (projectCircuit C R B good center root) x C.output = true := hx
    have hOut : C.output < n + C.gates.length := by
      by_contra hNot
      have hge : n + (projectCircuit C R B good center root).gates.length ≤ C.output := by
        simpa only [projectCircuit, rewrite_length] using (Nat.le_of_not_gt hNot)
      rw [wval_ge_len _ _ hge] at hv
      cases hv
    have hOld := project_wval_le_of_B_false hAO R B good center root hBackB hOrR x hBFalse
      C.output hOut hv
    change circuitFun n C x = true at hOld
    rwa [hF] at hOld

end VectorProjection

namespace VectorProjection

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo
  PEqualNP.Outside.L_meta_5012.H3.Rewrite

lemma ao_wval_mono {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {x y : Fin n → Bool} (hxy : ∀ i, x i = true → y i = true)
    (w : ℕ) (hw : w < n + C.gates.length) (hx : wval C x w = true) : wval C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hwInput : w < n
    · rw [wval_input _ _ _ hwInput] at hx ⊢
      exact hxy _ hx
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < C.gates.length := by omega
      have hChild (b : Fin 2) (hb : wval C x (opnd C j b) = true) :
          wval C y (opnd C j b) = true := by
        have hlt := opnd_lt hAO hj b
        exact ih _ hlt (by omega) hb
      rcases hAO.1 _ (gateAt_mem hj) with hAnd | hOr
      · rw [wval_gate_and hAO x hj hAnd, Bool.and_eq_true] at hx
        rw [wval_gate_and hAO y hj hAnd, Bool.and_eq_true]
        exact ⟨hChild 0 hx.1, hChild 1 hx.2⟩
      · rw [wval_gate_or hAO x hj hOr, Bool.or_eq_true] at hx
        rw [wval_gate_or hAO y hj hOr, Bool.or_eq_true]
        rcases hx with h0 | h1
        · exact Or.inl (hChild 0 h0)
        · exact Or.inr (hChild 1 h1)

lemma ao_circuitFun_mono {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {x y : Fin n → Bool} (hxy : ∀ i, x i = true → y i = true)
    (hx : circuitFun n C x = true) : circuitFun n C y = true := by
  change wval C x C.output = true at hx
  change wval C y C.output = true
  by_cases hOut : C.output < n + C.gates.length
  · exact ao_wval_mono hAO hxy C.output hOut hx
  · rw [wval_ge_len _ _ (Nat.le_of_not_gt hOut)] at hx
    cases hx

lemma ao_computes_graph_of_edge_pairs {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D : Circuit) (hAO : IsAO2 n D)
    (hBelow : ∀ x : Fin n → Bool, circuitFun n D x = true → graphFun G ∅ x = true)
    (hPairs : ∀ u v : Fin n, G.Adj u v → circuitFun n D (pairInput u v) = true) :
    circuitFun n D = graphFun G ∅ := by
  funext x
  apply Bool.eq_iff_iff.mpr
  constructor
  · exact hBelow x
  · intro hx
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq] at hx
    obtain ⟨u, v, hadj, hxu, hxv⟩ := hx
    apply ao_circuitFun_mono hAO _ (hPairs u v hadj)
    intro i hi
    simp only [pairInput, decide_eq_true_eq] at hi
    rcases hi with rfl | rfl
    · exact hxu
    · exact hxv

lemma project_computes_graph_of_edge_pairs {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (hF : circuitFun n C = graphFun G ∅)
    (R B : Finset ℕ) (good : ℕ → Bool) (center : ℕ → ℕ) (root : ℕ → ℕ)
    (hBackB : ∀ j < C.gates.length, j ∈ B → center j < n + j ∧ root j < n + j)
    (hOrR : ∀ j < C.gates.length, j ∈ R → (gateAt C j).op = GateOp.or)
    (hBelowB : ∀ j < C.gates.length, j ∈ B → BelowF G (projectCircuit C R B good center root) j)
    (hPairs : ∀ u v : Fin n, G.Adj u v →
      circuitFun n (projectCircuit C R B good center root) (pairInput u v) = true) :
    circuitFun n (projectCircuit C R B good center root) = graphFun G ∅ := by
  exact ao_computes_graph_of_edge_pairs G _ (project_isAO2 hAO R B good center root hBackB)
    (project_no_false_positive hAO hF R B good center root hBackB hOrR hBelowB) hPairs

end VectorProjection

namespace VectorProjectionSemantics

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.ReadTwo

open PEqualNP.Outside.L_meta_5012.H3.ProjectionSemantics

open PEqualNP.Outside.L_meta_5012.H3.Rewrite PEqualNP.Outside.L_meta_5012.H3.VectorProjection

lemma project_raw_semantics {n : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (R B : Finset ℕ) (supp : ℕ → Finset (Fin n)) (Good : Finset (Fin n))
    (center : ℕ → ℕ) (root : ℕ → ℕ)
    (hBackB : ∀ j < C.gates.length, j ∈ B → center j < n + j ∧ root j < n + j)
    (hBound : ∀ k ∈ R, k < C.gates.length)
    (hDisj : ∀ k ∈ R, k ∉ B)
    (hOr : ∀ k ∈ R, (gateAt C k).op = GateOp.or)
    (hInput : ∀ i : Fin n, supp i.val = {i})
    (hUnion : ∀ k ∈ R, supp (n + k) = supp (opnd C k 0) ∪ supp (opnd C k 1))
    (hClosed : ∀ k ∈ R, ∀ b : Fin 2,
      opnd C k b < n ∨ ∃ j ∈ R, opnd C k b = n + j)
    {w : ℕ} (hw : w < n ∨ ∃ k ∈ R, w = n + k)
    (hGood : (supp w ∩ Good).Nonempty) (x : Fin n → Bool) :
    wval (projectCircuit C R B (fun w => decide (supp w ∩ Good).Nonempty) center root) x w =
      supportValue (supp w ∩ Good) x := by
  apply projected_raw_semantics C _ hAO R supp Good hBound hInput hUnion hClosed _ hw hGood x
  intro k hk hg x
  rw [project_or_eval hAO R B _ center root hBackB x (hBound k hk) hk (hDisj k hk) (hOr k hk)]
  have hSome : (supp (opnd C k 0) ∩ Good).Nonempty ∨
      (supp (opnd C k 1) ∩ Good).Nonempty := by
    rw [hUnion k hk, Finset.union_inter_distrib_right] at hg
    exact Finset.union_nonempty.mp hg
  by_cases h0 : (supp (opnd C k 0) ∩ Good).Nonempty <;>
    by_cases h1 : (supp (opnd C k 1) ∩ Good).Nonempty <;> simp_all

end VectorProjectionSemantics

namespace VectorProjectionSemantics

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.ReadTwo

open PEqualNP.Outside.L_meta_5012.H3.ProjectionSemantics

open PEqualNP.Outside.L_meta_5012.H3.Rewrite PEqualNP.Outside.L_meta_5012.H3.VectorProjection

lemma project_has_duplicate_or {n : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (R B : Finset ℕ) (supp : ℕ → Finset (Fin n)) (Good : Finset (Fin n))
    (center : ℕ → ℕ) (root : ℕ → ℕ)
    (hBound : ∀ k ∈ R, k < C.gates.length)
    (hDisj : ∀ k ∈ R, k ∉ B)
    (hInput : ∀ i : Fin n, supp i.val = {i})
    (hUnion : ∀ k ∈ R, supp (n + k) = supp (opnd C k 0) ∪ supp (opnd C k 1))
    (hClosed : ∀ k ∈ R, ∀ b : Fin 2,
      opnd C k b < n ∨ ∃ j ∈ R, opnd C k b = n + j)
    (hMixed : ∃ k ∈ R, (supp (n + k) ∩ Good).Nonempty ∧ ¬ supp (n + k) ⊆ Good) :
    ∃ k < C.gates.length, ∃ t,
      gateAt (projectCircuit C R B (fun w => decide (supp w ∩ Good).Nonempty) center root) k =
        ⟨GateOp.or, [t, t]⟩ := by
  classical
  let k := Nat.find hMixed
  have hk : k ∈ R ∧ (supp (n + k) ∩ Good).Nonempty ∧ ¬ supp (n + k) ⊆ Good :=
    Nat.find_spec hMixed
  have hPure : ∀ b : Fin 2, (supp (opnd C k b) ∩ Good).Nonempty →
      supp (opnd C k b) ⊆ Good := by
    intro b hgood
    rcases hClosed k hk.1 b with hi | ⟨j, hj, he⟩
    · let i : Fin n := ⟨opnd C k b, hi⟩
      have hsi : supp (opnd C k b) = {i} := hInput i
      rw [hsi]
      obtain ⟨t, ht⟩ := hgood
      rw [hsi, Finset.mem_inter, Finset.mem_singleton] at ht
      exact Finset.singleton_subset_iff.mpr (ht.1 ▸ ht.2)
    · by_contra hn
      have hjm : j ∈ R ∧ (supp (n + j) ∩ Good).Nonempty ∧ ¬ supp (n + j) ⊆ Good := by
        rw [← he]
        exact ⟨hj, hgood, hn⟩
      have hle : k ≤ j := Nat.find_min' hMixed hjm
      have hlt := opnd_lt hAO (hBound k hk.1) b
      omega
  have hSome : (supp (opnd C k 0) ∩ Good).Nonempty ∨
      (supp (opnd C k 1) ∩ Good).Nonempty := by
    have hg := hk.2.1
    rw [hUnion k hk.1, Finset.union_inter_distrib_right] at hg
    exact Finset.union_nonempty.mp hg
  have hNotBoth : ¬ ((supp (opnd C k 0) ∩ Good).Nonempty ∧
      (supp (opnd C k 1) ∩ Good).Nonempty) := by
    intro hh
    apply hk.2.2
    rw [hUnion k hk.1]
    exact Finset.union_subset (hPure 0 hh.1) (hPure 1 hh.2)
  refine ⟨k, hBound k hk.1, ?_⟩
  change ∃ t, gateAt (rewriteCircuit C _) k = _
  rw [gateAt_rewrite C _ (hBound k hk.1)]
  rcases hSome with h0 | h1
  · have h1 : ¬ (supp (opnd C k 1) ∩ Good).Nonempty := fun hh => hNotBoth ⟨h0, hh⟩
    exact ⟨opnd C k 0, by simp [projectGate, keepGate, hDisj k hk.1, hk.1, h0, h1]⟩
  · have h0 : ¬ (supp (opnd C k 0) ∩ Good).Nonempty := fun hh => hNotBoth ⟨hh, h1⟩
    exact ⟨opnd C k 1, by simp [projectGate, keepGate, hDisj k hk.1, hk.1, h0, h1]⟩

end VectorProjectionSemantics

namespace VectorProjectionSemantics

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.ReadTwo

open PEqualNP.Outside.L_meta_5012.H3.ProjectionSemantics

open PEqualNP.Outside.L_meta_5012.H3.Rewrite PEqualNP.Outside.L_meta_5012.H3.VectorProjection

lemma project_gate_unchanged_of_uniform {n : ℕ} (C : Circuit)
    (R B : Finset ℕ) (supp : ℕ → Finset (Fin n)) (Good : Finset (Fin n))
    (center : ℕ → ℕ) (root : ℕ → ℕ) (k : ℕ) (hk : k < C.gates.length) (hkB : k ∉ B)
    (hUnion : k ∈ R → supp (n + k) = supp (opnd C k 0) ∪ supp (opnd C k 1))
    (hNonempty : k ∈ R → ∀ b : Fin 2, (supp (opnd C k b)).Nonempty)
    (hUniform : k ∈ R → ∀ u ∈ supp (n + k), ∀ v ∈ supp (n + k), (u ∈ Good ↔ v ∈ Good)) :
    gateAt (projectCircuit C R B (fun w => decide (supp w ∩ Good).Nonempty) center root) k =
      gateAt C k := by
  change gateAt (rewriteCircuit C _) k = _
  rw [gateAt_rewrite C _ hk]
  by_cases hkR : k ∈ R
  · apply projectGate_eq_of_not_B_flags_equal C R B _ center root k _ hkB
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨u, hu⟩
      obtain ⟨v, hv⟩ := hNonempty hkR 1
      refine ⟨v, Finset.mem_inter.mpr ⟨hv, ?_⟩⟩
      have hu' : u ∈ supp (n + k) := by
        rw [hUnion hkR]; exact Finset.mem_union_left _ (Finset.mem_inter.mp hu).1
      have hv' : v ∈ supp (n + k) := by
        rw [hUnion hkR]; exact Finset.mem_union_right _ hv
      exact (hUniform hkR u hu' v hv').mp (Finset.mem_inter.mp hu).2
    · rintro ⟨v, hv⟩
      obtain ⟨u, hu⟩ := hNonempty hkR 0
      refine ⟨u, Finset.mem_inter.mpr ⟨hu, ?_⟩⟩
      have hu' : u ∈ supp (n + k) := by
        rw [hUnion hkR]; exact Finset.mem_union_left _ hu
      have hv' : v ∈ supp (n + k) := by
        rw [hUnion hkR]; exact Finset.mem_union_right _ (Finset.mem_inter.mp hv).1
      exact (hUniform hkR u hu' v hv').mpr (Finset.mem_inter.mp hv).2
  · exact projectGate_eq_of_not_B_not_R C R B _ center root k _ hkB hkR

end VectorProjectionSemantics

namespace VectorProjectionSemantics

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.ReadTwo PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

open PEqualNP.Outside.L_meta_5012.H3.ProjectionSemantics

open PEqualNP.Outside.L_meta_5012.H3.Rewrite PEqualNP.Outside.L_meta_5012.H3.VectorProjection
  PEqualNP.Outside.L_meta_5012.H3.ProjectionTransfer

lemma projection_contradiction {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C)
    (R B : Finset ℕ) (supp : ℕ → Finset (Fin n)) (Good : Finset (Fin n))
    (center : ℕ → ℕ) (root : ℕ → ℕ) (D : Circuit)
    (hDef : D = projectCircuit C R B (fun w => decide (supp w ∩ Good).Nonempty) center root)
    (hBackB : ∀ j < C.gates.length, j ∈ B → center j < n + j ∧ root j < n + j)
    (hBound : ∀ k ∈ R, k < C.gates.length)
    (hDisj : ∀ k ∈ R, k ∉ B)
    (hOr : ∀ k ∈ R, (gateAt C k).op = GateOp.or)
    (hInput : ∀ i : Fin n, supp i.val = {i})
    (hUnion : ∀ k ∈ R, supp (n + k) = supp (opnd C k 0) ∪ supp (opnd C k 1))
    (hClosed : ∀ k ∈ R, ∀ b : Fin 2,
      opnd C k b < n ∨ ∃ j ∈ R, opnd C k b = n + j)
    (hMixed : ∃ k ∈ R, (supp (n + k) ∩ Good).Nonempty ∧ ¬ supp (n + k) ⊆ Good)
    (hBelowB : ∀ j < C.gates.length, j ∈ B → BelowF G D j)
    (hTop : ∀ a ∈ tops G C, gateAt D a = gateAt C a)
    (hOrOut : ∀ k < C.gates.length, (gateAt C k).op = GateOp.or →
      OrReaches n C C.output k → gateAt D k = gateAt C k)
    (hOrTop : ∀ a ∈ tops G C, ∀ b : Fin 2, ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.or → OrReaches n C (opnd C a b) k →
      gateAt D k = gateAt C k)
    (hNoOpp : ∀ a ∈ tops G C, ∀ b : Fin 2, ∀ j ∈ junk G C, ∀ k ∈ junk G C,
      OrReaches n C (opnd C a b) j → ¬ OrReaches n C (opnd C a (1 - b)) k)
    (hUseful : ∀ j ∈ junk G C, ∀ u v : Fin n, G.Adj u v →
      gateVal n C j (pairInput u v) = true → (u ∈ wmax G C j ∨ v ∈ wmax G C j) →
      gateVal n D j (pairInput u v) = true) : False := by
  subst D
  let good := fun w => decide (supp w ∩ Good).Nonempty
  let D := projectCircuit C R B good center root
  have hAO : IsAO2 n D := project_isAO2 hL.1 R B good center root hBackB
  have hLen : C.gates.length ≤ D.gates.length := by
    simp only [D, projectCircuit, rewrite_length, le_refl]
  have hPairs : ∀ u v : Fin n, G.Adj u v → circuitFun n D (pairInput u v) = true := by
    intro u v huv
    exact preserve_all_edges G C D hL.1 hAO hL.2.1 hT hLen rfl hTop hOrOut hOrTop hNoOpp hUseful huv
  have hF : circuitFun n D = graphFun G ∅ :=
    project_computes_graph_of_edge_pairs hL.1 hL.2.1 R B good center root hBackB
      (fun j _ hj => hOr j hj) hBelowB hPairs
  have hLeast : IsLeastAO G D :=
    rewrite_isLeastAO (projectGate C R B good center root) hL hAO hF
  obtain ⟨k, hk, t, hgate⟩ := project_has_duplicate_or C hL.1 R B supp Good center root
    hBound hDisj hInput hUnion hClosed hMixed
  have hkD : k < D.gates.length := by simpa only [D, projectCircuit, rewrite_length] using hk
  have hgateD : gateAt D k = ⟨GateOp.or, [t, t]⟩ := hgate
  have ht : t < n + k := hAO.2.1 k hkD t (by rw [hgateD]; simp)
  exact PEqualNP.Outside.L_meta_5012.H3.DuplicateOR.least_no_duplicate_or hLeast hkD ht hgateD

end VectorProjectionSemantics

namespace VectorCenterProjection

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.ReadTwo PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

open PEqualNP.Outside.L_meta_5012.H3.ProjectionSemantics (supportValue)

open PEqualNP.Outside.L_meta_5012.H3.Rewrite PEqualNP.Outside.L_meta_5012.H3.VectorProjection
  PEqualNP.Outside.L_meta_5012.H3.VectorProjectionSemantics

lemma no_least_of_projectable_roots {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C)
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (color : Bool) (center : ℕ → Fin n) (root : ℕ → ℕ)
    (hBack : ∀ j ∈ junk G C, root j < n+j)
    (hRaw : ∀ j ∈ junk G C, RawSupport.Raw n C (root j))
    (hGood : ∀ j ∈ junk G C, ∃ t ∈ orIn n C (root j), s t ≠ color)
    (hNeighbor : ∀ j ∈ junk G C, ∀ t ∈ orIn n C (root j), s t ≠ color → G.Adj (center j) t)
    (hMixed : ∃ j ∈ junk G C, ∃ t ∈ orIn n C (root j), s t = color)
    (hW : ∀ j ∈ junk G C, (wmax G C j).card ≤ 1)
    (hNoOpp : ∀ a ∈ tops G C, ∀ b : Fin 2, ∀ j ∈ junk G C, ∀ k ∈ junk G C,
      OrReaches n C (opnd C a b) j → ¬ OrReaches n C (opnd C a (1-b)) k)
    (hCover : ∀ j ∈ junk G C, ∀ u v : Fin n, G.Adj u v →
      gateVal n C j (pairInput u v) = true → (u ∈ wmax G C j ∨ v ∈ wmax G C j) →
      (u=center j ∧ v ∈ orIn n C (root j) ∧ s v ≠ color) ∨
        (v=center j ∧ u ∈ orIn n C (root j) ∧ s u ≠ color)) : False := by
  classical
  let R := RawSupport.region n C
  let B := junk G C
  let Good := Finset.univ.filter fun t : Fin n => s t ≠ color
  let supp := orIn n C
  let good := fun w => decide (supp w ∩ Good).Nonempty
  let D := projectCircuit C R B good (fun j => (center j).val) root
  have hGoodMem (t : Fin n) : t ∈ Good ↔ s t ≠ color := by simp [Good]
  have hBound (k : ℕ) (hk : k ∈ R) : k < C.gates.length := (RawSupport.mem_region.mp hk).1
  have hOr (k : ℕ) (hk : k ∈ R) : (gateAt C k).op = GateOp.or := RawSupport.region_or hL.1 hk
  have hDisj (k : ℕ) (hk : k ∈ R) : k ∉ B := by
    intro hkB
    have ho := (Critical.Base.junkData hkB).2.1
    rw [hOr k hk] at ho
    cases ho
  have hInput (i : Fin n) : supp i.val = {i} := RawSupport.orIn_input C i
  have hUnion (k : ℕ) (hk : k ∈ R) : supp (n+k) = supp (opnd C k 0) ∪ supp (opnd C k 1) :=
    RawSupport.orIn_or hL.1 (hBound k hk) (hOr k hk)
  have hClosed (k : ℕ) (hk : k ∈ R) (b : Fin 2) :
      opnd C k b < n ∨ ∃ j ∈ R, opnd C k b = n+j := RawSupport.region_closed hL.1 hk b
  have hBackB (j : ℕ) (_ : j < C.gates.length) (hj : j ∈ B) :
      (center j).val < n+j ∧ root j < n+j := ⟨by have := (center j).isLt; omega, hBack j hj⟩
  have hRootGood (j : ℕ) (hj : j ∈ B) : (supp (root j) ∩ Good).Nonempty := by
    obtain ⟨t, ht, htc⟩ := hGood j hj
    exact ⟨t, Finset.mem_inter.mpr ⟨ht, (hGoodMem t).mpr htc⟩⟩
  have hStar (j : ℕ) (hj : j ∈ B) (x : Fin n → Bool) :
      gateVal n D j x = (x (center j) && supportValue (supp (root j) ∩ Good) x) := by
    have hjl := (Critical.Base.junkData hj).1
    change wval D x (n+j) = _
    rw [project_and_eval C R B good (fun j => (center j).val) root x hjl hj (hBackB j hjl hj).1 (hBack j hj)]
    rw [wval_input _ _ (center j).val (center j).isLt]
    rw [project_raw_semantics C hL.1 R B supp Good (fun j => (center j).val) root hBackB hBound hDisj hOr
      hInput hUnion hClosed (hRaw j hj) (hRootGood j hj) x]
  have hBelow (j : ℕ) (_ : j < C.gates.length) (hj : j ∈ B) : BelowF G D j := by
    intro x hx
    rw [hStar j hj, Bool.and_eq_true] at hx
    obtain ⟨t, ht, hxt⟩ := (show ∃t∈supp (root j) ∩ Good, x t=true by
      simpa only [supportValue, decide_eq_true_eq] using hx.2)
    have ht' := Finset.mem_inter.mp ht
    have hadj := hNeighbor j hj t ht'.1 ((hGoodMem t).mp ht'.2)
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq]
    exact ⟨center j, t, hadj, hx.1, hxt⟩
  have hUseful : ∀ j ∈ junk G C, ∀ u v : Fin n, G.Adj u v →
      gateVal n C j (pairInput u v) = true → (u ∈ wmax G C j ∨ v ∈ wmax G C j) →
      gateVal n D j (pairInput u v) = true := by
    intro j hj u v huv hjv hw
    rw [hStar j hj, Bool.and_eq_true]
    rcases hCover j hj u v huv hjv hw with ⟨rfl, ht, hc⟩ | ⟨rfl, ht, hc⟩
    · refine ⟨Critical.Base.pairInput_left _ _, ?_⟩
      simp only [supportValue, decide_eq_true_eq]
      exact ⟨v, Finset.mem_inter.mpr ⟨ht, (hGoodMem v).mpr hc⟩, Critical.Base.pairInput_right _ _⟩
    · refine ⟨Critical.Base.pairInput_right _ _, ?_⟩
      simp only [supportValue, decide_eq_true_eq]
      exact ⟨u, Finset.mem_inter.mpr ⟨ht, (hGoodMem u).mpr hc⟩, Critical.Base.pairInput_left _ _⟩
  have hMixedR : ∃ k ∈ R, (supp (n+k) ∩ Good).Nonempty ∧ ¬ supp (n+k) ⊆ Good := by
    obtain ⟨j, hj, t, ht, htc⟩ := hMixed
    have hNot : ¬ supp (root j) ⊆ Good := by
      intro hsub
      exact ((hGoodMem t).mp (hsub ht)) htc
    rcases hRaw j hj with hi | ⟨k, hk, he⟩
    · let i : Fin n := ⟨root j, hi⟩
      have hsi : supp (root j) = {i} := hInput i
      obtain ⟨v, hv⟩ := hRootGood j hj
      rw [hsi, Finset.mem_inter, Finset.mem_singleton] at hv
      exact False.elim (hNot (by rw [hsi]; exact Finset.singleton_subset_iff.mpr (hv.1 ▸ hv.2)))
    · exact ⟨k, hk, he ▸ hRootGood j hj, he ▸ hNot⟩
  have hTop : ∀ a ∈ tops G C, gateAt D a = gateAt C a := by
    intro a ha
    obtain ⟨hal, hao, hab⟩ := Critical.Base.topData ha
    have haB : a ∉ B := by
      intro haj
      obtain ⟨_, _, x, hx, hf⟩ := Critical.Base.junkData haj
      have hh := hab x hx
      rw [hf] at hh
      cases hh
    have haR : a ∉ R := by
      intro har
      rw [hOr a har] at hao
      cases hao
    change gateAt (rewriteCircuit C _) a = _
    rw [gateAt_rewrite C _ hal]
    exact projectGate_eq_of_not_B_not_R C R B good (fun j => (center j).val) root a _ haB haR
  have hOrNotB (k : ℕ) (ho : (gateAt C k).op = GateOp.or) : k ∉ B := by
    intro hk
    have ha := (Critical.Base.junkData hk).2.1
    rw [ho] at ha
    cases ha
  have hOrOut : ∀ k < C.gates.length, (gateAt C k).op = GateOp.or →
      OrReaches n C C.output k → gateAt D k = gateAt C k := by
    intro k hk ho hr
    have hkR : k ∉ R := by
      intro hkr
      exact MixedClosure.raw_nonempty_not_orReaches_output hL.2.1
        (RawSupport.raw_support_nonempty hL.1 _ (Or.inr ⟨k,hkr,rfl⟩)) hr
    change gateAt (rewriteCircuit C _) k = _
    rw [gateAt_rewrite C _ hk]
    exact projectGate_eq_of_not_B_not_R C R B good (fun j => (center j).val) root k _ (hOrNotB k ho) hkR
  have hOrTop : ∀ a ∈ tops G C, ∀ b : Fin 2, ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.or → OrReaches n C (opnd C a b) k →
      gateAt D k = gateAt C k := by
    intro a ha b k hk ho hr
    apply project_gate_unchanged_of_uniform C R B supp Good (fun j => (center j).val) root k hk (hOrNotB k ho)
      (hUnion k)
    · intro hkr b
      exact RawSupport.raw_support_nonempty hL.1 _ (RawSupport.region_closed hL.1 hkr b)
    · intro _ u hu v hv
      have hsub := Critical.Base.orInTrans (Critical.Base.orReaches_reach k _ hr).1
      have he := MixedClosure.top_side_same_color s hbip hL.1 hT hW ha b (hsub hu) (hsub hv)
      rw [hGoodMem u, hGoodMem v, he]
  exact projection_contradiction G C hL hT R B supp Good (fun j => (center j).val) root D rfl hBackB hBound
    hDisj hOr hInput hUnion hClosed hMixedR hBelow hTop hOrOut hOrTop hNoOpp hUseful

end VectorCenterProjection

namespace SelectedFactor

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

open PEqualNP.EdgeOwnership PEqualNP.TopForm

open PEqualNP.Outside.L_meta_5012.H3.IndependentDescent

lemma mixed_factor {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (P Q : Finset (Fin n)) (w : Fin n) (hSafe : Safe G P Q w)
    (hI : (P ∩ Q).Nonempty)
    (hP : ∃ p ∈ P, ¬ G.Adj p w) (hQ : ∃ q ∈ Q, ¬ G.Adj q w) :
    ∃ U : Finset (Fin n), (U=P ∨ U=Q) ∧
      (∀ u ∈ U, s u ≠ s w → G.Adj w u) ∧
      (∀ i ∈ P ∩ Q, i ∈ U ∧ s i ≠ s w) ∧
      (∃ u ∈ U, s u ≠ s w) ∧ (∃ v ∈ U, s v = s w) := by
  obtain ⟨p,hp,hpw⟩ := hP
  obtain ⟨q,hq,hqw⟩ := hQ
  obtain ⟨i,hi⟩ := hI
  have hColor (v : Fin n) (hv : v ∈ P ∩ Q) : s v ≠ s w :=
    hbip v w (safe_overlap_adjacent G P Q hSafe hv).symm
  rcases Colors.safe_oriented_bad_factors G s hbip P Q hSafe hp hq hpw hqw with
    ⟨hBad,_⟩ | ⟨hBad,_⟩
  · refine ⟨P,Or.inl rfl,?_,?_,⟨i,(Finset.mem_inter.mp hi).1,hColor i hi⟩,
      ⟨p,hp,hBad p hp hpw⟩⟩
    · intro u hu hcu
      by_contra hAdj
      exact hcu (hBad u hu (fun h => hAdj h.symm))
    · intro v hv
      exact ⟨(Finset.mem_inter.mp hv).1,hColor v hv⟩
  · refine ⟨Q,Or.inr rfl,?_,?_,⟨i,(Finset.mem_inter.mp hi).2,hColor i hi⟩,
      ⟨q,hq,hBad q hq hqw⟩⟩
    · intro u hu hcu
      by_contra hAdj
      exact hcu (hBad u hu (fun h => hAdj h.symm))
    · intro v hv
      exact ⟨(Finset.mem_inter.mp hv).2,hColor v hv⟩

end SelectedFactor

namespace SameColorCenterCase

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo

open PEqualNP.Outside.L_meta_5012.H3.IndependentDescent

lemma same_color_centers_overlap_impossible {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C)
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    {g h : ℕ} (hJ : junk G C = {g,h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (center : ℕ → Fin n) (color : Bool) (hColor : ∀ j ∈ junk G C, s (center j) = color)
    (hW : ∀ j ∈ junk G C, wmax G C j = {center j})
    (hOutside : ∀ j ∈ junk G C, ∀ b : Fin 2, center j ∉ side (n := n) C j b)
    (hOverlap : ∀ j ∈ junk G C, (side (n := n) C j 0 ∩ side (n := n) C j 1).Nonempty)
    (hBad : ∀ j ∈ junk G C, ∀ b : Fin 2, ∃ p ∈ side (n := n) C j b, ¬ G.Adj p (center j)) :
    False := by
  classical
  have hCases (j : ℕ) (hj : j ∈ junk G C) : j=g ∨ j=h := by simpa [hJ] using hj
  have hEval (j : ℕ) (hj : j ∈ junk G C) : ∀ x : Fin n → Bool,
      gateVal n C j x = product (side (n := n) C j 0) (side (n := n) C j 1) x :=
    RawOperands.independent_product G C hL.1 hT g h hJ hgh hhg j (hCases j hj)
  have hSafe (j : ℕ) (hj : j ∈ junk G C) :
      Safe G (side (n := n) C j 0) (side (n := n) C j 1) (center j) := by
    apply (wmax_iff G C j _ _ (hEval j hj) (center j)).mp
    rw [hW j hj]
    simp
  have hChoice (j : ℕ) : ∃ b : Fin 2, ∀ hj : j ∈ junk G C,
      (∀ t ∈ side (n := n) C j b, s t ≠ color → G.Adj (center j) t) ∧
      (∀ i ∈ side (n := n) C j 0 ∩ side (n := n) C j 1,
        i ∈ side (n := n) C j b ∧ s i ≠ color) ∧
      (∃ t ∈ side (n := n) C j b, s t ≠ color) ∧
      (∃ t ∈ side (n := n) C j b, s t = color) := by
    by_cases hj : j ∈ junk G C
    · obtain ⟨U,hU,hn,hi,hgood,hbad⟩ := SelectedFactor.mixed_factor G s hbip
        (side (n := n) C j 0) (side (n := n) C j 1) (center j) (hSafe j hj)
        (hOverlap j hj) (hBad j hj 0) (hBad j hj 1)
      rw [hColor j hj] at hn hi hgood hbad
      rcases hU with rfl | rfl
      · exact ⟨0,fun _ => ⟨hn,hi,hgood,hbad⟩⟩
      · exact ⟨1,fun _ => ⟨hn,hi,hgood,hbad⟩⟩
    · exact ⟨0,fun hj' => False.elim (hj hj')⟩
  choose pick hpick using hChoice
  let root : ℕ → ℕ := fun j => opnd C j (pick j)
  apply VectorCenterProjection.no_least_of_projectable_roots G C hL hT s hbip color center root
  · intro j hj
    exact Lift.opnd_lt hL.1 (Critical.Base.junkData hj).1 (pick j)
  · intro j hj
    rcases hCases j hj with rfl | rfl
    · exact RawSupport.independent_operand_raw hL.1 hT hJ hhg (pick j)
    · exact RawSupport.independent_operand_raw hL.1 hT (by rw [hJ,Finset.pair_comm]) hgh (pick j)
  · intro j hj
    exact (hpick j hj).2.2.1
  · intro j hj
    exact (hpick j hj).1
  · have hgm : g ∈ junk G C := by rw [hJ]; simp
    obtain ⟨t,ht,htc⟩ := (hpick g hgm).2.2.2
    exact ⟨g,hgm,t,ht,htc⟩
  · intro j hj
    rw [hW j hj]
    simp
  · intro a ha b j hj k hk hr
    exact SameColor.no_opposite_top_same_color s hbip hL.1 _ _ _ _ (hEval j hj)
      (hEval k hk) (hSafe j hj) (hSafe k hk) (hOverlap j hj) (hOverlap k hk)
      ((hColor j hj).trans (hColor k hk).symm) ha b hr
  · intro j hj u v huv hjv hFilter
    have hUnique (z : Fin n) (hz : Safe G (side (n := n) C j 0) (side (n := n) C j 1) z) : z=center j := by
      have hm := (wmax_iff G C j _ _ (hEval j hj) z).mpr hz
      rw [hW j hj] at hm
      exact Finset.mem_singleton.mp hm
    have hUseful : Useful G (side (n := n) C j 0) (side (n := n) C j 1) u v := by
      refine ⟨huv,(hEval j hj _).symm.trans hjv,?_⟩
      rcases hFilter with hu | hv
      · exact Or.inl ((wmax_iff G C j _ _ (hEval j hj) u).mp hu)
      · exact Or.inr ((wmax_iff G C j _ _ (hEval j hj) v).mp hv)
    rcases SameColor.useful_at_unique_outside_center G _ _ (hOutside j hj 0)
      (hOutside j hj 1) hUnique u v hUseful with ⟨hu,hv⟩ | ⟨hv,hu⟩
    · exact Or.inl ⟨hu,(hpick j hj).2.1 v hv⟩
    · exact Or.inr ⟨hv,(hpick j hj).2.1 u hu⟩

end SameColorCenterCase

namespace FactorWitness

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo

open IndependentDescent

lemma factor_has_nonneighbor {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C)
    (hOne : ∀ D : Circuit, IsLeastAO G D → (junk G D).card ≠ 1)
    {j k : ℕ} (hne : j ≠ k) (hJ : junk G C = {j,k})
    (hCone : ¬ InCone n C j k) (hOtherCone : ¬ InCone n C k j)
    (hNoOpp : ∀ a ∈ tops G C, ∀ b : Fin 2,
      OrReaches n C (opnd C a b) j → ¬ OrReaches n C (opnd C a (1-b)) k)
    (center : Fin n) (hUnique : wmax G C j ⊆ {center})
    (hOutside : ∀ b : Fin 2, center ∉ side (n := n) C j b) :
    ∀ b : Fin 2, ∃ p ∈ side (n := n) C j b, ¬ G.Adj p center := by
  have hjMem : j ∈ junk G C := by rw [hJ]; simp
  have hj := (Critical.Base.junkData hjMem).1
  have hBound (b : Fin 2) : opnd C j b < n+j := Lift.opnd_lt hL.1 hj b
  have hRaw (b : Fin 2) (x : Fin n → Bool) :
      wval C x (opnd C j b) = decide (∃ p ∈ side (n := n) C j b, x p = true) :=
    RawOperands.independent_operand G C hL.1 hT j k hJ hCone hOtherCone j (Or.inl rfl) b x
  have hEval (x : Fin n → Bool) : gateVal n C j x =
      product (side (n := n) C j 0) (side (n := n) C j 1) x :=
    RawOperands.independent_product G C hL.1 hT j k hJ hCone hOtherCone j (Or.inl rfl) x
  have hUniqueSafe (z : Fin n)
      (hz : Safe G (side (n := n) C j 0) (side (n := n) C j 1) z) : z = center :=
    Finset.mem_singleton.mp (hUnique ((wmax_iff G C j _ _ hEval z).mpr hz))
  intro b
  by_contra hBad
  have hAll : ∀ p ∈ side (n := n) C j b, G.Adj p center := by
    intro p hp
    by_contra hadj
    exact hBad ⟨p,hp,hadj⟩
  apply CleanReplacement.no_clean_independent_replacement G C hL hOne hne hJ hCone
    ⟨GateOp.and,[center.val,opnd C j b]⟩ (Or.inl rfl) rfl
  · intro wire hwire
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hwire
    rcases hwire with rfl | rfl
    · have := center.isLt; omega
    · exact hBound b
  · intro x hFalse
    rw [FlagReduction.star_gate_bit C j (Nat.le_of_lt hj) center _ (hBound b) x, hRaw b x]
    apply Bool.eq_false_iff.mpr
    intro hTrue
    have hTrue' : x center = true ∧ ∃ p ∈ side (n := n) C j b, x p = true := by
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using hTrue
    obtain ⟨hcenter,p,hp,hxp⟩ := hTrue'
    have hf := (CleanReplacement.graph_true G x).mpr ⟨p,center,hAll p hp,hxp,hcenter⟩
    rw [hFalse] at hf
    cases hf
  · intro u v huv hCut
    have hUseful : Useful G (side (n := n) C j 0) (side (n := n) C j 1) u v := by
      obtain ⟨hjVal,hFilter⟩ := Critical.critical_edge_useful hL.1 hL.2.1 hT
        (g := k) (h := j) (by rw [hJ,Finset.pair_comm]) hne.symm hCone hNoOpp u v huv hCut
      refine ⟨huv,(hEval _).symm.trans hjVal,?_⟩
      rcases hFilter with hu | hv
      · exact Or.inl ((wmax_iff G C j _ _ hEval u).mp hu)
      · exact Or.inr ((wmax_iff G C j _ _ hEval v).mp hv)
    have hCases := SameColor.useful_at_unique_outside_center G _ _ (hOutside 0) (hOutside 1)
      hUniqueSafe u v hUseful
    rw [FlagReduction.star_gate_bit C j (Nat.le_of_lt hj) center _ (hBound b) _, hRaw b]
    have hInter (p : Fin n) (hp : p ∈ side (n := n) C j 0 ∩ side (n := n) C j 1) :
        p ∈ side (n := n) C j b := by
      fin_cases b
      · exact (Finset.mem_inter.mp hp).1
      · exact (Finset.mem_inter.mp hp).2
    rcases hCases with ⟨hu,hv⟩ | ⟨hv,hu⟩
    · subst u
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using
        (show pairInput center v center = true ∧ ∃ p ∈ side (n := n) C j b,
          pairInput center v p = true from ⟨by simp [pairInput],v,hInter v hv,by simp [pairInput]⟩)
    · subst v
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using
        (show pairInput u center center = true ∧ ∃ p ∈ side (n := n) C j b,
          pairInput u center p = true from ⟨by simp [pairInput],u,hInter u hu,by simp [pairInput]⟩)

lemma all_factors_have_nonneighbor {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C)
    (hOne : ∀ D : Circuit, IsLeastAO G D → (junk G D).card ≠ 1)
    {g h : ℕ} (hJ : junk G C = {g,h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (hNoOpp : ∀ a ∈ tops G C, ∀ b : Fin 2, ∀ j ∈ junk G C, ∀ k ∈ junk G C,
      OrReaches n C (opnd C a b) j → ¬ OrReaches n C (opnd C a (1-b)) k)
    (center : ℕ → Fin n) (hUnique : ∀ j ∈ junk G C, wmax G C j ⊆ {center j})
    (hOutside : ∀ j ∈ junk G C, ∀ b : Fin 2, center j ∉ side (n := n) C j b) :
    ∀ j ∈ junk G C, ∀ b : Fin 2, ∃ p ∈ side (n := n) C j b, ¬ G.Adj p (center j) := by
  have hne : g ≠ h := by
    intro he
    apply hOne C hL
    simp [hJ,he]
  have hg : g ∈ junk G C := by rw [hJ]; simp
  have hh : h ∈ junk G C := by rw [hJ]; simp
  intro j hj
  rcases Critical.Base.memJunkPair hJ hj with hjg | hjh
  · subst j
    exact factor_has_nonneighbor G C hL hT hOne hne hJ hgh hhg
      (fun a ha b => hNoOpp a ha b g hg h hh) (center g) (hUnique g hg) (hOutside g hg)
  · subst j
    exact factor_has_nonneighbor G C hL hT hOne hne.symm (by rw [hJ,Finset.pair_comm]) hhg hgh
      (fun a ha b => hNoOpp a ha b h hh g hg) (center h) (hUnique h hh) (hOutside h hh)

end FactorWitness

namespace SameColorCenterCase

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo

open PEqualNP.Outside.L_meta_5012.H3.IndependentDescent

lemma same_color_centers_overlap_impossible_without_bad {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C)
    (hOne : ∀ D : Circuit, IsLeastAO G D → (junk G D).card ≠ 1)
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    {g h : ℕ} (hJ : junk G C = {g,h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (center : ℕ → Fin n) (color : Bool) (hColor : ∀ j ∈ junk G C, s (center j) = color)
    (hW : ∀ j ∈ junk G C, wmax G C j = {center j})
    (hOutside : ∀ j ∈ junk G C, ∀ b : Fin 2, center j ∉ side (n := n) C j b)
    (hOverlap : ∀ j ∈ junk G C, (side (n := n) C j 0 ∩ side (n := n) C j 1).Nonempty) :
    False := by
  have hCases (j : ℕ) (hj : j ∈ junk G C) : j=g ∨ j=h := by simpa [hJ] using hj
  have hEval (j : ℕ) (hj : j ∈ junk G C) : ∀ x : Fin n → Bool,
      gateVal n C j x = product (side (n := n) C j 0) (side (n := n) C j 1) x :=
    RawOperands.independent_product G C hL.1 hT g h hJ hgh hhg j (hCases j hj)
  have hSafe (j : ℕ) (hj : j ∈ junk G C) :
      Safe G (side (n := n) C j 0) (side (n := n) C j 1) (center j) := by
    apply (wmax_iff G C j _ _ (hEval j hj) (center j)).mp
    rw [hW j hj]
    simp
  have hNoOpp : ∀ a ∈ tops G C, ∀ b : Fin 2, ∀ j ∈ junk G C, ∀ k ∈ junk G C,
      OrReaches n C (opnd C a b) j → ¬ OrReaches n C (opnd C a (1-b)) k := by
    intro a ha b j hj k hk hr
    exact SameColor.no_opposite_top_same_color s hbip hL.1 _ _ _ _ (hEval j hj)
      (hEval k hk) (hSafe j hj) (hSafe k hk) (hOverlap j hj) (hOverlap k hk)
      ((hColor j hj).trans (hColor k hk).symm) ha b hr
  have hBad := FactorWitness.all_factors_have_nonneighbor G C hL hT hOne hJ hgh hhg
    hNoOpp center (fun j hj => by rw [hW j hj]) hOutside
  exact same_color_centers_overlap_impossible G C hL hT s hbip hJ hgh hhg
    center color hColor hW hOutside hOverlap hBad

end SameColorCenterCase

namespace CommonCenterCase

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo

open PEqualNP.Outside.L_meta_5012.H3.IndependentDescent

end CommonCenterCase

namespace ProtectedTop

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo

end ProtectedTop

namespace InsideFlagPrivacy

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Core

open PEqualNP.Outside.L_meta_5012.H3.IndependentDescent

end InsideFlagPrivacy

namespace Liveness

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Core PEqualNP.ReadTwo

end Liveness

namespace LargeOverlapNoJoint

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo

open PEqualNP.Outside.L_meta_5012.H3.IndependentDescent

end LargeOverlapNoJoint

end PEqualNP.Outside.L_meta_5012.H3

namespace PEqualNP.Outside.L_meta_5012.OverlapCase

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma independent_large_overlaps_impossible {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C)
    (hOne : ∀ D : Circuit, IsLeastAO G D → (junk G D).card ≠ 1)
    (hT : TopForm G C) {g h : ℕ} (hne : g ≠ h) (hJ : junk G C = {g,h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G)
    (hLargeG : 2 ≤ (side (n := n) C g 0 ∩ side (n := n) C g 1).card)
    (hLargeH : 2 ≤ (side (n := n) C h 0 ∩ side (n := n) C h 1).card) : False := by
  have hNoG := both_large_overlap_no_opposite G C hL.1 hT hJ hgh hhg h4 hLargeG hLargeH
  have hJ' : junk G C = {h,g} := by rw [hJ, Finset.pair_comm]
  have hNoH := both_large_overlap_no_opposite G C hL.1 hT hJ' hhg hgh h4 hLargeH hLargeG
  obtain ⟨w, hW, hwOut⟩ := independent_overlap_unique_outside G C hL hOne hT hne hJ
    hgh hhg hNoG h4 hLargeG
  obtain ⟨z, hZ, hzOut⟩ := independent_overlap_unique_outside G C hL hOne hT hne.symm hJ'
    hhg hgh hNoH h4 hLargeH
  have hEq := independent_large_overlaps_same_filters G C hL hOne hT hne hJ hgh hhg
    s hbip h4 hLargeG hLargeH
  rw [hW, hZ] at hEq
  have hwz : w = z := Finset.singleton_inj.mp hEq
  subst z
  have hcases : ∀ j ∈ junk G C, j = g ∨ j = h := by
    intro j hj
    simpa only [hJ, Finset.mem_insert, Finset.mem_singleton] using hj
  apply H3.SameColorCenterCase.same_color_centers_overlap_impossible_without_bad
    G C hL hT hOne s hbip hJ hgh hhg (fun _ => w) (s w)
  · intro j hj
    rfl
  · intro j hj
    rcases hcases j hj with rfl | rfl
    · exact hW
    · exact hZ
  · intro j hj b
    rcases hcases j hj with rfl | rfl
    · intro hw
      apply hwOut
      fin_cases b
      · exact Finset.mem_union_left _ hw
      · exact Finset.mem_union_right _ hw
    · intro hw
      apply hzOut
      fin_cases b
      · exact Finset.mem_union_left _ hw
      · exact Finset.mem_union_right _ hw
  · intro j hj
    apply Finset.card_pos.mp
    rcases hcases j hj with rfl | rfl <;> omega

end PEqualNP.Outside.L_meta_5012.OverlapCase
