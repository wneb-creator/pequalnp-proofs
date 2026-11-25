import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2056_aux.TwoDirty.OneDirtyReduction.Support

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.SplitCount
  PEqualNP.Core

local instance : DecidableEq GateOp := gateOpDecEq

/-! ## Section 1: Basic Circuit Evaluation & Monotonicity -/

def wireStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl wireStep w

lemma wires_eq_wiresFrom (C : Circuit) (x : List Bool) :
    C.wires x = wiresFrom C.gates x := rfl

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_len (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    simp only [wiresFrom, List.foldl_cons] at ih ⊢
    rw [ih]; simp [wireStep]; omega

lemma wiresFrom_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have hi' : i < (wireStep w g).length := by simp [wireStep]; omega
    change (wiresFrom gs (wireStep w g)).getD i false = w.getD i false
    rw [ih (wireStep w g) hi']
    simp only [wireStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma wires_len (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq_wiresFrom, wiresFrom_len, List.length_ofFn]

lemma gateAt_eq_getElem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j ∈ C.gates := by
  rw [gateAt_eq_getElem C j hj]
  exact List.getElem_mem hj

lemma wireVal_input (n : ℕ) (C : Circuit) (i : Fin n) (x : Fin n → Bool) :
    wireVal n C i.val x = x i := by
  unfold wireVal
  rw [wires_eq_wiresFrom, wiresFrom_getD_lt _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD]

lemma wireVal_ge_len (n : ℕ) (C : Circuit) (w : ℕ) (x : Fin n → Bool)
    (hw : n + C.gates.length ≤ w) :
    wireVal n C w x = false := by
  unfold wireVal
  rw [List.getD_eq_default _ _ (by rw [wires_len]; exact hw)]

lemma gateVal_eq_wireVal (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    gateVal n C j x = wireVal n C (n + j) x := rfl

lemma circuitFun_eq_wireVal (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    circuitFun n C x = wireVal n C C.output x := rfl

lemma gateVal_eval (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (hRB : ReadsBack n C) (x : Fin n → Bool) :
    gateVal n C j x =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => wireVal n C i x) := by
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    rw [List.cons_getElem_drop_succ, List.take_append_drop]
  set pre := C.gates.take j
  set gj := C.gates[j]
  set post := C.gates.drop (j + 1)
  have hpre_len : pre.length = j := by simp [pre]; omega
  have hw_pre_len : (wiresFrom pre (List.ofFn x)).length = n + j := by
    rw [wiresFrom_len, List.length_ofFn, hpre_len]
  have h1 : C.wires (List.ofFn x) =
      wiresFrom post (wireStep (wiresFrom pre (List.ofFn x)) gj) := by
    rw [wires_eq_wiresFrom, hsplit, wiresFrom_append]
    rfl
  have hlt : n + j < (wireStep (wiresFrom pre (List.ofFn x)) gj).length := by
    simp [wireStep, hw_pre_len]
  unfold gateVal
  rw [h1, wiresFrom_getD_lt _ _ _ hlt]
  have hmid : (wireStep (wiresFrom pre (List.ofFn x)) gj).getD (n + j) false =
      gj.op.eval (gj.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false) := by
    simp only [wireStep, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (le_of_eq hw_pre_len),
      hw_pre_len, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  rw [hmid, gateAt_eq_getElem C j hj]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hilt : i < n + j := by
    have := hRB j hj i
    rw [gateAt_eq_getElem C j hj] at this
    exact this hi
  unfold wireVal
  rw [h1]
  have hilt2 : i < (wireStep (wiresFrom pre (List.ofFn x)) gj).length := by
    simp [wireStep, hw_pre_len]; omega
  rw [wiresFrom_getD_lt _ _ _ hilt2]
  simp only [wireStep, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by omega : i < (wiresFrom pre (List.ofFn x)).length)]

lemma eval_and_two (a b : Bool) : GateOp.and.eval [a, b] = (a && b) := by
  cases a <;> cases b <;> rfl

lemma eval_or_two (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by
  cases a <;> cases b <;> rfl

lemma list_length_two {α : Type} {l : List α} (h : l.length = 2) :
    ∃ a b, l = [a, b] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;> simp at h
  exact ⟨a, b, rfl⟩

lemma graphFun_empty_true_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
  simp [graphFun]

lemma graphFun_empty_unitInput {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (p : Fin n) : graphFun G ∅ (unitInput p) = false := by
  cases h : graphFun G ∅ (unitInput p) with
  | false => rfl
  | true =>
    obtain ⟨u, v, huv, hu, hv⟩ := (graphFun_empty_true_iff G _).mp h
    simp [unitInput] at hu hv
    subst hu; subst hv
    exact (G.ne_of_adj huv rfl).elim

lemma graphFun_empty_pairInput {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) (huv : G.Adj u v) : graphFun G ∅ (pairInput u v) = true := by
  apply (graphFun_empty_true_iff G _).mpr
  exact ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩

/-! ## Section 2: Cones and OR-Reachability -/

def conesFrom (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) : List (List ℕ) :=
  gs.foldl (coneStep n) cs

lemma cones_eq_conesFrom (n : ℕ) (C : Circuit) :
    cones n C = conesFrom n C.gates [] := rfl

lemma conesFrom_append (n : ℕ) (gs₁ gs₂ : List Gate) (cs : List (List ℕ)) :
    conesFrom n (gs₁ ++ gs₂) cs = conesFrom n gs₂ (conesFrom n gs₁ cs) := by
  simp [conesFrom, List.foldl_append]

lemma conesFrom_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (conesFrom n gs cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp [conesFrom]
  | cons g gs ih =>
    simp only [conesFrom, List.foldl_cons] at ih ⊢
    rw [ih]; simp [coneStep]; omega

lemma conesFrom_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (j : ℕ) (hj : j < cs.length) :
    (conesFrom n gs cs).getD j [] = cs.getD j [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    have hj' : j < (coneStep n cs g).length := by simp [coneStep]; omega
    change (conesFrom n gs (coneStep n cs g)).getD j [] = cs.getD j []
    rw [ih (coneStep n cs g) hj']
    simp only [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

lemma cones_getD_eq (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    (cones n C).getD j [] =
      ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
        (fun w => (w - n) :: (cones n C).getD (w - n) []) := by
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    rw [List.cons_getElem_drop_succ, List.take_append_drop]
  set pre := C.gates.take j
  set gj := C.gates[j]
  set post := C.gates.drop (j + 1)
  have hpre_len : pre.length = j := by simp [pre]; omega
  have hcs_len : (conesFrom n pre []).length = j := by rw [conesFrom_len, hpre_len]; simp
  have h1 : cones n C = conesFrom n post (coneStep n (conesFrom n pre []) gj) := by
    rw [cones_eq_conesFrom, hsplit, conesFrom_append]; rfl
  have hlt : j < (coneStep n (conesFrom n pre []) gj).length := by
    simp [coneStep, hcs_len]
  rw [h1, conesFrom_getD_lt n post _ j hlt]
  have hmid : (coneStep n (conesFrom n pre []) gj).getD j [] =
      (gj.inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
        (fun w => (w - n) :: (conesFrom n pre []).getD (w - n) []) := by
    simp only [coneStep, hcs_len, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (le_of_eq hcs_len), Nat.sub_self,
      List.getElem?_cons_zero, Option.getD_some]
  rw [hmid, gateAt_eq_getElem C j hj]
  apply List.flatMap_congr
  intro w hw
  simp only [List.mem_filter, decide_eq_true_eq] at hw
  have hwlt : w - n < j := by omega
  have hwlt' : w - n < (coneStep n (conesFrom n pre []) gj).length := by
    simp [coneStep, hcs_len]; omega
  congr 1
  rw [conesFrom_getD_lt n post _ (w - n) hwlt']
  simp only [coneStep, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by omega : w - n < (conesFrom n pre []).length)]

lemma InCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) (hj : j < C.gates.length) :
    InCone n C i j ↔
      ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ w < n + j ∧ (i = w - n ∨ InCone n C i (w - n)) := by
  unfold InCone
  rw [cones_getD_eq n C j hj]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw1, hw2, hw3⟩, h⟩
    exact ⟨w, hw1, hw2, hw3, h⟩
  · rintro ⟨w, hw1, hw2, hw3, h⟩
    exact ⟨w, ⟨hw1, hw2, hw3⟩, h⟩

lemma InCone_ge_len (n : ℕ) (C : Circuit) (i j : ℕ) (hj : C.gates.length ≤ j) :
    ¬ InCone n C i j := by
  unfold InCone
  rw [List.getD_eq_default _ _ (by rw [cones_eq_conesFrom, conesFrom_len]; simp; omega)]
  simp

lemma InCone_lt (n : ℕ) (C : Circuit) {i j : ℕ} (h : InCone n C i j) : i < j := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    by_cases hj : j < C.gates.length
    · obtain ⟨w, _, hw1, hw2, h'⟩ := (InCone_iff n C i j hj).mp h
      rcases h' with rfl | h'
      · omega
      · have := ih (w - n) (by omega) h'
        omega
    · exact (InCone_ge_len n C i j (by omega) h).elim

lemma InCone_lt_len (n : ℕ) (C : Circuit) {i j : ℕ} (h : InCone n C i j) :
    i < C.gates.length := by
  by_cases hj : j < C.gates.length
  · exact lt_trans (InCone_lt n C h) hj
  · exact (InCone_ge_len n C i j (by omega) h).elim

lemma InCone_of_mem_inputs (n : ℕ) (C : Circuit) {i j : ℕ}
    (hj : j < C.gates.length) (hRB : ReadsBack n C)
    (hm : n + i ∈ (gateAt C j).inputs) : InCone n C i j := by
  rw [InCone_iff n C i j hj]
  have hlt := hRB j hj (n + i) hm
  exact ⟨n + i, hm, by omega, hlt, Or.inl (by omega)⟩

lemma InCone_trans (n : ℕ) (C : Circuit) {i j k : ℕ}
    (h1 : InCone n C i j) (h2 : InCone n C j k) : InCone n C i k := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    by_cases hk : k < C.gates.length
    · obtain ⟨w, hwm, hw1, hw2, h'⟩ := (InCone_iff n C j k hk).mp h2
      rw [InCone_iff n C i k hk]
      rcases h' with rfl | h'
      · exact ⟨w, hwm, hw1, hw2, Or.inr h1⟩
      · exact ⟨w, hwm, hw1, hw2, Or.inr (ih (w - n) (by omega) h')⟩
    · exact (InCone_ge_len n C j k (by omega) h2).elim

lemma InOutputCone_of_InCone (n : ℕ) (C : Circuit) {i j : ℕ}
    (h1 : InCone n C i j) (h2 : InOutputCone n C j) : InOutputCone n C i := by
  refine ⟨InCone_lt_len n C h1, ?_⟩
  rcases h2.2 with ho | ⟨hn, hc⟩
  · right
    refine ⟨by omega, ?_⟩
    rw [ho, Nat.add_sub_cancel_left]
    exact h1
  · right
    exact ⟨hn, InCone_trans n C h1 hc⟩

lemma mem_coneSet_iff (n : ℕ) (C : Circuit) (c : ℕ) (hc : c < C.gates.length) (i : ℕ) :
    i ∈ coneSet n C c ↔ i = c ∨ InCone n C i c := by
  unfold coneSet
  simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro (rfl | ⟨_, h⟩)
    · exact Or.inl rfl
    · exact Or.inr h
  · rintro (rfl | h)
    · exact Or.inl rfl
    · exact Or.inr ⟨InCone_lt_len n C h, h⟩

lemma coneSet_subset_range (n : ℕ) (C : Circuit) (c : ℕ) (hc : c < C.gates.length) :
    coneSet n C c ⊆ Finset.range C.gates.length := by
  intro i hi
  rw [Finset.mem_range]
  rcases (mem_coneSet_iff n C c hc i).mp hi with rfl | h
  · exact hc
  · exact InCone_lt_len n C h

lemma InCone_has_reader (n : ℕ) (C : Circuit) {i c : ℕ} (hc : c < C.gates.length)
    (h : InCone n C i c) :
    ∃ k ∈ coneSet n C c, n + i ∈ (gateAt C k).inputs := by
  induction c using Nat.strong_induction_on with
  | ind c ih =>
    obtain ⟨w, hwm, hw1, hw2, h'⟩ := (InCone_iff n C i c hc).mp h
    rcases h' with rfl | h'
    · refine ⟨c, (mem_coneSet_iff n C c hc c).mpr (Or.inl rfl), ?_⟩
      rwa [show n + (w - n) = w by omega]
    · have hwlt : w - n < C.gates.length := by omega
      obtain ⟨k, hk, hkin⟩ := ih (w - n) (by omega) hwlt h'
      refine ⟨k, ?_, hkin⟩
      rw [mem_coneSet_iff n C c hc]
      rcases (mem_coneSet_iff n C (w - n) hwlt k).mp hk with rfl | hk'
      · exact Or.inr ((InCone_iff n C (w - n) c hc).mpr ⟨w, hwm, hw1, hw2, Or.inl rfl⟩)
      · exact Or.inr ((InCone_iff n C k c hc).mpr ⟨w, hwm, hw1, hw2, Or.inr hk'⟩)

end PEqualNP.Outside.L_meta_2056_aux.TwoDirty.OneDirtyReduction.Support


namespace PEqualNP.Outside.L_meta_2056_aux.TwoDirty.OneDirtyReduction
open Finset

def large {α : Type*} [DecidableEq α] (S : ℕ → Finset α) (n : ℕ) : Finset ℕ :=
  (Finset.range n).filter fun w => 1 < (S w).card

theorem union_budget {α : Type*} [DecidableEq α] (S : ℕ → Finset α)
    (merge : ∀ w, 1 < (S w).card → ∃ a < w, ∃ b < w, S w=S a ∪ S b)
    (n : ℕ) (I : Finset ℕ) (hi : I ⊆ range n) :
    (I.biUnion S).card ≤ (large S n).card+I.card := by
  classical
  induction n generalizing I with
  | zero =>
    have : I=∅:=by simpa using hi
    simp [this]
  | succ n ind =>
    have step : large S (n+1) = if 1 < (S n).card then insert n (large S n) else large S n := by
      simp [large,range_add_one,filter_insert]
    have fresh : n∉large S n := by simp [large]
    by_cases hn : n∈I
    · let J:=I.erase n
      have hj : J⊆range n := by
        intro k hk
        obtain ⟨hne,hm⟩:=mem_erase.mp hk
        have lt:=mem_range.mp (hi hm)
        exact mem_range.mpr (by omega)
      have hjcard : J.card+1=I.card := card_erase_add_one hn
      have hu : I.biUnion S=S n ∪ J.biUnion S := by
        calc
          I.biUnion S=(insert n J).biUnion S := by rw [show insert n J=I from insert_erase hn]
          _ = _ := by simp
      by_cases big : 1 < (S n).card
      · obtain ⟨a,ha,b,hb,m⟩:=merge n big
        let K:=insert a (insert b J)
        have hk : K⊆range n := by simpa [K,insert_subset_iff] using
          (show a∈range n ∧ b∈range n ∧ J⊆range n from ⟨mem_range.mpr ha,mem_range.mpr hb,hj⟩)
        have kcard : K.card≤J.card+2 := by
          have p:=Finset.card_insert_le a (insert b J)
          have q:=Finset.card_insert_le b J
          dsimp [K];omega
        have eq : I.biUnion S=K.biUnion S := by rw [hu,m];simp [K,union_assoc]
        have h:=ind K hk
        rw [eq,step,ite_eq_left big,card_insert_of_notMem fresh]
        omega
      · have small : (S n).card≤1:=by omega
        have h:=ind J hj
        rw [hu,step,ite_eq_right big]
        have hle:=card_union_le (S n) (J.biUnion S)
        omega
    · have hj : I⊆range n := by
        intro k hk
        have lt:=mem_range.mp (hi hk)
        have ne:k≠n:=fun e=>hn (e ▸ hk)
        exact mem_range.mpr (by omega)
      have h:=ind I hj
      have bigger : large S n ⊆ large S (n+1) := by
        intro k hk
        obtain ⟨hl,hc⟩:=mem_filter.mp hk
        exact mem_filter.mpr ⟨mem_range.mpr (by have:=mem_range.mp hl;omega),hc⟩
      have hh:=card_le_card bigger
      omega

theorem marked_cone_count {α : Type*} [DecidableEq α] (S : ℕ → Finset α)
    (merge : ∀ w, 1 < (S w).card → ∃ a < w, ∃ b < w, S w=S a ∪ S b)
    (w : ℕ) : (S w).card≤(large S (w+1)).card+1 := by
  have h:=union_budget S merge (w+1) {w} (by simp)
  simpa using h

end PEqualNP.Outside.L_meta_2056_aux.TwoDirty.OneDirtyReduction

namespace PEqualNP.Outside.L_meta_2056_aux.TwoDirty.OneDirtyReduction
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.SplitCount
  PEqualNP.Core PEqualNP.Outside.L_meta_2056_aux.TwoDirty.OneDirtyReduction.Support

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

abbrev Sound (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (w : ℕ) :=
  ∀ x : Fin n → Bool, wireVal n C w x = true → graphFun G ∅ x = true

abbrev NoSoundOperands (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) :=
  ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
    ∀ w ∈ (gateAt C k).inputs, ¬ Sound G C w

theorem on_ones (ao : IsAO2 n C) (w : ℕ) (hb : w < n + C.gates.length) :
    wireVal n C w (fun _ => true) = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw : w<n
    · rw [show w=(⟨w,hw⟩ : Fin n).val from rfl, wireVal_input]
    let j:=w-n
    have hj : j<C.gates.length := by dsimp [j];omega
    have eq : w=n+j := by dsimp [j];omega
    rw [eq, ← gateVal_eq_wireVal, gateVal_eval n C j hj ao.2.1]
    have mem:=gateAt_mem C j hj
    obtain ⟨a,b,e⟩:=list_length_two (ao.2.2 _ mem)
    have ha:=ao.2.1 j hj a (by simp [e])
    have hh:=ao.2.1 j hj b (by simp [e])
    rw [e]
    simp only [List.map_cons,List.map_nil,ih a (by omega) (by omega),ih b (by omega) (by omega)]
    rcases ao.1 _ mem with ep|ep <;> rw [ep] <;> rfl

theorem mem_opnd {j w : ℕ} (ao : IsAO2 n C) (hj : j<C.gates.length)
    (hm : w∈(gateAt C j).inputs) : ∃ b : Fin 2, opnd C j b=w := by
  obtain ⟨a,b,e⟩:=list_length_two (ao.2.2 _ (gateAt_mem C j hj))
  simp only [e,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl|rfl
  · exact ⟨0,by simp [opnd,e]⟩
  · exact ⟨1,by simp [opnd,e]⟩

theorem sound_read {j w : ℕ} (ao : IsAO2 n C) (hf : IsLiftFixedPoint G C)
    (hl : ∀ k < C.gates.length, InOutputCone n C k) (hn : NoSoundOperands G C)
    (hj : j<C.gates.length) (hm : w∈(gateAt C j).inputs) (hs : Sound G C w) :
    (gateAt C j).op=GateOp.or ∧ BelowF G C j := by
  rcases ao.1 _ (gateAt_mem C j hj) with ha|ho
  · exact (hn j hj ha w hm hs).elim
  refine ⟨ho,?_⟩
  by_contra h
  obtain ⟨b,eb⟩:=mem_opnd ao hj hm
  have hs': IsImpWire G C w := ⟨hs, (fun _ => true),on_ones ao w (by have:=ao.2.1 j hj w hm; omega)⟩
  apply hf
  exact ⟨j,hj,b,hl j hj,ho,h,eb ▸ hs'⟩

theorem sound_ancestor {i j : ℕ} (ao : IsAO2 n C) (hf : IsLiftFixedPoint G C)
    (hl : ∀ k < C.gates.length, InOutputCone n C k) (hn : NoSoundOperands G C)
    (hi : BelowF G C i) (hj : j<C.gates.length) (hc : InCone n C i j) :
    (gateAt C j).op=GateOp.or ∧ BelowF G C j := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    obtain ⟨w,hm,hw,lt,h⟩:=(InCone_iff n C i j hj).mp hc
    apply sound_read ao hf hl hn hj hm
    have ew : w=n+(w-n) := by omega
    rcases h with rfl|h
    · rwa [ew] 
    · have ans:=ih (w-n) (by omega) (by omega) h
      rw [ew]
      exact ans.2

theorem top_form (ao : IsAO2 n C) (hf : IsLiftFixedPoint G C)
    (hl : ∀ k < C.gates.length, InOutputCone n C k) (hn : NoSoundOperands G C) :
    TopForm G C := by
  intro i _ j hj _ hi hjand hc
  have h:=(sound_ancestor ao hf hl hn hi hj hc).1
  rw [hjand] at h
  cases h

theorem unique_and_ancestor {g : ℕ} (ao : IsAO2 n C) (hf : IsLiftFixedPoint G C)
    (hl : ∀ k < C.gates.length, InOutputCone n C k) (hn : NoSoundOperands G C)
    (clean : ∀ k<C.gates.length, (gateAt C k).op=GateOp.and → k≠g → BelowF G C k)
    {i j : ℕ} (hj : j<C.gates.length) (a : (gateAt C i).op=GateOp.and)
    (b : (gateAt C j).op=GateOp.and) (h : InCone n C i j) : i=g := by
  by_contra he
  have hi:=InCone_lt_len n C h
  exact top_form ao hf hl hn i hi j hj a (clean i hi a he) b h

end PEqualNP.Outside.L_meta_2056_aux.TwoDirty.OneDirtyReduction
namespace PEqualNP.Outside.L_meta_2056_aux.TwoDirty.OneDirtyReduction
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.SplitCount
  PEqualNP.Core PEqualNP.Outside.L_meta_2056_aux.TwoDirty.OneDirtyReduction.Support
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

inductive Rise (n : ℕ) (C : Circuit) (t : ℕ) : ℕ → Prop
  | refl : Rise n C t t
  | step {w j : ℕ} : Rise n C t w → j<C.gates.length → (gateAt C j).op=GateOp.or →
    w∈(gateAt C j).inputs → Rise n C t (n+j)

def IsAndWire (n : ℕ) (C : Circuit) (w : ℕ) := n≤w ∧ w-n<C.gates.length ∧ (gateAt C (w-n)).op=GateOp.and

noncomputable def Raw (n : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin n) := by
  classical exact Finset.univ.filter fun v => Rise n C v.val w

theorem mem_raw {v : Fin n} {w} : v ∈ Raw n C w ↔ Rise n C v.val w := by
  classical simp [Raw]

theorem rise_le {u w : ℕ} (ao : IsAO2 n C) (h : Rise n C u w) : u≤w := by
  induction h with
  | refl => rfl
  | step _ hj _ hm ih => exact le_trans ih (ao.2.1 _ hj _ hm).le

theorem rise_gate {i w : ℕ} (ao : IsAO2 n C) (h : Rise n C (n+i) w) :
    n+i=w ∨ (n≤w ∧ InCone n C i (w-n)) := by
  induction h with
  | refl => exact Or.inl rfl
  | @step w j _ hj _ hm ih =>
    right
    refine ⟨by omega,?_⟩
    rw [Nat.add_sub_cancel_left]
    rw [InCone_iff n C i j hj]
    rcases ih with e|⟨hle,ih⟩
    · exact ⟨w,hm,by omega,ao.2.1 _ hj _ hm,Or.inl (by omega)⟩
    · exact ⟨w,hm,hle,ao.2.1 _ hj _ hm,Or.inr ih⟩

theorem rise_operand {i j w : ℕ} (ao : IsAO2 n C) (hj : j<C.gates.length)
    (hm : w ∈ (gateAt C j).inputs) (h : Rise n C (n+i) w) : InCone n C i j := by
  rcases rise_gate ao h with e|⟨hle,hc⟩
  · exact InCone_of_mem_inputs n C hj ao.2.1 (e ▸ hm)
  · exact (InCone_iff n C i j hj).mpr ⟨w,hm,hle,ao.2.1 _ hj _ hm,Or.inr hc⟩

def OrVal (n : ℕ) (C : Circuit) (v : ℕ → Bool) : Prop :=
  ∀ j < C.gates.length, (gateAt C j).op=GateOp.or →
    (v (n+j)=true ↔ ∃ w ∈ (gateAt C j).inputs, v w=true)

theorem val_is_or (ao : IsAO2 n C) (x : Fin n → Bool) : OrVal n C (fun w => wireVal n C w x) := by
  intro j hj ho
  dsimp only
  rw [←gateVal_eq_wireVal,gateVal_eval n C j hj ao.2.1,ho]
  change (List.map _ _).any id = true ↔ _
  simp

theorem rise_val {v : ℕ→Bool} (hv : OrVal n C v) {t w} (hr : Rise n C t w) (ht : v t=true) : v w=true := by
  induction hr with
  | refl => exact ht
  | step _ hj ho hm ih => exact (hv _ hj ho).mpr ⟨_,hm,ih⟩

theorem wire_sources {v : ℕ→Bool} (ao : IsAO2 n C) (hv : OrVal n C v) {w : ℕ}
    (hw : w<n+C.gates.length) : v w=true ↔
    (∃ t : Fin n, t∈Raw n C w ∧ v t.val=true) ∨
    ∃ i<C.gates.length, (gateAt C i).op=GateOp.and ∧ Rise n C (n+i) w ∧ v (n+i)=true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    constructor
    · intro ht
      by_cases hr : w<n
      · exact Or.inl ⟨⟨w,hr⟩,mem_raw.mpr .refl,ht⟩
      let j:=w-n
      have hj : j<C.gates.length := by dsimp [j];omega
      have e : w=n+j := by dsimp [j];omega
      rcases ao.1 _ (gateAt_mem C j hj) with ha|ho
      · exact Or.inr ⟨j,hj,ha,e ▸ Rise.refl,e ▸ ht⟩
      obtain ⟨u,hm,hu⟩:=(hv j hj ho).mp (e ▸ ht)
      have lt:=ao.2.1 j hj u hm
      rcases (ih u (by omega) (by omega)).mp hu with ⟨t,h,ht⟩|⟨i,hi,h,hh,ht⟩
      · exact Or.inl ⟨t,mem_raw.mpr (e ▸ .step (mem_raw.mp h) hj ho hm),ht⟩
      · exact Or.inr ⟨i,hi,h,e ▸ .step hh hj ho hm,ht⟩
    · rintro (⟨t,h,ht⟩|⟨_,_,_,h,ht⟩)
      · exact rise_val hv (mem_raw.mp h) ht
      · exact rise_val hv h ht

theorem operand_value {g j w : ℕ} (ao : IsAO2 n C) (hf : IsLiftFixedPoint G C)
    (hl : ∀ k < C.gates.length, InOutputCone n C k) (hn : NoSoundOperands G C)
    (clean : ∀ k<C.gates.length, (gateAt C k).op=GateOp.and → k≠g → BelowF G C k)
    (hg : g<C.gates.length) (ga : (gateAt C g).op=GateOp.and)
    (hj : j<C.gates.length) (ja : (gateAt C j).op=GateOp.and)
    (hm : w∈(gateAt C j).inputs) {v : ℕ→Bool} (hv : OrVal n C v) :
    v w=true ↔ (∃ t : Fin n, t∈Raw n C w ∧ v t.val=true) ∨
      (Rise n C (n+g) w ∧ v (n+g)=true) := by
  rw [wire_sources ao hv (by have:=ao.2.1 j hj w hm;omega)]
  constructor
  · rintro (h|⟨i,_,ia,r,e⟩)
    · exact Or.inl h
    · have hi:=unique_and_ancestor ao hf hl hn clean hj ia ja (rise_operand ao hj hm r)
      exact Or.inr (hi ▸ And.intro r e)
  · rintro (h|⟨r,e⟩)
    · exact Or.inl h
    · exact Or.inr ⟨g,hg,ga,r,e⟩

end PEqualNP.Outside.L_meta_2056_aux.TwoDirty.OneDirtyReduction
namespace PEqualNP.Outside.L_meta_2056_aux.TwoDirty.OneDirtyReduction
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.SplitCount
  PEqualNP.Core PEqualNP.Outside.L_meta_2056_aux.TwoDirty.OneDirtyReduction.Support

structure Model (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (g : ℕ) : Prop where
  ao : IsAO2 n C
  correct : circuitFun n C=graphFun G ∅
  fixed : IsLiftFixedPoint G C
  live : ∀ k<C.gates.length, InOutputCone n C k
  operands : NoSoundOperands G C
  singleton : ∀ k<C.gates.length, (gateAt C k).op=GateOp.and → ∀ p : Fin n, gateVal n C k (unitInput p)=false
  glt : g<C.gates.length
  gand : (gateAt C g).op=GateOp.and
  dirty : ¬ BelowF G C g
  clean : ∀ k<C.gates.length, (gateAt C k).op=GateOp.and → k≠g → BelowF G C k

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {g : ℕ}

def Hits (S : Finset (Fin n)) (x : Fin n→Bool) := ∃ t∈S,x t=true
noncomputable def side (n : ℕ) (C : Circuit) (j : ℕ) (b : Fin 2) := Raw n C (opnd C j b)
def flag (n : ℕ) (C : Circuit) (g j : ℕ) (b : Fin 2) := Rise n C (n+g) (opnd C j b)
def visible (n : ℕ) (C : Circuit) (j : ℕ) := Rise n C (n+j) C.output
def rawBoth (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n→Bool) := ∀ b : Fin 2, Hits (side n C j b) x
def remaining (n : ℕ) (C : Circuit) (g : ℕ) (x : Fin n→Bool) :=
  ∃ j<C.gates.length, (gateAt C j).op=GateOp.and ∧ j≠g ∧ visible n C j ∧ rawBoth n C j x

theorem opnd_mem (ao : IsAO2 n C) {j} (hj : j<C.gates.length) (b : Fin 2) :
    opnd C j b ∈ (gateAt C j).inputs := by
  obtain ⟨a,t,eq⟩:=list_length_two (ao.2.2 _ (gateAt_mem C j hj))
  fin_cases b <;> simp [opnd,eq]

theorem and_val (ao : IsAO2 n C) {j} (hj : j<C.gates.length) (ha : (gateAt C j).op=GateOp.and)
    (x : Fin n→Bool) : gateVal n C j x=true ↔ ∀ b : Fin 2, wireVal n C (opnd C j b) x=true := by
  rw [gateVal_eval n C j hj ao.2.1,ha]
  change (List.map _ _).all id = true ↔ _
  simp only [List.all_map,List.all_eq_true,Function.comp_apply,id_eq]
  constructor
  · intro h b
    exact h _ (opnd_mem ao hj b)
  · intro h w hm
    obtain ⟨b,rfl⟩:=mem_opnd ao hj hm
    exact h b

theorem side_val (m : Model n G C g) {j} (hj : j<C.gates.length) (ja : (gateAt C j).op=GateOp.and)
    (b : Fin 2) (x : Fin n→Bool) : wireVal n C (opnd C j b) x=true ↔
    Hits (side n C j b) x ∨ (flag n C g j b ∧ gateVal n C g x=true) := by
  have h:=operand_value m.ao m.fixed m.live m.operands m.clean m.glt m.gand hj ja
    (opnd_mem m.ao hj b) (val_is_or m.ao x)
  simpa only [wireVal_input,Hits,side,flag,gateVal_eq_wireVal] using h

theorem dirty_val (m : Model n G C g) (x : Fin n→Bool) :
    gateVal n C g x=true ↔ rawBoth n C g x := by
  rw [and_val m.ao m.glt m.gand]
  constructor
  · intro h b
    rcases (side_val m m.glt m.gand b x).mp (h b) with hh|⟨r,_⟩
    · exact hh
    · have hle:=rise_le m.ao r
      have hlt:=m.ao.2.1 g m.glt _ (opnd_mem m.ao m.glt b)
      omega
  · intro h b
    exact (side_val m m.glt m.gand b x).mpr (Or.inl (h b))

theorem hit_pair {S : Finset (Fin n)} {u v : Fin n} : Hits S (pairInput u v) ↔ u∈S ∨ v∈S := by
  simp [Hits,pairInput,exists_or, and_or_left]

theorem pair_graph {u v : Fin n} : graphFun G ∅ (pairInput u v)=true ↔ G.Adj u v := by
  rw [graphFun_empty_true_iff]
  constructor
  · rintro ⟨a,b,hab,ha,hb⟩
    simp only [pairInput,decide_eq_true_eq] at ha hb
    rcases ha with rfl|rfl <;> rcases hb with rfl|rfl <;> first | exact hab | exact hab.symm | exact False.elim (G.loopless.irrefl _ hab)
  · intro h; exact ⟨u,v,h,by simp [pairInput],by simp [pairInput]⟩

theorem side_ne (m : Model n G C g) (b : Fin 2) : (side n C g b).Nonempty := by
  have h:=on_ones m.ao (n+g) (by have:=m.glt;omega)
  obtain ⟨t,ht,_⟩:=(dirty_val m _).mp h b
  exact ⟨t,ht⟩

theorem side_disjoint (m : Model n G C g) : Disjoint (side n C g 0) (side n C g 1) := by
  rw [Finset.disjoint_left]
  intro u h0 h1
  have h: gateVal n C g (unitInput u)=true := (dirty_val m _).mpr (by
    intro b
    fin_cases b
    · exact ⟨u,h0,by simp [unitInput]⟩
    · exact ⟨u,h1,by simp [unitInput]⟩)
  rw [m.singleton g m.glt m.gand u] at h
  cases h

theorem not_both (m : Model n G C g) {j} (hj : j<C.gates.length)
    (ja : (gateAt C j).op=GateOp.and) (jg : j≠g) : ¬ ∀ b : Fin 2, flag n C g j b := by
  intro f
  apply m.dirty
  intro x hx
  apply m.clean j hj ja jg x
  apply (and_val m.ao hj ja x).mpr
  intro b
  exact (side_val m hj ja b x).mpr (Or.inr ⟨f b,hx⟩)

theorem out_lt (m : Model n G C g) : C.output<n+C.gates.length := by
  rcases (m.live g m.glt).2 with e|⟨hh,hc⟩
  · have:=m.glt;omega
  · by_contra! he
    exact InCone_ge_len n C g (C.output-n) (by omega) hc

theorem out_and (m : Model n G C g) (x : Fin n→Bool) : graphFun G ∅ x=true ↔
    ∃ j<C.gates.length, (gateAt C j).op=GateOp.and ∧ j≠g ∧ visible n C j ∧ gateVal n C j x=true := by
  have eval (y : Fin n→Bool) : wireVal n C C.output y = graphFun G ∅ y := congrFun m.correct y
  rw [←eval]
  constructor
  · intro h
    rcases (wire_sources m.ao (val_is_or m.ao x) (out_lt m)).mp h with ⟨u,hr,_⟩|⟨j,hj,ha,r,ht⟩
    · have h1:=rise_val (val_is_or m.ao (unitInput u)) (mem_raw.mp hr)
        (show wireVal n C u.val (unitInput u)=true by rw [wireVal_input];simp [unitInput])
      change wireVal n C C.output _=true at h1
      rw [eval,graphFun_empty_unitInput] at h1
      cases h1
    · refine ⟨j,hj,ha,?_,r,ht⟩
      intro eq
      subst j
      apply m.dirty
      intro y hy
      exact (eval y) ▸ rise_val (val_is_or m.ao y) r hy
  · rintro ⟨_,_,_,_,hr,hy⟩
    exact rise_val (val_is_or m.ao x) hr hy

theorem raw_sound (m : Model n G C g) {x : Fin n→Bool} (h : remaining n C g x) : graphFun G ∅ x=true := by
  obtain ⟨j,hj,ha,jg,r,h⟩:=h
  apply (out_and m x).mpr
  refine ⟨j,hj,ha,jg,r,(and_val m.ao hj ha x).mpr ?_⟩
  intro b
  exact (side_val m hj ha b x).mpr (Or.inl (h b))

end PEqualNP.Outside.L_meta_2056_aux.TwoDirty.OneDirtyReduction
namespace PEqualNP.Outside.L_meta_2056_aux.TwoDirty.OneDirtyReduction
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.SplitCount
  PEqualNP.Core PEqualNP.Outside.L_meta_2056_aux.TwoDirty.OneDirtyReduction.Support
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {g : ℕ}

def Missing (G : SimpleGraph (Fin n)) (C : Circuit) (g : ℕ) (u v : Fin n) :=
  G.Adj u v ∧ ¬ remaining n C g (pairInput u v)

theorem raw_pair_symm {u v : Fin n} : pairInput u v = pairInput v u := by
  funext x
  simp [pairInput,or_comm]

theorem top_witness (m : Model n G C g) {u v : Fin n} (h : Missing G C g u v) :
    gateVal n C g (pairInput u v)=true ∧
    ∃ j<C.gates.length, ∃ b t : Fin 2, b≠t ∧ (gateAt C j).op=GateOp.and ∧ j≠g ∧
      visible n C j ∧ flag n C g j b ∧ Hits (side n C j t) (pairInput u v) ∧
      (∀ x : Fin n→Bool, gateVal n C g x=true → Hits (side n C j t) x → graphFun G ∅ x=true) ∧
      (∀ x : Fin n→Bool, Hits (side n C j b) x → Hits (side n C j t) x → graphFun G ∅ x=true) := by
  obtain ⟨j,hj,ja,jg,r,e⟩:=(out_and m _).mp (pair_graph.mpr h.1)
  have nf : ¬ rawBoth n C j (pairInput u v) := fun hh=>h.2 ⟨j,hj,ja,jg,r,hh⟩
  obtain ⟨b,nb⟩:=Classical.not_forall.mp nf
  have sideTrue:= (and_val m.ao hj ja _).mp e
  obtain ⟨fb,eg⟩:=((side_val m hj ja b _).mp (sideTrue b)).resolve_left nb
  let t:Fin 2:=if b=0 then 1 else 0
  have ne : b≠t := by fin_cases b <;> decide
  have pair (q : Fin 2) : q=b ∨ q=t := by fin_cases b <;> fin_cases q <;> decide
  have nt : ¬ flag n C g j t := by
    intro ht
    apply not_both m hj ja jg
    intro q
    rcases pair q with rfl|rfl
    · exact fb
    · exact ht
  have single:=((side_val m hj ja t _).mp (sideTrue t)).resolve_right (fun hh=>nt hh.1)
  refine ⟨eg,j,hj,b,t,ne,ja,jg,r,fb,single,?_,?_⟩
  · intro x gx ht
    apply m.clean j hj ja jg x
    apply (and_val m.ao hj ja x).mpr
    intro q
    rcases pair q with rfl|rfl
    · exact (side_val m hj ja _ _).mpr (Or.inr ⟨fb,gx⟩)
    · exact (side_val m hj ja _ _).mpr (Or.inl ht)
  · intro x h1 h2
    apply m.clean j hj ja jg x
    apply (and_val m.ao hj ja x).mpr
    intro q
    rcases pair q with rfl|rfl
    · exact (side_val m hj ja _ _).mpr (Or.inl h1)
    · exact (side_val m hj ja _ _).mpr (Or.inl h2)

theorem dirty_pair (m : Model n G C g) {u v : Fin n} :
    gateVal n C g (pairInput u v)=true ↔
    (u∈side n C g 0 ∧ v∈side n C g 1) ∨ (v∈side n C g 0 ∧ u∈side n C g 1) := by
  rw [dirty_val m]
  have hd:=Finset.disjoint_left.mp (side_disjoint m)
  constructor
  · intro h
    rcases hit_pair.mp (h 0) with hu|hv <;> rcases hit_pair.mp (h 1) with hu'|hv'
    · exact False.elim (hd hu hu')
    · exact Or.inl ⟨hu,hv'⟩
    · exact Or.inr ⟨hv,hu'⟩
    · exact False.elim (hd hv hv')
  · intro h b
    apply hit_pair.mpr
    fin_cases b <;> rcases h with h|h
    · exact Or.inl h.1
    · exact Or.inr h.1
    · exact Or.inr h.2
    · exact Or.inl h.2

theorem universal_loss (m : Model n G C g) {u v : Fin n} (h : Missing G C g u v)
    (hu : u∈side n C g 0) (hv : v∈side n C g 1) :
    (∀ v'∈side n C g 1, G.Adj u v') ∨ (∀ u'∈side n C g 0, G.Adj u' v) := by
  obtain ⟨_,j,_,_,t,_,_,_,_,_,hh,force,_⟩:=top_witness m h
  rcases hit_pair.mp hh with up|vp
  · left
    intro v' hv'
    apply pair_graph.mp
    apply force
    · exact (dirty_pair m).mpr (Or.inl ⟨hu,hv'⟩)
    · exact hit_pair.mpr (Or.inl up)
  · right
    intro u' hu'
    apply pair_graph.mp
    apply force
    · exact (dirty_pair m).mpr (Or.inl ⟨hu',hv⟩)
    · exact hit_pair.mpr (Or.inr vp)

theorem loss_orientation (m : Model n G C g) {u v : Fin n} (h : Missing G C g u v) :
    (u∈side n C g 0 ∧ v∈side n C g 1) ∨ (v∈side n C g 0 ∧ u∈side n C g 1) :=
  (dirty_pair m).mp (top_witness m h).1

end PEqualNP.Outside.L_meta_2056_aux.TwoDirty.OneDirtyReduction
namespace PEqualNP.Outside.L_meta_2056_aux.TwoDirty.OneDirtyReduction
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.SplitCount
  PEqualNP.Core PEqualNP.Outside.L_meta_2056_aux.TwoDirty.OneDirtyReduction.Support
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {g : ℕ}

def sole (n : ℕ) (C : Circuit) (g h : ℕ) := ∀ j<C.gates.length, n+g∈(gateAt C j).inputs → j=h

theorem rise_trans {a b w : ℕ} (r : Rise n C a b) (s : Rise n C b w) : Rise n C a w := by
  induction s with
  | refl => exact r
  | step _ hj ho hm ih => exact .step ih hj ho hm

theorem rise_via {h w : ℕ} (one : sole n C g h) (r : Rise n C (n+g) w) :
    w=n+g ∨ Rise n C (n+h) w := by
  induction r with
  | refl => exact Or.inl rfl
  | @step t j _ hj ho hm ih =>
    right
    rcases ih with rfl|ih
    · have hh:=one j hj hm
      subst j
      exact .refl
    · exact .step ih hj ho hm

theorem visible_raw_common {h j : ℕ} {z : Fin n} (one : sole n C g h)
    (hor : (gateAt C h).op=GateOp.or) (hz : z∈Raw n C (n+h))
    (ao : IsAO2 n C) (hj : j<C.gates.length) (ja : (gateAt C j).op=GateOp.and)
    (b : Fin 2) (f : flag n C g j b) : z∈side n C j b := by
  apply mem_raw.mpr
  apply rise_trans (mem_raw.mp hz)
  rcases rise_via one f with e|r
  · have eq:=one j hj (e ▸ opnd_mem ao hj b)
    exact (by rw [eq,hor] at ja; cases ja)
  · exact r

theorem unique_common {a b v : Fin n} (m : Model n G C g) {h} (one : sole n C g h)
    (hor : (gateAt C h).op=GateOp.or) (hv : v∈Raw n C (n+h))
    (lost : Missing G C g a b) (ha : a∈side n C g 0) (hb : b∈side n C g 1) :
    (G.Adj v a ∨ ∀ x∈side n C g 0, G.Adj x b) ∧
    (G.Adj v b ∨ ∀ x∈side n C g 1, G.Adj a x) := by
  obtain ⟨_,j,hj,p,t,_,ja,_,_,fp,ht,force,raw⟩:=top_witness m lost
  have inz:=visible_raw_common one hor hv m.ao hj ja p fp
  rcases hit_pair.mp ht with aS|bS
  · refine ⟨Or.inl (pair_graph.mp (raw _ (hit_pair.mpr (Or.inl inz)) (hit_pair.mpr (Or.inr aS)))),Or.inr ?_⟩
    intro x hx
    exact pair_graph.mp (force _ ((dirty_pair m).mpr (Or.inl ⟨ha,hx⟩)) (hit_pair.mpr (Or.inl aS)))
  · refine ⟨Or.inr ?_,Or.inl (pair_graph.mp (raw _ (hit_pair.mpr (Or.inl inz)) (hit_pair.mpr (Or.inr bS))))⟩
    intro x hx
    exact pair_graph.mp (force _ ((dirty_pair m).mpr (Or.inl ⟨hx,hb⟩)) (hit_pair.mpr (Or.inr bS)))

theorem single_reader_mixed {c d a b : Fin n} (m : Model n G C g)
    (s : Fin n→Bool) (bip : ∀ x y : Fin n, G.Adj x y → s x≠s y)
    {h} (one : sole n C g h) (hor : (gateAt C h).op=GateOp.or)
    (hc : c∈side n C g 0) (hd : d∈side n C g 1) (ha : a∈side n C g 0) (hb : b∈side n C g 1)
    (hcB : ∀ x∈side n C g 1,G.Adj c x)
    (haB : ¬∀ x∈side n C g 1,G.Adj a x) (hbA : ¬∀ x∈side n C g 0,G.Adj x b)
    (loss₁ : Missing G C g c b) (loss₂ : Missing G C g a d) : Raw n C (n+h)=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have zc:=((unique_common m one hor hz loss₁ hc hb).1).resolve_right hbA
  have zd:=((unique_common m one hor hz loss₂ ha hd).2).resolve_right haB
  have q:=bip c d (hcB d hd)
  have p:=bip z c zc
  have r:=bip z d zd
  exact (show ∀ a b c : Bool, a≠b → a≠c → b≠c → False by decide) (s z) (s c) (s d) p r q

theorem common_unique {c d a b : Fin n} (no4 : NoFourCycle G) (hne : a≠b)
    (ca : G.Adj c a) (cb : G.Adj c b) (da : G.Adj d a) (db : G.Adj d b) : c=d := by
  classical
  by_contra h
  have small:=no4 a b hne
  rw [Finset.card_le_one] at small
  exact h (small c (by simp [ca.symm,cb.symm]) d (by simp [da.symm,db.symm]))

end PEqualNP.Outside.L_meta_2056_aux.TwoDirty.OneDirtyReduction
namespace PEqualNP.Outside.L_meta_2056_aux.TwoDirty.OneDirtyReduction
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.SplitCount
  PEqualNP.Core PEqualNP.Outside.L_meta_2056_aux.TwoDirty.OneDirtyReduction.Support

inductive Formula (n : ℕ) where
  | lit (u : Fin n)
  | bin (isAnd : Bool) (a b : Formula n)
  deriving DecidableEq

namespace Formula
variable {n : ℕ}
def eval (x : Fin n→Bool) : Formula n→Bool
  | lit u => x u
  | bin true a b => a.eval x && b.eval x
  | bin false a b => a.eval x || b.eval x

def rank : Formula n → ℕ
  | lit _ => 0
  | bin _ a b => a.rank+b.rank+1

def depth : Formula n → ℕ
  | lit _ => 0
  | bin f a b => max a.depth b.depth + (if f then 1 else 0)

def ops : Formula n→Finset (Formula n)
  | lit _ => ∅
  | bin f a b => insert (bin f a b) (a.ops ∪ b.ops)

theorem sub_ops {root e : Formula n} (h : e∈root.ops) : e.ops⊆root.ops := by
  induction root with
  | lit => simp [ops] at h
  | bin f a b ia ib =>
    rw [ops,Finset.mem_insert, Finset.mem_union] at h
    rcases h with rfl|ha|hb
    · exact Finset.Subset.rfl
    · intro t ht; exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (ia ha ht))
    · intro t ht; exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (ib hb ht))

theorem op_bin {root e : Formula n} (h : e∈root.ops) : ∃ f a b, e=bin f a b := by
  induction root with
  | lit => simp [ops] at h
  | bin f a b ia ib =>
    simp only [ops,Finset.mem_insert,Finset.mem_union] at h
    rcases h with rfl|ha|hb
    · exact ⟨_,_,_,rfl⟩
    · exact ia ha
    · exact ib hb

theorem sub_depth {root e : Formula n} (h : e∈root.ops) : e.depth≤root.depth := by
  induction root with
  | lit => simp [ops] at h
  | bin f a b ia ib =>
    simp only [ops,Finset.mem_insert,Finset.mem_union] at h
    rcases h with rfl|ha|hb
    · exact le_rfl
    · have:=ia ha; simp only [depth];omega
    · have:=ib hb; simp only [depth];omega

noncomputable def order (r : Formula n) : List (Formula n) :=
  r.ops.toList.mergeSort fun a b => decide (a.rank≤b.rank)

theorem order_perm (r : Formula n) : r.order.Perm r.ops.toList := List.mergeSort_perm _ _
theorem mem_order {r e : Formula n} : e∈r.order ↔ e∈r.ops :=
  (order_perm _).mem_iff.trans Finset.mem_toList
theorem order_nd (r : Formula n) : r.order.Nodup := (order_perm r).nodup_iff.mpr r.ops.nodup_toList
theorem order_len (r : Formula n) : r.order.length=r.ops.card := by rw [(order_perm r).length_eq,Finset.length_toList]
theorem order_sorted (r : Formula n) : r.order.Pairwise (fun a b => a.rank≤b.rank) := by
  have h:=List.pairwise_mergeSort (le:=fun a b : Formula n=>decide (a.rank≤b.rank))
    (by simp only [decide_eq_true_eq];exact fun _ _ _ => Nat.le_trans)
    (by intro a b;simpa using (le_total a.rank b.rank)) r.ops.toList
  simpa [order] using h

noncomputable def wire (root : Formula n) : Formula n→ℕ
  | lit v => v.val
  | bin f a b => n+root.order.idxOf (bin f a b)

noncomputable def row (root : Formula n) : Formula n→Gate
  | lit _ => ⟨.or,[0,0]⟩
  | bin f a b => ⟨if f then .and else .or,[wire root a,wire root b]⟩

noncomputable def circuit (root : Formula n) : Circuit := ⟨root.order.map (row root),wire root root⟩

theorem circuit_len (root : Formula n) : root.circuit.gates.length=root.order.length := by simp [circuit]
theorem circuit_size (root : Formula n) : root.circuit.size=root.ops.card := by
  change root.circuit.gates.length = _
  rw [circuit_len,order_len]

theorem wire_lt (root : Formula n) {j f a b} (hj : j<root.order.length)
    (eq : root.order[j]=bin f a b) {e : Formula n} (he : e=a ∨ e=b) :
    wire root e < n+j := by
  cases e with
  | lit u => exact lt_of_lt_of_le u.isLt (Nat.le_add_right ..)
  | bin p x y =>
    let t:=bin p x y
    have hBin : bin f a b∈root.ops := mem_order.mp (eq ▸ List.getElem_mem hj)
    have ht : t∈root.order := by
      apply mem_order.mpr
      apply sub_ops hBin
      dsimp [t]
      rcases he with rfl|rfl <;> simp [ops]
    have hi:=List.idxOf_lt_length_of_mem ht
    have get:=List.getElem_idxOf hi
    have rk : t.rank<(root.order[j]).rank := by
      rw [eq];simp only [rank]
      rcases he with e|e <;> change t = _ at e <;> rw [←e] <;> omega
    change n+root.order.idxOf t<n+j
    by_contra! h
    have le : j≤root.order.idxOf t := by omega
    rcases le.eq_or_lt with e|lt
    · have hget : root.order[j]=t := by subst j;exact get
      rw [hget] at rk;omega
    · have hh:=List.pairwise_iff_getElem.mp (order_sorted root) j _ hj hi lt
      rw [get] at hh;omega

theorem get_row (r : Formula n) (j) (hj : j<r.circuit.gates.length) :
    gateAt r.circuit j=row r (r.order[j]'(by simpa [circuit_len] using hj)) := by
  rw [gateAt_eq_getElem _ _ hj]
  exact List.getElem_map ..

theorem circuit_ao (r : Formula n) : IsAO2 n r.circuit := by
  refine ⟨?_,?_,?_⟩
  · intro gt hm
    obtain ⟨e,_,rfl⟩:=List.mem_map.mp (show gt∈r.order.map (row r) from hm)
    cases e with
    | lit => exact Or.inr rfl
    | bin f a b => cases f <;> simp [row]
  · intro j hj w hw
    rw [get_row r j hj] at hw
    have hj':j<r.order.length := by simpa [circuit_len] using hj
    obtain ⟨f,a,b,e⟩:=op_bin (mem_order.mp (List.getElem_mem hj'))
    rw [e] at hw
    simp only [row,List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl|rfl
    · exact wire_lt r hj' e (Or.inl rfl)
    · exact wire_lt r hj' e (Or.inr rfl)
  · intro gt hm
    obtain ⟨e,_,rfl⟩:=List.mem_map.mp (show gt∈r.order.map (row r) from hm)
    cases e <;> rfl

theorem eval_wire (r e : Formula n) (h : e.ops⊆r.ops) (x : Fin n→Bool) :
    wireVal n r.circuit (wire r e) x=e.eval x := by
  induction e with
  | lit u => exact wireVal_input n r.circuit u x
  | bin f a b ia ib =>
    have mem : bin f a b∈r.order := mem_order.mpr (h (by simp [ops]))
    have ht:=List.idxOf_lt_length_of_mem mem
    have ht' : r.order.idxOf (bin f a b)<r.circuit.gates.length := by rwa [circuit_len]
    rw [wire,←gateVal_eq_wireVal,gateVal_eval _ _ _ ht' (circuit_ao r).2.1,get_row _ _ ht',List.getElem_idxOf ht]
    have le₁ : a.ops⊆r.ops := fun t ht=>h (by simp [ops,ht])
    have le₂ : b.ops⊆r.ops := fun t ht=>h (by simp [ops,ht])
    cases f <;> simp [row, eval, eval_and_two,eval_or_two,ia le₁,ib le₂]

theorem circuit_eval (r : Formula n) (x : Fin n→Bool) : circuitFun n r.circuit x=r.eval x :=
  eval_wire r r (Finset.Subset.rfl) x

theorem child_depth (root : Formula n) {j i : ℕ} (hj : j<root.circuit.gates.length)
    (hw : n+i∈(gateAt root.circuit j).inputs) :
    ∃ hi : i<root.order.length, (root.order[i]).depth + (if (gateAt root.circuit j).op matches .and then 1 else 0) ≤
      (root.order[j]'(by simpa [circuit_len] using hj)).depth := by
  have hj':j<root.order.length := by simpa [circuit_len] using hj
  obtain ⟨f,a,b,e⟩:=op_bin (mem_order.mp (List.getElem_mem hj'))
  have sub (q : Formula n) (hq : q=a ∨ q=b) (he : n+i=wire root q) :
      ∃ hi : i<root.order.length, root.order[i]=q := by
    cases q with
    | lit u => change n+i=u.val at he;have:=u.isLt;omega
    | bin p u v =>
      have be : bin p u v∈root.order := by
        apply mem_order.mpr
        apply sub_ops (mem_order.mp (e ▸ List.getElem_mem hj'))
        rcases hq with rfl|rfl <;> simp [ops]
      change n+i=n+root.order.idxOf (bin p u v) at he
      have hi : i=root.order.idxOf (bin p u v) := by omega
      subst i
      exact ⟨List.idxOf_lt_length_of_mem be,List.getElem_idxOf _⟩
  rw [get_row _ _ hj,e] at hw ⊢
  simp only [row,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with h|h
  · obtain ⟨hi,eq⟩:=sub a (Or.inl rfl) h
    refine ⟨hi,?_⟩;rw [eq];cases f <;> simp [row,depth]
  · obtain ⟨hi,eq⟩:=sub b (Or.inr rfl) h
    refine ⟨hi,?_⟩;rw [eq];cases f <;> simp [row,depth]

theorem ancestor_depth (r : Formula n) {i j : ℕ} (hj : j<r.circuit.gates.length) (h : InCone n r.circuit i j) :
    ∃ hi : i<r.order.length, (r.order[i]).depth + (if (gateAt r.circuit j).op matches .and then 1 else 0) ≤
      (r.order[j]'(by simpa [circuit_len] using hj)).depth := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    obtain ⟨w,hm,hw,hl,hr⟩:=(InCone_iff n r.circuit i j hj).mp h
    have eq : w=n+(w-n) := by omega
    have ⟨hk,dk⟩:=child_depth r hj (eq ▸ hm)
    rcases hr with rfl|hr
    · exact ⟨hk,dk⟩
    · have ⟨hi,di⟩:=ih (w-n) (by omega) (by simpa [circuit_len] using hk) hr
      exact ⟨hi,by omega⟩

theorem circuit_flat (r : Formula n) (d : r.depth≤1) :
    ∀ i<r.circuit.gates.length, ∀ j<r.circuit.gates.length,
      (gateAt r.circuit i).op=GateOp.and → (gateAt r.circuit j).op=GateOp.and → ¬InCone n r.circuit i j := by
  intro i hi j hj ai aj h
  obtain ⟨hi',ineq⟩:=ancestor_depth r hj h
  rw [aj] at ineq
  obtain ⟨f,a,b,e⟩:=op_bin (mem_order.mp (List.getElem_mem hi'))
  have ge : 1≤(r.order[i]).depth := by
    rw [get_row _ _ hi,e] at ai
    rw [e]; cases f <;> simp_all [row,depth]
  have ub:=sub_depth (mem_order.mp (List.getElem_mem (show j<r.order.length by simpa [circuit_len] using hj)))
  change (r.order[i]).depth+1≤_ at ineq
  omega

end Formula
end PEqualNP.Outside.L_meta_2056_aux.TwoDirty.OneDirtyReduction
namespace PEqualNP.Outside.L_meta_2056_aux.TwoDirty.OneDirtyReduction
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.SplitCount
  PEqualNP.Core PEqualNP.Outside.L_meta_2056_aux.TwoDirty.OneDirtyReduction.Support

variable {n : ℕ} {C : Circuit}
abbrev Opt (n : ℕ) := Option (Formula n)

def joinF (f : Bool) (a b : Opt n) : Opt n :=
  match a,b with
  | some x,some y => some (.bin f x y)
  | none,other | other,none => if f then none else other

def oe (e : Opt n) (x : Fin n→Bool) := e.any (Formula.eval x)
def og (e : Opt n) := (e.map Formula.ops).getD ∅
def od (e : Opt n) := (e.map Formula.depth).getD 0

theorem oe_join (f : Bool) (a b : Opt n) (x : Fin n→Bool) :
    oe (joinF f a b) x = if f then oe a x && oe b x else oe a x || oe b x := by
  cases a <;> cases b <;> cases f <;> simp [oe,joinF,Formula.eval]

theorem og_join {f : Bool} {a b : Opt n} {t : Formula n} (h : t∈og (joinF f a b)) :
    (∃ x y, a=some x ∧ b=some y ∧ t=.bin f x y) ∨ t∈og a ∨ t∈og b := by
  cases a <;> cases b <;> cases f <;> simp_all [joinF,og,Formula.ops]

theorem og_join_card (f : Bool) (a b : Opt n) :
    (og (joinF f a b)).card ≤ (og a).card+(og b).card+1 := by
  cases a with
  | none => cases b <;> cases f <;> simp [joinF,og]
  | some x =>
    cases b with
    | none => cases f <;> simp [joinF,og]
    | some y =>
      simpa [joinF,og,Formula.ops] using
        (Finset.card_insert_le (.bin f x y) (x.ops∪y.ops)).trans (by have:=Finset.card_union_le x.ops y.ops;omega)

theorem od_join (f : Bool) (a b : Opt n) :
    od (joinF f a b)≤ max (od a) (od b)+(if f then 1 else 0) := by
  cases a <;> cases b <;> cases f <;> simp [od,joinF,Formula.depth]

abbrev FoldPair (n : ℕ) := Opt n × Opt n

def foldAt {α : Type*} (n : ℕ) (C : Circuit) (ao : IsAO2 n C) (input : Fin n→α) (fallback : α)
    (gate : ℕ→α→α→α) (w : ℕ) : α :=
  if h:w<n then input ⟨w,h⟩
  else if _hj:w-n<C.gates.length then
    gate (w-n) (foldAt n C ao input fallback gate (opnd C (w-n) 0))
      (foldAt n C ao input fallback gate (opnd C (w-n) 1))
  else fallback
termination_by w
decreasing_by all_goals have h0:=ao.2.1 (w-n) _hj _ (opnd_mem ao _hj 0); have h1:=ao.2.1 (w-n) _hj _ (opnd_mem ao _hj 1); omega

theorem fold_input {α : Type*} {ao : IsAO2 n C} (input : Fin n→α) (fallback : α)
    (gate : ℕ→α→α→α) (i : Fin n) : foldAt n C ao input fallback gate i.val=input i := by
  rw [foldAt, dite_eq_left i.isLt]

theorem fold_gate {α : Type*} {ao : IsAO2 n C} (input : Fin n→α) (fallback : α)
    (gate : ℕ→α→α→α) {j : ℕ} (hj : j<C.gates.length) :
    foldAt n C ao input fallback gate (n+j)=gate j
      (foldAt n C ao input fallback gate (opnd C j 0)) (foldAt n C ao input fallback gate (opnd C j 1)) := by
  rw [foldAt,dite_eq_right (by omega),Nat.add_sub_cancel_left,dite_eq_left hj]

local instance : DecidableEq GateOp := gateOpDecEq

def project (ao : IsAO2 n C) (g : ℕ) (w : ℕ) : FoldPair n :=
  foldAt n C ao (fun i => (some (.lit i),none)) (none,none)
    (fun j a b => if (gateAt C j).op=GateOp.or then (joinF false a.1 b.1,joinF false a.2 b.2)
        else (none,if j=g then none else joinF true a.1 b.1)) w

theorem project_input (ao : IsAO2 n C) (g : ℕ) (i : Fin n) :
    project ao g i.val=(some (.lit i),none) := fold_input .. 

theorem project_or (ao : IsAO2 n C) (g : ℕ) {j : ℕ} (hj : j<C.gates.length) (ho : (gateAt C j).op=GateOp.or) :
    project ao g (n+j)=(joinF false (project ao g (opnd C j 0)).1 (project ao g (opnd C j 1)).1,
      joinF false (project ao g (opnd C j 0)).2 (project ao g (opnd C j 1)).2) := by
  unfold project
  rw [fold_gate _ _ _ hj,ite_eq_left ho]

theorem project_and (ao : IsAO2 n C) (g : ℕ) {j : ℕ} (hj : j<C.gates.length) (ha : (gateAt C j).op=GateOp.and) :
    project ao g (n+j)=(none,if j=g then none else
        joinF true (project ao g (opnd C j 0)).1 (project ao g (opnd C j 1)).1) := by
  unfold project
  rw [fold_gate _ _ _ hj,ha,ite_eq_right (by decide : GateOp.and≠GateOp.or)]

theorem rise_input_iff {t} {i : Fin n} : Rise n C t i.val ↔ t=i.val := by
  constructor
  · intro h
    have bound:=i.isLt
    generalize e : i.val=w at h bound ⊢
    cases h with
    | refl => rfl
    | step => omega
  · rintro rfl;exact .refl

theorem rise_gate_iff {t j} : Rise n C t (n+j) ↔ t=n+j ∨
    ((gateAt C j).op=GateOp.or ∧ j<C.gates.length ∧ ∃ w∈(gateAt C j).inputs, Rise n C t w) := by
  constructor
  · intro h
    generalize e : n+j=w at h ⊢
    cases h with
    | refl => exact Or.inl rfl
    | @step u k r hk ho hm =>
      have eq : j=k := by omega
      subst k
      exact Or.inr ⟨ho,hk,u,hm,r⟩
  · rintro (rfl|⟨ho,hj,w,hm,r⟩)
    · exact .refl
    · exact .step r hj ho hm

theorem low_eval (ao : IsAO2 n C) (g : ℕ) (x : Fin n→Bool) (w) (bound : w<n+C.gates.length) :
    oe (project ao g w).1 x=true ↔ Hits (Raw n C w) x := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases h : w<n
    · let u : Fin n:=⟨w,h⟩
      rw [show w=u.val from rfl,project_input]
      simp [oe,Formula.eval,Hits,mem_raw,rise_input_iff,Fin.val_inj]
    let j:=w-n
    have hj : j<C.gates.length := by dsimp [j];omega
    have eq : w=n+j := by dsimp [j];omega
    have sub (b : Fin 2) := ao.2.1 j hj _ (opnd_mem ao hj b)
    rw [eq]
    rcases ao.1 _ (gateAt_mem C j hj) with ha|ho
    · rw [project_and ao g hj ha]
      simp only [oe,Option.any_none,Bool.false_eq_true,false_iff]
      rintro ⟨u,hu,_⟩
      rcases rise_gate_iff.mp (mem_raw.mp hu) with e|⟨e,_⟩
      · have:=u.isLt;omega
      · rw [ha] at e;cases e
    · rw [project_or ao g hj ho,oe_join]
      simp only [Bool.false_eq_true,ite_false,Bool.or_eq_true]
      constructor
      · rintro (hl|hr)
        · obtain ⟨u,hu,hx⟩:=(ih _ (by have:=sub 0;omega) (by have:=sub 0;omega)).mp hl
          exact ⟨u,mem_raw.mpr (.step (mem_raw.mp hu) hj ho (opnd_mem ao hj 0)),hx⟩
        · obtain ⟨u,hu,hx⟩:=(ih _ (by have:=sub 1;omega) (by have:=sub 1;omega)).mp hr
          exact ⟨u,mem_raw.mpr (.step (mem_raw.mp hu) hj ho (opnd_mem ao hj 1)),hx⟩
      · rintro ⟨u,hu,hx⟩
        rcases rise_gate_iff.mp (mem_raw.mp hu) with e|⟨_,_,t,hm,ht⟩
        · have:=u.isLt;omega
        obtain ⟨b,rfl⟩:=mem_opnd ao hj hm
        have h':=(ih _ (by have:=sub b;omega) (by have:=sub b;omega)).mpr ⟨u,mem_raw.mpr ht,hx⟩
        fin_cases b
        · exact Or.inl h'
        · exact Or.inr h'

end PEqualNP.Outside.L_meta_2056_aux.TwoDirty.OneDirtyReduction
namespace PEqualNP.Outside.L_meta_2056_aux.TwoDirty.OneDirtyReduction
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.SplitCount
  PEqualNP.Core PEqualNP.Outside.L_meta_2056_aux.TwoDirty.OneDirtyReduction.Support
variable {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {g : ℕ}

theorem eval_ones (f : Formula n) : f.eval (fun _=>true)=true := by
  induction f with
  | lit => rfl
  | bin op a b ia ib => cases op <;> simp [Formula.eval,ia,ib]

theorem some_iff (o : Opt n) : o.isSome=true ↔ oe o (fun _=>true)=true := by
  cases o <;> simp [oe,eval_ones]

theorem low_some (ao : IsAO2 n C) (g w) (hw : w<n+C.gates.length) :
    (project ao g w).1.isSome=true ↔ (Raw n C w).Nonempty := by
  rw [some_iff, low_eval ao g _ w hw]
  simp [Hits,Finset.Nonempty]

theorem up_or (ao : IsAO2 n C) (g : ℕ) (x : Fin n→Bool) :
    OrVal n C (fun w=>oe (project ao g w).2 x) := by
  intro j hj ho
  dsimp only
  rw [project_or ao g hj ho,oe_join]
  simp only [Bool.false_eq_true,ite_false,Bool.or_eq_true]
  constructor
  · rintro (h|h)
    · exact ⟨_,opnd_mem ao hj 0,h⟩
    · exact ⟨_,opnd_mem ao hj 1,h⟩
  · rintro ⟨w,hm,h⟩
    obtain ⟨b,rfl⟩:=mem_opnd ao hj hm
    fin_cases b
    · exact Or.inl h
    · exact Or.inr h

theorem up_and (ao : IsAO2 n C) (g : ℕ) (x : Fin n→Bool) {i} (hi : i<C.gates.length)
    (ha : (gateAt C i).op=GateOp.and) : oe (project ao g (n+i)).2 x=true ↔ i≠g ∧ rawBoth n C i x := by
  rw [project_and ao g hi ha]
  by_cases h : i=g
  · simp [h,oe]
  simp only [h,ite_false,oe_join,ite_true,Bool.and_eq_true,ne_eq,not_false_eq_true,true_and]
  have sub (b : Fin 2) : opnd C i b<n+C.gates.length := by have:=ao.2.1 i hi _ (opnd_mem ao hi b);omega
  rw [low_eval ao g _ _ (sub 0),low_eval ao g _ _ (sub 1)]
  constructor
  · rintro ⟨l,r⟩ b;fin_cases b
    · exact l
    · exact r
  · intro p;exact ⟨p 0,p 1⟩

theorem up_eval (ao : IsAO2 n C) (g : ℕ) (x : Fin n→Bool) (w) (bound : w<n+C.gates.length) :
    oe (project ao g w).2 x=true ↔ ∃ i<C.gates.length, (gateAt C i).op=GateOp.and ∧ i≠g ∧
      Rise n C (n+i) w ∧ rawBoth n C i x := by
  have h:=wire_sources ao (up_or ao g x) bound
  rw [h]
  constructor
  · rintro (⟨v,_,e⟩|⟨i,hi,ia,hr,e⟩)
    · rw [project_input] at e;cases e
    · obtain ⟨ne,eh⟩:=(up_and ao g x hi ia).mp e
      exact ⟨i,hi,ia,ne,hr,eh⟩
  · rintro ⟨i,hi,ia,ne,hr,eh⟩
    exact Or.inr ⟨i,hi,ia,hr,(up_and ao g x hi ia).mpr ⟨ne,eh⟩⟩

theorem projected_output (m : Model n G C g) (x : Fin n→Bool) :
    oe (project m.ao g C.output).2 x=true ↔ remaining n C g x :=
  up_eval m.ao g x C.output (out_lt m)

theorem project_depth (ao : IsAO2 n C) (g w) (bound : w<n+C.gates.length) :
    od (project ao g w).1=0 ∧ od (project ao g w).2≤1 := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases h : w<n
    · rw [show w=(⟨w,h⟩ : Fin n).val from rfl,project_input]
      exact ⟨rfl,Nat.zero_le 1⟩
    let j:=w-n
    have hj : j<C.gates.length := by dsimp [j];omega
    have eq : w=n+j := by dsimp [j];omega
    have sub (b : Fin 2) := ao.2.1 j hj _ (opnd_mem ao hj b)
    have s0:=ih (opnd C j 0) (by have:=sub 0;omega) (by have:=sub 0;omega)
    have s1:=ih (opnd C j 1) (by have:=sub 1;omega) (by have:=sub 1;omega)
    rw [eq]
    rcases ao.1 _ (gateAt_mem C j hj) with ha|ho
    · rw [project_and ao g hj ha]
      refine ⟨rfl,?_⟩
      by_cases e : j=g
      · simp [e,od]
      · simp only [e,ite_false]
        have hh:=od_join true (project ao g (opnd C j 0)).1 (project ao g (opnd C j 1)).1
        simpa [s0.1,s1.1] using hh
    · rw [project_or ao g hj ho]
      constructor
      · have hh:=od_join false (project ao g (opnd C j 0)).1 (project ao g (opnd C j 1)).1
        simpa [s0.1,s1.1] using hh
      · have hh:=od_join false (project ao g (opnd C j 0)).2 (project ao g (opnd C j 1)).2
        simp only [Bool.false_eq_true,ite_false,Nat.add_zero] at hh
        exact hh.trans (max_le s0.2 s1.2)

theorem raw_at_visible (m : Model n G C g) {w} (r : Rise n C w C.output) : Raw n C w=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro t ht
  have out:=rise_val (val_is_or m.ao (unitInput t)) (rise_trans (mem_raw.mp ht) r)
    (show wireVal n C t.val (unitInput t)=true by rw [wireVal_input];simp [unitInput])
  have eq:=congrFun m.correct (unitInput t)
  change wireVal n C C.output _ = _ at eq
  rw [show wireVal n C C.output (unitInput t)=true from out,graphFun_empty_unitInput] at eq
  cases eq

end PEqualNP.Outside.L_meta_2056_aux.TwoDirty.OneDirtyReduction
namespace PEqualNP.Outside.L_meta_2056_aux.TwoDirty.OneDirtyReduction
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.SplitCount
  PEqualNP.Core PEqualNP.Outside.L_meta_2056_aux.TwoDirty.OneDirtyReduction.Support
variable {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {g : ℕ}

def validSide (ao : IsAO2 n C) (g j : ℕ) := ∀ b : Fin 2,(project ao g (opnd C j b)).1.isSome=true
def validUp (ao : IsAO2 n C) (g j : ℕ) := ∀ b : Fin 2,(project ao g (opnd C j b)).2.isSome=true
def UsedLow (ao : IsAO2 n C) (g i : ℕ) := ∃ j<C.gates.length, (gateAt C j).op=GateOp.and ∧ j≠g ∧
    visible n C j ∧ validSide ao g j ∧ ∃ b : Fin 2, Rise n C (n+i) (opnd C j b)
def Keep (ao : IsAO2 n C) (g i : ℕ) := i≠g ∧
    (((gateAt C i).op=GateOp.or ∧ validSide ao g i ∧ UsedLow ao g i) ∨
    (visible n C i ∧ (((gateAt C i).op=GateOp.or ∧ validUp ao g i) ∨
      ((gateAt C i).op=GateOp.and ∧ validSide ao g i))))
noncomputable def kept (ao : IsAO2 n C) (g : ℕ) : Finset ℕ := by
  classical exact (Finset.range C.gates.length).filter (Keep ao g)

def repres (ao : IsAO2 n C) (g i : ℕ) : Opt n := (project ao g (n+i)).1.or (project ao g (n+i)).2

theorem both_s {f : Bool} {a b : Opt n} {t : Formula n} (h : t∈og (joinF f a b)) :
    (a.isSome=true ∧ b.isSome=true ∧ joinF f a b=some t) ∨ t∈og a ∨ t∈og b := by
  rcases og_join h with ⟨x,y,rfl,rfl,rfl⟩|h
  · exact Or.inl ⟨rfl,rfl,rfl⟩
  · exact Or.inr h

theorem and_nonempty {a b : Opt n} {t : Formula n} (h : t∈og (joinF true a b)) :
    a.isSome=true ∧ b.isSome=true := by
  cases a <;> cases b <;> simp_all [joinF,og]

theorem low_origin (ao : IsAO2 n C) (g w) (bound : w<n+C.gates.length) {t : Formula n}
    (h : t∈og (project ao g w).1) :
    ∃ i<C.gates.length, (gateAt C i).op=GateOp.or ∧ validSide ao g i ∧
      Rise n C (n+i) w ∧ (project ao g (n+i)).1=some t := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw : w<n
    · rw [show w=(⟨w,hw⟩ : Fin n).val from rfl,project_input] at h
      simp [og,Formula.ops] at h
    let j:=w-n
    have hj : j<C.gates.length := by dsimp [j];omega
    have eq : w=n+j := by dsimp [j];omega
    have sub (b : Fin 2) := ao.2.1 j hj _ (opnd_mem ao hj b)
    rcases ao.1 _ (gateAt_mem C j hj) with ja|jo
    · rw [eq,project_and ao g hj ja] at h;simp [og] at h
    rw [eq,project_or ao g hj jo] at h
    change t∈og (joinF _ _ _) at h
    have recur (b : Fin 2) (hb : t∈og (project ao g (opnd C j b)).1) := ih _ (by have:=sub b;omega) (by have:=sub b;omega) hb
    rcases both_s h with ⟨s0,s1,e⟩|h0|h1
    · refine ⟨j,hj,jo,?_,eq ▸ Rise.refl,?_⟩
      · intro b;fin_cases b
        · exact s0
        · exact s1
      · rw [project_or ao g hj jo];exact e
    · obtain ⟨i,hi,io,vs,ri,e⟩:=recur 0 h0
      exact ⟨i,hi,io,vs,eq ▸ Rise.step ri hj jo (opnd_mem ao hj 0),e⟩
    · obtain ⟨i,hi,io,vs,ri,e⟩:=recur 1 h1
      exact ⟨i,hi,io,vs,eq ▸ Rise.step ri hj jo (opnd_mem ao hj 1),e⟩

theorem rep_visible (m : Model n G C g) {j} (hj : j<C.gates.length) (rv : visible n C j) :
    repres m.ao g j=(project m.ao g (n+j)).2 := by
  have emp:=raw_at_visible m rv
  have bound : n+j<n+C.gates.length := by omega
  have h : (project m.ao g (n+j)).1=none := by
    cases eq:(project m.ao g (n+j)).1 with
    | none => rfl
    | some f =>
      have h:=(low_some m.ao g _ bound).mp (by simp [eq])
      simp [emp] at h
  simp [repres,h]

theorem up_origin (m : Model n G C g) (w) (bound : w<n+C.gates.length)
    (rv : Rise n C w C.output) {t : Formula n} (h : t∈og (project m.ao g w).2) :
    ∃ i∈kept m.ao g, repres m.ao g i=some t := by
  classical
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw : w<n
    · rw [show w=(⟨w,hw⟩ : Fin n).val from rfl,project_input] at h;simp [og] at h
    let j:=w-n
    have hj : j<C.gates.length := by dsimp [j];omega
    have eq : w=n+j := by dsimp [j];omega
    have vis : visible n C j:=by unfold visible; rwa [←eq]
    have sub (b : Fin 2) := m.ao.2.1 j hj _ (opnd_mem m.ao hj b)
    have member {i} (hi : i<C.gates.length) (hk : Keep m.ao g i) : i∈kept m.ao g :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi,hk⟩
    rcases m.ao.1 _ (gateAt_mem C j hj) with ja|jo
    · rw [eq,project_and m.ao g hj ja] at h
      by_cases same : j=g
      · simp [same,og] at h
      simp only [same,ite_false] at h
      have both:=and_nonempty h
      have vs : validSide m.ao g j := by intro b;fin_cases b;exact both.1;exact both.2
      have low (b : Fin 2) (hb : t∈og (project m.ao g (opnd C j b)).1) :
          ∃ i∈kept m.ao g, repres m.ao g i=some t := by
        obtain ⟨i,hi,io,vi,r,e⟩:=low_origin m.ao g _ (by have:=sub b;omega) hb
        have ne : i≠g := by intro eq;rw [eq,m.gand] at io;cases io
        refine ⟨i,member hi ⟨ne,Or.inl ⟨io,vi,j,hj,ja,same,vis,vs,b,r⟩⟩,?_⟩
        simp [repres,e]
      rcases both_s h with ⟨_,_,e⟩|l|r
      · refine ⟨j,member hj ⟨same,Or.inr ⟨vis,Or.inr ⟨ja,vs⟩⟩⟩,?_⟩
        rw [rep_visible m hj vis,project_and m.ao g hj ja,ite_eq_right same];exact e
      · exact low 0 l
      · exact low 1 r
    · rw [eq,project_or m.ao g hj jo] at h
      change t∈og (joinF _ _ _) at h
      have recur (b : Fin 2) (hb : t∈og (project m.ao g (opnd C j b)).2) :=
        ih _ (by have:=sub b;omega) (by have:=sub b;omega)
          (rise_trans (Rise.step Rise.refl hj jo (opnd_mem m.ao hj b)) vis) hb
      rcases both_s h with ⟨l,r,e⟩|l|r
      · have vs : validUp m.ao g j := by intro b;fin_cases b;exact l;exact r
        have ne : j≠g := by intro eq;rw [eq,m.gand] at jo;cases jo
        refine ⟨j,member hj ⟨ne,Or.inr ⟨vis,Or.inl ⟨jo,vs⟩⟩⟩,?_⟩
        rw [rep_visible m hj vis,project_or m.ao g hj jo];exact e
      · exact recur 0 l
      · exact recur 1 r

theorem cut_budget (m : Model n G C g) :
    (og (project m.ao g C.output).2).card≤(kept m.ao g).card := by
  classical
  set U:=og (project m.ao g C.output).2
  have sub : U.image some ⊆ (kept m.ao g).image (repres m.ao g) := by
    intro e he
    obtain ⟨t,ht,rfl⟩:=Finset.mem_image.mp he
    obtain ⟨i,hi,ei⟩:=up_origin m _ (out_lt m) .refl ht
    exact Finset.mem_image.mpr ⟨i,hi,ei⟩
  have h:=(Finset.card_le_card sub).trans Finset.card_image_le
  rwa [Finset.card_image_of_injective _ (Option.some_injective _)] at h

end PEqualNP.Outside.L_meta_2056_aux.TwoDirty.OneDirtyReduction
namespace PEqualNP.Outside.L_meta_2056_aux.TwoDirty.OneDirtyReduction
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.SplitCount
  PEqualNP.Core PEqualNP.Outside.L_meta_2056_aux.TwoDirty.OneDirtyReduction.Support
open Finset
variable {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {g : ℕ}

theorem raw_input (i : Fin n) : Raw n C i.val={i} := by
  ext t
  simp [mem_raw,rise_input_iff,Fin.val_inj]

theorem raw_or (ao : IsAO2 n C) {j} (hj : j<C.gates.length) (jo : (gateAt C j).op=GateOp.or) :
    Raw n C (n+j)=Raw n C (opnd C j 0) ∪ Raw n C (opnd C j 1) := by
  ext u
  simp only [Finset.mem_union,mem_raw,rise_gate_iff]
  constructor
  · rintro (e|⟨_,_,w,hm,r⟩)
    · have:=u.isLt;omega
    obtain ⟨b,rfl⟩:=mem_opnd ao hj hm
    fin_cases b
    · exact Or.inl r
    · exact Or.inr r
  · rintro (h|h)
    · exact Or.inr ⟨jo,hj,_,opnd_mem ao hj 0,h⟩
    · exact Or.inr ⟨jo,hj,_,opnd_mem ao hj 1,h⟩

theorem raw_and {j} (ja : (gateAt C j).op=GateOp.and) : Raw n C (n+j)=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro t ht
  rcases rise_gate_iff.mp (mem_raw.mp ht) with e|⟨ho,_⟩
  · have:=t.isLt;omega
  · rw [ja] at ho;cases ho

noncomputable def mark (n : ℕ) (C : Circuit) (V : ℕ) (U : Finset (Fin n)) (w : ℕ) : Finset (Fin n) := by
  classical exact if Rise n C w V then Raw n C w∩U else ∅

noncomputable def marked (n : ℕ) (C : Circuit) (V : ℕ) (U : Finset (Fin n)) : Finset ℕ :=
  (range C.gates.length).filter fun i=>1<(mark n C V U (n+i)).card

theorem mark_mem {V w : ℕ} {U : Finset (Fin n)} {v} : v∈mark n C V U w ↔ Rise n C w V ∧ v∈Raw n C w ∧ v∈U := by
  classical by_cases r:Rise n C w V <;> simp [mark,r]

theorem raw_rise {a b : ℕ} (r : Rise n C a b) : Raw n C a⊆Raw n C b := by
  intro x hx
  exact mem_raw.mpr (rise_trans (mem_raw.mp hx) r)

theorem marked_input {V} {U : Finset (Fin n)} {w} (hw : w<n) : (mark n C V U w).card≤1 := by
  have sub : mark n C V U w ⊆ ({⟨w,hw⟩} : Finset (Fin n)) := by
    intro p hp
    rw [←raw_input (C:=C) ⟨w,hw⟩]
    exact (mark_mem.mp hp).2.1
  simpa using card_le_card sub

theorem mark_count (ao : IsAO2 n C) (V) (hV : V<n+C.gates.length) (U : Finset (Fin n))
    (sub : U⊆Raw n C V) : U.card≤(marked n C V U).card+1 := by
  classical
  let S:=mark n C V U
  have merge (w : ℕ) (big : 1<(S w).card) : ∃ a<w, ∃ b<w,S w=S a∪S b := by
    obtain ⟨v,hv⟩:=card_pos.mp (show 0<(S w).card by omega)
    obtain ⟨rv,_,_⟩:=mark_mem.mp hv
    have hle:=rise_le ao rv
    have hn : n≤w := by by_contra! hw; have le : (S w).card≤1:=marked_input (C:=C) (U:=U) (V:=V) hw;omega
    let j:=w-n
    have hj : j<C.gates.length := by dsimp [j];omega
    have eq : w=n+j := by dsimp [j];omega
    rcases ao.1 _ (gateAt_mem C j hj) with ja|jo
    · have raw:= (mark_mem.mp hv).2.1
      rw [eq,raw_and ja] at raw;cases raw
    let a:=opnd C j 0
    let b:=opnd C j 1
    have lt (d : Fin 2) := ao.2.1 j hj _ (opnd_mem ao hj d)
    refine ⟨a,by dsimp [a];have:=lt 0;omega,b,by dsimp [b];have:=lt 1;omega,?_⟩
    have down (d : Fin 2) : Rise n C (opnd C j d) V := rise_trans (.step .refl hj jo (opnd_mem ao hj d)) (eq ▸ rv)
    ext p
    simp only [S,mark_mem,mem_union,rv,true_and,a,b,down]
    rw [eq,raw_or ao hj jo,mem_union]
    tauto
  have sv : S V=U := by
    ext p;simp only [S,mark_mem,show Rise n C V V from .refl,true_and]
    exact ⟨And.right,fun hp=>⟨sub hp,hp⟩⟩
  have kb:=marked_cone_count S merge V
  rw [sv] at kb
  have shift : large S (V+1) ⊆ (marked n C V U).image (n+·) := by
    intro w hw
    obtain ⟨hl,hb⟩:=mem_filter.mp hw
    have bound:=mem_range.mp hl
    have hn : n≤w := by by_contra! hw; have le : (S w).card≤1:=marked_input (C:=C) (U:=U) (V:=V) hw;omega
    have eq : n+(w-n)=w := by omega
    exact mem_image.mpr ⟨w-n,mem_filter.mpr ⟨mem_range.mpr (by omega),by rw [eq];exact hb⟩,eq⟩
  have sc:=(card_le_card shift).trans card_image_le
  omega

theorem marked_early (ao : IsAO2 n C) {V i} {U : Finset (Fin n)} (hV : V<n+g)
    (hi : i∈marked n C V U) : i<g := by
  obtain ⟨_,hb⟩:=mem_filter.mp hi
  obtain ⟨v,hv⟩:=card_pos.mp (show 0<(mark n C V U (n+i)).card by omega)
  have:=rise_le ao (mark_mem.mp hv).1;omega

theorem disjoint_marked (m : Model n G C g) (U V : Finset (Fin n)) :
    Disjoint (marked n C (opnd C g 0) U) (marked n C (opnd C g 1) V) := by
  rw [Finset.disjoint_left]
  intro i ha hb
  have witness {w} {T : Finset (Fin n)} (hi : i∈marked n C w T) :
      Rise n C (n+i) w ∧ (Raw n C (n+i)).Nonempty := by
    have hh:=(mem_filter.mp hi).2
    obtain ⟨v,hv⟩:=card_pos.mp (show 0<(mark n C w T (n+i)).card by omega)
    obtain ⟨r,hr,_⟩:=mark_mem.mp hv
    exact ⟨r,v,hr⟩
  obtain ⟨r0,v,hv⟩:=witness ha
  obtain ⟨r1,_⟩:=witness hb
  exact Finset.disjoint_left.mp (side_disjoint m) (raw_rise r0 hv) (raw_rise r1 hv)

theorem marked_dead (m : Model n G C g) (no4 : NoFourCycle G) {c : Fin n} {U : Finset (Fin n)}
    (neigh : ∀ p∈U,G.Adj c p) (one : ∀ p∈U, ∀ q∈U, ¬ Missing G C g c p → ¬ Missing G C g c q → p=q)
    {V i} (hi : i∈marked n C V U) : i∉kept m.ao g := by
  classical
  intro hk
  have big:=(mem_filter.mp hi).2
  have ⟨p,hp,q,hq,pq⟩:=Finset.one_lt_card.mp big
  obtain ⟨_,pr,pu⟩:=mark_mem.mp hp
  obtain ⟨_,qr,qu⟩:=mark_mem.mp hq
  rcases (mem_filter.mp hk).2.2 with ⟨_,_,j,hj,ja,jg,vis,vs,b,r⟩|⟨vis,_⟩
  · let t : Fin 2:=if b=0 then 1 else 0
    have bt (k : Fin 2) : k=b ∨ k=t := by fin_cases b <;> fin_cases k <;> decide
    have bound : opnd C j t<n+C.gates.length := by have:=m.ao.2.1 j hj _ (opnd_mem m.ao hj t);omega
    obtain ⟨y,hy⟩:=(low_some m.ao g _ bound).mp (vs t)
    have rem (z : Fin n) (hz : z∈Raw n C (n+i)) : remaining n C g (pairInput y z) := by
      refine ⟨j,hj,ja,jg,vis,?_⟩
      intro k
      apply hit_pair.mpr
      rcases bt k with rfl|rfl
      · exact Or.inr (raw_rise r hz)
      · exact Or.inl hy
    have yp:=pair_graph.mp (raw_sound m (rem p pr))
    have yq:=pair_graph.mp (raw_sound m (rem q qr))
    have yc:=common_unique no4 pq yp yq (neigh p pu) (neigh q qu)
    subst y
    have notp : ¬ Missing G C g c p := fun h=>h.2 (rem p pr)
    have notq : ¬ Missing G C g c q := fun h=>h.2 (rem q qr)
    exact pq (one p pu q qu notp notq)
  · rw [raw_at_visible m vis] at pr
    exact Finset.notMem_empty _ pr

end PEqualNP.Outside.L_meta_2056_aux.TwoDirty.OneDirtyReduction
namespace PEqualNP.Outside.L_meta_2056_aux.TwoDirty.OneDirtyReduction
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.SplitCount
  PEqualNP.Core PEqualNP.Outside.L_meta_2056_aux.TwoDirty.OneDirtyReduction.Support
open Finset
variable {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {g : ℕ}

noncomputable def afterSet (ao : IsAO2 n C) (g : ℕ) : Finset ℕ := by
  classical exact (range C.gates.length).filter fun j=>g≤j ∧ ¬ Keep ao g j

theorem reader_of_live (m : Model n G C g) {i} (hi : i<C.gates.length) (no : C.output≠n+i) :
    ∃ j<C.gates.length,n+i∈(gateAt C j).inputs := by
  obtain ⟨ho,hc⟩:=((m.live i hi).2).resolve_left no
  have hout:=out_lt m
  obtain ⟨k,hk,hm⟩:=InCone_has_reader n C (by omega) hc
  exact ⟨k,mem_range.mp (coneSet_subset_range n C _ (by omega) hk),hm⟩

theorem g_reader (m : Model n G C g) : ∃ j<C.gates.length,n+g∈(gateAt C j).inputs := by
  apply reader_of_live m m.glt
  intro e
  apply m.dirty
  intro x hx
  have h:=congrFun m.correct x
  change wireVal n C C.output x=_ at h
  rw [e] at h
  exact h ▸ hx

theorem g_cut (m : Model n G C g) : project m.ao g (n+g)=(none,none) := by
  simp [project_and m.ao g m.glt m.gand]

theorem not_keep_reader (m : Model n G C g) {i j} (hj : j<C.gates.length)
    (hm : n+i∈(gateAt C j).inputs) (cut : project m.ao g (n+i)=(none,none)) : ¬ Keep m.ao g j := by
  obtain ⟨b,eb⟩:=mem_opnd m.ao hj hm
  have nl : ¬ validSide m.ao g j := by intro v;have h:=v b;rw [eb,cut] at h;cases h
  have nu : ¬ validUp m.ao g j := by intro v;have h:=v b;rw [eb,cut] at h;cases h
  rintro ⟨_,⟨_,v,_⟩|⟨_,⟨_,v⟩|⟨_,v⟩⟩⟩
  · exact nl v
  · exact nu v
  · exact nl v

theorem post_g (m : Model n G C g) : g∈afterSet m.ao g := by
  classical
  exact mem_filter.mpr ⟨mem_range.mpr m.glt,le_rfl,fun h=>h.1 rfl⟩

theorem post_r (m : Model n G C g) {i j : ℕ} (hge : g ≤ i) (hj : j<C.gates.length)
    (hm : n+i∈(gateAt C j).inputs) (cut : project m.ao g (n+i)=(none,none)) :
    j∈afterSet m.ao g := by classical exact mem_filter.mpr ⟨mem_range.mpr hj,by have:=m.ao.2.1 j hj _ hm;omega,
      not_keep_reader m hj hm cut⟩

theorem two_post (m : Model n G C g) : 2≤(afterSet m.ao g).card := by
  obtain ⟨j,hj,hm⟩:=g_reader m
  exact one_lt_card.mpr ⟨g,post_g m,j,post_r m le_rfl hj hm (g_cut m),by have:=m.ao.2.1 j hj _ hm;omega⟩

theorem three_mem {S : Finset ℕ} {a b c : ℕ} (ha : a∈S) (hb : b∈S) (hc : c∈S)
    (ab : a≠b) (bc : b≠c) (ac : a≠c) : 3≤S.card := by
  have sub : {a,b,c}⊆S := by simp [insert_subset_iff,ha,hb,hc]
  have bound:=card_le_card sub
  simpa [ab,bc,ac] using bound

theorem three_post (m : Model n G C g) (loss : ∃ u v, Missing G C g u v)
    (mixed : ∀ h, sole n C g h → (gateAt C h).op=GateOp.or → Raw n C (n+h)=∅)
    (nonempty : (project m.ao g C.output).2≠none) : 3≤(afterSet m.ao g).card := by
  classical
  obtain ⟨h,hh,memg⟩:=g_reader m
  have afterh:=post_r m le_rfl hh memg (g_cut m)
  have gh : g<h := by have:=m.ao.2.1 h hh _ memg;omega
  by_cases one : sole n C g h
  · have cut : project m.ao g (n+h)=(none,none) := by
      apply Prod.ext
      · rcases m.ao.1 _ (gateAt_mem C h hh) with ha|ho
        · rw [project_and m.ao g hh ha]
        · cases e:(project m.ao g (n+h)).1 with
          | none => rfl
          | some t =>
            have hne:=(low_some m.ao g (n+h) (by omega)).mp (by simp [e])
            simp [mixed h one ho] at hne
      · cases e:(project m.ao g (n+h)).2 with
        | none => rfl
        | some t =>
          have val:=some_iff ((project m.ao g (n+h)).2) |>.mp (by simp [e])
          rcases m.ao.1 _ (gateAt_mem C h hh) with ha|ho
          · obtain ⟨_,hx⟩:=(up_and m.ao g _ hh ha).mp val
            obtain ⟨b,eb⟩:=mem_opnd m.ao hh memg
            obtain ⟨v,hv,_⟩:=hx b
            change v∈Raw n C (opnd C h b) at hv
            rw [eb,raw_and m.gand] at hv;cases hv
          obtain ⟨u,v,loss⟩:=loss
          obtain ⟨_,j,hj,b,_,_,ja,_,_,flag,_,_,_⟩:=top_witness m loss
          obtain ⟨i,hi,ia,ig,ri,_⟩:=(up_eval m.ao g _ (n+h) (by omega)).mp val
          have path : Rise n C (n+h) (opnd C j b) := by
            rcases rise_via one flag with e|r
            · have jh:=one j hj (e ▸ opnd_mem m.ao hj b)
              rw [jh,ho] at ja;cases ja
            · exact r
          exact False.elim (ig (unique_and_ancestor m.ao m.fixed m.live m.operands m.clean hj ia ja
            (rise_operand m.ao hj (opnd_mem m.ao hj b) (rise_trans ri path))))
    have notout : C.output≠n+h := by intro eq;exact nonempty (by rw [eq,cut])
    obtain ⟨j,hj,r⟩:=reader_of_live m hh notout
    have hj' : h<j := by have:=m.ao.2.1 j hj _ r;omega
    exact three_mem (post_g m) afterh (post_r m gh.le hj r cut) (by omega) (by omega) (by omega)
  · unfold sole at one
    push Not at one
    obtain ⟨j,hj,r,ne⟩:=one
    have gj : g<j := by have:=m.ao.2.1 j hj _ r;omega
    exact three_mem (post_g m) afterh (post_r m le_rfl hj r (g_cut m)) (by omega) ne.symm (by omega)

end PEqualNP.Outside.L_meta_2056_aux.TwoDirty.OneDirtyReduction
namespace PEqualNP.Outside.L_meta_2056_aux.TwoDirty.OneDirtyReduction
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.SplitCount
  PEqualNP.Core PEqualNP.Outside.L_meta_2056_aux.TwoDirty.OneDirtyReduction.Support
open Finset
variable {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {g : ℕ}

def Ray (c : Fin n) (U : Finset (Fin n)) (x y : Fin n) := (x=c ∧ y∈U) ∨ (y=c ∧ x∈U)

theorem ray_symm {c u v : Fin n} {U} (h : Ray c U u v) : Ray c U v u := h.symm

omit [DecidableRel G.Adj] in
theorem loss_symm {u v} (h : Missing G C g u v) : Missing G C g v u :=
  ⟨h.1.symm,raw_pair_symm (u:=v) (v:=u) ▸ h.2⟩

def OneRay (G : SimpleGraph (Fin n)) (C : Circuit) (g : ℕ) :=
  ∃ (b : Fin 2) (c : Fin n) (U : Finset (Fin n)), U.Nonempty ∧ U⊆side n C g b ∧
    (∀ p∈U,Missing G C g c p) ∧ (∀ x y, Missing G C g x y → Ray c U x y)

def TwoRays (G : SimpleGraph (Fin n)) (C : Circuit) (g : ℕ) :=
  ∃ (c d : Fin n) (U V : Finset (Fin n)), U.Nonempty ∧ V.Nonempty ∧ U⊆side n C g 0 ∧
    V⊆side n C g 1 ∧ d∉V ∧ d∈side n C g 1 ∧ G.Adj c d ∧
    (∀ p∈U,Missing G C g d p) ∧ (∀ p∈V,Missing G C g c p) ∧
    (∀ x y, Missing G C g x y → Ray d U x y ∨ Ray c V x y) ∧
    ∀ h, sole n C g h → (gateAt C h).op=GateOp.or → Raw n C (n+h)=∅

theorem classify (m : Model n G C g) (no4 : NoFourCycle G) (s : Fin n→Bool)
    (col : ∀ x y,G.Adj x y → s x≠s y) (active : ∃ x y,Missing G C g x y) : OneRay G C g ∨ TwoRays G C g := by
  classical
  let A:=side n C g 0
  let B:=side n C g 1
  let P (a b : Fin n):=Missing G C g a b
  have orient {R : Fin n→Fin n→Prop} (rs : ∀ x y,R x y→R y x)
      (rect : ∀ a∈A,∀ b∈B,P a b → R a b) (x y) (h : P x y) : R x y := by
    rcases loss_orientation m h with ⟨xa,yb⟩|⟨ya,xb⟩
    · exact rect x xa y yb h
    · exact rs _ _ (rect y ya x xb (loss_symm h))
  have edge : ∃ a∈A,∃ b∈B,P a b := by
    obtain ⟨a,b,h⟩:=active
    rcases loss_orientation m h with ⟨xa,yb⟩|⟨ya,xb⟩
    · exact ⟨a,xa,b,yb,h⟩
    · exact ⟨b,ya,a,xb,loss_symm h⟩
  obtain ⟨a0,ha0,b0,hb0,e0⟩:=edge
  by_cases row : ∃ c : Fin n, ∀ a∈A,∀ b∈B,P a b→a=c
  · obtain ⟨c,hc⟩:=row
    let V:=B.filter (P c)
    have h0:=hc _ ha0 _ hb0 e0
    subst c
    left
    refine ⟨1,a0,V,⟨b0,mem_filter.mpr ⟨hb0,e0⟩⟩,filter_subset ..,fun _ h=>(mem_filter.mp h).2,?_⟩
    apply orient (fun _ _=>ray_symm)
    intro a ha b hb h
    have e:=hc _ ha _ hb h
    subst a
    exact Or.inl ⟨rfl,mem_filter.mpr ⟨hb,h⟩⟩
  by_cases column : ∃ d : Fin n, ∀ a∈A,∀ b∈B,P a b→b=d
  · obtain ⟨d,hd⟩:=column
    let U:=A.filter (fun a=>P a d)
    have h0:=hd _ ha0 _ hb0 e0
    subst d
    left
    refine ⟨0,b0,U,⟨a0,mem_filter.mpr ⟨ha0,e0⟩⟩,filter_subset ..,fun _ h=>loss_symm (mem_filter.mp h).2,?_⟩
    apply orient (fun _ _=>ray_symm)
    intro a ha b hb h
    have e:=hd _ ha _ hb h
    subst b
    exact Or.inr ⟨rfl,mem_filter.mpr ⟨ha,h⟩⟩
  have nr (c : Fin n) : ∃ a∈A,∃ b∈B,P a b ∧ a≠c := by
    have h:=not_exists.mp row c
    push Not at h
    exact h
  have nc (d : Fin n) : ∃ a∈A,∃ b∈B,P a b ∧ b≠d := by
    have h:=not_exists.mp column d
    push Not at h
    exact h
  obtain ⟨a1,ha1,_,_,_,da⟩:=nr a0
  obtain ⟨_,_,b1,hb1,_,db⟩:=nc b0
  let rowAll (a : Fin n):=∀ b∈B,G.Adj a b
  let colAll (b : Fin n):=∀ a∈A,G.Adj a b
  have ur {a x : Fin n} (h : rowAll a) (k : rowAll x) : a=x :=
    common_unique no4 db (h _ hb1) (h _ hb0) (k _ hb1) (k _ hb0)
  have uc {b y : Fin n} (h : colAll b) (k : colAll y) : b=y :=
    common_unique no4 da (h _ ha1).symm (h _ ha0).symm (k _ ha1).symm (k _ ha0).symm
  have centerR : ∃ c∈A,rowAll c := by
    by_contra! h
    have each {a b} (ha : a∈A) (hb : b∈B) (e : P a b) : colAll b :=
      (universal_loss m e ha hb).resolve_left (h a ha)
    exact column ⟨b0,fun a ha b hb e=>uc (each ha hb e) (each ha0 hb0 e0)⟩
  have centerC : ∃ d∈B,colAll d := by
    by_contra! h
    have each {a b} (ha : a∈A) (hb : b∈B) (e : P a b) : rowAll a :=
      (universal_loss m e ha hb).resolve_right (h b hb)
    exact row ⟨a0,fun a ha b hb e=>ur (each ha hb e) (each ha0 hb0 e0)⟩
  obtain ⟨c,hc,rc⟩:=centerR
  obtain ⟨d,hd,cc⟩:=centerC
  have assign {a b} (ha : a∈A) (hb : b∈B) (e : P a b) : a=c∨b=d :=
    (universal_loss m e ha hb).imp (fun h=>ur h rc) (fun h=>uc h cc)
  obtain ⟨x,hx,z,hz,lossxz,xc⟩:=nr c
  have zd:=(assign hx hz lossxz).resolve_left xc
  subst z
  obtain ⟨v,hv,y,hy,lossvy,yd⟩:=nc d
  have vc:=(assign hv hy lossvy).resolve_right yd
  subst v
  let U:=A.filter (fun a=>P a d)
  let V:=B.filter (fun b=>b≠d ∧ P c b)
  right
  refine ⟨c,d,U,V,⟨x,mem_filter.mpr ⟨hx,lossxz⟩⟩,⟨y,mem_filter.mpr ⟨hy,yd,lossvy⟩⟩,filter_subset ..,filter_subset ..,
    fun h=>(mem_filter.mp h).2.1 rfl,hd,rc _ hd,fun _ h=>loss_symm (mem_filter.mp h).2,fun _ h=>(mem_filter.mp h).2.2,?_,?_⟩
  · apply orient (R:=fun x y=>Ray d U x y ∨ Ray c V x y) (fun _ _ h=>h.imp ray_symm ray_symm)
    intro a ha b hb e
    by_cases bd : b=d
    · subst b;exact Or.inl (Or.inr ⟨rfl,mem_filter.mpr ⟨ha,e⟩⟩)
    · have ac:=(assign ha hb e).resolve_right bd
      subst a;exact Or.inr (Or.inl ⟨rfl,mem_filter.mpr ⟨hb,bd,e⟩⟩)
  · intro h hs ho
    exact single_reader_mixed m s col hs ho hc hd hx hy rc (fun hh=>xc (ur hh rc)) (fun hh=>yd (uc hh cc)) lossvy lossxz

end PEqualNP.Outside.L_meta_2056_aux.TwoDirty.OneDirtyReduction
namespace PEqualNP.Outside.L_meta_2056_aux.TwoDirty.OneDirtyReduction
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.SplitCount
  PEqualNP.Core PEqualNP.Outside.L_meta_2056_aux.TwoDirty.OneDirtyReduction.Support
open Finset
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {g : ℕ}

def chain : List (Fin n)  →  Opt n
  | [] => none
  | a::tl => joinF false (some (.lit a)) (chain tl)

theorem chain_eval (xs : List (Fin n)) (x : Fin n → Bool) :
    oe (chain xs) x=true ↔ ∃ p∈xs,x p=true := by
  induction xs with
  | nil => simp [chain,oe]
  | cons u us ih =>
    simp only [chain,oe_join,Bool.false_eq_true,ite_false,Bool.or_eq_true,List.mem_cons]
    change (x u=true ∨ _) ↔ _
    rw [ih]
    grind

theorem chain_depth (xs : List (Fin n)) : od (chain xs)=0 := by
  induction xs with
  | nil => rfl
  | cons u us ih =>
    have h:=od_join false (some (.lit u)) (chain us)
    rw [ih,show od (some (.lit u))=0 from rfl] at h
    exact Nat.le_zero.mp h

theorem chain_cost (xs : List (Fin n)) (hne : xs≠[]) : (og (chain xs)).card+1≤xs.length := by
  induction xs with
  | nil => contradiction
  | cons u us ih =>
    by_cases hu : us=[]
    · subst us;simp [chain,joinF,og,Formula.ops]
    · have sub:=ih hu
      have hh:=og_join_card false (some (.lit u)) (chain us)
      change (og (joinF false (some (.lit u)) (chain us))).card+1≤(u::us).length
      simpa only [List.length_cons] using (show (og (joinF false (some (.lit u)) (chain us))).card+1≤us.length+1 from by
        have zero : (og (some (.lit u))).card=0:=rfl
        omega)

noncomputable def star (c : Fin n) (U : Finset (Fin n)) : Opt n :=
  joinF true (some (.lit c)) (chain U.toList)

theorem star_eval (c : Fin n) (U : Finset (Fin n)) (x : Fin n → Bool) :
    oe (star c U) x=true ↔ x c=true ∧ Hits U x := by
  rw [star,oe_join]
  simp only [ite_true,Bool.and_eq_true,chain_eval,Finset.mem_toList]
  rfl
  
theorem star_depth (c : Fin n) (U : Finset (Fin n)) : od (star c U)≤1 := by
  have h:=od_join true (some (.lit c)) (chain U.toList)
  rw [chain_depth,show od (some (.lit c))=0 from rfl] at h
  exact h

theorem star_cost (c : Fin n) (U : Finset (Fin n)) (h : U.Nonempty) : (og (star c U)).card≤U.card := by
  have hh:=og_join_card true (some (.lit c)) (chain U.toList)
  have sub:=chain_cost U.toList (by simpa using h.ne_empty)
  rw [Finset.length_toList] at sub
  change (og (joinF true (some (.lit c)) (chain U.toList))).card≤_
  have zero : (og (some (.lit c))).card=0:=rfl
  omega

theorem star_sound {c : Fin n} {U : Finset (Fin n)} (h : ∀ u∈U,G.Adj c u) {x : Fin n → Bool}
    (r : oe (star c U) x=true) : graphFun G ∅ x=true := by
  obtain ⟨hc,u,hu,hx⟩:=(star_eval _ _ _).mp r
  exact (graphFun_empty_true_iff G x).mpr ⟨c,u,h _ hu,hc,hx⟩

theorem ray_true {c u v : Fin n} {U : Finset (Fin n)} (h : Ray c U u v) {x : Fin n → Bool}
    (hu : x u=true) (hv : x v=true) : oe (star c U) x=true := by
  apply (star_eval ..).mpr
  rcases h with ⟨rfl,hv'⟩|⟨rfl,hu'⟩
  · exact ⟨hu,_,hv',hv⟩
  · exact ⟨hv,_,hu',hu⟩

theorem formula_mono (e : Formula n) {x y : Fin n → Bool} (le : ∀ v,x v=true → y v=true)
    (h : e.eval x=true) : e.eval y=true := by
  induction e with
  | lit u => exact le _ h
  | bin f a b ia ib =>
    cases f
    · simp only [Formula.eval,Bool.or_eq_true] at h ⊢
      exact h.imp ia ib
    · simp only [Formula.eval,Bool.and_eq_true] at h ⊢
      exact ⟨ia h.1,ib h.2⟩

theorem oe_mono (o : Opt n) {x y : Fin n → Bool} (le : ∀ v,x v=true → y v=true)
    (h : oe o x=true) : oe o y=true := by
  cases o with
  | none => cases h
  | some f => exact formula_mono f le h

theorem restore (m : Model n G C g) (extra : Opt n)
    (sound : ∀ x,oe extra x=true → graphFun G ∅ x=true)
    (restoreLoss : ∀ u v,Missing G C g u v → ∀ x : Fin n → Bool,x u=true → x v=true → oe extra x=true) (x) :
    oe (joinF false (project m.ao g C.output).2 extra) x=graphFun G ∅ x := by
  apply Bool.eq_iff_iff.mpr
  rw [oe_join]
  simp only [Bool.false_eq_true,ite_false,Bool.or_eq_true]
  constructor
  · rintro (h|h)
    · exact raw_sound m ((projected_output m _).mp h)
    · exact sound _ h
  · intro h
    obtain ⟨u,v,uv,hu,hv⟩:=(graphFun_empty_true_iff G _).mp h
    by_cases r : remaining n C g (pairInput u v)
    · left
      apply oe_mono _ _ ((projected_output m _).mpr r)
      intro t ht
      simp only [pairInput,decide_eq_true_eq] at ht
      rcases ht with rfl|rfl <;> assumption
    · exact Or.inr (restoreLoss u v ⟨uv,r⟩ _ hu hv)

theorem join_zero (o : Opt n) : joinF false none o=o := by cases o <;> rfl

end PEqualNP.Outside.L_meta_2056_aux.TwoDirty.OneDirtyReduction
namespace PEqualNP.Outside.L_meta_2056_aux.TwoDirty.OneDirtyReduction
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.SplitCount
  PEqualNP.Core PEqualNP.Outside.L_meta_2056_aux.TwoDirty.OneDirtyReduction.Support
open Finset
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {g : ℕ}

def Result (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) :=
  ∃ D : Circuit, IsAO2 n D ∧ D.size≤C.size ∧ circuitFun n D=graphFun G ∅ ∧
    ∀ i<D.gates.length, ∀ j<D.gates.length, (gateAt D i).op=GateOp.and →
      (gateAt D j).op=GateOp.and → ¬InCone n D i j

theorem finish_formula (m : Model n G C g) (o : Opt n)
    (ok : ∀ x : Fin n→Bool, oe o x=graphFun G ∅ x) (flat : od o≤1) (cost : (og o).card≤C.size) :
    Result n G C := by
  cases o with
  | none =>
    have v:=on_ones m.ao C.output (out_lt m)
    have h:=congrFun m.correct (fun _=>true)
    change wireVal n C C.output _ = _ at h
    have eq:=ok (fun _=>true)
    change false=_ at eq
    rw [←h,v] at eq
    cases eq
  | some f =>
    refine ⟨f.circuit,f.circuit_ao,?_,?_,f.circuit_flat flat⟩
    · rw [f.circuit_size];exact cost
    · funext x
      rw [f.circuit_eval]
      exact ok x

theorem partition_budget (m : Model n G C g) (S : Finset ℕ) (early : ∀ i∈S,i<g)
    (dead : ∀ i∈S,i∉kept m.ao g) :
    (kept m.ao g).card+(afterSet m.ao g).card+S.card ≤ C.size := by
  classical
  let K:=kept m.ao g
  let T:=afterSet m.ao g
  have dk : Disjoint K T := by
    rw [Finset.disjoint_left]
    exact fun _ hk ht=>(mem_filter.mp ht).2.2 (mem_filter.mp hk).2
  have ds : Disjoint (K∪T) S := by
    rw [Finset.disjoint_left]
    intro i hk hs
    rcases mem_union.mp hk with h|h
    · exact dead i hs h
    · have le:=(mem_filter.mp h).2.1;have:=early i hs;omega
  have sub : K∪T∪S ⊆ range C.gates.length := by
    intro i hi
    rcases mem_union.mp hi with h|h
    · rcases mem_union.mp h with h|h <;> exact (mem_filter.mp h).1
    · exact mem_range.mpr (lt_trans (early i h) m.glt)
  have h:=card_le_card sub
  rw [card_union_of_disjoint ds,card_union_of_disjoint dk,card_range] at h
  exact h

theorem marks_spec (m : Model n G C g) (no4 : NoFourCycle G) {c : Fin n} {U : Finset (Fin n)}
    (b : Fin 2) (sub : U⊆side n C g b) (neighbors : ∀ p∈U,G.Adj c p)
    (one : ∀ p∈U,∀ q∈U, ¬ Missing G C g c p → ¬ Missing G C g c q → p=q) :
    let S:=marked n C (opnd C g b) U
    U.card≤S.card+1 ∧ (∀ i∈S,i<g) ∧ (∀ i∈S,i∉kept m.ao g) := by
  have lt:=m.ao.2.1 g m.glt _ (opnd_mem m.ao m.glt b)
  exact ⟨mark_count m.ao _ (by have:=m.glt;omega) U sub,
    fun _ h=>marked_early m.ao lt h,fun _ h=>marked_dead m no4 neighbors one h⟩

theorem baseline (m : Model n G C g) (no : ¬∃x y,Missing G C g x y) : Result n G C := by
  let B:=(project m.ao g C.output).2
  have ok:=restore m none (by intro x h;cases h) (by intro u v h;exact (no ⟨u,v,h⟩).elim)
  have e : joinF false B none=B := by cases B <;> rfl
  apply finish_formula m B
  · intro x
    rw [←e]
    exact ok x
  · exact (project_depth m.ao g _ (out_lt m)).2
  · have q:=partition_budget m ∅ (by simp) (by simp)
    have b:=cut_budget m
    dsimp [B];omega

theorem one_done (m : Model n G C g) (no4 : NoFourCycle G) (h : OneRay G C g) : Result n G C := by
  obtain ⟨b,c,U,un,us,um,cover⟩:=h
  let B:=(project m.ao g C.output).2
  have nb (p) (hp : p∈U) := (um p hp).1
  have ⟨mc,early,dead⟩:=marks_spec m no4 b us nb (fun p hp _ _ h=>False.elim (h (um p hp)))
  have count:=partition_budget m _ early dead
  let F:=joinF false B (star c U)
  apply finish_formula m F
  · exact restore m _ (fun _=>star_sound nb) (fun u v h _=>ray_true (cover u v h))
  · have l : od B≤1:=(project_depth m.ao g _ (out_lt m)).2
    have s:=star_depth c U
    have hh:=od_join false B (star c U)
    change od (joinF false B (star c U))≤1
    simp only [Bool.false_eq_true,ite_false,Nat.add_zero] at hh
    exact hh.trans (max_le l s)
  · have cost : (og B).card≤(kept m.ao g).card:=cut_budget m
    have s:=star_cost c U un
    have f:=og_join_card false B (star c U)
    have extra:=two_post m
    dsimp [F];omega

theorem two_done (m : Model n G C g) (no4 : NoFourCycle G) (h : TwoRays G C g) : Result n G C := by
  classical
  obtain ⟨c,d,U,V,un,vn,us,vs,dv,db,cd,um,vm,cover,mixed⟩:=h
  let P:=marked n C (opnd C g 0) U
  let Q:=marked n C (opnd C g 1) (insert d V)
  have ub (p) (hp : p∈U) := (um p hp).1
  have vb (p) (hp : p∈V) := (vm p hp).1
  have ⟨cu,pu,du⟩:=marks_spec m no4 0 us ub (fun p hp _ _ h=>False.elim (h (um p hp)))
  have nd {p} (hp : p∈insert d V) (nl : ¬Missing G C g c p) : p=d :=
    (mem_insert.mp hp).resolve_right (fun h=>nl (vm p h))
  have nv (p) (hp : p∈insert d V) : G.Adj c p := by
    rcases mem_insert.mp hp with rfl|h
    · exact cd
    · exact vb p h
  have ⟨cv,pv,dd⟩:=marks_spec m no4 1 (insert_subset db vs) nv (fun _ hp _ hq p q=>(nd hp p).trans (nd hq q).symm)
  have count:=partition_budget m (P∪Q)
    (fun i h=>(mem_union.mp h).elim (pu i) (pv i))
    (fun i h=>(mem_union.mp h).elim (du i) (dd i))
  rw [card_union_of_disjoint (disjoint_marked m U (insert d V))] at count
  rw [card_insert_of_notMem dv] at cv
  let B:=(project m.ao g C.output).2
  let E:=joinF false (star d U) (star c V)
  let F:=joinF false B E
  have truth (x : Fin n→Bool) : oe E x=true ↔ oe (star d U) x=true ∨ oe (star c V) x=true := by
    simp [E,oe_join]
  apply finish_formula m F
  · apply restore m E
    · intro x hx
      exact ((truth _).mp hx).elim (star_sound ub) (star_sound vb)
    · intro u v h x hu hv
      apply (truth x).mpr
      exact (cover u v h).imp (fun hh=>ray_true hh hu hv) (fun hh=>ray_true hh hu hv)
  · have l : od B≤1:=(project_depth m.ao g _ (out_lt m)).2
    have s:=od_join false (star d U) (star c V)
    have t:=od_join false B E
    simp only [Bool.false_eq_true,ite_false,Nat.add_zero] at s t
    exact t.trans (max_le l (s.trans (max_le (star_depth d U) (star_depth c V))))
  · have cost : (og B).card≤(kept m.ao g).card:=cut_budget m
    have su:=star_cost d U un
    have sv:=star_cost c V vn
    have ce : (og E).card≤(og (star d U)).card+(og (star c V)).card+1:=og_join_card false _ _
    have big : (og F).card≤(og B).card+(og E).card+1:=og_join_card false _ _
    change U.card≤P.card+1 at cu
    change V.card+1≤Q.card+1 at cv
    change (kept m.ao g).card+(afterSet m.ao g).card+(P.card+Q.card)≤C.size at count
    by_cases emp : B=none
    · have e : F=E := by dsimp [F];rw [emp,join_zero]
      rw [e]
      have extra:=two_post m
      omega
    · obtain ⟨u,hu⟩:=un
      have extra:=three_post m ⟨d,u,um u hu⟩ mixed emp
      omega

theorem complete (m : Model n G C g) (no4 : NoFourCycle G) (s : Fin n→Bool)
    (bip : ∀ a b,G.Adj a b → s a≠s b) : Result n G C := by
  classical
  by_cases h : ∃ u v, Missing G C g u v
  · exact (classify m no4 s bip h).elim (one_done m no4) (two_done m no4)
  · exact baseline m h

end PEqualNP.Outside.L_meta_2056_aux.TwoDirty.OneDirtyReduction

namespace PEqualNP.Outside.L_meta_2056_aux.TwoDirty.FlatSumPlane

-- toolkit and cone lemmas copied from extra/submitted/L_meta_4846.lean (cones from the merged L_meta_2067)
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl step (List.ofFn x)).getD i false

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_cons]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma val_nil {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    val [] x i = if h : i < n then x ⟨i, h⟩ else false := by
  unfold val
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

lemma val_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (i : ℕ) :
    val (gs ++ [g]) x i =
      if i = n + gs.length then g.op.eval (g.inputs.map fun j => val gs x j)
      else val gs x i := by
  unfold val
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, step]
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rcases lt_trichotomy i (n + gs.length) with h | h | h
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  · rw [if_pos h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hl, h]
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

lemma val_ge {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : n + gs.length ≤ i) :
    val gs x i = false := by
  unfold val
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

lemma val_lt {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    val gs x i = x ⟨i, hi⟩ := by
  induction gs using List.reverseRecOn with
  | nil =>
    rw [val_nil]
    simp [hi]
  | append_singleton gs g ih =>
    rw [val_snoc, if_neg (by omega)]
    exact ih

lemma val_gate {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    ∀ (k : ℕ) (hk : k < gs.length), val gs x (n + k) =
      gs[k].op.eval (gs[k].inputs.map fun j => if j < n + k then val gs x j else false) := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro k hk
    simp at hk
  | append_singleton gs g ih =>
    intro k hk
    by_cases hkl : k = gs.length
    · subst hkl
      have hgl : (gs ++ [g])[gs.length]'hk = g := by simp
      rw [hgl, val_snoc, if_pos rfl]
      congr 1
      apply List.map_congr_left
      intro j _
      by_cases hj : j < n + gs.length
      · rw [if_pos hj, val_snoc, if_neg (by omega)]
      · rw [if_neg hj, val_ge gs x j (by omega)]
    · have hk' : k < gs.length + 1 := by simpa using hk
      have hk2 : k < gs.length := by omega
      have hget : (gs ++ [g])[k]'hk = gs[k] := List.getElem_append_left hk2
      rw [hget, val_snoc, if_neg (by omega), ih k hk2]
      congr 1
      apply List.map_congr_left
      intro j _
      by_cases hj : j < n + k
      · rw [if_pos hj, if_pos hj, val_snoc, if_neg (by omega)]
      · rw [if_neg hj, if_neg hj]

def eof {n : ℕ} (u : Fin n) : Fin n → Bool := fun c => decide (c = u)

def pr {n : ℕ} (u v : Fin n) : Fin n → Bool := fun c => decide (c = u ∨ c = v)

-- cone characterisation (cones_len .. inCone_trans) copied from the merged L_meta_2067
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

lemma inCone_lt (n : ℕ) (C : Circuit) (i : ℕ) :
    ∀ j, InCone n C i j → i < j ∧ j < C.gates.length := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k, hk, _, h3 | h3⟩ := h
    · exact ⟨by omega, h0⟩
    · have := (ih k hk h3).1
      exact ⟨by omega, h0⟩

lemma inCone_trans (n : ℕ) (C : Circuit) (a k : ℕ) (hak : InCone n C a k) :
    ∀ j, InCone n C k j → InCone n C a j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k2, hk2, hin, h3 | h3⟩ := h
    · subst h3
      rw [inCone_iff]
      exact ⟨h0, k, hk2, hin, Or.inr hak⟩
    · rw [inCone_iff]
      exact ⟨h0, k2, hk2, hin, Or.inr (ih k2 hk2 h3)⟩

lemma gateAt_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  unfold gateAt
  simp [List.getD_eq_getElem?_getD, hj]


-- geometry of the projective plane of order 3 on the 26 variables
def incB (p l : ℕ) : Bool :=
  decide ((p + l) % 13 = 0 ∨ (p + l) % 13 = 1 ∨ (p + l) % 13 = 3 ∨
    (p + l) % 13 = 9)

def adjB (u v : Fin 26) : Bool :=
  (decide (u.val < 13) && decide (13 ≤ v.val) && incB u.val (v.val - 13)) ||
    (decide (v.val < 13) && decide (13 ≤ u.val) && incB v.val (u.val - 13))

lemma inc_iff : ∀ p l : Fin 13, ((p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) ↔
    incB p.val l.val = true := by decide

lemma adj_symm (u v : Fin 26) : adjB u v = adjB v u := by
  unfold adjB; rw [Bool.or_comm]

lemma adj_irr : ∀ v : Fin 26, adjB v v = false := by decide

lemma adj_cl : ∀ p l : Fin 13, incB p.val l.val = true →
    adjB (Fin.castAdd 13 p) (Fin.natAdd 13 l) = true := by decide

lemma adj_diag : ∀ p : Fin 13, adjB (Fin.castAdd 13 p) (Fin.natAdd 13 (-p)) = true := by decide

lemma cl_ne : ∀ p l : Fin 13, Fin.castAdd 13 p ≠ Fin.natAdd 13 l := by decide

lemma common : ∀ c c' : Fin 26, c ≠ c' →
    (Finset.univ.filter (fun y => adjB c y = true ∧ adjB c' y = true)).card ≤ 1 := by
  decide +kernel

lemma ecard : (Finset.univ.filter (fun p : Fin 26 × Fin 26 => adjB p.1 p.2 = true)).card = 104 := by
  decide +kernel


open Classical

-- abstract leaf count: a family closed under unions of two earlier members
lemma leaf_count {α : Type*} [DecidableEq α] (cls : ℕ → Prop) (T : ℕ → Finset α)
    (h : ∀ w, cls w → (T w).card ≤ 1 ∨ ∃ a b, a < w ∧ b < w ∧ cls a ∧ cls b ∧ T w = T a ∪ T b) :
    ∀ M (W : Finset ℕ), (∀ w ∈ W, w < M ∧ cls w) →
      (W.biUnion T).card ≤ W.card +
        ((Finset.range M).filter (fun k => cls k ∧ 2 ≤ (T k).card ∧ T k ⊆ W.biUnion T)).card := by
  intro M
  induction M with
  | zero =>
    intro W hW
    have : W = ∅ := by
      ext w
      simp only [Finset.notMem_empty, iff_false]
      intro hw
      exact absurd (hW w hw).1 (by omega)
    subst this
    simp
  | succ M ih =>
    intro W hW
    have hmono : ∀ U U' : Finset α, U ⊆ U' →
        ((Finset.range M).filter (fun k => cls k ∧ 2 ≤ (T k).card ∧ T k ⊆ U)).card ≤
        ((Finset.range (M + 1)).filter (fun k => cls k ∧ 2 ≤ (T k).card ∧ T k ⊆ U')).card := by
      intro U U' hU
      apply Finset.card_le_card
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
      exact ⟨by omega, hk.2.1, hk.2.2.1, hk.2.2.2.trans hU⟩
    by_cases hM : M ∈ W
    · have hWe : W = insert M (W.erase M) := (Finset.insert_erase hM).symm
      have hW' : ∀ w ∈ W.erase M, w < M ∧ cls w := by
        intro w hw
        rw [Finset.mem_erase] at hw
        have := hW w hw.2
        exact ⟨by omega, this.2⟩
      have hnot : M ∉ W.erase M := Finset.notMem_erase M W
      have hcard : W.card = (W.erase M).card + 1 := by
        rw [Finset.card_erase_of_mem hM]
        have := Finset.card_pos.mpr ⟨M, hM⟩
        omega
      have hU : W.biUnion T = T M ∪ (W.erase M).biUnion T := by
        conv_lhs => rw [hWe]
        rw [Finset.biUnion_insert]
      by_cases h1 : (T M).card ≤ 1
      · have ih1 := ih (W.erase M) hW'
        have hsub : (W.erase M).biUnion T ⊆ W.biUnion T := by
          rw [hU]; exact Finset.subset_union_right
        have := hmono _ _ hsub
        have hu := Finset.card_union_le (T M) ((W.erase M).biUnion T)
        rw [hU] at this ⊢
        omega
      · rcases h M (hW M hM).2 with h2 | ⟨a, b, ha, hb, ca, cb, hT⟩
        · exact absurd h2 h1
        · set W2 := insert a (insert b (W.erase M)) with hW2
          have hW2' : ∀ w ∈ W2, w < M ∧ cls w := by
            intro w hw
            rw [hW2, Finset.mem_insert, Finset.mem_insert] at hw
            rcases hw with rfl | rfl | hw
            · exact ⟨ha, ca⟩
            · exact ⟨hb, cb⟩
            · exact hW' w hw
          have hU2 : W2.biUnion T = W.biUnion T := by
            rw [hW2, Finset.biUnion_insert, Finset.biUnion_insert, hU, hT, Finset.union_assoc]
          have hc2 : W2.card ≤ (W.erase M).card + 2 := by
            rw [hW2]
            have e1 := Finset.card_insert_le a (insert b (W.erase M))
            have e2 := Finset.card_insert_le b (W.erase M)
            omega
          have ih2 := ih W2 hW2'
          rw [hU2] at ih2
          have hsplit : (Finset.range (M + 1)).filter
              (fun k => cls k ∧ 2 ≤ (T k).card ∧ T k ⊆ W.biUnion T) =
              insert M ((Finset.range M).filter
                (fun k => cls k ∧ 2 ≤ (T k).card ∧ T k ⊆ W.biUnion T)) := by
            rw [Finset.range_add_one, Finset.filter_insert, if_pos]
            refine ⟨(hW M hM).2, by omega, ?_⟩
            rw [hU]; exact Finset.subset_union_left
          rw [hsplit, Finset.card_insert_of_notMem (by simp)]
          omega
    · have hW' : ∀ w ∈ W, w < M ∧ cls w := by
        intro w hw
        have := hW w hw
        have hne : w ≠ M := fun he => hM (he ▸ hw)
        exact ⟨by omega, this.2⟩
      have := ih W hW'
      have := hmono (W.biUnion T) (W.biUnion T) le_rfl
      omega

section circ

variable (C : Circuit)

lemma gv (hC : PEqualNP.TopForm.IsAO2 26 C) (w : ℕ) (h1 : 26 ≤ w) (h2 : w < 26 + C.gates.length) :
    ∃ a b, (gateAt C (w - 26)).inputs = [a, b] ∧ a < w ∧ b < w ∧
      ((gateAt C (w - 26)).op = GateOp.and ∨ (gateAt C (w - 26)).op = GateOp.or) ∧
      ∀ x : Fin 26 → Bool, val C.gates x w =
        (gateAt C (w - 26)).op.eval [val C.gates x a, val C.gates x b] := by
  obtain ⟨k, rfl⟩ : ∃ k, w = 26 + k := ⟨w - 26, by omega⟩
  have hk : k < C.gates.length := by omega
  have e : 26 + k - 26 = k := by omega
  rw [e]
  obtain ⟨hAO, hRB, hL⟩ := hC
  have hmem := List.getElem_mem hk
  have h2 := hL _ hmem
  have hop := hAO _ hmem
  rw [← gateAt_eq C k hk] at h2 hop
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp h2
  have ha := hRB k hk a (by rw [hab]; simp)
  have hb := hRB k hk b (by rw [hab]; simp)
  refine ⟨a, b, hab, ha, hb, hop, fun x => ?_⟩
  rw [val_gate C.gates x k hk, ← gateAt_eq C k hk, hab]
  simp [ha, hb]

lemma ev_and (p q : Bool) : GateOp.and.eval [p, q] = (p && q) := by simp [GateOp.eval]

lemma ev_or (p q : Bool) : GateOp.or.eval [p, q] = (p || q) := by simp [GateOp.eval]

def S (w : ℕ) : Finset (Fin 26) := Finset.univ.filter (fun v => val C.gates (eof v) w = true)

lemma mem_S (w : ℕ) (v : Fin 26) : v ∈ S C w ↔ val C.gates (eof v) w = true := by simp [S]

lemma S_inp (w : ℕ) (hw : w < 26) : S C w = {⟨w, hw⟩} := by
  ext v
  rw [mem_S, val_lt C.gates _ w hw]
  simp only [eof, decide_eq_true_eq, Finset.mem_singleton]
  exact eq_comm

lemma S_or (a b w : ℕ)
    (hv : ∀ x : Fin 26 → Bool, val C.gates x w = (val C.gates x a || val C.gates x b)) :
    S C w = S C a ∪ S C b := by
  ext v
  simp only [Finset.mem_union, mem_S, hv, Bool.or_eq_true]

def Lin (w : ℕ) : Prop := w < 26 ∨ (26 ≤ w ∧ w < 26 + C.gates.length ∧
  ∀ i, (gateAt C i).op = GateOp.and → 26 + i ≠ w ∧ ¬ InCone 26 C i (w - 26))

lemma cone_in (j a : ℕ) (hj : j < C.gates.length) (ha : a ∈ (gateAt C j).inputs)
    (h1 : 26 ≤ a) (h2 : a < 26 + j) : InCone 26 C (a - 26) j :=
  (inCone_iff 26 C (a - 26) j).mpr
    ⟨hj, a - 26, by omega, by rw [show 26 + (a - 26) = a by omega]; exact ha, Or.inl rfl⟩

lemma input_lin (j a : ℕ) (hj : j < C.gates.length) (ha : a ∈ (gateAt C j).inputs)
    (hlt : a < 26 + j) (hfree : ∀ i, (gateAt C i).op = GateOp.and → ¬ InCone 26 C i j) :
    Lin C a := by
  by_cases h1 : a < 26
  · exact Or.inl h1
  · right
    have hc := cone_in C j a hj ha (by omega) hlt
    refine ⟨by omega, by omega, fun i hi => ⟨?_, ?_⟩⟩
    · intro he
      apply hfree i hi
      rw [show i = a - 26 by omega]
      exact hc
    · intro hin
      exact hfree i hi (inCone_trans 26 C i (a - 26) hin j hc)

lemma lin_struct (hC : PEqualNP.TopForm.IsAO2 26 C) (w : ℕ) (hw : Lin C w) (h26 : 26 ≤ w) :
    ∃ a b, a < w ∧ b < w ∧ Lin C a ∧ Lin C b ∧ (gateAt C (w - 26)).op = GateOp.or ∧
      ∀ x : Fin 26 → Bool, val C.gates x w = (val C.gates x a || val C.gates x b) := by
  rcases hw with hw | ⟨_, hM, hfree⟩
  · omega
  obtain ⟨a, b, hab, ha, hb, hop, hv⟩ := gv C hC w h26 hM
  have hor : (gateAt C (w - 26)).op = GateOp.or := by
    rcases hop with hop | hop
    · exact absurd (by omega) (hfree (w - 26) hop).1
    · exact hop
  have hk : w - 26 < C.gates.length := by omega
  have hf : ∀ i, (gateAt C i).op = GateOp.and → ¬ InCone 26 C i (w - 26) :=
    fun i hi => (hfree i hi).2
  refine ⟨a, b, ha, hb, input_lin C (w - 26) a hk (by rw [hab]; simp) (by omega) hf,
    input_lin C (w - 26) b hk (by rw [hab]; simp) (by omega) hf, hor, fun x => ?_⟩
  rw [hv x, hor, ev_or]

lemma lin_sem (hC : PEqualNP.TopForm.IsAO2 26 C) : ∀ w, Lin C w → ∀ u v : Fin 26,
    (val C.gates (pr u v) w = true ↔ (u ∈ S C w ∨ v ∈ S C w)) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw u v
    by_cases h26 : w < 26
    · rw [S_inp C w h26, val_lt C.gates _ w h26]
      simp only [pr, decide_eq_true_eq, Finset.mem_singleton]
      constructor
      · rintro (h | h)
        · exact Or.inl h.symm
        · exact Or.inr h.symm
      · rintro (h | h)
        · exact Or.inl h.symm
        · exact Or.inr h.symm
    · obtain ⟨a, b, ha, hb, la, lb, _, hv⟩ := lin_struct C hC w hw (by omega)
      rw [hv, Bool.or_eq_true, ih a ha la, ih b hb lb, S_or C a b w hv]
      simp only [Finset.mem_union]
      tauto

lemma lin_ne (hC : PEqualNP.TopForm.IsAO2 26 C) : ∀ w, Lin C w → (S C w).Nonempty := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases h26 : w < 26
    · rw [S_inp C w h26]; simp
    · obtain ⟨a, b, ha, hb, la, lb, _, hv⟩ := lin_struct C hC w hw (by omega)
      rw [S_or C a b w hv]
      obtain ⟨y, hy⟩ := ih a ha la
      exact ⟨y, Finset.mem_union_left _ hy⟩

lemma lin_cls (hC : PEqualNP.TopForm.IsAO2 26 C) (w : ℕ) (hw : Lin C w) :
    (S C w).card ≤ 1 ∨ ∃ a b, a < w ∧ b < w ∧ Lin C a ∧ Lin C b ∧ S C w = S C a ∪ S C b := by
  by_cases h26 : w < 26
  · left; rw [S_inp C w h26]; simp
  · obtain ⟨a, b, ha, hb, la, lb, _, hv⟩ := lin_struct C hC w hw (by omega)
    exact Or.inr ⟨a, b, ha, hb, la, lb, S_or C a b w hv⟩

def Z (w : ℕ) : Prop :=
  26 ≤ w ∧ w < 26 + C.gates.length ∧ ∀ v : Fin 26, val C.gates (eof v) w = false

lemma z_struct (hC : PEqualNP.TopForm.IsAO2 26 C) (w : ℕ) (hz : Z C w) :
    (gateAt C (w - 26)).op = GateOp.and ∨ ((gateAt C (w - 26)).op = GateOp.or ∧
      ∃ a b, (gateAt C (w - 26)).inputs = [a, b] ∧ a < w ∧ b < w ∧ Z C a ∧ Z C b ∧
        ∀ x : Fin 26 → Bool, val C.gates x w = (val C.gates x a || val C.gates x b)) := by
  obtain ⟨h1, h2, h3⟩ := hz
  obtain ⟨a, b, hab, ha, hb, hop, hv⟩ := gv C hC w h1 h2
  rcases hop with hop | hop
  · exact Or.inl hop
  · right
    have hv' : ∀ x : Fin 26 → Bool, val C.gates x w = (val C.gates x a || val C.gates x b) := by
      intro x; rw [hv x, hop, ev_or]
    have hza : ∀ c, c < w → (∀ v : Fin 26, val C.gates (eof v) w = false → val C.gates (eof v) c = false) →
        Z C c := by
      intro c hc hcv
      refine ⟨?_, by omega, fun v => hcv v (h3 v)⟩
      by_contra hlt
      push_neg at hlt
      have := hcv ⟨c, hlt⟩ (h3 _)
      rw [val_lt C.gates _ c hlt] at this
      simp [eof] at this
    refine ⟨hop, a, b, hab, ha, hb, hza a ha ?_, hza b hb ?_, hv'⟩
    · intro v hv0; rw [hv'] at hv0; simp only [Bool.or_eq_false_iff] at hv0; exact hv0.1
    · intro v hv0; rw [hv'] at hv0; simp only [Bool.or_eq_false_iff] at hv0; exact hv0.2

inductive Reach : ℕ → ℕ → Prop
  | self (w : ℕ) : 26 ≤ w → w < 26 + C.gates.length → (gateAt C (w - 26)).op = GateOp.and →
      Reach w w
  | up (j w a : ℕ) : 26 ≤ w → w < 26 + C.gates.length → (gateAt C (w - 26)).op = GateOp.or →
      a ∈ (gateAt C (w - 26)).inputs → Reach j a → Reach j w

lemma reach_and (hC : PEqualNP.TopForm.IsAO2 26 C) (j w : ℕ) (h : Reach C j w) :
    26 ≤ j ∧ j < 26 + C.gates.length ∧ (gateAt C (j - 26)).op = GateOp.and ∧ j ≤ w := by
  induction h with
  | self h1 h2 h3 => exact ⟨h1, h2, h3, le_rfl⟩
  | up w a h1 h2 _ h4 _ ih =>
    obtain ⟨a', b', hab, ha, hb, _, _⟩ := gv C hC w h1 h2
    rw [hab] at h4
    have : a < w := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h4
      rcases h4 with rfl | rfl <;> assumption
    exact ⟨ih.1, ih.2.1, ih.2.2.1, by omega⟩

lemma reach_val (hC : PEqualNP.TopForm.IsAO2 26 C) (j w : ℕ) (h : Reach C j w) :
    ∀ x : Fin 26 → Bool, val C.gates x j = true → val C.gates x w = true := by
  induction h with
  | self _ _ _ => exact fun x hx => hx
  | up w a h1 h2 h3 h4 _ ih =>
    intro x hx
    obtain ⟨a', b', hab, _, _, _, hv⟩ := gv C hC w h1 h2
    rw [hab] at h4
    rw [hv x, h3, ev_or, Bool.or_eq_true]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h4
    rcases h4 with rfl | rfl
    · exact Or.inl (ih x hx)
    · exact Or.inr (ih x hx)

lemma z_sem (hC : PEqualNP.TopForm.IsAO2 26 C) : ∀ w, Z C w → ∀ x : Fin 26 → Bool,
    val C.gates x w = true → ∃ j, Reach C j w ∧ val C.gates x j = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hz x hx
    rcases z_struct C hC w hz with hop | ⟨hop, a, b, hab, ha, hb, za, zb, hv⟩
    · exact ⟨w, Reach.self w hz.1 hz.2.1 hop, hx⟩
    · rw [hv, Bool.or_eq_true] at hx
      rcases hx with hx | hx
      · obtain ⟨j, hj, hjx⟩ := ih a ha za x hx
        exact ⟨j, Reach.up j w a hz.1 hz.2.1 hop (by rw [hab]; simp) hj, hjx⟩
      · obtain ⟨j, hj, hjx⟩ := ih b hb zb x hx
        exact ⟨j, Reach.up j w b hz.1 hz.2.1 hop (by rw [hab]; simp) hj, hjx⟩

lemma reach_inv (j w : ℕ) (h : Reach C j w) :
    (j = w ∧ 26 ≤ w ∧ w < 26 + C.gates.length ∧ (gateAt C (w - 26)).op = GateOp.and) ∨
    (26 ≤ w ∧ w < 26 + C.gates.length ∧ (gateAt C (w - 26)).op = GateOp.or ∧
      ∃ a ∈ (gateAt C (w - 26)).inputs, Reach C j a) := by
  cases h
  · exact Or.inl ⟨rfl, by assumption, by assumption, by assumption⟩
  · exact Or.inr ⟨by assumption, by assumption, by assumption, _, by assumption, by assumption⟩

noncomputable def A (w : ℕ) : Finset ℕ :=
  (Finset.range (26 + C.gates.length)).filter (fun j => Reach C j w)

lemma mem_A (hC : PEqualNP.TopForm.IsAO2 26 C) (j w : ℕ) : j ∈ A C w ↔ Reach C j w := by
  unfold A
  rw [Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨(reach_and C hC j w h).2.1, h⟩

lemma A_and (hC : PEqualNP.TopForm.IsAO2 26 C) (w : ℕ) (h1 : 26 ≤ w)
    (h2 : w < 26 + C.gates.length) (hop : (gateAt C (w - 26)).op = GateOp.and) :
    A C w = {w} := by
  ext j
  rw [mem_A C hC, Finset.mem_singleton]
  constructor
  · intro h
    rcases reach_inv C j w h with ⟨h0, _⟩ | ⟨_, _, h3, _⟩
    · exact h0
    · rw [hop] at h3; exact absurd h3 (by simp)
  · rintro rfl
    exact Reach.self j h1 h2 hop

lemma z_cls (hC : PEqualNP.TopForm.IsAO2 26 C) (w : ℕ) (hz : Z C w) :
    (A C w).card ≤ 1 ∨ ∃ a b, a < w ∧ b < w ∧ Z C a ∧ Z C b ∧ A C w = A C a ∪ A C b := by
  rcases z_struct C hC w hz with hop | ⟨hop, a, b, hab, ha, hb, za, zb, _⟩
  · left; rw [A_and C hC w hz.1 hz.2.1 hop]; simp
  · right
    refine ⟨a, b, ha, hb, za, zb, ?_⟩
    ext j
    rw [Finset.mem_union, mem_A C hC, mem_A C hC, mem_A C hC]
    constructor
    · intro h
      rcases reach_inv C j w h with ⟨_, _, _, h3⟩ | ⟨_, _, _, a0, h4, h5⟩
      · rw [hop] at h3; exact absurd h3 (by simp)
      · rw [hab] at h4
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h4
        rcases h4 with rfl | rfl
        · exact Or.inl h5
        · exact Or.inr h5
    · rintro (h | h)
      · exact Reach.up j w a hz.1 hz.2.1 hop (by rw [hab]; simp) h
      · exact Reach.up j w b hz.1 hz.2.1 hop (by rw [hab]; simp) h

end circ


section stars

variable (C : Circuit)

lemma spec (hF : ∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
      ∃ p l : Fin 13, ((p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) ∧
        x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) (u v : Fin 26) :
    val C.gates (pr u v) C.output = true ↔ adjB u v = true := by
  have e : val C.gates (pr u v) C.output = C.eval (List.ofFn (pr u v)) := rfl
  rw [e, hF]
  constructor
  · rintro ⟨p, l, hpl, h1, h2⟩
    rw [inc_iff] at hpl
    have hc := adj_cl p l hpl
    simp only [pr, decide_eq_true_eq] at h1 h2
    have hne := cl_ne p l
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · rw [← h1, ← h2]; exact hc
    · rw [← h1, ← h2, adj_symm]; exact hc
    · exact absurd (h1.trans h2.symm) hne
  · intro h
    unfold adjB at h
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩
    · refine ⟨⟨u.val, h1⟩, ⟨v.val - 13, by omega⟩, (inc_iff _ _).mpr h3, ?_, ?_⟩
      · simp only [pr, decide_eq_true_eq]; left; apply Fin.ext; rfl
      · simp only [pr, decide_eq_true_eq]; right; apply Fin.ext
        show 13 + (v.val - 13) = v.val; omega
    · refine ⟨⟨v.val, h1⟩, ⟨u.val - 13, by omega⟩, (inc_iff _ _).mpr h3, ?_, ?_⟩
      · simp only [pr, decide_eq_true_eq]; right; apply Fin.ext; rfl
      · simp only [pr, decide_eq_true_eq]; left; apply Fin.ext
        show 13 + (u.val - 13) = u.val; omega

lemma pr_self (v : Fin 26) : pr v v = eof v := by
  funext c; simp [pr, eof]

lemma out_Z (hout : ∀ u v : Fin 26, val C.gates (pr u v) C.output = true ↔ adjB u v = true) :
    Z C C.output := by
  have hf : ∀ v : Fin 26, val C.gates (eof v) C.output = false := by
    intro v
    rw [← pr_self]
    cases hv : val C.gates (pr v v) C.output
    · rfl
    · rw [hout, adj_irr] at hv; exact absurd hv (by simp)
  refine ⟨?_, ?_, hf⟩
  · by_contra h
    push_neg at h
    have := hf ⟨C.output, h⟩
    rw [val_lt C.gates _ _ h] at this
    simp [eof] at this
  · by_contra h
    push_neg at h
    have h1 := (hout (Fin.castAdd 13 (0 : Fin 13)) (Fin.natAdd 13 (0 : Fin 13))).mpr (adj_diag 0)
    rw [val_ge C.gates _ _ h] at h1
    exact absurd h1 (by simp)

def ia (j : ℕ) : ℕ := (gateAt C (j - 26)).inputs.getD 0 0

def ib (j : ℕ) : ℕ := (gateAt C (j - 26)).inputs.getD 1 0

lemma star (hC : PEqualNP.TopForm.IsAO2 26 C)
    (hno : ¬∃ x4 x5 : ℕ, (gateAt C x4).op = GateOp.and ∧ (gateAt C x5).op = GateOp.and ∧
      InCone 26 C x4 x5) (j : ℕ) (hj : Reach C j C.output) :
    Lin C (ia C j) ∧ Lin C (ib C j) ∧ ia C j < j ∧ ib C j < j ∧
      ∀ u v : Fin 26, (val C.gates (pr u v) j = true ↔
        (u ∈ S C (ia C j) ∨ v ∈ S C (ia C j)) ∧ (u ∈ S C (ib C j) ∨ v ∈ S C (ib C j))) := by
  obtain ⟨h1, h2, hop, _⟩ := reach_and C hC j _ hj
  obtain ⟨a, b, hab, ha, hb, _, hv⟩ := gv C hC j h1 h2
  have ea : ia C j = a := by simp [ia, hab]
  have eb : ib C j = b := by simp [ib, hab]
  rw [ea, eb]
  have hk : j - 26 < C.gates.length := by omega
  have hfree : ∀ i, (gateAt C i).op = GateOp.and → ¬ InCone 26 C i (j - 26) :=
    fun i hi hc => hno ⟨i, j - 26, hi, hop, hc⟩
  have la := input_lin C (j - 26) a hk (by rw [hab]; simp) (by omega) hfree
  have lb := input_lin C (j - 26) b hk (by rw [hab]; simp) (by omega) hfree
  refine ⟨la, lb, ha, hb, fun u v => ?_⟩
  rw [hv, hop, ev_and, Bool.and_eq_true, lin_sem C hC a la, lin_sem C hC b lb]

lemma star2 (hC : PEqualNP.TopForm.IsAO2 26 C)
    (hno : ¬∃ x4 x5 : ℕ, (gateAt C x4).op = GateOp.and ∧ (gateAt C x5).op = GateOp.and ∧
      InCone 26 C x4 x5)
    (hout : ∀ u v : Fin 26, val C.gates (pr u v) C.output = true ↔ adjB u v = true)
    (j : ℕ) (hj : Reach C j C.output) :
    (∀ v, ¬ (v ∈ S C (ia C j) ∧ v ∈ S C (ib C j))) ∧
    (∀ u ∈ S C (ia C j), ∀ v ∈ S C (ib C j), adjB u v = true) ∧
    ((S C (ia C j)).card = 1 ∨ (S C (ib C j)).card = 1) := by
  obtain ⟨la, lb, _, _, hs⟩ := star C hC hno j hj
  have hadj : ∀ u v, val C.gates (pr u v) j = true → adjB u v = true := by
    intro u v h
    exact (hout u v).mp (reach_val C hC j _ hj _ h)
  have hd : ∀ v, ¬ (v ∈ S C (ia C j) ∧ v ∈ S C (ib C j)) := by
    rintro v ⟨h1, h2⟩
    have := hadj v v ((hs v v).mpr ⟨Or.inl h1, Or.inl h2⟩)
    rw [adj_irr] at this
    exact absurd this (by simp)
  have hc : ∀ u ∈ S C (ia C j), ∀ v ∈ S C (ib C j), adjB u v = true :=
    fun u hu v hv => hadj u v ((hs u v).mpr ⟨Or.inl hu, Or.inr hv⟩)
  refine ⟨hd, hc, ?_⟩
  by_contra hne
  push_neg at hne
  have n1 := (lin_ne C hC _ la).card_pos
  have n2 := (lin_ne C hC _ lb).card_pos
  obtain ⟨p1, hp1, p2, hp2, hp⟩ := Finset.one_lt_card.mp (show 1 < (S C (ia C j)).card by omega)
  obtain ⟨q1, hq1, q2, hq2, hq⟩ := Finset.one_lt_card.mp (show 1 < (S C (ib C j)).card by omega)
  have := common p1 p2 hp
  have := Finset.card_le_one.mp this q1 (by simp [hc p1 hp1 q1 hq1, hc p2 hp2 q1 hq1])
    q2 (by simp [hc p1 hp1 q2 hq2, hc p2 hp2 q2 hq2])
  exact hq this

def cw (j : ℕ) : ℕ := if (S C (ia C j)).card = 1 then ia C j else ib C j

def lw (j : ℕ) : ℕ := if (S C (ia C j)).card = 1 then ib C j else ia C j

lemma cw_facts (hC : PEqualNP.TopForm.IsAO2 26 C)
    (hno : ¬∃ x4 x5 : ℕ, (gateAt C x4).op = GateOp.and ∧ (gateAt C x5).op = GateOp.and ∧
      InCone 26 C x4 x5)
    (hout : ∀ u v : Fin 26, val C.gates (pr u v) C.output = true ↔ adjB u v = true)
    (j : ℕ) (hj : Reach C j C.output) :
    (S C (cw C j)).card = 1 ∧ Lin C (lw C j) ∧ lw C j < j ∧
      (∀ c ∈ S C (cw C j), ∀ y ∈ S C (lw C j), adjB c y = true) := by
  obtain ⟨la, lb, ha, hb, _⟩ := star C hC hno j hj
  obtain ⟨_, hc, h1⟩ := star2 C hC hno hout j hj
  by_cases h : (S C (ia C j)).card = 1
  · simp only [cw, lw, if_pos h]
    exact ⟨h, lb, hb, hc⟩
  · simp only [cw, lw, if_neg h]
    refine ⟨h1.resolve_left h, la, ha, fun c hc' y hy => ?_⟩
    rw [adj_symm]
    exact hc y hy c hc'

lemma cover (hC : PEqualNP.TopForm.IsAO2 26 C)
    (hno : ¬∃ x4 x5 : ℕ, (gateAt C x4).op = GateOp.and ∧ (gateAt C x5).op = GateOp.and ∧
      InCone 26 C x4 x5)
    (hout : ∀ u v : Fin 26, val C.gates (pr u v) C.output = true ↔ adjB u v = true)
    (u v : Fin 26) (huv : adjB u v = true) :
    ∃ j, Reach C j C.output ∧ ((u ∈ S C (cw C j) ∧ v ∈ S C (lw C j)) ∨
      (v ∈ S C (cw C j) ∧ u ∈ S C (lw C j))) := by
  obtain ⟨j, hj, hv⟩ := z_sem C hC _ (out_Z C hout) _ ((hout u v).mpr huv)
  refine ⟨j, hj, ?_⟩
  obtain ⟨_, _, _, _, hs⟩ := star C hC hno j hj
  obtain ⟨hd, _, _⟩ := star2 C hC hno hout j hj
  have h := (hs u v).mp hv
  have hu := hd u
  have hv' := hd v
  by_cases hc : (S C (ia C j)).card = 1
  · simp only [cw, lw, if_pos hc]
    tauto
  · simp only [cw, lw, if_neg hc]
    tauto

end stars


section count

variable (C : Circuit)

lemma dbl (s : Finset ℕ) (T : ℕ → Finset (Fin 26)) (h : ∀ j ∈ s, (T j).card = 1) :
    ∑ c : Fin 26, (s.filter (fun j => c ∈ T j)).card = s.card := by
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  have : ∀ j ∈ s, ∑ c : Fin 26, (if c ∈ T j then 1 else 0) = 1 := by
    intro j hj
    rw [Finset.sum_boole]
    simp [Finset.filter_mem_eq_inter, h j hj]
  rw [Finset.sum_congr rfl this]
  simp

noncomputable def G (c : Fin 26) : Finset ℕ :=
  (A C C.output).filter (fun j => c ∈ S C (cw C j))

noncomputable def D (c : Fin 26) : Finset (Fin 26) := (G C c).biUnion (fun j => S C (lw C j))

noncomputable def Lc (c : Fin 26) : Finset ℕ := (Finset.range (26 + C.gates.length)).filter
  (fun k => Lin C k ∧ 2 ≤ (S C k).card ∧ S C k ⊆ D C c)

noncomputable def LL : Finset ℕ := (Finset.range (26 + C.gates.length)).filter
  (fun k => Lin C k ∧ 2 ≤ (S C k).card)

noncomputable def PU : Finset ℕ := (Finset.range (26 + C.gates.length)).filter
  (fun k => Z C k ∧ 2 ≤ (A C k).card ∧ A C k ⊆ A C C.output)

lemma memG (c : Fin 26) (j : ℕ) : j ∈ G C c ↔ j ∈ A C C.output ∧ c ∈ S C (cw C j) := by
  simp [G]

lemma memD (c y : Fin 26) : y ∈ D C c ↔ ∃ j ∈ G C c, y ∈ S C (lw C j) := by
  simp [D]

variable (hC : PEqualNP.TopForm.IsAO2 26 C)
    (hno : ¬∃ x4 x5 : ℕ, (gateAt C x4).op = GateOp.and ∧ (gateAt C x5).op = GateOp.and ∧
      InCone 26 C x4 x5)
    (hout : ∀ u v : Fin 26, val C.gates (pr u v) C.output = true ↔ adjB u v = true)

include hC hno hout in
lemma dn (c : Fin 26) : ∀ y ∈ D C c, adjB c y = true := by
  intro y hy
  obtain ⟨j, hjG, hy⟩ := (memD C c y).mp hy
  obtain ⟨hjA, hc⟩ := (memG C c j).mp hjG
  exact (cw_facts C hC hno hout j ((mem_A C hC j _).mp hjA)).2.2.2 c hc y hy

include hC hno hout in
lemma dc_le (c : Fin 26) : (D C c).card ≤ (G C c).card + (Lc C c).card := by
  have hW : ∀ w ∈ (G C c).image (lw C), w < 26 + C.gates.length ∧ Lin C w := by
    intro w hw
    obtain ⟨j, hjG, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hjA, _⟩ := (memG C c j).mp hjG
    have hr := (mem_A C hC j _).mp hjA
    obtain ⟨_, hl, hlt, _⟩ := cw_facts C hC hno hout j hr
    have := (reach_and C hC j _ hr).2.1
    exact ⟨by omega, hl⟩
  have h := leaf_count (Lin C) (S C) (lin_cls C hC) _ _ hW
  rw [Finset.image_biUnion] at h
  have hi : ((G C c).image (lw C)).card ≤ (G C c).card := Finset.card_image_le
  have h' : (D C c).card ≤ ((G C c).image (lw C)).card + (Lc C c).card := h
  omega

include hC hno hout in
lemma lsum : ∑ c : Fin 26, (Lc C c).card ≤ (LL C).card := by
  have hdisj : ((Finset.univ : Finset (Fin 26)) : Set (Fin 26)).PairwiseDisjoint (Lc C) := by
    intro c _ c' _ hne
    show Disjoint (Lc C c) (Lc C c')
    rw [Finset.disjoint_left]
    intro k hk hk'
    simp only [Lc, Finset.mem_filter] at hk hk'
    obtain ⟨y1, hy1, y2, hy2, hy⟩ := Finset.one_lt_card.mp (show 1 < (S C k).card by omega)
    have a1 := dn C hC hno hout c y1 (hk.2.2.2 hy1)
    have a2 := dn C hC hno hout c y2 (hk.2.2.2 hy2)
    have b1 := dn C hC hno hout c' y1 (hk'.2.2.2 hy1)
    have b2 := dn C hC hno hout c' y2 (hk'.2.2.2 hy2)
    have := Finset.card_le_one.mp (common c c' hne) y1 (by simp [a1, b1]) y2 (by simp [a2, b2])
    exact hy this
  rw [← Finset.card_biUnion hdisj]
  apply Finset.card_le_card
  intro k hk
  rw [Finset.mem_biUnion] at hk
  obtain ⟨c, _, hk⟩ := hk
  simp only [Lc, LL, Finset.mem_filter] at hk ⊢
  exact ⟨hk.1, hk.2.1, hk.2.2.1⟩

include hC hno hout in
lemma e_le : 104 ≤ 2 * ∑ c : Fin 26, (D C c).card := by
  set I : Finset (Fin 26 × Fin 26) :=
    Finset.univ.biUnion (fun c => (D C c).image (fun y => (c, y))) with hI
  have h1 : I.card ≤ ∑ c : Fin 26, (D C c).card :=
    le_trans Finset.card_biUnion_le (Finset.sum_le_sum fun c _ => Finset.card_image_le)
  have h2 : (Finset.univ.filter (fun p : Fin 26 × Fin 26 => adjB p.1 p.2 = true)) ⊆
      I ∪ I.image Prod.swap := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨j, hj, h⟩ := cover C hC hno hout p.1 p.2 hp.2
    have hjA : j ∈ A C C.output := (mem_A C hC j _).mpr hj
    rcases h with ⟨hu, hv⟩ | ⟨hv, hu⟩
    · apply Finset.mem_union_left
      rw [hI, Finset.mem_biUnion]
      refine ⟨p.1, Finset.mem_univ _, Finset.mem_image.mpr ⟨p.2, ?_, rfl⟩⟩
      exact (memD C _ _).mpr ⟨j, (memG C _ _).mpr ⟨hjA, hu⟩, hv⟩
    · apply Finset.mem_union_right
      rw [Finset.mem_image]
      refine ⟨(p.2, p.1), ?_, rfl⟩
      rw [hI, Finset.mem_biUnion]
      refine ⟨p.2, Finset.mem_univ _, Finset.mem_image.mpr ⟨p.1, ?_, rfl⟩⟩
      exact (memD C _ _).mpr ⟨j, (memG C _ _).mpr ⟨hjA, hv⟩, hu⟩
  have h3 := Finset.card_le_card h2
  rw [ecard] at h3
  have h4 := Finset.card_union_le I (I.image Prod.swap)
  have h5 : (I.image Prod.swap).card ≤ I.card := Finset.card_image_le
  omega

include hC hno hout in
lemma gsum : ∑ c : Fin 26, (G C c).card = (A C C.output).card :=
  dbl (A C C.output) (fun j => S C (cw C j))
    (fun j hj => (cw_facts C hC hno hout j ((mem_A C hC j _).mp hj)).1)

include hC hno hout in
lemma cen : 13 ≤ (A C C.output).card := by
  set Cen := Finset.univ.filter (fun c : Fin 26 => (G C c).Nonempty) with hCen
  set f : Fin 26 → Fin 13 := fun c =>
    if h : c.val < 13 then ⟨c.val, h⟩ else -⟨c.val - 13, by omega⟩ with hf
  have hfP : ∀ p : Fin 13, f (Fin.castAdd 13 p) = p := by decide
  have hfL : ∀ p : Fin 13, f (Fin.natAdd 13 (-p)) = p := by decide
  have h1 : (Finset.univ : Finset (Fin 13)) ⊆ Cen.image f := by
    intro p _
    rw [Finset.mem_image]
    have hp := p.isLt
    obtain ⟨j, hj, h⟩ := cover C hC hno hout _ _ (adj_diag p)
    have hjA : j ∈ A C C.output := (mem_A C hC j _).mpr hj
    rcases h with ⟨hu, _⟩ | ⟨hv, _⟩
    · refine ⟨Fin.castAdd 13 p, ?_, ?_⟩
      · rw [hCen, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, j, (memG C _ _).mpr ⟨hjA, hu⟩⟩
      · exact hfP p
    · refine ⟨Fin.natAdd 13 (-p), ?_, ?_⟩
      · rw [hCen, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, j, (memG C _ _).mpr ⟨hjA, hv⟩⟩
      · exact hfL p
  have h2 := Finset.card_le_card h1
  have h3 : (Cen.image f).card ≤ Cen.card := Finset.card_image_le
  have h4 : Cen.card ≤ ∑ c : Fin 26, (G C c).card := by
    rw [Finset.card_eq_sum_ones]
    calc ∑ c ∈ Cen, 1 ≤ ∑ c ∈ Cen, (G C c).card := Finset.sum_le_sum (fun c hc => by
            rw [hCen, Finset.mem_filter] at hc; exact hc.2.card_pos)
      _ ≤ ∑ c : Fin 26, (G C c).card := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  rw [gsum C hC hno hout] at h4
  simp only [Finset.card_univ, Fintype.card_fin] at h2
  omega

include hC hout in
lemma pu_le : (A C C.output).card ≤ 1 + (PU C).card := by
  have hz := out_Z C hout
  have h := leaf_count (Z C) (A C) (z_cls C hC) (26 + C.gates.length) {C.output} (by
    intro w hw
    rw [Finset.mem_singleton] at hw
    subst hw
    exact ⟨hz.2.1, hz⟩)
  rw [Finset.singleton_biUnion, Finset.card_singleton] at h
  exact h

include hC in
lemma size_le : (LL C).card + (A C C.output).card + (PU C).card ≤ C.gates.length := by
  have hLL : ∀ k ∈ LL C, 26 ≤ k ∧ k < 26 + C.gates.length ∧
      (gateAt C (k - 26)).op = GateOp.or := by
    intro k hk
    simp only [LL, Finset.mem_filter, Finset.mem_range] at hk
    have h26 : 26 ≤ k := by
      by_contra h
      push_neg at h
      have := hk.2.2
      rw [S_inp C k h, Finset.card_singleton] at this
      omega
    obtain ⟨_, _, _, _, _, _, hor, _⟩ := lin_struct C hC k hk.2.1 h26
    exact ⟨h26, hk.1, hor⟩
  have hAA : ∀ k ∈ A C C.output, 26 ≤ k ∧ k < 26 + C.gates.length ∧
      (gateAt C (k - 26)).op = GateOp.and := by
    intro k hk
    obtain ⟨h1, h2, h3, _⟩ := reach_and C hC k _ ((mem_A C hC k _).mp hk)
    exact ⟨h1, h2, h3⟩
  have hPP : ∀ k ∈ PU C, Z C k ∧ 2 ≤ (A C k).card := by
    intro k hk
    simp only [PU, Finset.mem_filter] at hk
    exact ⟨hk.2.1, hk.2.2.1⟩
  have d1 : Disjoint (LL C) (A C C.output) := by
    rw [Finset.disjoint_left]
    intro k h1 h2
    have := (hLL k h1).2.2
    rw [(hAA k h2).2.2] at this
    exact absurd this (by simp)
  have d2 : Disjoint (LL C ∪ A C C.output) (PU C) := by
    rw [Finset.disjoint_left]
    intro k h1 h2
    obtain ⟨hz, h2c⟩ := hPP k h2
    rcases Finset.mem_union.mp h1 with h1 | h1
    · simp only [LL, Finset.mem_filter] at h1
      have : S C k = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro v hv
        rw [mem_S, hz.2.2 v] at hv
        exact absurd hv (by simp)
      rw [this] at h1
      simp at h1
    · obtain ⟨a1, a2, a3⟩ := hAA k h1
      rw [A_and C hC k a1 a2 a3, Finset.card_singleton] at h2c
      omega
  have hsub : LL C ∪ A C C.output ∪ PU C ⊆ Finset.Ico 26 (26 + C.gates.length) := by
    intro k hk
    rw [Finset.mem_Ico]
    rcases Finset.mem_union.mp hk with hk | hk
    · rcases Finset.mem_union.mp hk with hk | hk
      · exact ⟨(hLL k hk).1, (hLL k hk).2.1⟩
      · exact ⟨(hAA k hk).1, (hAA k hk).2.1⟩
    · exact ⟨(hPP k hk).1.1, (hPP k hk).1.2.1⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint d2, Finset.card_union_of_disjoint d1, Nat.card_Ico] at this
  omega

end count

theorem main (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 26 C)
    (hF : ∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
      ∃ p l : Fin 13, ((p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) ∧
        x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true)
    (hno : ¬∃ x4 x5 : ℕ, (gateAt C x4).op = GateOp.and ∧ (gateAt C x5).op = GateOp.and ∧
      InCone 26 C x4 x5) : 64 ≤ C.size := by
  have hout := spec C hF
  have e1 := e_le C hC hno hout
  have e2 : ∑ c : Fin 26, (D C c).card ≤ (A C C.output).card + (LL C).card := by
    calc ∑ c : Fin 26, (D C c).card ≤ ∑ c : Fin 26, ((G C c).card + (Lc C c).card) :=
          Finset.sum_le_sum (fun c _ => dc_le C hC hno hout c)
      _ = ∑ c : Fin 26, (G C c).card + ∑ c : Fin 26, (Lc C c).card := Finset.sum_add_distrib
      _ ≤ (A C C.output).card + (LL C).card := by
          rw [gsum C hC hno hout]
          exact Nat.add_le_add_left (lsum C hC hno hout) _
  have e3 := cen C hC hno hout
  have e4 := pu_le C hC hout
  have e5 := size_le C hC
  show 64 ≤ C.gates.length
  omega

end PEqualNP.Outside.L_meta_2056_aux.TwoDirty.FlatSumPlane


namespace PEqualNP.Outside.L_meta_2056_aux.TwoDirty.OneDirtyPlane

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.Core
  PEqualNP.EdgeOwnership PEqualNP.SplitCount
open PEqualNP.Outside.L_meta_2056_aux.TwoDirty.FlatSumPlane

abbrev SumInc (p l : Fin 13) : Prop :=
  (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)

def plane : SimpleGraph (Fin 26) where
  Adj u v := adjB u v = true
  symm := by
    constructor
    intro u v h
    exact (adj_symm u v).symm.trans h
  loopless := by
    constructor
    intro v h
    rw [adj_irr] at h
    cases h

instance : DecidableRel plane.Adj := fun u v => inferInstanceAs (Decidable (adjB u v = true))

lemma plane_no_four : NoFourCycle plane := common

lemma plane_bip : ∀ u v : Fin 26, plane.Adj u v → decide (u.val < 13) ≠ decide (v.val < 13) := by
  decide

lemma plane_spec (x : Fin 26 → Bool) : graphFun plane ∅ x = true ↔
    ∃ p l : Fin 13, SumInc p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq]
  constructor
  · rintro ⟨u, v, h, hu, hv⟩
    change adjB u v = true at h
    unfold adjB at h
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩
    · refine ⟨⟨u.val, h1⟩, ⟨v.val - 13, by omega⟩, (inc_iff _ _).mpr h3, ?_, ?_⟩
      · have e : Fin.castAdd 13 (⟨u.val, h1⟩ : Fin 13) = u := Fin.ext rfl
        simpa only [e] using hu
      · have e : Fin.natAdd 13 (⟨v.val - 13, by omega⟩ : Fin 13) = v := by
          apply Fin.ext; change 13 + (v.val - 13) = v.val; omega
        simpa only [e] using hv
    · refine ⟨⟨v.val, h1⟩, ⟨u.val - 13, by omega⟩, (inc_iff _ _).mpr h3, ?_, ?_⟩
      · have e : Fin.castAdd 13 (⟨v.val, h1⟩ : Fin 13) = v := Fin.ext rfl
        simpa only [e] using hv
      · have e : Fin.natAdd 13 (⟨u.val - 13, by omega⟩ : Fin 13) = u := by
          apply Fin.ext; change 13 + (u.val - 13) = u.val; omega
        simpa only [e] using hu
  · rintro ⟨p, l, hi, hp, hl⟩
    exact ⟨Fin.castAdd 13 p, Fin.natAdd 13 l, adj_cl p l ((inc_iff p l).mp hi), hp, hl⟩

lemma and_index_lt (C : Circuit) (i : ℕ) (h : (gateAt C i).op = GateOp.and) :
    i < C.gates.length := by
  by_contra hn
  have hi : C.gates.length ≤ i := Nat.le_of_not_gt hn
  simp only [gateAt, List.getD_eq_default _ _ hi] at h
  cases h

lemma flat_lower (C : Circuit) (ao : IsAO2 26 C)
    (correct : circuitFun 26 C = graphFun plane ∅)
    (flat : ∀ i < C.gates.length, ∀ j < C.gates.length,
      (gateAt C i).op = GateOp.and → (gateAt C j).op = GateOp.and → ¬ InCone 26 C i j) :
    64 ≤ C.size := by
  apply PEqualNP.Outside.L_meta_2056_aux.TwoDirty.FlatSumPlane.main C ao
  · intro x
    change circuitFun 26 C x = true ↔ _
    rw [correct]
    exact plane_spec x
  · rintro ⟨i, j, hi, hj, hc⟩
    exact flat i (and_index_lt C i hi) j (and_index_lt C j hj) hi hj hc

theorem normalized_at_most_one_dirty_lower (C : Circuit)
    (ao : IsAO2 26 C) (correct : circuitFun 26 C = graphFun plane ∅)
    (fixed : IsLiftFixedPoint plane C)
    (live : ∀ k < C.gates.length, InOutputCone 26 C k)
    (operands : PEqualNP.Outside.L_meta_2056_aux.TwoDirty.OneDirtyReduction.NoSoundOperands plane C)
    (singleton : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ∀ p : Fin 26, gateVal 26 C k (unitInput p) = false)
    (one : ∀ i < C.gates.length, ∀ j < C.gates.length,
      (gateAt C i).op = GateOp.and → (gateAt C j).op = GateOp.and →
      ¬ BelowF plane C i → ¬ BelowF plane C j → i = j) :
    64 ≤ C.size := by
  classical
  by_cases hd : ∃ g < C.gates.length, (gateAt C g).op = GateOp.and ∧ ¬ BelowF plane C g
  · obtain ⟨g, hg, ha, hn⟩ := hd
    have clean : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → k ≠ g → BelowF plane C k := by
      intro k hk hka hkg
      by_contra hkn
      exact hkg (one k hk g hg hka ha hkn hn)
    have model : PEqualNP.Outside.L_meta_2056_aux.TwoDirty.OneDirtyReduction.Model 26 plane C g :=
      ⟨ao, correct, fixed, live, operands, singleton, hg, ha, hn, clean⟩
    obtain ⟨D, hD, hs, hF, hflat⟩ :=
      PEqualNP.Outside.L_meta_2056_aux.TwoDirty.OneDirtyReduction.complete model plane_no_four
        (fun u => decide (u.val < 13)) plane_bip
    exact (flat_lower D hD hF hflat).trans hs
  · apply flat_lower C ao correct
    intro i hi j hj ha hb hc
    have clean : BelowF plane C i := by
      by_contra h
      exact hd ⟨i, hi, ha, h⟩
    have ho := (PEqualNP.Outside.L_meta_2056_aux.TwoDirty.OneDirtyReduction.sound_ancestor
      ao fixed live operands clean hj hc).1
    rw [hb] at ho
    cases ho

end PEqualNP.Outside.L_meta_2056_aux.TwoDirty.OneDirtyPlane


namespace PEqualNP.Outside.L_meta_2056_aux.TwoDirty.AllCleanBudget

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadK

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
lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl
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

lemma inCone_trans (n : ℕ) (C : Circuit) (a k : ℕ) (hak : InCone n C a k) :
    ∀ j, InCone n C k j → InCone n C a j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k2, hk2, hin, h3 | h3⟩ := h
    · subst h3
      rw [inCone_iff]
      exact ⟨h0, k, hk2, hin, Or.inr hak⟩
    · rw [inCone_iff]
      exact ⟨h0, k2, hk2, hin, Or.inr (ih k2 hk2 h3)⟩

def reachable (n : ℕ) (C : Circuit) (k : ℕ) : Prop :=
  k < C.gates.length ∧ (n + k = C.output ∨ InCone n C k (C.output - n))

lemma reachable_child {n : ℕ} {C : Circuit} (rb : ReadsBack n C)
    {k j : ℕ} (hk : reachable n C k) (hj : n + j ∈ (gateAt C k).inputs) :
    reachable n C j := by
  have hlt := rb k hk.1 (n + j) hj
  have hbound := hk.1
  refine ⟨by omega, Or.inr ?_⟩
  have hcone : InCone n C j k := (inCone_iff n C j k).2
    ⟨hk.1, j, by omega, hj, Or.inl rfl⟩
  rcases hk.2 with h | h
  · rwa [show C.output - n = k by omega]
  · exact inCone_trans n C j k hcone _ h

lemma cone_reader {n : ℕ} {C : Circuit} {i j : ℕ} (h : InCone n C i j) :
    ∃ k, k < C.gates.length ∧ (k = j ∨ InCone n C k j) ∧
      n + i ∈ (gateAt C k).inputs := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    obtain ⟨hj, k, hkj, hin, rfl | hc⟩ := (inCone_iff n C i j).1 h
    · exact ⟨j, hj, Or.inl rfl, hin⟩
    · obtain ⟨l, hl, rfl | hlc, hread⟩ := ih k hkj hc
      · exact ⟨l, hl, Or.inr ((inCone_iff n C l j).2
          ⟨hj, l, hkj, hin, Or.inl rfl⟩), hread⟩
      · exact ⟨l, hl, Or.inr ((inCone_iff n C l j).2
          ⟨hj, k, hkj, hin, Or.inr hlc⟩), hread⟩

lemma reachable_reader {n : ℕ} {C : Circuit} {i : ℕ}
    (hi : reachable n C i) (hne : i ≠ C.output - n) :
    ∃ k, reachable n C k ∧ n + i ∈ (gateAt C k).inputs := by
  rcases hi.2 with he | hc
  · omega
  · obtain ⟨k, hk, hr | hr, hin⟩ := cone_reader hc
    · have hn : n ≤ C.output := by
        by_contra h
        obtain ⟨_, j, hj, _, _⟩ := (inCone_iff n C i (C.output - n)).1 hc
        omega
      exact ⟨k, ⟨hk, Or.inl (by omega)⟩, hin⟩
    · exact ⟨k, ⟨hk, Or.inr hr⟩, hin⟩

def singletonSupport (n : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun u => val C (List.ofFn (pairInput u u)) w = true

lemma mem_support {n : ℕ} {C : Circuit} {w : ℕ} {u : Fin n} :
    u ∈ singletonSupport n C w ↔ val C (List.ofFn (pairInput u u)) w = true := by
  simp [singletonSupport]

lemma support_input {n : ℕ} {C : Circuit} (u : Fin n) :
    singletonSupport n C u.val = {u} := by
  ext v
  rw [mem_support, val_ofFn]
  simp [pairInput, eq_comm]

lemma support_or {n : ℕ} {C : Circuit} (rb : ReadsBack n C)
    {k : ℕ} (hk : k < C.gates.length) (hop : (gateAt C k).op = GateOp.or) (u : Fin n) :
    u ∈ singletonSupport n C (n + k) ↔
      ∃ w ∈ (gateAt C k).inputs, u ∈ singletonSupport n C w := by
  simp only [mem_support, val_or (by simp : (List.ofFn (pairInput u u)).length = n) hk hop]
  exact ⟨fun ⟨w, hw, _, ht⟩ => ⟨w, hw, ht⟩, fun ⟨w, hw, ht⟩ => ⟨w, hw, rb k hk w hw, ht⟩⟩

lemma gate_op {C : Circuit} (hm : Monotone2 C) {k : ℕ} (hk : k < C.gates.length) :
    (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or := by
  simpa using (hm _ (gateAt_mem hk)).1

lemma input_card {C : Circuit} (hm : Monotone2 C) {k : ℕ} (hk : k < C.gates.length) :
    (gateAt C k).inputs.toFinset.card ≤ 2 :=
  (List.toFinset_card_le _).trans (hm _ (gateAt_mem hk)).2

noncomputable def births (n : ℕ) (C : Circuit) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter fun k =>
    reachable n C k ∧ (gateAt C k).op = GateOp.and ∧
      ∃ a b, (gateAt C k).inputs = [a, b] ∧
        (singletonSupport n C a).Nonempty ∧ (singletonSupport n C b).Nonempty

lemma mem_births {n : ℕ} {C : Circuit} {k : ℕ} :
    k ∈ births n C ↔ reachable n C k ∧ (gateAt C k).op = GateOp.and ∧
      ∃ a b, (gateAt C k).inputs = [a, b] ∧
        (singletonSupport n C a).Nonempty ∧ (singletonSupport n C b).Nonempty := by
  classical
  simp only [births, Finset.mem_filter, Finset.mem_range]
  exact ⟨And.right, fun h => ⟨h.1.1, h⟩⟩

def positiveInputs (n : ℕ) (C : Circuit) (k : ℕ) : Finset ℕ := by
  classical
  exact (gateAt C k).inputs.toFinset.filter fun w => (singletonSupport n C w).Nonempty

lemma mem_positiveInputs {n : ℕ} {C : Circuit} {k w : ℕ} :
    w ∈ positiveInputs n C k ↔ w ∈ (gateAt C k).inputs ∧ (singletonSupport n C w).Nonempty := by
  classical
  simp [positiveInputs]

noncomputable def merges (n : ℕ) (C : Circuit) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter fun k =>
    reachable n C k ∧ (gateAt C k).op = GateOp.or ∧
      1 < (singletonSupport n C (n + k)).card ∧ 1 < (positiveInputs n C k).card

lemma mem_merges {n : ℕ} {C : Circuit} {k : ℕ} :
    k ∈ merges n C ↔ reachable n C k ∧ (gateAt C k).op = GateOp.or ∧
      1 < (singletonSupport n C (n + k)).card ∧ 1 < (positiveInputs n C k).card := by
  classical
  simp only [merges, Finset.mem_filter, Finset.mem_range]
  exact ⟨And.right, fun h => ⟨h.1.1, h⟩⟩

-- Each reachable wire with empty singleton support other than the output
-- is read by some reachable gate. Counting these reads pays for connecting
-- the edge-producing AND gates, even when the circuit shares subcircuits.
lemma gate_budget {n : ℕ} {C : Circuit} (hm : Monotone2 C) (rb : ReadsBack n C)
    (hclean : ∀ k, reachable n C k → (gateAt C k).op = GateOp.and →
      singletonSupport n C (n + k) = ∅) :
    2 * (births n C).card + (merges n C).card ≤ C.size + 1 := by
  classical
  let R := (Finset.range C.gates.length).filter (reachable n C)
  let Z := R.filter fun k => singletonSupport n C (n + k) = ∅
  let D := fun k => (gateAt C k).inputs.toFinset.filter fun w =>
    n ≤ w ∧ singletonSupport n C w = ∅
  let E := fun k => (D k).image fun w => w - n
  have hR (k) : k ∈ R ↔ reachable n C k := by
    simp only [R, Finset.mem_filter, Finset.mem_range]
    exact ⟨And.right, fun h => ⟨h.1, h⟩⟩
  have hZ (k) : k ∈ Z ↔ k ∈ R ∧ singletonSupport n C (n + k) = ∅ := Finset.mem_filter
  have hread : Z.erase (C.output - n) ⊆ R.biUnion E := by
    intro j hj
    obtain ⟨hne, hz⟩ := Finset.mem_erase.1 hj
    obtain ⟨k, hk, hin⟩ := reachable_reader ((hR j).1 ((hZ j).1 hz).1) hne
    refine Finset.mem_biUnion.2 ⟨k, (hR k).2 hk, Finset.mem_image.2 ⟨n + j, ?_, by omega⟩⟩
    exact Finset.mem_filter.2 ⟨List.mem_toFinset.2 hin, by omega, ((hZ j).1 hz).2⟩
  have hsum : Z.card ≤ (∑ k ∈ R, (D k).card) + 1 := by
    calc
      Z.card ≤ (Z.erase (C.output - n)).card + 1 := by
        by_cases h : C.output - n ∈ Z
        · exact Nat.le_of_eq (Finset.card_erase_add_one h).symm
        · rw [Finset.erase_eq_of_notMem h]; omega
      _ ≤ (R.biUnion E).card + 1 := Nat.add_le_add_right (Finset.card_le_card hread) _
      _ ≤ (∑ k ∈ R, (E k).card) + 1 := Nat.add_le_add_right Finset.card_biUnion_le _
      _ ≤ _ := Nat.add_le_add_right (Finset.sum_le_sum fun _ _ => Finset.card_image_le) _
  have hlocal : ∀ k ∈ R, (D k).card + 2 * (if k ∈ births n C then 1 else 0) +
      (if k ∈ merges n C then 1 else 0) ≤ 1 + (if k ∈ Z then 1 else 0) := by
    intro k hk
    have hr := (hR k).1 hk
    have hdp : Disjoint (D k) (positiveInputs n C k) := by
      rw [Finset.disjoint_left]
      intro w hd hp
      have he := (Finset.mem_filter.1 hd).2.2
      simpa [he] using (mem_positiveInputs.1 hp).2
    have hcap : (D k).card + (positiveInputs n C k).card ≤ 2 := by
      rw [← Finset.card_union_of_disjoint hdp]
      exact (Finset.card_le_card (Finset.union_subset
        (Finset.filter_subset _ _) (Finset.filter_subset _ _))).trans (input_card hm hr.1)
    by_cases hb : k ∈ births n C
    · obtain ⟨_, hop, a, b, hab, ha, hb'⟩ := mem_births.1 hb
      have hz := (hZ k).2 ⟨hk, hclean k hr hop⟩
      have hl : k ∉ merges n C := by
        intro h
        have hh := (mem_merges.1 h).2.1
        rw [hop] at hh
        cases hh
      have hd : D k = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.2
        intro w hw
        have hw' := Finset.mem_filter.1 hw
        have hh : w = a ∨ w = b := by simpa [hab] using hw'.1
        rcases hh with rfl | rfl
        · simp [hw'.2.2] at ha
        · simp [hw'.2.2] at hb'
      simp [hb, hz, hl, hd]
    · by_cases hl : k ∈ merges n C
      · have hpos := (mem_merges.1 hl).2.2.2
        simp only [hb, hl, ite_false, ite_true, Nat.mul_zero, Nat.add_zero]
        split_ifs <;> omega
      · by_cases hz : k ∈ Z
        · simp only [hb, hl, hz, ite_false, ite_true, Nat.mul_zero, Nat.add_zero]
          omega
        · have hs : (singletonSupport n C (n + k)).Nonempty :=
            Finset.nonempty_iff_ne_empty.2 fun h => hz ((hZ k).2 ⟨hk, h⟩)
          have hop : (gateAt C k).op = GateOp.or :=
            (gate_op hm hr.1).resolve_left fun h => hs.ne_empty (hclean k hr h)
          obtain ⟨u, hu⟩ := hs
          obtain ⟨w, hw, huw⟩ := (support_or rb hr.1 hop u).1 hu
          have hpos := Finset.card_pos.2 ⟨w, mem_positiveInputs.2 ⟨hw, u, huw⟩⟩
          simp only [hb, hl, hz, ite_false, Nat.mul_zero, Nat.add_zero]
          omega
  have count (T : Finset ℕ) (hT : T ⊆ R) :
      (∑ k ∈ R, if k ∈ T then 1 else 0) = T.card := by
    rw [← Finset.card_filter]
    congr 1
    ext k
    simp only [Finset.mem_filter]
    exact ⟨And.right, fun h => ⟨hT h, h⟩⟩
  have hB : births n C ⊆ R := fun _ h => (hR _).2 (mem_births.1 h).1
  have hL : merges n C ⊆ R := fun _ h => (hR _).2 (mem_merges.1 h).1
  have h := Finset.sum_le_sum hlocal
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    count _ hB, count _ hL, Finset.sum_add_distrib,
    count Z (Finset.filter_subset _ _)] at h
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at h
  have hRc : R.card ≤ C.size := by
    change R.card ≤ C.gates.length
    exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)
  omega

noncomputable def mergePool {n : ℕ} (C : Circuit) (G : SimpleGraph (Fin n))
    (c : Fin n) (m : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range m).filter fun k => k ∈ merges n C ∧
    ∀ v ∈ singletonSupport n C (n + k), G.Adj c v

lemma mem_mergePool {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} {c : Fin n}
    {m k : ℕ} : k ∈ mergePool C G c m ↔ k < m ∧ k ∈ merges n C ∧
      ∀ v ∈ singletonSupport n C (n + k), G.Adj c v := by
  classical
  simp [mergePool]

-- Expand the largest root with wide singleton support into its positive inputs.
-- A two-input expansion can add one root and is charged to that OR gate.
lemma leaf_budget {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} {c : Fin n}
    (hm : Monotone2 C) (rb : ReadsBack n C)
    (hclean : ∀ k, reachable n C k → (gateAt C k).op = GateOp.and →
      singletonSupport n C (n + k) = ∅)
    (m : ℕ) (roots : Finset ℕ)
    (hvalid : ∀ w ∈ roots, w < n ∨ reachable n C (w - n))
    (hadj : ∀ w ∈ roots, ∀ v ∈ singletonSupport n C w, G.Adj c v)
    (hbound : ∀ w ∈ roots, 1 < (singletonSupport n C w).card → w < n + m) :
    (roots.biUnion (singletonSupport n C)).card ≤ roots.card + (mergePool C G c m).card := by
  classical
  induction m generalizing roots with
  | zero =>
    have hsmall : ∀ w ∈ roots, (singletonSupport n C w).card ≤ 1 := by
      intro w hw
      by_contra! hb
      have hw' := hbound w hw hb
      have hs := support_input (C := C) (⟨w, by omega⟩ : Fin n)
      simp [hs] at hb
    calc
      _ ≤ ∑ w ∈ roots, (singletonSupport n C w).card := Finset.card_biUnion_le
      _ ≤ ∑ _w ∈ roots, 1 := Finset.sum_le_sum hsmall
      _ = _ := by simp [mergePool]
  | succ m ih =>
    have hpool : mergePool C G c m ⊆ mergePool C G c (m + 1) := by
      intro k hk
      obtain ⟨hk, hh⟩ := mem_mergePool.1 hk
      exact mem_mergePool.2 ⟨by omega, hh⟩
    by_cases htop : n + m ∈ roots ∧ 1 < (singletonSupport n C (n + m)).card
    · obtain ⟨hmem, hlarge⟩ := htop
      have hr : reachable n C m := by
        rcases hvalid _ hmem with h | h
        · omega
        · simpa using h
      have hor : (gateAt C m).op = GateOp.or := (gate_op hm hr.1).resolve_left fun h => by
        simp [hclean m hr h] at hlarge
      let P := positiveInputs n C m
      let T := roots.erase (n + m) ∪ P
      have hback : ∀ w ∈ P, w < n + m :=
        fun w hw => rb m hr.1 w (mem_positiveInputs.1 hw).1
      have hup : ∀ w ∈ P, singletonSupport n C w ⊆ singletonSupport n C (n + m) := by
        intro w hw u hu
        exact (support_or rb hr.1 hor u).2 ⟨w, (mem_positiveInputs.1 hw).1, hu⟩
      have hTvalid : ∀ w ∈ T, w < n ∨ reachable n C (w - n) := by
        intro w hw
        rcases Finset.mem_union.1 hw with hw | hw
        · exact hvalid _ (Finset.mem_of_mem_erase hw)
        · by_cases hn : w < n
          · exact Or.inl hn
          · exact Or.inr (reachable_child rb hr (by
              rw [show n + (w - n) = w by omega]
              exact (mem_positiveInputs.1 hw).1))
      have hTadj : ∀ w ∈ T, ∀ v ∈ singletonSupport n C w, G.Adj c v := by
        intro w hw v hv
        rcases Finset.mem_union.1 hw with hw | hw
        · exact hadj _ (Finset.mem_of_mem_erase hw) v hv
        · exact hadj _ hmem v (hup _ hw hv)
      have hTbound : ∀ w ∈ T, 1 < (singletonSupport n C w).card → w < n + m := by
        intro w hw hcard
        rcases Finset.mem_union.1 hw with hw | hw
        · have hlt := hbound w (Finset.mem_of_mem_erase hw) hcard
          have hne := (Finset.mem_erase.1 hw).1
          omega
        · exact hback w hw
      have hsub : roots.biUnion (singletonSupport n C) ⊆ T.biUnion (singletonSupport n C) := by
        intro u hu
        obtain ⟨w, hw, huw⟩ := Finset.mem_biUnion.1 hu
        by_cases he : w = n + m
        · subst w
          obtain ⟨a, ha, hua⟩ := (support_or rb hr.1 hor u).1 huw
          exact Finset.mem_biUnion.2 ⟨a, Finset.mem_union_right _
            (mem_positiveInputs.2 ⟨ha, u, hua⟩), hua⟩
        · exact Finset.mem_biUnion.2 ⟨w, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨he, hw⟩), huw⟩
      have hfirst := (Finset.card_le_card hsub).trans (ih T hTvalid hTadj hTbound)
      have hTcard := Finset.card_union_le (roots.erase (n + m)) P
      have herase := Finset.card_erase_add_one hmem
      have hPc : P.card ≤ 2 := (Finset.card_filter_le _ _).trans (input_card hm hr.1)
      by_cases hp : 1 < P.card
      · have hnew : m ∈ mergePool C G c (m + 1) := mem_mergePool.2
          ⟨by omega, mem_merges.2 ⟨hr, hor, hlarge, hp⟩, hadj _ hmem⟩
        have hn : m ∉ mergePool C G c m := fun h => (Nat.lt_irrefl m) (mem_mergePool.1 h).1
        have hsubpool : insert m (mergePool C G c m) ⊆ mergePool C G c (m + 1) :=
          Finset.insert_subset_iff.2 ⟨hnew, hpool⟩
        have hinc := Finset.card_le_card hsubpool
        rw [Finset.card_insert_of_notMem hn] at hinc
        change T.card ≤ (roots.erase (n + m)).card + P.card at hTcard
        omega
      · have hinc := Finset.card_le_card hpool
        change T.card ≤ (roots.erase (n + m)).card + P.card at hTcard
        omega
    · have hnew : ∀ w ∈ roots, 1 < (singletonSupport n C w).card → w < n + m := by
        intro w hw hw'
        have hlt := hbound w hw hw'
        have hne : w ≠ n + m := fun he => htop ⟨he ▸ hw, he ▸ hw'⟩
        omega
      have hfirst := ih roots hvalid hadj hnew
      have hinc := Finset.card_le_card hpool
      omega

lemma pair_mono {n : ℕ} {C : Circuit} (hm : Monotone2 C)
    {x y : Fin n → Bool} (hxy : ∀ u, x u = true → y u = true) :
    ∀ w, val C (List.ofFn x) w = true → val C (List.ofFn y) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hinput : w < n
    · let u : Fin n := ⟨w, hinput⟩
      change val C (List.ofFn x) u.val = true at hw
      change val C (List.ofFn y) u.val = true
      rw [val_ofFn] at *
      exact hxy u hw
    · have hwlt : w < n + C.gates.length := by
        by_contra! h
        rw [val_ge (by simp : (List.ofFn x).length = n) h] at hw
        cases hw
      obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < C.gates.length := by omega
      rcases gate_op hm hk with hop | hop
      · apply (val_and (by simp) hk hop).2
        intro i hi
        obtain ⟨hlt, ht⟩ := (val_and (by simp) hk hop).1 hw i hi
        exact ⟨hlt, ih i hlt ht⟩
      · obtain ⟨i, hi, hlt, ht⟩ := (val_or (by simp) hk hop).1 hw
        exact (val_or (by simp) hk hop).2 ⟨i, hi, hlt, ih i hlt ht⟩

lemma crossing {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)}
    (hm : Monotone2 C) (rb : ReadsBack n C)
    (hsafe : ∀ k, reachable n C k → (gateAt C k).op = GateOp.and →
      ∀ u v, gateVal n C k (pairInput u v) = true → G.Adj u v)
    {k a b : ℕ} (hk : reachable n C k) (hop : (gateAt C k).op = GateOp.and)
    (hab : (gateAt C k).inputs = [a,b]) :
    ∀ u ∈ singletonSupport n C a, ∀ v ∈ singletonSupport n C b, G.Adj u v := by
  intro u hu v hv
  apply hsafe k hk hop u v
  rw [gateVal_eq_val]
  apply (val_and (by simp) hk.1 hop).2
  intro w hw
  refine ⟨rb k hk.1 w hw, ?_⟩
  have hw' : w = a ∨ w = b := by simpa [hab] using hw
  rcases hw' with rfl | rfl
  · exact pair_mono hm (by intro i; simp [pairInput]; exact Or.inl) _ (mem_support.1 hu)
  · exact pair_mono hm (by intro i; simp [pairInput]; exact Or.inr) _ (mem_support.1 hv)

lemma birth_route {n : ℕ} {C : Circuit} (hm : Monotone2 C) (rb : ReadsBack n C)
    (hclean : ∀ k, reachable n C k → (gateAt C k).op = GateOp.and →
      singletonSupport n C (n + k) = ∅)
    (hempty : ∀ k, reachable n C k → (gateAt C k).op = GateOp.and →
      gateVal n C k (fun _ => false) = false)
    (u v : Fin n) :
    ∀ w, (w < n ∨ reachable n C (w - n)) → val C (List.ofFn (pairInput u v)) w = true →
      (∃ k ∈ births n C, ∀ a ∈ (gateAt C k).inputs,
        u ∈ singletonSupport n C a ∨ v ∈ singletonSupport n C a) ∨
      u ∈ singletonSupport n C w ∨ v ∈ singletonSupport n C w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw ht
    by_cases hi : w < n
    · let t : Fin n := ⟨w, hi⟩
      change val C (List.ofFn (pairInput u v)) t.val = true at ht
      change _ ∨ u ∈ singletonSupport n C t.val ∨ v ∈ singletonSupport n C t.val
      rw [val_ofFn] at ht
      rw [support_input]
      have he : t = u ∨ t = v := of_decide_eq_true ht
      exact Or.inr (he.imp (fun h => Finset.mem_singleton.2 h.symm) (fun h => Finset.mem_singleton.2 h.symm))
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : reachable n C k := by simpa using hw.resolve_left hi
      have sub (a) (ha : a ∈ (gateAt C k).inputs)
          (ht' : val C (List.ofFn (pairInput u v)) a = true) := by
        apply ih a (rb k hk.1 a ha) _ ht'
        by_cases hn : a < n
        · exact Or.inl hn
        · exact Or.inr (reachable_child rb hk (by rwa [show n + (a - n) = a by omega]))
      rcases gate_op hm hk.1 with hop | hop
      · by_cases hborn : ∃ k ∈ births n C, ∀ a ∈ (gateAt C k).inputs,
            u ∈ singletonSupport n C a ∨ v ∈ singletonSupport n C a
        · exact Or.inl hborn
        · have hone : ∀ a ∈ (gateAt C k).inputs,
              u ∈ singletonSupport n C a ∨ v ∈ singletonSupport n C a :=
            fun a ha => (sub a ha ((val_and (by simp) hk.1 hop).1 ht a ha).2).resolve_left hborn
          have hno (t : Fin n) : ¬ ∀ a ∈ (gateAt C k).inputs, t ∈ singletonSupport n C a := by
            intro h
            have hh := (val_and (by simp) hk.1 hop).2 (fun a ha => ⟨rb k hk.1 a ha,
              mem_support.1 (h a ha)⟩ : ∀ a ∈ (gateAt C k).inputs,
                a < n + k ∧ val C (List.ofFn (pairInput t t)) a = true)
            have hs := mem_support.2 hh
            simp [hclean k hk hop] at hs
          have hlen := (hm _ (gateAt_mem hk.1)).2
          generalize he : (gateAt C k).inputs = l at hlen
          cases l with
          | nil =>
            have hz := hempty k hk hop
            rw [gateVal_eq_val, (show val C (List.ofFn (fun _ : Fin n => false)) (n + k) = true from
              (val_and (by simp) hk.1 hop).2 (by simp [he]))] at hz
            cases hz
          | cons a as =>
            cases as with
            | nil =>
              rcases hone a (by simp [he]) with ha | ha
              · exact (hno u (by simpa [he] using ha)).elim
              · exact (hno v (by simpa [he] using ha)).elim
            | cons b bs =>
              have hb0 : bs = [] := List.length_eq_zero_iff.1 (by simp only [List.length_cons] at hlen; omega)
              subst bs
              have nonemp (a) (ha : a ∈ (gateAt C k).inputs) :
                  (singletonSupport n C a).Nonempty := by
                rcases hone a ha with hu | hv
                · exact ⟨u, hu⟩
                · exact ⟨v, hv⟩
              exact Or.inl ⟨k, mem_births.2 ⟨hk, hop, a, b, he,
                nonemp a (by simp [he]), nonemp b (by simp [he])⟩, hone⟩
      · obtain ⟨a, ha, _, ht'⟩ := (val_or (by simp) hk.1 hop).1 ht
        rcases sub a ha ht' with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl ((support_or rb hk.1 hop u).2 ⟨a, ha, h⟩))
        · exact Or.inr (Or.inr ((support_or rb hk.1 hop v).2 ⟨a, ha, h⟩))

lemma birth_star {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)}
    (hm : Monotone2 C) (rb : ReadsBack n C)
    (hsafe : ∀ k, reachable n C k → (gateAt C k).op = GateOp.and →
      ∀ u v, gateVal n C k (pairInput u v) = true → G.Adj u v)
    (hcommon : ∀ c d v w : Fin n, c ≠ d → v ≠ w →
      G.Adj c v → G.Adj c w → G.Adj d v → G.Adj d w → False)
    {k : ℕ} (hk : k ∈ births n C) :
    ∃ (c : Fin n) (w : ℕ), w ∈ (gateAt C k).inputs ∧
      (∀ v ∈ singletonSupport n C w, G.Adj c v) ∧
      ∀ u v : Fin n, (∀ a ∈ (gateAt C k).inputs,
        u ∈ singletonSupport n C a ∨ v ∈ singletonSupport n C a) →
        (u = c ∧ v ∈ singletonSupport n C w) ∨ (v = c ∧ u ∈ singletonSupport n C w) := by
  obtain ⟨hr, hop, a, b, hab, ha, hb⟩ := mem_births.1 hk
  have hex := crossing hm rb hsafe hr hop hab
  have hsmall : (singletonSupport n C a).card ≤ 1 ∨ (singletonSupport n C b).card ≤ 1 := by
    by_contra! h
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.1 h.1
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 h.2
    exact hcommon u v x y huv hxy (hex u hu x hx) (hex u hu y hy) (hex v hv x hx) (hex v hv y hy)
  have star (s w : ℕ) (hs : (singletonSupport n C s).Nonempty)
      (hcard : (singletonSupport n C s).card ≤ 1)
      (hsin : s ∈ (gateAt C k).inputs) (hwin : w ∈ (gateAt C k).inputs)
      (hcross : ∀ u ∈ singletonSupport n C s, ∀ v ∈ singletonSupport n C w, G.Adj u v) :
      ∃ (c : Fin n) (w : ℕ), w ∈ (gateAt C k).inputs ∧
        (∀ v ∈ singletonSupport n C w, G.Adj c v) ∧
        ∀ u v : Fin n, (∀ a ∈ (gateAt C k).inputs,
          u ∈ singletonSupport n C a ∨ v ∈ singletonSupport n C a) →
          (u = c ∧ v ∈ singletonSupport n C w) ∨ (v = c ∧ u ∈ singletonSupport n C w) := by
    obtain ⟨c, hc⟩ := hs
    have heq : ∀ t ∈ singletonSupport n C s, t = c :=
      fun t ht => Finset.card_le_one.1 hcard t ht c hc
    refine ⟨c, w, hwin, hcross c hc, ?_⟩
    intro u v h
    rcases h s hsin with hu | hv
    · left
      refine ⟨heq u hu, (h w hwin).resolve_left fun hw => ?_⟩
      exact G.irrefl (hcross u hu u hw)
    · right
      refine ⟨heq v hv, (h w hwin).resolve_right fun hw => ?_⟩
      exact G.irrefl (hcross v hv v hw)
  rcases hsmall with h | h
  · exact star a b ha h (by simp [hab]) (by simp [hab]) hex
  · exact star b a hb h (by simp [hab]) (by simp [hab]) (fun u hu v hv => (hex v hv u hu).symm)

def edgeKey {n : ℕ} (c v : Fin n) : Fin n × Fin n := (min c v, max c v)

lemma edgeKey_comm {n : ℕ} (c v : Fin n) : edgeKey c v = edgeKey v c := by
  simp only [edgeKey, min_comm c v, max_comm c v]

lemma graph_budget {n : ℕ} {C : Circuit} (G : SimpleGraph (Fin n)) (seed : Fin n)
    (hm : Monotone2 C) (rb : ReadsBack n C)
    (hsafe : ∀ k, reachable n C k → (gateAt C k).op = GateOp.and →
      ∀ u v, gateVal n C k (pairInput u v) = true → G.Adj u v)
    (hempty : ∀ k, reachable n C k → (gateAt C k).op = GateOp.and →
      gateVal n C k (fun _ => false) = false)
    (hcommon : ∀ c d v w : Fin n, c ≠ d → v ≠ w →
      G.Adj c v → G.Adj c w → G.Adj d v → G.Adj d w → False)
    (hout : singletonSupport n C C.output = ∅)
    (hpair : ∀ u v, G.Adj u v → C.eval (List.ofFn (pairInput u v)) = true)
    (E : Finset (Fin n × Fin n))
    (hE : ∀ p ∈ E, G.Adj p.1 p.2 ∧ p.1 ≤ p.2) :
    ∃ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
      T.card ≤ (births n C).card ∧ E.card + (births n C).card ≤ C.size + 1 := by
  classical
  have hclean (k) (hk : reachable n C k) (hop : (gateAt C k).op = GateOp.and) :
      singletonSupport n C (n + k) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.2
    intro u hu
    exact G.irrefl (hsafe k hk hop u u (mem_support.1 hu))
  let B := births n C
  let star (k : ℕ) (hk : k ∈ B) := birth_star hm rb hsafe hcommon hk
  let c (k : ℕ) := if hk : k ∈ B then (star k hk).choose else seed
  let w (k : ℕ) := if hk : k ∈ B then (star k hk).choose_spec.choose else 0
  have choose_spec (k) (hk : k ∈ B) :
    w k ∈ (gateAt C k).inputs ∧
      (∀ v ∈ singletonSupport n C (w k), G.Adj (c k) v) ∧
      ∀ u v : Fin n, (∀ a ∈ (gateAt C k).inputs,
        u ∈ singletonSupport n C a ∨ v ∈ singletonSupport n C a) →
        (u = c k ∧ v ∈ singletonSupport n C (w k)) ∨ (v = c k ∧ u ∈ singletonSupport n C (w k)) := by
    simpa only [c, w, dite_eq_left hk] using (star k hk).choose_spec.choose_spec
  have cover (u v) (huv : G.Adj u v) :
      ∃ k ∈ B, (u = c k ∧ v ∈ singletonSupport n C (w k)) ∨
        (v = c k ∧ u ∈ singletonSupport n C (w k)) := by
    have hv := hpair u v huv
    rw [eval_eq_val] at hv
    have hl : C.output < n + C.gates.length := by
      by_contra! hh
      rw [val_ge (by simp : (List.ofFn (pairInput u v)).length = n) hh] at hv
      cases hv
    have hn : n ≤ C.output := by
      by_contra! hh
      have he := support_input (C := C) (⟨C.output, hh⟩ : Fin n)
      rw [hout] at he
      exact (Finset.singleton_nonempty _).ne_empty he.symm
    have hr : reachable n C (C.output - n) := ⟨by omega, Or.inl (by omega)⟩
    rcases birth_route hm rb hclean hempty u v C.output (Or.inr hr) hv with h | h
    · obtain ⟨k, hk, ha⟩ := h
      exact ⟨k, hk, (choose_spec k hk).2.2 u v ha⟩
    · simp [hout] at h
  let T := B.image c
  let fiber (u : Fin n) := B.filter fun k => c k = u
  let roots (u : Fin n) := (fiber u).image w
  let leaves (u : Fin n) := (roots u).biUnion (singletonSupport n C)
  have hcov : ∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T := by
    intro u v huv
    obtain ⟨k, hk, ⟨rfl, _⟩ | ⟨rfl, _⟩⟩ := cover u v huv
    · exact Or.inl (Finset.mem_image_of_mem c hk)
    · exact Or.inr (Finset.mem_image_of_mem c hk)
  have hEsub : E ⊆ T.biUnion (fun t => (leaves t).image (edgeKey t)) := by
    rintro ⟨u, v⟩ hp
    obtain ⟨huv, huv'⟩ := hE _ hp
    obtain ⟨k, hk, h⟩ := cover u v huv
    have hroot : w k ∈ roots (c k) := Finset.mem_image_of_mem w (Finset.mem_filter.2 ⟨hk, rfl⟩)
    refine Finset.mem_biUnion.2 ⟨c k, Finset.mem_image_of_mem c hk, ?_⟩
    have hkey : edgeKey u v = (u, v) := by simp [edgeKey, min_eq_left huv', max_eq_right huv']
    rcases h with ⟨he, h⟩ | ⟨he, h⟩
    · exact Finset.mem_image.2 ⟨v, Finset.mem_biUnion.2 ⟨w k, hroot, h⟩, by rwa [← he]⟩
    · exact Finset.mem_image.2 ⟨u, Finset.mem_biUnion.2 ⟨w k, hroot, h⟩, by rwa [← he, edgeKey_comm]⟩
  have hleaf (t : Fin n) : (leaves t).card ≤ (fiber t).card +
      (mergePool C G t C.gates.length).card := by
    have hr (a) (ha : a ∈ roots t) : ∃ k ∈ B, c k = t ∧ w k = a := by
      obtain ⟨k, hk, he⟩ := Finset.mem_image.1 ha
      exact ⟨k, (Finset.mem_filter.1 hk).1, (Finset.mem_filter.1 hk).2, he⟩
    have h := leaf_budget (G := G) (c := t) hm rb hclean C.gates.length (roots t) (by
      intro a ha
      obtain ⟨k, hk, _, rfl⟩ := hr a ha
      by_cases hn : w k < n
      · exact Or.inl hn
      · apply Or.inr
        exact reachable_child rb (mem_births.1 hk).1 (by
          rw [show n + (w k - n) = w k by omega]
          exact (choose_spec k hk).1)) (by
      intro a ha v hv
      obtain ⟨k, hk, rfl, rfl⟩ := hr a ha
      exact (choose_spec k hk).2.1 v hv) (by
      intro a ha _
      obtain ⟨k, hk, _, rfl⟩ := hr a ha
      have hk' := (mem_births.1 hk).1.1
      have := rb k hk' (w k) (choose_spec k hk).1
      omega)
    exact h.trans (Nat.add_le_add_right Finset.card_image_le _)
  have hdisjFib : (T : Set (Fin n)).PairwiseDisjoint fiber := by
    intro a _ b _ hab
    rw [Function.onFun, Finset.disjoint_left]
    intro k hka hkb
    exact hab ((Finset.mem_filter.1 hka).2.symm.trans (Finset.mem_filter.1 hkb).2)
  have hsumB : (∑ t ∈ T, (fiber t).card) = B.card := by
    rw [← Finset.card_biUnion hdisjFib]
    congr 1
    ext k
    constructor
    · intro hk
      obtain ⟨_, _, hf⟩ := Finset.mem_biUnion.1 hk
      exact (Finset.mem_filter.1 hf).1
    · intro hk
      exact Finset.mem_biUnion.2 ⟨c k, Finset.mem_image_of_mem c hk, Finset.mem_filter.2 ⟨hk, rfl⟩⟩
  have hdisjPool : (T : Set (Fin n)).PairwiseDisjoint (fun t => mergePool C G t C.gates.length) := by
    intro a _ b _ hab
    rw [Function.onFun, Finset.disjoint_left]
    intro k hka hkb
    obtain ⟨_, hk, ha⟩ := mem_mergePool.1 hka
    have hb := (mem_mergePool.1 hkb).2.2
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.1 (mem_merges.1 hk).2.2.1
    exact hcommon a b u v hab huv (ha u hu) (ha v hv) (hb u hu) (hb v hv)
  have hsumL : (∑ t ∈ T, (mergePool C G t C.gates.length).card) ≤ (merges n C).card := by
    rw [← Finset.card_biUnion hdisjPool]
    apply Finset.card_le_card
    intro k hk
    obtain ⟨t, _, ht⟩ := Finset.mem_biUnion.1 hk
    exact (mem_mergePool.1 ht).2.1
  have hEL : E.card ≤ B.card + (merges n C).card := by
    calc
      _ ≤ (T.biUnion fun t => (leaves t).image (edgeKey t)).card := Finset.card_le_card hEsub
      _ ≤ ∑ t ∈ T, ((leaves t).image (edgeKey t)).card := Finset.card_biUnion_le
      _ ≤ ∑ t ∈ T, (leaves t).card := Finset.sum_le_sum fun _ _ => Finset.card_image_le
      _ ≤ ∑ t ∈ T, ((fiber t).card + (mergePool C G t C.gates.length).card) :=
        Finset.sum_le_sum fun t _ => hleaf t
      _ ≤ _ := by rw [Finset.sum_add_distrib, hsumB]; exact Nat.add_le_add_left hsumL _
  have hgate := gate_budget hm rb hclean
  change 2 * B.card + (merges n C).card ≤ C.size + 1 at hgate
  exact ⟨T, hcov, Finset.card_image_le, by change E.card + B.card ≤ C.size + 1; omega⟩

private lemma no_four_cycle {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hNoC4 : NoFourCycle G) {a b w1 w2 : Fin n} (hab : a ≠ b) (hw : w1 ≠ w2)
    (haw1 : G.Adj a w1) (haw2 : G.Adj a w2) (hbw1 : G.Adj b w1) (hbw2 : G.Adj b w2) : False := by
  have hle : (Finset.univ.filter fun w => G.Adj a w ∧ G.Adj b w).card ≤ 1 := hNoC4 a b hab
  have h1 : w1 ∈ Finset.univ.filter fun w => G.Adj a w ∧ G.Adj b w := by
    simp [haw1, hbw1]
  have h2 : w2 ∈ Finset.univ.filter fun w => G.Adj a w ∧ G.Adj b w := by
    simp [haw2, hbw2]
  have hgt : 1 < (Finset.univ.filter fun w => G.Adj a w ∧ G.Adj b w).card :=
    Finset.one_lt_card.mpr ⟨w1, h1, w2, h2, hw⟩
  omega

private def edgeTrue {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) : Prop :=
  ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true

private lemma graph_true {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {x : Fin n → Bool} : graphFun G ∅ x = true ↔ edgeTrue G x := by
  simp [graphFun, edgeTrue]

private lemma edge_true_pair {n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n} :
    edgeTrue G (pairInput u v) ↔ G.Adj u v := by
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    simp only [pairInput, decide_eq_true_eq] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro h
    exact ⟨u, v, h, by simp [pairInput], by simp [pairInput]⟩

private lemma sorted_edges {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ∃ E : Finset (Fin n × Fin n), E.card = G.edgeFinset.card ∧
      ∀ p ∈ E, G.Adj p.1 p.2 ∧ p.1 ≤ p.2 := by
  let E := Finset.univ.filter fun p : Fin n × Fin n => G.Adj p.1 p.2 ∧ p.1 ≤ p.2
  refine ⟨E, ?_, fun p hp => (Finset.mem_filter.1 hp).2⟩
  apply Finset.card_bij (fun p _ => s(p.1, p.2))
  · exact fun p hp => SimpleGraph.mem_edgeFinset.2 (Finset.mem_filter.1 hp).2.1
  · intro a ha b hb hab
    rcases Sym2.eq_iff.1 hab with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Prod.ext h₁ h₂
    · have hle₁ := (Finset.mem_filter.1 ha).2.2
      have hle₂ := (Finset.mem_filter.1 hb).2.2
      have he : b.1 = b.2 := le_antisymm hle₂ (by rwa [h₁, h₂] at hle₁)
      exact Prod.ext (h₁.trans he.symm) (h₂.trans he)
  · intro e he
    induction e using Sym2.ind with
    | _ u v =>
      have h := SimpleGraph.mem_edgeFinset.1 he
      rcases le_total u v with huv | hvu
      · exact ⟨(u, v), Finset.mem_filter.2 ⟨Finset.mem_univ _, h, huv⟩, rfl⟩
      · exact ⟨(v, u), Finset.mem_filter.2 ⟨Finset.mem_univ _, h.symm, hvu⟩, Sym2.eq_swap⟩

lemma all_clean_budget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (seed : Fin n) (hfour : NoFourCycle G)
    (hC : IsAO2 n C) (hc : circuitFun n C = graphFun G ∅)
    (hclean : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → BelowF G C j) :
    ∃ T : Finset (Fin n), G.IsVertexCover ↑T ∧
      G.edgeFinset.card + T.card ≤ C.size + 1 := by
  classical
  have hm : Monotone2 C := by
    intro g hg
    exact ⟨by simpa using hC.1 g hg, (hC.2.2 g hg).le⟩
  obtain ⟨E, hcard, hE⟩ := sorted_edges G
  obtain ⟨T, hcover, hT, hbound⟩ := graph_budget (C := C) G seed hm hC.2.1
    (fun j hj hop a b ht => edge_true_pair.1 (graph_true.1 (hclean j hj.1 hop _ ht)))
    (by
      intro j hj hop
      cases h : gateVal n C j (fun _ => false)
      · rfl
      · obtain ⟨a, b, hab, ha, hb⟩ := graph_true.1 (hclean j hj.1 hop _ h)
        cases ha)
    (fun _ _ _ _ => no_four_cycle hfour)
    (by
      apply Finset.eq_empty_iff_forall_notMem.2
      intro a ha
      have hh : circuitFun n C (pairInput a a) = true := mem_support.1 ha
      rw [hc] at hh
      exact G.irrefl (edge_true_pair.1 (graph_true.1 hh)))
    (by
      intro u v huv
      change circuitFun n C (pairInput u v) = true
      rw [hc]
      exact graph_true.2 (edge_true_pair.2 huv)) E hE
  refine ⟨T, hcover, ?_⟩
  omega

end PEqualNP.Outside.L_meta_2056_aux.TwoDirty.AllCleanBudget

namespace PEqualNP.Outside.L_meta_2056_aux.TwoDirty.SingletonReduction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Core PEqualNP.SplitCount PEqualNP.ReadTwo

lemma foldl_wires_len (gs : List Gate) (acc : List Bool) :
    (gs.foldl (fun w gt => w ++ [gt.op.eval (gt.inputs.map fun i => w.getD i false)]) acc).length =
      acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons gt rest ih =>
    simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_wires_getD_lt (gs : List Gate) (acc : List Bool) (i : ℕ) (hi : i < acc.length) :
    (gs.foldl (fun w gt => w ++ [gt.op.eval (gt.inputs.map fun idx => w.getD idx false)]) acc).getD i false =
      acc.getD i false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons gt rest ih =>
    simp only [List.foldl_cons]
    have hlt : i < (acc ++ [gt.op.eval (gt.inputs.map fun idx => acc.getD idx false)]).length := by
      simp only [List.length_append, List.length_singleton]
      omega
    rw [ih _ hlt]
    simp [List.getD, List.getElem?_append_left hi]

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  unfold Circuit.wires
  exact foldl_wires_len C.gates x

lemma wval_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    wval C x i = x ⟨i, hi⟩ := by
  unfold wval Circuit.wires
  have hlen : i < (List.ofFn x).length := by simpa using hi
  rw [foldl_wires_getD_lt C.gates (List.ofFn x) i hlen]
  simp [List.getD, hi]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j ∈ C.gates := by
  unfold gateAt
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

lemma gate_inputs_eq {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
  have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 (gateAt C j) (gateAt_mem hj)
  unfold opnd
  cases hl : (gateAt C j).inputs with
  | nil => simp [hl] at hlen
  | cons a l =>
    cases l with
    | nil => simp [hl] at hlen
    | cons b l' =>
      cases l' with
      | nil => simp [hl]
      | cons c l'' => simp [hl] at hlen

lemma opnd_mem {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b ∈ (gateAt C j).inputs := by
  rw [gate_inputs_eq hAO hj]
  fin_cases b <;> simp

lemma opnd_lt {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b < n + j :=
  hAO.2.1 j hj (opnd C j b) (opnd_mem hAO hj b)

lemma wval_gate_eval {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) :
    wval C x (n + j) = (gateAt C j).op.eval [wval C x (opnd C j 0), wval C x (opnd C j 1)] := by
  unfold wval Circuit.wires
  have hsplit : C.gates = C.gates.take j ++ gateAt C j :: C.gates.drop (j + 1) := by
    have hg : gateAt C j = C.gates[j] := by
      unfold gateAt
      exact List.getD_eq_getElem _ _ hj
    rw [hg]
    simpa using (List.take_append_drop j C.gates).symm.trans (by
      congr 1
      exact (List.cons_getElem_drop_succ (h := hj)).symm)
  set step : List Bool → Gate → List Bool :=
    fun w gt => w ++ [gt.op.eval (gt.inputs.map fun i => w.getD i false)]
  set pre := (C.gates.take j).foldl step (List.ofFn x)
  have hpre_len : pre.length = n + j := by
    have h1 := foldl_wires_len (C.gates.take j) (List.ofFn x)
    simp only [List.length_ofFn, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)] at h1
    exact h1
  have h_eq : C.gates.foldl step (List.ofFn x) =
      (C.gates.drop (j + 1)).foldl step (step pre (gateAt C j)) := by
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have h_pre_get : ∀ i < n + j, (C.gates.foldl step (List.ofFn x)).getD i false = pre.getD i false := by
    intro i hi
    rw [h_eq]
    have hi1 : i < (step pre (gateAt C j)).length := by
      simp only [step, List.length_append, List.length_singleton, hpre_len]
      omega
    rw [foldl_wires_getD_lt _ _ i hi1]
    simp only [step]
    have hi2 : i < pre.length := by omega
    simp [List.getD, List.getElem?_append_left hi2]
  have h_nj : (C.gates.foldl step (List.ofFn x)).getD (n + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => pre.getD i false) := by
    rw [h_eq]
    have hlt : n + j < (step pre (gateAt C j)).length := by
      simp only [step, List.length_append, List.length_singleton, hpre_len]
      omega
    rw [foldl_wires_getD_lt _ _ (n + j) hlt]
    simp only [step]
    have hle : pre.length ≤ n + j := by omega
    simp [List.getD, List.getElem?_append_right hle, hpre_len]
  rw [h_nj, gate_inputs_eq hAO hj]
  have h0 := h_pre_get (opnd C j 0) (opnd_lt hAO hj 0)
  have h1 := h_pre_get (opnd C j 1) (opnd_lt hAO hj 1)
  simp only [List.map_cons, List.map_nil, ← h0, ← h1]

lemma wval_gate_and {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) :
    wval C x (n + j) = (wval C x (opnd C j 0) && wval C x (opnd C j 1)) := by
  rw [wval_gate_eval hAO x hj, hop]
  simp [GateOp.eval]

lemma wval_gate_or {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) :
    wval C x (n + j) = (wval C x (opnd C j 0) || wval C x (opnd C j 1)) := by
  rw [wval_gate_eval hAO x hj, hop]
  simp [GateOp.eval]

lemma wval_ge_len {n : ℕ} (C : Circuit) (x : Fin n → Bool) {w : ℕ} (hw : n + C.gates.length ≤ w) :
    wval C x w = false := by
  unfold wval
  have hlen : (C.wires (List.ofFn x)).length ≤ w := by
    rw [wires_length, List.length_ofFn]
    exact hw
  exact List.getD_eq_default _ _ hlen

lemma wval_allTrue {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) :
    ∀ w < n + C.gates.length, wval C (fun _ : Fin n => true) w = true := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw
    by_cases hlt : w < n
    · rw [wval_input C _ w hlt]
    · have hj : w - n < C.gates.length := by omega
      have hwn : w = n + (w - n) := by omega
      rw [hwn]
      have h0 : opnd C (w - n) 0 < w := by
        have := opnd_lt hAO hj 0
        omega
      have h1 : opnd C (w - n) 1 < w := by
        have := opnd_lt hAO hj 1
        omega
      have hv0 := ih (opnd C (w - n) 0) h0 (by omega)
      have hv1 := ih (opnd C (w - n) 1) h1 (by omega)
      rcases hAO.1 (gateAt C (w - n)) (gateAt_mem hj) with hop | hop
      · rw [wval_gate_and hAO _ hj hop, hv0, hv1]; rfl
      · rw [wval_gate_or hAO _ hj hop, hv0, hv1]; rfl

lemma wval_mono {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {x y : Fin n → Bool}
    (hxy : ∀ i : Fin n, x i = true → y i = true) :
    ∀ w, wval C x w = true → wval C y w = true := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hx
    by_cases hlt : w < n
    · rw [wval_input C x w hlt] at hx
      rw [wval_input C y w hlt]
      exact hxy ⟨w, hlt⟩ hx
    · by_cases hw : w < n + C.gates.length
      · have hj : w - n < C.gates.length := by omega
        have hwn : w = n + (w - n) := by omega
        rw [hwn] at hx ⊢
        have h0 : opnd C (w - n) 0 < w := by
          have := opnd_lt hAO hj 0
          omega
        have h1 : opnd C (w - n) 1 < w := by
          have := opnd_lt hAO hj 1
          omega
        rcases hAO.1 (gateAt C (w - n)) (gateAt_mem hj) with hop | hop
        · rw [wval_gate_and hAO x hj hop, Bool.and_eq_true] at hx
          rw [wval_gate_and hAO y hj hop, Bool.and_eq_true]
          exact ⟨ih _ h0 hx.1, ih _ h1 hx.2⟩
        · rw [wval_gate_or hAO x hj hop, Bool.or_eq_true] at hx
          rw [wval_gate_or hAO y hj hop, Bool.or_eq_true]
          exact hx.elim (fun h => Or.inl (ih _ h0 h)) (fun h => Or.inr (ih _ h1 h))
      · rw [wval_ge_len C x (by omega)] at hx
        cases hx

lemma foldl_cones_len (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) :
    (gs.foldl (coneStep n) acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons gt rest ih =>
    simp only [List.foldl_cons, ih, coneStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_cones_getD_lt (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) (i : ℕ) (hi : i < acc.length) :
    (gs.foldl (coneStep n) acc).getD i [] = acc.getD i [] := by
  induction gs generalizing acc with
  | nil => rfl
  | cons gt rest ih =>
    simp only [List.foldl_cons]
    have hlt : i < (coneStep n acc gt).length := by
      simp only [coneStep, List.length_append, List.length_singleton]
      omega
    rw [ih _ hlt]
    simp [coneStep, List.getD, List.getElem?_append_left hi]

lemma cones_length (n : ℕ) (C : Circuit) : (cones n C).length = C.gates.length := by
  unfold cones
  simpa using foldl_cones_len n C.gates []

lemma inCone_lt_len {n : ℕ} {C : Circuit} {i j : ℕ} (h : InCone n C i j) : j < C.gates.length := by
  unfold InCone at h
  by_contra hge
  have hle : (cones n C).length ≤ j := by rw [cones_length]; omega
  rw [List.getD_eq_default _ _ hle] at h
  simp at h

lemma inCone_iff {n : ℕ} {C : Circuit} {i j : ℕ} (hj : j < C.gates.length) :
    InCone n C i j ↔
      ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ w < n + j ∧ (i = w - n ∨ InCone n C i (w - n)) := by
  unfold InCone cones
  have hsplit : C.gates = C.gates.take j ++ gateAt C j :: C.gates.drop (j + 1) := by
    have hg : gateAt C j = C.gates[j] := by
      unfold gateAt
      exact List.getD_eq_getElem _ _ hj
    rw [hg]
    simpa using (List.take_append_drop j C.gates).symm.trans (by
      congr 1
      exact (List.cons_getElem_drop_succ (h := hj)).symm)
  set pre := (C.gates.take j).foldl (coneStep n) []
  have hpre_len : pre.length = j := by
    have h1 := foldl_cones_len n (C.gates.take j) []
    simp only [List.length_nil, Nat.zero_add, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)] at h1
    exact h1
  have h_eq : C.gates.foldl (coneStep n) [] =
      (C.gates.drop (j + 1)).foldl (coneStep n) (coneStep n pre (gateAt C j)) := by
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have h_pre_get : ∀ k < j, (C.gates.foldl (coneStep n) []).getD k [] = pre.getD k [] := by
    intro k hk
    rw [h_eq]
    have hk1 : k < (coneStep n pre (gateAt C j)).length := by
      simp only [coneStep, List.length_append, List.length_singleton, hpre_len]
      omega
    rw [foldl_cones_getD_lt _ _ _ k hk1]
    have hk2 : k < pre.length := by omega
    simp [coneStep, List.getD, List.getElem?_append_left hk2]
  have h_j : (C.gates.foldl (coneStep n) []).getD j [] =
      ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
        (fun w => (w - n) :: pre.getD (w - n) []) := by
    rw [h_eq]
    have hlt : j < (coneStep n pre (gateAt C j)).length := by
      simp only [coneStep, List.length_append, List.length_singleton, hpre_len]
      omega
    rw [foldl_cones_getD_lt _ _ _ j hlt]
    have hle : pre.length ≤ j := by omega
    simp [coneStep, List.getD, List.getElem?_append_right hle, hpre_len]
  rw [h_j]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hwm, hwn, hwlt⟩, hmem⟩
    refine ⟨w, hwm, hwn, hwlt, ?_⟩
    rcases hmem with rfl | hmem
    · exact Or.inl rfl
    · right
      rw [← h_pre_get (w - n) (by omega)] at hmem
      exact hmem
  · rintro ⟨w, hwm, hwn, hwlt, hmem⟩
    refine ⟨w, ⟨hwm, hwn, hwlt⟩, ?_⟩
    rcases hmem with rfl | hmem
    · exact Or.inl rfl
    · right
      rw [h_pre_get (w - n) (by omega)] at hmem
      exact hmem

lemma inCone_lt {n : ℕ} {C : Circuit} {i j : ℕ} : InCone n C i j → i < j := by
  induction j using Nat.strongRecOn with
  | ind j ih =>
    intro h
    have hj : j < C.gates.length := inCone_lt_len h
    rw [inCone_iff hj] at h
    rcases h with ⟨w, _, hwn, hwlt, rfl | hsub⟩
    · omega
    · have h1 := ih (w - n) (by omega) hsub
      omega

lemma graphFun_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
  simp [graphFun]

lemma graphFun_unitInput_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) :
    graphFun G ∅ (unitInput v) = false := by
  cases hf : graphFun G ∅ (unitInput v) with
  | false => rfl
  | true =>
    rw [graphFun_iff] at hf
    rcases hf with ⟨u, w, hadj, hu, hw⟩
    simp only [unitInput, decide_eq_true_eq] at hu hw
    subst hu; subst hw
    exact (G.ne_of_adj hadj rfl).elim

lemma graphFun_pairInput_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  rw [graphFun_iff]
  constructor
  · rintro ⟨a, b, hadj, ha, hb⟩
    simp only [pairInput, decide_eq_true_eq] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.ne_of_adj hadj rfl).elim
    · exact hadj
    · exact hadj.symm
    · exact (G.ne_of_adj hadj rfl).elim
  · intro hadj
    exact ⟨u, v, hadj, by simp [pairInput], by simp [pairInput]⟩

def tripleInput {n : ℕ} (u w z : Fin n) : Fin n → Bool :=
  fun t => decide (t = u ∨ t = w ∨ t = z)

lemma graphFun_tripleInput_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u w z : Fin n) :
    graphFun G ∅ (tripleInput u w z) = true ↔ G.Adj u w ∨ G.Adj u z ∨ G.Adj w z := by
  rw [graphFun_iff]
  constructor
  · rintro ⟨a, b, hadj, ha, hb⟩
    simp only [tripleInput, decide_eq_true_eq] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    · exact (G.ne_of_adj hadj rfl).elim
    · exact Or.inl hadj
    · exact Or.inr (Or.inl hadj)
    · exact Or.inl hadj.symm
    · exact (G.ne_of_adj hadj rfl).elim
    · exact Or.inr (Or.inr hadj)
    · exact Or.inr (Or.inl hadj.symm)
    · exact Or.inr (Or.inr hadj.symm)
    · exact (G.ne_of_adj hadj rfl).elim
  · rintro (h | h | h)
    · exact ⟨u, w, h, by simp [tripleInput], by simp [tripleInput]⟩
    · exact ⟨u, z, h, by simp [tripleInput], by simp [tripleInput]⟩
    · exact ⟨w, z, h, by simp [tripleInput], by simp [tripleInput]⟩

lemma noFourCycle_unique {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hC4 : NoFourCycle G) {a b z1 z2 : Fin n} (hab : a ≠ b)
    (ha1 : G.Adj a z1) (hb1 : G.Adj b z1) (ha2 : G.Adj a z2) (hb2 : G.Adj b z2) :
    z1 = z2 := by
  have hcard := hC4 a b hab
  have h1 : z1 ∈ Finset.univ.filter (fun w => G.Adj a w ∧ G.Adj b w) := by
    simp [ha1, hb1]
  have h2 : z2 ∈ Finset.univ.filter (fun w => G.Adj a w ∧ G.Adj b w) := by
    simp [ha2, hb2]
  exact Finset.card_le_one.mp hcard z1 h1 z2 h2

lemma circuitFun_eq_graphFun_of {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {D : Circuit} (hAO : IsAO2 n D)
    (hle : ∀ x : Fin n → Bool, circuitFun n D x = true → graphFun G ∅ x = true)
    (hge : ∀ u v : Fin n, G.Adj u v → circuitFun n D (pairInput u v) = true) :
    circuitFun n D = graphFun G ∅ := by
  funext x
  cases hD : circuitFun n D x with
  | true =>
    exact (hle x hD).symm
  | false =>
    cases hF : graphFun G ∅ x with
    | false => rfl
    | true =>
      rw [graphFun_iff] at hF
      rcases hF with ⟨u, v, hadj, hu, hv⟩
      have hp : circuitFun n D (pairInput u v) = true := hge u v hadj
      have hmono : circuitFun n D x = true := wval_mono hAO (fun i hi => by
        simp only [pairInput, decide_eq_true_eq] at hi
        rcases hi with rfl | rfl <;> assumption) D.output hp
      rw [hD] at hmono
      cases hmono

def WireBelowF {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (w : ℕ) : Prop :=
  ∀ x : Fin n → Bool, wval C x w = true → graphFun G ∅ x = true

lemma not_wireBelowF_input {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    {w : ℕ} (hw : w < n) : ¬ WireBelowF G C w := by
  intro h
  have h1 : wval C (unitInput ⟨w, hw⟩) w = true := by
    rw [wval_input C _ w hw]
    simp [unitInput]
  have h2 := h (unitInput ⟨w, hw⟩) h1
  rw [graphFun_unitInput_false] at h2
  cases h2

lemma wireBelowF_gate_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (k : ℕ) :
    WireBelowF G C (n + k) ↔ BelowF G C k := Iff.rfl

def usesG (n : ℕ) (C : Circuit) (g : ℕ) (w : ℕ) : Bool :=
  if w < n then false
  else if w = n + g then true
  else
    let k := w - n
    if k < C.gates.length then
      if h : opnd C k 0 < w ∧ opnd C k 1 < w then
        usesG n C g (opnd C k 0) || usesG n C g (opnd C k 1)
      else false
    else false
termination_by w
decreasing_by
  · exact h.1
  · exact h.2

def varSet (n : ℕ) (C : Circuit) (g : ℕ) (w : ℕ) : Finset (Fin n) :=
  if h : w < n then {⟨w, h⟩}
  else if w = n + g then ∅
  else
    let k := w - n
    if k < C.gates.length then
      if h2 : opnd C k 0 < w ∧ opnd C k 1 < w then
        varSet n C g (opnd C k 0) ∪ varSet n C g (opnd C k 1)
      else ∅
    else ∅
termination_by w
decreasing_by
  · exact h2.1
  · exact h2.2

lemma usesG_input (n : ℕ) (C : Circuit) (g w : ℕ) (hw : w < n) :
    usesG n C g w = false := by
  rw [usesG]; simp [hw]

lemma usesG_g (n : ℕ) (C : Circuit) (g : ℕ) :
    usesG n C g (n + g) = true := by
  rw [usesG]
  have h1 : ¬ n + g < n := by omega
  simp [h1]

lemma usesG_gate {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (g k : ℕ)
    (hk : k < C.gates.length) (hkg : k ≠ g) :
    usesG n C g (n + k) = (usesG n C g (opnd C k 0) || usesG n C g (opnd C k 1)) := by
  rw [usesG]
  have h1 : ¬ n + k < n := by omega
  have h3 : n + k - n = k := by omega
  have hlt0 : opnd C k 0 < n + k := opnd_lt hAO hk 0
  have hlt1 : opnd C k 1 < n + k := opnd_lt hAO hk 1
  simp [h1, hkg, h3, hk, hlt0, hlt1]

lemma usesG_lt_g {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (g : ℕ) :
    ∀ w < n + g, usesG n C g w = false := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw
    by_cases hlt : w < n
    · exact usesG_input n C g w hlt
    · by_cases hk : w - n < C.gates.length
      · have hwn : w = n + (w - n) := by omega
        have hkg : w - n ≠ g := by omega
        rw [hwn, usesG_gate hAO g (w - n) hk hkg]
        have h0 : opnd C (w - n) 0 < w := by have := opnd_lt hAO hk 0; omega
        have h1 : opnd C (w - n) 1 < w := by have := opnd_lt hAO hk 1; omega
        rw [ih _ h0 (by omega), ih _ h1 (by omega)]
        rfl
      · rw [usesG]
        have hne : w ≠ n + g := by omega
        simp [hlt, hne, hk]

lemma varSet_input (n : ℕ) (C : Circuit) (g w : ℕ) (hw : w < n) :
    varSet n C g w = {⟨w, hw⟩} := by
  rw [varSet]; simp [hw]

lemma varSet_g (n : ℕ) (C : Circuit) (g : ℕ) :
    varSet n C g (n + g) = ∅ := by
  rw [varSet]
  have h1 : ¬ n + g < n := by omega
  simp [h1]

lemma varSet_gate {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (g k : ℕ)
    (hk : k < C.gates.length) (hkg : k ≠ g) :
    varSet n C g (n + k) = varSet n C g (opnd C k 0) ∪ varSet n C g (opnd C k 1) := by
  rw [varSet]
  have h1 : ¬ n + k < n := by omega
  have h3 : n + k - n = k := by omega
  have hlt0 : opnd C k 0 < n + k := opnd_lt hAO hk 0
  have hlt1 : opnd C k 1 < n + k := opnd_lt hAO hk 1
  simp [h1, hkg, h3, hk, hlt0, hlt1]

def zSet (n : ℕ) (C : Circuit) (g : ℕ) : Finset (Fin n) :=
  (Finset.range C.gates.length).biUnion fun a =>
    match (gateAt C a).op with
    | GateOp.and =>
      if a ≠ g then
        (if usesG n C g (opnd C a 0) = true then varSet n C g (opnd C a 1) else ∅) ∪
        (if usesG n C g (opnd C a 1) = true then varSet n C g (opnd C a 0) else ∅)
      else ∅
    | _ => ∅

def delMap (n g r w : ℕ) : ℕ :=
  if w < n + g then w
  else if w = n + g then r
  else w - 1

def delGateMap (g k : ℕ) : ℕ :=
  if k < g then k else k - 1

lemma delMap_gate (n g r k : ℕ) (hkg : k ≠ g) :
    delMap n g r (n + k) = n + delGateMap g k := by
  unfold delMap delGateMap
  split_ifs <;> omega

def delCircuit (n : ℕ) (C : Circuit) (g r : ℕ) : Circuit :=
  { gates := List.ofFn fun i : Fin (C.gates.length - 1) =>
      let src := if i.val < g then i.val else i.val + 1
      let gt := gateAt C src
      ⟨gt.op, gt.inputs.map (delMap n g r)⟩
    output := delMap n g r C.output }

lemma delCircuit_len (n : ℕ) (C : Circuit) (g r : ℕ) :
    (delCircuit n C g r).gates.length = C.gates.length - 1 := by
  simp [delCircuit]

lemma delCircuit_size (n : ℕ) (C : Circuit) (g r : ℕ) :
    (delCircuit n C g r).size ≤ C.size := by
  simp [Circuit.size, delCircuit]

lemma delCircuit_gateAt {n : ℕ} {C : Circuit} {g r i : ℕ} (hi : i < C.gates.length - 1) :
    gateAt (delCircuit n C g r) i =
      let src := if i < g then i else i + 1
      let gt := gateAt C src
      ⟨gt.op, gt.inputs.map (delMap n g r)⟩ := by
  have hlt : i < (delCircuit n C g r).gates.length := by rw [delCircuit_len]; exact hi
  conv_lhs => unfold gateAt
  rw [List.getD_eq_getElem _ _ hlt]
  simp [delCircuit]

lemma delCircuit_gateAt_src {n : ℕ} {C : Circuit} {g r k : ℕ}
    (hg : g < C.gates.length) (hk : k < C.gates.length) (hkg : k ≠ g) :
    gateAt (delCircuit n C g r) (delGateMap g k) =
      ⟨(gateAt C k).op, (gateAt C k).inputs.map (delMap n g r)⟩ := by
  have hi : delGateMap g k < C.gates.length - 1 := by
    unfold delGateMap; split_ifs <;> omega
  rw [delCircuit_gateAt hi]
  have hsrc : (if delGateMap g k < g then delGateMap g k else delGateMap g k + 1) = k := by
    unfold delGateMap; split_ifs <;> omega
  simp [hsrc]

lemma delCircuit_isAO2 {n : ℕ} {C : Circuit} {g r : ℕ}
    (hAO : IsAO2 n C) (hg : g < C.gates.length) (hr : r < n + g) :
    IsAO2 n (delCircuit n C g r) := by
  refine ⟨?_, ?_, ?_⟩
  · intro gt hgt
    simp only [delCircuit, List.mem_ofFn] at hgt
    rcases hgt with ⟨i, rfl⟩
    have hsrc : (if i.val < g then i.val else i.val + 1) < C.gates.length := by
      split_ifs <;> omega
    exact hAO.1 (gateAt C (if i.val < g then i.val else i.val + 1)) (gateAt_mem hsrc)
  · intro i hi w hw
    rw [delCircuit_len] at hi
    rw [delCircuit_gateAt hi] at hw
    simp only [List.mem_map] at hw
    rcases hw with ⟨u, hu, rfl⟩
    by_cases hig : i < g
    · simp only [hig, ↓reduceIte] at hu
      have hult : u < n + i := hAO.2.1 i (by omega) u hu
      unfold delMap
      split_ifs <;> omega
    · simp only [hig, ↓reduceIte] at hu
      have hult : u < n + (i + 1) := hAO.2.1 (i + 1) (by omega) u hu
      unfold delMap
      split_ifs <;> omega
  · intro gt hgt
    simp only [delCircuit, List.mem_ofFn] at hgt
    rcases hgt with ⟨i, rfl⟩
    have hsrc : (if i.val < g then i.val else i.val + 1) < C.gates.length := by
      split_ifs <;> omega
    simp [hAO.2.2 _ (gateAt_mem hsrc)]

lemma delCircuit_opnd {n : ℕ} {C : Circuit} {g r k : ℕ}
    (hAO : IsAO2 n C) (hg : g < C.gates.length) (hk : k < C.gates.length) (hkg : k ≠ g) (b : Fin 2) :
    opnd (delCircuit n C g r) (delGateMap g k) b = delMap n g r (opnd C k b) := by
  unfold opnd
  rw [delCircuit_gateAt_src hg hk hkg, gate_inputs_eq hAO hk]
  fin_cases b <;> simp [opnd]

lemma delCircuit_wval_lt {n : ℕ} {C : Circuit} {g r : ℕ}
    (hAO : IsAO2 n C) (hg : g < C.gates.length) (hr : r < n + g) (x : Fin n → Bool) :
    ∀ w < n + g, wval (delCircuit n C g r) x w = wval C x w := by
  have hAO' := delCircuit_isAO2 hAO hg hr
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw
    by_cases hlt : w < n
    · rw [wval_input _ x w hlt, wval_input _ x w hlt]
    · have hk : w - n < g := by omega
      have hklt : w - n < C.gates.length := by omega
      have hkg : w - n ≠ g := by omega
      have hwn : w = n + (w - n) := by omega
      have hdgm : delGateMap g (w - n) = w - n := by simp [delGateMap, hk]
      have hk' : w - n < (delCircuit n C g r).gates.length := by rw [delCircuit_len]; omega
      have h0lt : opnd C (w - n) 0 < w := by have := opnd_lt hAO hklt 0; omega
      have h1lt : opnd C (w - n) 1 < w := by have := opnd_lt hAO hklt 1; omega
      have hop0 : opnd (delCircuit n C g r) (w - n) 0 = opnd C (w - n) 0 := by
        conv_lhs => rw [← hdgm]
        rw [delCircuit_opnd hAO hg hklt hkg 0]
        unfold delMap; split_ifs <;> omega
      have hop1 : opnd (delCircuit n C g r) (w - n) 1 = opnd C (w - n) 1 := by
        conv_lhs => rw [← hdgm]
        rw [delCircuit_opnd hAO hg hklt hkg 1]
        unfold delMap; split_ifs <;> omega
      have hgate : (gateAt (delCircuit n C g r) (w - n)).op = (gateAt C (w - n)).op := by
        conv_lhs => rw [← hdgm]
        rw [delCircuit_gateAt_src hg hklt hkg]
      rw [hwn]
      rcases hAO.1 _ (gateAt_mem hklt) with hop | hop
      · rw [wval_gate_and hAO' x hk' (hgate.trans hop), wval_gate_and hAO x hklt hop,
          hop0, hop1, ih _ h0lt (by omega), ih _ h1lt (by omega)]
      · rw [wval_gate_or hAO' x hk' (hgate.trans hop), wval_gate_or hAO x hklt hop,
          hop0, hop1, ih _ h0lt (by omega), ih _ h1lt (by omega)]

lemma delCircuit_wval_le {n : ℕ} {C : Circuit} {g r : ℕ}
    (hAO : IsAO2 n C) (hg : g < C.gates.length) (hr : r < n + g) (x : Fin n → Bool)
    (hle : wval C x r = true → gateVal n C g x = true) :
    ∀ w < n + C.gates.length, wval (delCircuit n C g r) x (delMap n g r w) = true → wval C x w = true := by
  have hAO' := delCircuit_isAO2 hAO hg hr
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw hD
    by_cases hlt : w < n + g
    · have hm : delMap n g r w = w := by simp [delMap, hlt]
      rw [hm, delCircuit_wval_lt hAO hg hr x w hlt] at hD
      exact hD
    · by_cases hwg : w = n + g
      · subst hwg
        have hm : delMap n g r (n + g) = r := by simp [delMap]
        rw [hm, delCircuit_wval_lt hAO hg hr x r hr] at hD
        exact hle hD
      · have hk : w - n < C.gates.length := by omega
        have hkg : w - n ≠ g := by omega
        have hwn : w = n + (w - n) := by omega
        have hdm : delMap n g r w = n + delGateMap g (w - n) := by
          conv_lhs => rw [hwn]
          exact delMap_gate n g r (w - n) hkg
        have hk' : delGateMap g (w - n) < (delCircuit n C g r).gates.length := by
          rw [delCircuit_len]; unfold delGateMap; split_ifs <;> omega
        have h0lt : opnd C (w - n) 0 < w := by have := opnd_lt hAO hk 0; omega
        have h1lt : opnd C (w - n) 1 < w := by have := opnd_lt hAO hk 1; omega
        have hgate : (gateAt (delCircuit n C g r) (delGateMap g (w - n))).op = (gateAt C (w - n)).op := by
          rw [delCircuit_gateAt_src hg hk hkg]
        rw [hdm] at hD
        rw [hwn]
        rcases hAO.1 _ (gateAt_mem hk) with hop | hop
        · rw [wval_gate_and hAO' x hk' (hgate.trans hop), Bool.and_eq_true,
            delCircuit_opnd hAO hg hk hkg 0, delCircuit_opnd hAO hg hk hkg 1] at hD
          rw [wval_gate_and hAO x hk hop, Bool.and_eq_true]
          exact ⟨ih _ h0lt (by omega) hD.1, ih _ h1lt (by omega) hD.2⟩
        · rw [wval_gate_or hAO' x hk' (hgate.trans hop), Bool.or_eq_true,
            delCircuit_opnd hAO hg hk hkg 0, delCircuit_opnd hAO hg hk hkg 1] at hD
          rw [wval_gate_or hAO x hk hop, Bool.or_eq_true]
          exact hD.elim (fun h => Or.inl (ih _ h0lt (by omega) h))
            (fun h => Or.inr (ih _ h1lt (by omega) h))

lemma delCircuit_wval_ge {n : ℕ} {C : Circuit} {g r : ℕ}
    (hAO : IsAO2 n C) (hg : g < C.gates.length) (hr : r < n + g) (x : Fin n → Bool)
    (hge : gateVal n C g x = true → wval C x r = true) :
    ∀ w < n + C.gates.length, wval C x w = true → wval (delCircuit n C g r) x (delMap n g r w) = true := by
  have hAO' := delCircuit_isAO2 hAO hg hr
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw hC
    by_cases hlt : w < n + g
    · have hm : delMap n g r w = w := by simp [delMap, hlt]
      rw [hm, delCircuit_wval_lt hAO hg hr x w hlt]
      exact hC
    · by_cases hwg : w = n + g
      · subst hwg
        have hm : delMap n g r (n + g) = r := by simp [delMap]
        rw [hm, delCircuit_wval_lt hAO hg hr x r hr]
        exact hge hC
      · have hk : w - n < C.gates.length := by omega
        have hkg : w - n ≠ g := by omega
        have hwn : w = n + (w - n) := by omega
        have hdm : delMap n g r w = n + delGateMap g (w - n) := by
          conv_lhs => rw [hwn]
          exact delMap_gate n g r (w - n) hkg
        have hk' : delGateMap g (w - n) < (delCircuit n C g r).gates.length := by
          rw [delCircuit_len]; unfold delGateMap; split_ifs <;> omega
        have h0lt : opnd C (w - n) 0 < w := by have := opnd_lt hAO hk 0; omega
        have h1lt : opnd C (w - n) 1 < w := by have := opnd_lt hAO hk 1; omega
        have hgate : (gateAt (delCircuit n C g r) (delGateMap g (w - n))).op = (gateAt C (w - n)).op := by
          rw [delCircuit_gateAt_src hg hk hkg]
        rw [hdm]
        rw [hwn] at hC
        rcases hAO.1 _ (gateAt_mem hk) with hop | hop
        · rw [wval_gate_and hAO x hk hop, Bool.and_eq_true] at hC
          rw [wval_gate_and hAO' x hk' (hgate.trans hop), Bool.and_eq_true,
            delCircuit_opnd hAO hg hk hkg 0, delCircuit_opnd hAO hg hk hkg 1]
          exact ⟨ih _ h0lt (by omega) hC.1, ih _ h1lt (by omega) hC.2⟩
        · rw [wval_gate_or hAO x hk hop, Bool.or_eq_true] at hC
          rw [wval_gate_or hAO' x hk' (hgate.trans hop), Bool.or_eq_true,
            delCircuit_opnd hAO hg hk hkg 0, delCircuit_opnd hAO hg hk hkg 1]
          exact hC.elim (fun h => Or.inl (ih _ h0lt (by omega) h))
            (fun h => Or.inr (ih _ h1lt (by omega) h))

def isTwoSided {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (v : Fin n) (g w : ℕ) : Prop :=
  w < n + C.gates.length ∧ ¬ WireBelowF G C w ∧
    (∃ u ∈ varSet n C g w, s u = s v) ∧ (∃ u ∈ varSet n C g w, s u ≠ s v)

def isRSided {n : ℕ} (C : Circuit) (s : Fin n → Bool) (v : Fin n) (g w : ℕ) : Prop :=
  ∀ u ∈ varSet n C g w, s u ≠ s v

def restrictMap {n : ℕ} (C : Circuit) (s : Fin n → Bool) (v : Fin n) (g w : ℕ) : ℕ :=
  if ∀ u ∈ varSet n C g w, s u ≠ s v then v.val else w

def restrictTwoSided {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (v : Fin n) (g : ℕ) : Circuit :=
  { gates := List.ofFn fun i : Fin C.gates.length =>
      let gt := gateAt C i.val
      if ¬ BelowF G C i.val ∧ (∃ u ∈ varSet n C g (n + i.val), s u = s v) ∧
          (∃ u ∈ varSet n C g (n + i.val), s u ≠ s v) then
        ⟨gt.op, gt.inputs.map (restrictMap C s v g)⟩
      else gt
    output := C.output }

lemma restrictTwoSided_len {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (v : Fin n) (g : ℕ) :
    (restrictTwoSided G C s v g).gates.length = C.gates.length := by
  simp [restrictTwoSided]

lemma restrictTwoSided_gateAt {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (v : Fin n) (g k : ℕ) (hk : k < C.gates.length) :
    gateAt (restrictTwoSided G C s v g) k =
      if ¬ BelowF G C k ∧ (∃ u ∈ varSet n C g (n + k), s u = s v) ∧
          (∃ u ∈ varSet n C g (n + k), s u ≠ s v) then
        ⟨(gateAt C k).op, (gateAt C k).inputs.map (restrictMap C s v g)⟩
      else gateAt C k := by
  have hlt : k < (restrictTwoSided G C s v g).gates.length := by rw [restrictTwoSided_len]; exact hk
  conv_lhs => unfold gateAt
  rw [List.getD_eq_getElem _ _ hlt]
  simp [restrictTwoSided]

lemma restrictTwoSided_isAO2 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (s : Fin n → Bool) (v : Fin n) (g : ℕ) :
    IsAO2 n (restrictTwoSided G C s v g) := by
  refine ⟨?_, ?_, ?_⟩
  · intro gt hgt
    simp only [restrictTwoSided, List.mem_ofFn] at hgt
    rcases hgt with ⟨i, rfl⟩
    split_ifs
    · exact hAO.1 (gateAt C i.val) (gateAt_mem i.isLt)
    · exact hAO.1 (gateAt C i.val) (gateAt_mem i.isLt)
  · intro k hk w hw
    rw [restrictTwoSided_len] at hk
    rw [restrictTwoSided_gateAt G C s v g k hk] at hw
    split_ifs at hw with hts
    · simp only [List.mem_map] at hw
      rcases hw with ⟨u, hu, rfl⟩
      unfold restrictMap
      split_ifs
      · omega
      · exact hAO.2.1 k hk u hu
    · exact hAO.2.1 k hk w hw
  · intro gt hgt
    simp only [restrictTwoSided, List.mem_ofFn] at hgt
    rcases hgt with ⟨i, rfl⟩
    split_ifs
    · simp [hAO.2.2 _ (gateAt_mem i.isLt)]
    · exact hAO.2.2 _ (gateAt_mem i.isLt)

def remapC (n jb g w : ℕ) : ℕ :=
  if w < n + jb then w
  else if w < n + g then w - 1
  else w

def remapCGate (jb g k : ℕ) : ℕ :=
  if k < jb then k
  else if k < g then k - 1
  else k

lemma remapC_gate (n jb g k : ℕ) (hkjb : k ≠ jb) :
    remapC n jb g (n + k) = n + remapCGate jb g k := by
  unfold remapC remapCGate
  split_ifs <;> omega

def rewriteCircuit (n : ℕ) (C : Circuit) (jb g aW : ℕ) (v m : Fin n) : Circuit :=
  { gates := List.ofFn fun i : Fin C.gates.length =>
      if i.val < jb then
        gateAt C i.val
      else if i.val + 1 < g then
        let gt := gateAt C (i.val + 1)
        ⟨gt.op, gt.inputs.map (remapC n jb g)⟩
      else if i.val + 1 = g then
        ⟨GateOp.and, [remapC n jb g aW, m.val]⟩
      else if i.val = g then
        ⟨GateOp.or, [v.val, n + (g - 1)]⟩
      else
        let gt := gateAt C i.val
        ⟨gt.op, gt.inputs.map (remapC n jb g)⟩
    output := C.output }

lemma rewriteCircuit_len (n : ℕ) (C : Circuit) (jb g aW : ℕ) (v m : Fin n) :
    (rewriteCircuit n C jb g aW v m).gates.length = C.gates.length := by
  simp [rewriteCircuit]

lemma rewriteCircuit_size (n : ℕ) (C : Circuit) (jb g aW : ℕ) (v m : Fin n) :
    (rewriteCircuit n C jb g aW v m).size ≤ C.size := by
  simp [Circuit.size, rewriteCircuit]

lemma rewriteCircuit_gateAt {n : ℕ} {C : Circuit} {jb g aW i : ℕ} {v m : Fin n}
    (hi : i < C.gates.length) :
    gateAt (rewriteCircuit n C jb g aW v m) i =
      if i < jb then
        gateAt C i
      else if i + 1 < g then
        let gt := gateAt C (i + 1)
        ⟨gt.op, gt.inputs.map (remapC n jb g)⟩
      else if i + 1 = g then
        ⟨GateOp.and, [remapC n jb g aW, m.val]⟩
      else if i = g then
        ⟨GateOp.or, [v.val, n + (g - 1)]⟩
      else
        let gt := gateAt C i
        ⟨gt.op, gt.inputs.map (remapC n jb g)⟩ := by
  have hlt : i < (rewriteCircuit n C jb g aW v m).gates.length := by rw [rewriteCircuit_len]; exact hi
  conv_lhs => unfold gateAt
  rw [List.getD_eq_getElem _ _ hlt]
  simp [rewriteCircuit]

lemma rewriteCircuit_isAO2 {n : ℕ} {C : Circuit} {jb g aW : ℕ} (v m : Fin n)
    (hAO : IsAO2 n C) (hjbg : jb < g) (hg : g < C.gates.length)
    (haWlt : aW < n + g) (haWne : aW ≠ n + jb)
    (hno : ∀ k < C.gates.length, k ≠ g → n + jb ∉ (gateAt C k).inputs) :
    IsAO2 n (rewriteCircuit n C jb g aW v m) := by
  refine ⟨?_, ?_, ?_⟩
  · intro gt hgt
    simp only [rewriteCircuit, List.mem_ofFn] at hgt
    rcases hgt with ⟨i, rfl⟩
    split_ifs with h1 h2 h3 h4
    · exact hAO.1 (gateAt C i.val) (gateAt_mem i.isLt)
    · exact hAO.1 (gateAt C (i.val + 1)) (gateAt_mem (by omega))
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact hAO.1 (gateAt C i.val) (gateAt_mem i.isLt)
  · intro i hi w hw
    rw [rewriteCircuit_len] at hi
    rw [rewriteCircuit_gateAt hi] at hw
    split_ifs at hw with h1 h2 h3 h4
    · exact hAO.2.1 i hi w hw
    · simp only [List.mem_map] at hw
      rcases hw with ⟨u, hu, rfl⟩
      have hult := hAO.2.1 (i + 1) (by omega) u hu
      have hune : u ≠ n + jb := fun heq => hno (i + 1) (by omega) (by omega) (heq ▸ hu)
      unfold remapC
      split_ifs <;> omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · unfold remapC; split_ifs <;> omega
      · omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> omega
    · simp only [List.mem_map] at hw
      rcases hw with ⟨u, hu, rfl⟩
      have hult := hAO.2.1 i hi u hu
      unfold remapC
      split_ifs <;> omega
  · intro gt hgt
    simp only [rewriteCircuit, List.mem_ofFn] at hgt
    rcases hgt with ⟨i, rfl⟩
    split_ifs with h1 h2 h3 h4
    · exact hAO.2.2 (gateAt C i.val) (gateAt_mem i.isLt)
    · have hlt2 : i.val + 1 < C.gates.length := by omega
      simp [hAO.2.2 (gateAt C (i.val + 1)) (gateAt_mem hlt2)]
    · rfl
    · rfl
    · simp [hAO.2.2 (gateAt C i.val) (gateAt_mem i.isLt)]

lemma rewriteCircuit_wval_lt_g {n : ℕ} {C : Circuit} {jb g aW : ℕ} {v m : Fin n}
    (hAO : IsAO2 n C) (hjbg : jb < g) (hg : g < C.gates.length)
    (haWlt : aW < n + g) (haWne : aW ≠ n + jb)
    (hno : ∀ k < C.gates.length, k ≠ g → n + jb ∉ (gateAt C k).inputs)
    (x : Fin n → Bool) :
    ∀ w < n + g, w ≠ n + jb → wval (rewriteCircuit n C jb g aW v m) x (remapC n jb g w) = wval C x w := by
  have hAO' := rewriteCircuit_isAO2 v m hAO hjbg hg haWlt haWne hno
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw hwne
    by_cases hlt : w < n
    · have hm : remapC n jb g w = w := by unfold remapC; split_ifs <;> omega
      rw [hm, wval_input _ x w hlt, wval_input _ x w hlt]
    · have hk : w - n < g := by omega
      have hklt : w - n < C.gates.length := by omega
      have hkjb : w - n ≠ jb := by omega
      have hkg : w - n ≠ g := by omega
      have hwn : w = n + (w - n) := by omega
      have hrm : remapC n jb g w = n + remapCGate jb g (w - n) := by
        conv_lhs => rw [hwn]
        exact remapC_gate n jb g (w - n) hkjb
      have hi : remapCGate jb g (w - n) < (rewriteCircuit n C jb g aW v m).gates.length := by
        rw [rewriteCircuit_len]; unfold remapCGate; split_ifs <;> omega
      have h0lt : opnd C (w - n) 0 < w := by have := opnd_lt hAO hklt 0; omega
      have h1lt : opnd C (w - n) 1 < w := by have := opnd_lt hAO hklt 1; omega
      have h0ne : opnd C (w - n) 0 ≠ n + jb :=
        fun heq => hno (w - n) hklt hkg (heq ▸ opnd_mem hAO hklt 0)
      have h1ne : opnd C (w - n) 1 ≠ n + jb :=
        fun heq => hno (w - n) hklt hkg (heq ▸ opnd_mem hAO hklt 1)
      have hgt : gateAt (rewriteCircuit n C jb g aW v m) (remapCGate jb g (w - n)) =
          ⟨(gateAt C (w - n)).op, (gateAt C (w - n)).inputs.map (remapC n jb g)⟩ := by
        rw [rewriteCircuit_gateAt (by simpa [rewriteCircuit_len] using hi)]
        unfold remapCGate
        by_cases hltjb : w - n < jb
        · simp only [hltjb, ↓reduceIte]
          have h0m : remapC n jb g (opnd C (w - n) 0) = opnd C (w - n) 0 := by
            have := opnd_lt hAO hklt 0; unfold remapC; split_ifs <;> omega
          have h1m : remapC n jb g (opnd C (w - n) 1) = opnd C (w - n) 1 := by
            have := opnd_lt hAO hklt 1; unfold remapC; split_ifs <;> omega
          have hinp := gate_inputs_eq hAO hklt
          cases hc : gateAt C (w - n) with
          | mk op ins =>
            rw [hc] at hinp
            dsimp at hinp
            rw [hinp]
            simp [h0m, h1m]
        · have hif1 : ¬ w - n - 1 < jb := by omega
          have hif2 : w - n - 1 + 1 < g := by omega
          have heq : w - n - 1 + 1 = w - n := by omega
          simp only [hltjb, hk, ↓reduceIte, hif1, hif2, heq]
      have hop0 : opnd (rewriteCircuit n C jb g aW v m) (remapCGate jb g (w - n)) 0 =
          remapC n jb g (opnd C (w - n) 0) := by
        unfold opnd; rw [hgt, gate_inputs_eq hAO hklt]; rfl
      have hop1 : opnd (rewriteCircuit n C jb g aW v m) (remapCGate jb g (w - n)) 1 =
          remapC n jb g (opnd C (w - n) 1) := by
        unfold opnd; rw [hgt, gate_inputs_eq hAO hklt]; rfl
      have hop_eq : (gateAt (rewriteCircuit n C jb g aW v m) (remapCGate jb g (w - n))).op =
          (gateAt C (w - n)).op := by rw [hgt]
      rw [hrm]
      conv_rhs => rw [hwn]
      rcases hAO.1 _ (gateAt_mem hklt) with hop | hop
      · rw [wval_gate_and hAO' x hi (hop_eq.trans hop), wval_gate_and hAO x hklt hop,
          hop0, hop1, ih _ h0lt (by omega) h0ne, ih _ h1lt (by omega) h1ne]
      · rw [wval_gate_or hAO' x hi (hop_eq.trans hop), wval_gate_or hAO x hklt hop,
          hop0, hop1, ih _ h0lt (by omega) h0ne, ih _ h1lt (by omega) h1ne]

lemma rewriteCircuit_wval_and {n : ℕ} {C : Circuit} {jb g aW : ℕ} {v m : Fin n}
    (hAO : IsAO2 n C) (hjbg : jb < g) (hg : g < C.gates.length)
    (haWlt : aW < n + g) (haWne : aW ≠ n + jb)
    (hno : ∀ k < C.gates.length, k ≠ g → n + jb ∉ (gateAt C k).inputs)
    (x : Fin n → Bool) :
    gateVal n (rewriteCircuit n C jb g aW v m) (g - 1) x = (wval C x aW && x m) := by
  have hAO' := rewriteCircuit_isAO2 v m hAO hjbg hg haWlt haWne hno
  have hi : g - 1 < (rewriteCircuit n C jb g aW v m).gates.length := by
    rw [rewriteCircuit_len]; omega
  have hgt : gateAt (rewriteCircuit n C jb g aW v m) (g - 1) =
      ⟨GateOp.and, [remapC n jb g aW, m.val]⟩ := by
    rw [rewriteCircuit_gateAt (by omega)]
    have h1 : ¬ g - 1 < jb := by omega
    have h3 : g - 1 + 1 = g := by omega
    simp [h1, h3]
  have hop : (gateAt (rewriteCircuit n C jb g aW v m) (g - 1)).op = GateOp.and := by rw [hgt]
  have hop0 : opnd (rewriteCircuit n C jb g aW v m) (g - 1) 0 = remapC n jb g aW := by
    unfold opnd; rw [hgt]; rfl
  have hop1 : opnd (rewriteCircuit n C jb g aW v m) (g - 1) 1 = m.val := by
    unfold opnd; rw [hgt]; rfl
  change wval (rewriteCircuit n C jb g aW v m) x (n + (g - 1)) = _
  rw [wval_gate_and hAO' x hi hop, hop0, hop1,
    rewriteCircuit_wval_lt_g hAO hjbg hg haWlt haWne hno x aW haWlt haWne,
    wval_input _ x m.val m.isLt]

lemma rewriteCircuit_wval_g {n : ℕ} {C : Circuit} {jb g aW : ℕ} {v m : Fin n}
    (hAO : IsAO2 n C) (hjbg : jb < g) (hg : g < C.gates.length)
    (haWlt : aW < n + g) (haWne : aW ≠ n + jb)
    (hno : ∀ k < C.gates.length, k ≠ g → n + jb ∉ (gateAt C k).inputs)
    (x : Fin n → Bool) :
    gateVal n (rewriteCircuit n C jb g aW v m) g x = (x v || (wval C x aW && x m)) := by
  have hAO' := rewriteCircuit_isAO2 v m hAO hjbg hg haWlt haWne hno
  have hi : g < (rewriteCircuit n C jb g aW v m).gates.length := by
    rw [rewriteCircuit_len]; exact hg
  have hgt : gateAt (rewriteCircuit n C jb g aW v m) g =
      ⟨GateOp.or, [v.val, n + (g - 1)]⟩ := by
    rw [rewriteCircuit_gateAt hg]
    have h1 : ¬ g < jb := by omega
    have h2 : ¬ g + 1 < g := by omega
    simp [h1, h2]
  have hop : (gateAt (rewriteCircuit n C jb g aW v m) g).op = GateOp.or := by rw [hgt]
  have hop0 : opnd (rewriteCircuit n C jb g aW v m) g 0 = v.val := by
    unfold opnd; rw [hgt]; rfl
  have hop1 : opnd (rewriteCircuit n C jb g aW v m) g 1 = n + (g - 1) := by
    unfold opnd; rw [hgt]; rfl
  change wval (rewriteCircuit n C jb g aW v m) x (n + g) = _
  rw [wval_gate_or hAO' x hi hop, hop0, hop1, wval_input _ x v.val v.isLt]
  exact congrArg (x v || ·) (rewriteCircuit_wval_and hAO hjbg hg haWlt haWne hno x)

lemma rewriteCircuit_wval_le {n : ℕ} {C : Circuit} {jb g aW : ℕ} {v m : Fin n}
    (hAO : IsAO2 n C) (hjbg : jb < g) (hg : g < C.gates.length)
    (haWlt : aW < n + g) (haWne : aW ≠ n + jb)
    (hno : ∀ k < C.gates.length, k ≠ g → n + jb ∉ (gateAt C k).inputs)
    (x : Fin n → Bool)
    (hle_g : (x v || (wval C x aW && x m)) = true → gateVal n C g x = true) :
    ∀ w < n + C.gates.length, w ≠ n + jb →
      wval (rewriteCircuit n C jb g aW v m) x (remapC n jb g w) = true → wval C x w = true := by
  have hAO' := rewriteCircuit_isAO2 v m hAO hjbg hg haWlt haWne hno
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw hwne hD
    by_cases hlt : w < n + g
    · rw [rewriteCircuit_wval_lt_g hAO hjbg hg haWlt haWne hno x w hlt hwne] at hD
      exact hD
    · by_cases hwg : w = n + g
      · subst hwg
        have hm : remapC n jb g (n + g) = n + g := by unfold remapC; split_ifs <;> omega
        rw [hm] at hD
        change gateVal n (rewriteCircuit n C jb g aW v m) g x = true at hD
        rw [rewriteCircuit_wval_g hAO hjbg hg haWlt haWne hno x] at hD
        exact hle_g hD
      · have hk : w - n < C.gates.length := by omega
        have hkg : w - n ≠ g := by omega
        have hgt_g : g < w - n := by omega
        have hwn : w = n + (w - n) := by omega
        have hm : remapC n jb g w = n + (w - n) := by unfold remapC; split_ifs <;> omega
        have hi : w - n < (rewriteCircuit n C jb g aW v m).gates.length := by
          rw [rewriteCircuit_len]; exact hk
        have hgt : gateAt (rewriteCircuit n C jb g aW v m) (w - n) =
            ⟨(gateAt C (w - n)).op, (gateAt C (w - n)).inputs.map (remapC n jb g)⟩ := by
          rw [rewriteCircuit_gateAt hk]
          have h1 : ¬ w - n < jb := by omega
          have h2 : ¬ w - n + 1 < g := by omega
          have h3 : w - n + 1 ≠ g := by omega
          simp [h1, h2, h3, hkg]
        have hop0 : opnd (rewriteCircuit n C jb g aW v m) (w - n) 0 =
            remapC n jb g (opnd C (w - n) 0) := by
          unfold opnd; rw [hgt, gate_inputs_eq hAO hk]; rfl
        have hop1 : opnd (rewriteCircuit n C jb g aW v m) (w - n) 1 =
            remapC n jb g (opnd C (w - n) 1) := by
          unfold opnd; rw [hgt, gate_inputs_eq hAO hk]; rfl
        have hop_eq : (gateAt (rewriteCircuit n C jb g aW v m) (w - n)).op = (gateAt C (w - n)).op := by
          rw [hgt]
        have h0lt : opnd C (w - n) 0 < w := by have := opnd_lt hAO hk 0; omega
        have h1lt : opnd C (w - n) 1 < w := by have := opnd_lt hAO hk 1; omega
        have h0ne : opnd C (w - n) 0 ≠ n + jb :=
          fun heq => hno (w - n) hk hkg (heq ▸ opnd_mem hAO hk 0)
        have h1ne : opnd C (w - n) 1 ≠ n + jb :=
          fun heq => hno (w - n) hk hkg (heq ▸ opnd_mem hAO hk 1)
        rw [hm] at hD
        rw [hwn]
        rcases hAO.1 _ (gateAt_mem hk) with hop | hop
        · rw [wval_gate_and hAO' x hi (hop_eq.trans hop), Bool.and_eq_true, hop0, hop1] at hD
          rw [wval_gate_and hAO x hk hop, Bool.and_eq_true]
          exact ⟨ih _ h0lt (by omega) h0ne hD.1, ih _ h1lt (by omega) h1ne hD.2⟩
        · rw [wval_gate_or hAO' x hi (hop_eq.trans hop), Bool.or_eq_true, hop0, hop1] at hD
          rw [wval_gate_or hAO x hk hop, Bool.or_eq_true]
          exact hD.elim (fun h => Or.inl (ih _ h0lt (by omega) h0ne h))
            (fun h => Or.inr (ih _ h1lt (by omega) h1ne h))

lemma or_and_or_iff {a1 a2 r1 r2 : Prop} :
    ((a1 ∨ r1) ∨ (a2 ∨ r2)) ↔ ((a1 ∨ a2) ∨ (r1 ∨ r2)) := by
  constructor
  · rintro ((h | h) | (h | h))
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inr h)
  · rintro ((h | h) | (h | h))
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inr h)

lemma bool_eq_of_ne_ne {a b c : Bool} (hab : a ≠ b) (hac : a ≠ c) : b = c := by
  cases a <;> cases b <;> cases c <;> simp_all

set_option maxHeartbeats 800000 in
lemma main :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (g : ℕ),
      (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C →
      PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C →
      (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ t ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs, ¬ (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, t⟩ (List.ofFn x) = true → PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true)) →
      (∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k) →
      g < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and → ¬ PEqualNP.TopForm.BelowF G C g →
      (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → k ≠ g → PEqualNP.TopForm.BelowF G C k) →
      (∃ v : Fin n, PEqualNP.EdgeOwnership.gateVal n C g (PEqualNP.SplitCount.unitInput v) = true) →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n D ∧ D.size ≤ C.size ∧
        PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧
        ∀ k < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D k).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.TopForm.BelowF G D k := by
  intro n G _ C s g h_bip h_c4 hAO h_eq h_lift h_no_imp h_cone hg_lt hg_and hg_dirty h_clean_and h_unit
  rcases h_unit with ⟨v, hv_g⟩
  have h_out_below : WireBelowF G C C.output := by
    intro x hx
    change circuitFun n C x = true at hx
    rw [h_eq] at hx
    exact hx
  have h_out_gt_g : n + g < C.output ∧ C.output < n + C.gates.length := by
    have hc := h_cone g hg_lt
    rcases hc.2 with hout | ⟨hnle, hinc⟩
    · exfalso
      apply hg_dirty
      intro x hx
      have : wval C x C.output = true := by rw [hout]; exact hx
      exact h_out_below x this
    · have hlt_len : C.output - n < C.gates.length := inCone_lt_len hinc
      have hgt : g < C.output - n := inCone_lt hinc
      omega
  have h_out_below_gate : BelowF G C (C.output - n) := by
    intro x hx
    apply h_out_below x
    have : n + (C.output - n) = C.output := by omega
    rw [← this]
    exact hx
  have h_dirty_or : ∀ k < C.gates.length, ¬ BelowF G C k → k ≠ g → (gateAt C k).op = GateOp.or := by
    intro k hk hdirty hkg
    rcases hAO.1 _ (gateAt_mem hk) with hop | hop
    · exact (hdirty (h_clean_and k hk hop hkg)).elim
    · exact hop
  have h_dirty_inputs : ∀ k < C.gates.length, ¬ BelowF G C k → ∀ b : Fin 2, ¬ WireBelowF G C (opnd C k b) := by
    intro k hk hdirty b hwb
    rcases hAO.1 _ (gateAt_mem hk) with hop | hop
    · exact h_no_imp k hk hop (opnd C k b) (opnd_mem hAO hk b) hwb
    · apply h_lift
      refine ⟨k, hk, b, h_cone k hk, hop, hdirty, hwb, fun _ => true, ?_⟩
      exact wval_allTrue hAO (opnd C k b) (by have := opnd_lt hAO hk b; omega)
  have h_clean_or_inputs : ∀ k < C.gates.length, BelowF G C k → (gateAt C k).op = GateOp.or →
      ∀ b : Fin 2, n ≤ opnd C k b ∧ opnd C k b - n < k ∧ BelowF G C (opnd C k b - n) := by
    intro k hk hbf hop b
    have hwb : WireBelowF G C (opnd C k b) := by
      intro x hx
      apply hbf x
      change wval C x (n + k) = true
      rw [wval_gate_or hAO x hk hop, Bool.or_eq_true]
      fin_cases b
      · exact Or.inl hx
      · exact Or.inr hx
    have hge : n ≤ opnd C k b := by
      by_contra hlt
      exact not_wireBelowF_input G C (by omega) hwb
    have hlt := opnd_lt hAO hk b
    refine ⟨hge, by omega, ?_⟩
    intro x hx
    apply hwb x
    have : n + (opnd C k b - n) = opnd C k b := by omega
    rw [← this]
    exact hx
  have h_wval_dirty : ∀ w < n + C.gates.length, ¬ WireBelowF G C w → ∀ x : Fin n → Bool,
      wval C x w = true ↔ (usesG n C g w = true ∧ gateVal n C g x = true) ∨ (∃ u ∈ varSet n C g w, x u = true) := by
    intro w
    induction w using Nat.strongRecOn with
    | ind w ih =>
      intro hw hdw x
      by_cases hlt : w < n
      · rw [wval_input C x w hlt, usesG_input n C g w hlt, varSet_input n C g w hlt]
        simp
      · by_cases hwg : w = n + g
        · subst hwg
          rw [usesG_g, varSet_g]
          simp [gateVal, wval]
        · have hk : w - n < C.gates.length := by omega
          have hkg : w - n ≠ g := by omega
          have hwn : w = n + (w - n) := by omega
          have hdk : ¬ BelowF G C (w - n) := by
            intro hbf; apply hdw; rw [hwn]; exact hbf
          have hop : (gateAt C (w - n)).op = GateOp.or := h_dirty_or (w - n) hk hdk hkg
          have h0lt : opnd C (w - n) 0 < w := by have := opnd_lt hAO hk 0; omega
          have h1lt : opnd C (w - n) 1 < w := by have := opnd_lt hAO hk 1; omega
          have h0d := h_dirty_inputs (w - n) hk hdk 0
          have h1d := h_dirty_inputs (w - n) hk hdk 1
          have ih0 := ih _ h0lt (by omega) h0d x
          have ih1 := ih _ h1lt (by omega) h1d x
          rw [hwn, wval_gate_or hAO x hk hop, Bool.or_eq_true,
            usesG_gate hAO g (w - n) hk hkg, varSet_gate hAO g (w - n) hk hkg, ih0, ih1]
          simp only [Bool.or_eq_true, Finset.mem_union, or_and_right, exists_or]
          exact or_and_or_iff
  have h_varSet_nonempty : ∀ w < n + C.gates.length, ¬ WireBelowF G C w → usesG n C g w = false →
      (varSet n C g w).Nonempty := by
    intro w hw hdw hug
    have ht := (h_wval_dirty w hw hdw (fun _ => true)).mp (wval_allTrue hAO w hw)
    rw [hug] at ht
    rcases ht with ⟨hfalse, _⟩ | ⟨u, hu, _⟩
    · cases hfalse
    · exact ⟨u, hu⟩
  have h_g_op0_lt : opnd C g 0 < n + g := opnd_lt hAO hg_lt 0
  have h_g_op1_lt : opnd C g 1 < n + g := opnd_lt hAO hg_lt 1
  have h_g_op0_dirty : ¬ WireBelowF G C (opnd C g 0) := h_dirty_inputs g hg_lt hg_dirty 0
  have h_g_op1_dirty : ¬ WireBelowF G C (opnd C g 1) := h_dirty_inputs g hg_lt hg_dirty 1
  have h_g_op0_val : ∀ x, wval C x (opnd C g 0) = true ↔ ∃ u ∈ varSet n C g (opnd C g 0), x u = true := by
    intro x
    have h := h_wval_dirty (opnd C g 0) (by omega) h_g_op0_dirty x
    rw [usesG_lt_g hAO g _ h_g_op0_lt] at h
    simpa using h
  have h_g_op1_val : ∀ x, wval C x (opnd C g 1) = true ↔ ∃ u ∈ varSet n C g (opnd C g 1), x u = true := by
    intro x
    have h := h_wval_dirty (opnd C g 1) (by omega) h_g_op1_dirty x
    rw [usesG_lt_g hAO g _ h_g_op1_lt] at h
    simpa using h
  have h_g_val : ∀ x, gateVal n C g x = true ↔
      (∃ u ∈ varSet n C g (opnd C g 0), x u = true) ∧ (∃ w ∈ varSet n C g (opnd C g 1), x w = true) := by
    intro x
    change wval C x (n + g) = true ↔ _
    rw [wval_gate_and hAO x hg_lt hg_and, Bool.and_eq_true, h_g_op0_val, h_g_op1_val]
  have hv_in_01 : v ∈ varSet n C g (opnd C g 0) ∧ v ∈ varSet n C g (opnd C g 1) := by
    have hv := (h_g_val (unitInput v)).mp hv_g
    rcases hv with ⟨⟨u0, hu0, heq0⟩, ⟨u1, hu1, heq1⟩⟩
    simp only [unitInput, decide_eq_true_eq] at heq0 heq1
    subst heq0; subst heq1
    exact ⟨hu0, hu1⟩
  have h_and_not_both_g : ∀ a < C.gates.length, (gateAt C a).op = GateOp.and → a ≠ g →
      ¬ (usesG n C g (opnd C a 0) = true ∧ usesG n C g (opnd C a 1) = true) := by
    intro a ha hop hag ⟨hu0, hu1⟩
    have hbf := h_clean_and a ha hop hag
    have hd0 : ¬ WireBelowF G C (opnd C a 0) := h_no_imp a ha hop _ (opnd_mem hAO ha 0)
    have hd1 : ¬ WireBelowF G C (opnd C a 1) := h_no_imp a ha hop _ (opnd_mem hAO ha 1)
    have h0 : wval C (unitInput v) (opnd C a 0) = true :=
      (h_wval_dirty _ (by have := opnd_lt hAO ha 0; omega) hd0 (unitInput v)).mpr (Or.inl ⟨hu0, hv_g⟩)
    have h1 : wval C (unitInput v) (opnd C a 1) = true :=
      (h_wval_dirty _ (by have := opnd_lt hAO ha 1; omega) hd1 (unitInput v)).mpr (Or.inl ⟨hu1, hv_g⟩)
    have ha_t : gateVal n C a (unitInput v) = true := by
      change wval C (unitInput v) (n + a) = true
      rw [wval_gate_and hAO _ ha hop, h0, h1]; rfl
    have hf := hbf (unitInput v) ha_t
    rw [graphFun_unitInput_false] at hf
    cases hf
  have h_dirty_cone_usesG : ∀ k < C.gates.length, ¬ BelowF G C k → (g = k ∨ InCone n C g k) →
      usesG n C g (n + k) = true := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro hk hdk hreach
      rcases hreach with hgk | hinc
      · rw [← hgk]; exact usesG_g n C g
      · have hkg : k ≠ g := by have := inCone_lt hinc; omega
        rw [inCone_iff hk] at hinc
        rcases hinc with ⟨w, hwm, hwn, hwlt, hsub⟩
        have hwk : w - n < k := by omega
        have hwn' : w = n + (w - n) := by omega
        have hdw : ¬ BelowF G C (w - n) := by
          intro hbf
          rw [gate_inputs_eq hAO hk] at hwm
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hwm
          rcases hwm with rfl | rfl
          · exact h_dirty_inputs k hk hdk 0 (by rw [hwn']; exact hbf)
          · exact h_dirty_inputs k hk hdk 1 (by rw [hwn']; exact hbf)
        have hug := ih (w - n) hwk (by omega) hdw hsub
        rw [usesG_gate hAO g k hk hkg, Bool.or_eq_true]
        rw [gate_inputs_eq hAO hk] at hwm
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hwm
        rcases hwm with rfl | rfl
        · exact Or.inl (by rw [hwn']; exact hug)
        · exact Or.inr (by rw [hwn']; exact hug)
  have h_exists_reader : ∃ a < C.gates.length, (gateAt C a).op = GateOp.and ∧ a ≠ g ∧
      (usesG n C g (opnd C a 0) = true ∨ usesG n C g (opnd C a 1) = true) := by
    have hP : ∃ a, a < C.gates.length ∧ (g = a ∨ InCone n C g a) ∧ BelowF G C a := by
      refine ⟨C.output - n, by omega, Or.inr ?_, h_out_below_gate⟩
      have hc := h_cone g hg_lt
      rcases hc.2 with hout | ⟨_, hinc⟩
      · omega
      · exact hinc
    let a := Nat.find hP
    have ha_spec := Nat.find_spec hP
    have ha_min : ∀ k < a, ¬ (k < C.gates.length ∧ (g = k ∨ InCone n C g k) ∧ BelowF G C k) :=
      fun k hk => Nat.find_min hP hk
    rcases ha_spec with ⟨ha_lt, ha_reach, ha_bf⟩
    have hag : a ≠ g := fun heq => hg_dirty (heq ▸ ha_bf)
    have hinc : InCone n C g a := ha_reach.resolve_left hag.symm
    rw [inCone_iff ha_lt] at hinc
    rcases hinc with ⟨w, hwm, hwn, hwlt, hsub⟩
    have hwk : w - n < a := by omega
    have hdw : ¬ BelowF G C (w - n) := fun hbf => ha_min (w - n) hwk ⟨by omega, hsub, hbf⟩
    have hop : (gateAt C a).op = GateOp.and := by
      rcases hAO.1 _ (gateAt_mem ha_lt) with hop | hop
      · exact hop
      · exfalso
        rw [gate_inputs_eq hAO ha_lt] at hwm
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hwm
        rcases hwm with rfl | rfl
        · exact hdw (h_clean_or_inputs a ha_lt ha_bf hop 0).2.2
        · exact hdw (h_clean_or_inputs a ha_lt ha_bf hop 1).2.2
    have hug : usesG n C g w = true := by
      have : w = n + (w - n) := by omega
      rw [this]
      exact h_dirty_cone_usesG (w - n) (by omega) hdw hsub
    refine ⟨a, ha_lt, hop, hag, ?_⟩
    rw [gate_inputs_eq hAO ha_lt] at hwm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hwm
    rcases hwm with rfl | rfl
    · exact Or.inl hug
    · exact Or.inr hug
  have h_mem_zSet : ∀ z : Fin n, z ∈ zSet n C g ↔
      ∃ a < C.gates.length, (gateAt C a).op = GateOp.and ∧ a ≠ g ∧
        ((usesG n C g (opnd C a 0) = true ∧ z ∈ varSet n C g (opnd C a 1)) ∨
         (usesG n C g (opnd C a 1) = true ∧ z ∈ varSet n C g (opnd C a 0))) := by
    intro z
    unfold zSet
    simp only [Finset.mem_biUnion, Finset.mem_range]
    constructor
    · rintro ⟨a, ha, hmem⟩
      cases hop : (gateAt C a).op with
      | and =>
        rw [hop] at hmem
        dsimp only at hmem
        by_cases hag : a ≠ g
        · rw [if_pos hag, Finset.mem_union] at hmem
          refine ⟨a, ha, hop, hag, ?_⟩
          rcases hmem with h0 | h1
          · split_ifs at h0 with hu0
            · exact Or.inl ⟨hu0, h0⟩
            · simp at h0
          · split_ifs at h1 with hu1
            · exact Or.inr ⟨hu1, h1⟩
            · simp at h1
        · simp [hag] at hmem
      | or => rw [hop] at hmem; simp at hmem
      | not => rw [hop] at hmem; simp at hmem
      | mod m => rw [hop] at hmem; simp at hmem
      | maj => rw [hop] at hmem; simp at hmem
    · rintro ⟨a, ha, hop, hag, hside⟩
      refine ⟨a, ha, ?_⟩
      rw [hop]
      simp only [hag, ne_eq, not_false_eq_true, ↓reduceIte, Finset.mem_union]
      rcases hside with ⟨hu0, hz1⟩ | ⟨hu1, hz0⟩
      · left; simp [hu0, hz1]
      · right; simp [hu1, hz0]
  have h_zSet_nonempty : (zSet n C g).Nonempty := by
    rcases h_exists_reader with ⟨a, ha, hop, hag, hu0 | hu1⟩
    · have hu1f : usesG n C g (opnd C a 1) = false := by
        cases h : usesG n C g (opnd C a 1)
        · rfl
        · exact (h_and_not_both_g a ha hop hag ⟨hu0, h⟩).elim
      have hd1 : ¬ WireBelowF G C (opnd C a 1) := h_no_imp a ha hop _ (opnd_mem hAO ha 1)
      rcases h_varSet_nonempty (opnd C a 1) (by have := opnd_lt hAO ha 1; omega) hd1 hu1f with ⟨z, hz⟩
      exact ⟨z, (h_mem_zSet z).mpr ⟨a, ha, hop, hag, Or.inl ⟨hu0, hz⟩⟩⟩
    · have hu0f : usesG n C g (opnd C a 0) = false := by
        cases h : usesG n C g (opnd C a 0)
        · rfl
        · exact (h_and_not_both_g a ha hop hag ⟨h, hu1⟩).elim
      have hd0 : ¬ WireBelowF G C (opnd C a 0) := h_no_imp a ha hop _ (opnd_mem hAO ha 0)
      rcases h_varSet_nonempty (opnd C a 0) (by have := opnd_lt hAO ha 0; omega) hd0 hu0f with ⟨z, hz⟩
      exact ⟨z, (h_mem_zSet z).mpr ⟨a, ha, hop, hag, Or.inr ⟨hu1, hz⟩⟩⟩
  have h_zSet_below : ∀ z ∈ zSet n C g, ∀ x : Fin n → Bool,
      gateVal n C g x = true → x z = true → graphFun G ∅ x = true := by
    intro z hz x hgx hxz
    rcases (h_mem_zSet z).mp hz with ⟨a, ha, hop, hag, ⟨hu0, hz1⟩ | ⟨hu1, hz0⟩⟩
    · have hd0 : ¬ WireBelowF G C (opnd C a 0) := h_no_imp a ha hop _ (opnd_mem hAO ha 0)
      have hd1 : ¬ WireBelowF G C (opnd C a 1) := h_no_imp a ha hop _ (opnd_mem hAO ha 1)
      have h0 : wval C x (opnd C a 0) = true :=
        (h_wval_dirty _ (by have := opnd_lt hAO ha 0; omega) hd0 x).mpr (Or.inl ⟨hu0, hgx⟩)
      have h1 : wval C x (opnd C a 1) = true :=
        (h_wval_dirty _ (by have := opnd_lt hAO ha 1; omega) hd1 x).mpr (Or.inr ⟨z, hz1, hxz⟩)
      apply h_clean_and a ha hop hag x
      change wval C x (n + a) = true
      rw [wval_gate_and hAO x ha hop, h0, h1]; rfl
    · have hd0 : ¬ WireBelowF G C (opnd C a 0) := h_no_imp a ha hop _ (opnd_mem hAO ha 0)
      have hd1 : ¬ WireBelowF G C (opnd C a 1) := h_no_imp a ha hop _ (opnd_mem hAO ha 1)
      have h0 : wval C x (opnd C a 0) = true :=
        (h_wval_dirty _ (by have := opnd_lt hAO ha 0; omega) hd0 x).mpr (Or.inr ⟨z, hz0, hxz⟩)
      have h1 : wval C x (opnd C a 1) = true :=
        (h_wval_dirty _ (by have := opnd_lt hAO ha 1; omega) hd1 x).mpr (Or.inl ⟨hu1, hgx⟩)
      apply h_clean_and a ha hop hag x
      change wval C x (n + a) = true
      rw [wval_gate_and hAO x ha hop, h0, h1]; rfl
  have h_zSet_adj_v : ∀ z ∈ zSet n C g, G.Adj v z := by
    intro z hz
    rw [← graphFun_pairInput_iff G v z]
    apply h_zSet_below z hz (pairInput v z)
    · rw [h_g_val]
      exact ⟨⟨v, hv_in_01.1, by simp [pairInput]⟩, ⟨v, hv_in_01.2, by simp [pairInput]⟩⟩
    · simp [pairInput]
  have h_zSet_color : ∀ z ∈ zSet n C g, s z ≠ s v := fun z hz => (h_bip v z (h_zSet_adj_v z hz)).symm
  have h_clean_and_no_two_sided : ∀ a < C.gates.length, (gateAt C a).op = GateOp.and → a ≠ g →
      ∀ b : Fin 2, ¬ ((∃ uL ∈ varSet n C g (opnd C a b), s uL = s v) ∧
                      (∃ uR ∈ varSet n C g (opnd C a b), s uR ≠ s v)) := by
    intro a ha hop hag b ⟨⟨uL, huL, hsL⟩, ⟨uR, huR, hsR⟩⟩
    let b' : Fin 2 := if b = 0 then 1 else 0
    have hbf := h_clean_and a ha hop hag
    have hdb : ¬ WireBelowF G C (opnd C a b) := h_no_imp a ha hop _ (opnd_mem hAO ha b)
    have hdb' : ¬ WireBelowF G C (opnd C a b') := h_no_imp a ha hop _ (opnd_mem hAO ha b')
    have h_pair_adj : ∀ x : Fin n → Bool, wval C x (opnd C a b) = true → wval C x (opnd C a b') = true →
        graphFun G ∅ x = true := by
      intro x hx1 hx2
      apply hbf x
      change wval C x (n + a) = true
      rw [wval_gate_and hAO x ha hop, Bool.and_eq_true]
      fin_cases b
      · exact ⟨hx1, hx2⟩
      · exact ⟨hx2, hx1⟩
    cases hub' : usesG n C g (opnd C a b') with
    | true =>
      have h1 : wval C (pairInput v uL) (opnd C a b) = true :=
        (h_wval_dirty _ (by have := opnd_lt hAO ha b; omega) hdb _).mpr
          (Or.inr ⟨uL, huL, by simp [pairInput]⟩)
      have hgv : gateVal n C g (pairInput v uL) = true := by
        rw [h_g_val]
        exact ⟨⟨v, hv_in_01.1, by simp [pairInput]⟩, ⟨v, hv_in_01.2, by simp [pairInput]⟩⟩
      have h2 : wval C (pairInput v uL) (opnd C a b') = true :=
        (h_wval_dirty _ (by have := opnd_lt hAO ha b'; omega) hdb' _).mpr (Or.inl ⟨hub', hgv⟩)
      have hadj : G.Adj v uL := (graphFun_pairInput_iff G v uL).mp (h_pair_adj _ h1 h2)
      exact h_bip v uL hadj hsL.symm
    | false =>
      rcases h_varSet_nonempty (opnd C a b') (by have := opnd_lt hAO ha b'; omega) hdb' hub' with ⟨z, hz⟩
      by_cases hsz : s z = s v
      · have h1 : wval C (pairInput uL z) (opnd C a b) = true :=
          (h_wval_dirty _ (by have := opnd_lt hAO ha b; omega) hdb _).mpr
            (Or.inr ⟨uL, huL, by simp [pairInput]⟩)
        have h2 : wval C (pairInput uL z) (opnd C a b') = true :=
          (h_wval_dirty _ (by have := opnd_lt hAO ha b'; omega) hdb' _).mpr
            (Or.inr ⟨z, hz, by simp [pairInput]⟩)
        have hadj : G.Adj uL z := (graphFun_pairInput_iff G uL z).mp (h_pair_adj _ h1 h2)
        exact h_bip uL z hadj (hsL.trans hsz.symm)
      · have h1 : wval C (pairInput uR z) (opnd C a b) = true :=
          (h_wval_dirty _ (by have := opnd_lt hAO ha b; omega) hdb _).mpr
            (Or.inr ⟨uR, huR, by simp [pairInput]⟩)
        have h2 : wval C (pairInput uR z) (opnd C a b') = true :=
          (h_wval_dirty _ (by have := opnd_lt hAO ha b'; omega) hdb' _).mpr
            (Or.inr ⟨z, hz, by simp [pairInput]⟩)
        have hadj : G.Adj uR z := (graphFun_pairInput_iff G uR z).mp (h_pair_adj _ h1 h2)
        have hsr : s uR = s z := bool_eq_of_ne_ne (Ne.symm hsR) (Ne.symm hsz)
        exact h_bip uR z hadj hsr
  have h_solve_ordered :
      ∀ (aW bW : ℕ),
        aW < n + g → bW < n + g →
        ¬ WireBelowF G C aW → ¬ WireBelowF G C bW →
        (∀ x, gateVal n C g x = (wval C x aW && wval C x bW)) →
        (∀ w ∈ (gateAt C g).inputs, w = aW ∨ w = bW) →
        (∀ u ∈ varSet n C g aW, s u = s v) →
        ∃ D : Circuit, IsAO2 n D ∧ D.size ≤ C.size ∧
          circuitFun n D = graphFun G ∅ ∧
          ∀ k < D.gates.length, (gateAt D k).op = GateOp.and → BelowF G D k := by
    intro aW bW haW_lt hbW_lt haW_d hbW_d hg_ab hg_in hA_L
    set A := varSet n C g aW
    set B := varSet n C g bW
    set Z := zSet n C g
    have haW_val : ∀ x, wval C x aW = true ↔ ∃ u ∈ A, x u = true := by
      intro x
      have h := h_wval_dirty aW (by omega) haW_d x
      rw [usesG_lt_g hAO g aW haW_lt] at h
      simpa using h
    have hbW_val : ∀ x, wval C x bW = true ↔ ∃ w ∈ B, x w = true := by
      intro x
      have h := h_wval_dirty bW (by omega) hbW_d x
      rw [usesG_lt_g hAO g bW hbW_lt] at h
      simpa using h
    have hg_AB : ∀ x, gateVal n C g x = true ↔ (∃ u ∈ A, x u = true) ∧ (∃ w ∈ B, x w = true) := by
      intro x
      rw [hg_ab, Bool.and_eq_true, haW_val, hbW_val]
    have hv_A : v ∈ A := by
      rcases ((hg_AB (unitInput v)).mp hv_g).1 with ⟨u, hu, heq⟩
      simp only [unitInput, decide_eq_true_eq] at heq
      exact heq ▸ hu
    have hv_B : v ∈ B := by
      rcases ((hg_AB (unitInput v)).mp hv_g).2 with ⟨w, hw, heq⟩
      simp only [unitInput, decide_eq_true_eq] at heq
      exact heq ▸ hw
    have h_two_sided_le_b : ∀ k < C.gates.length, ¬ BelowF G C k → k ≠ g →
        (∃ uL ∈ varSet n C g (n + k), s uL = s v) →
        (∃ uR ∈ varSet n C g (n + k), s uR ≠ s v) → n + k ≤ bW := by
      intro k hk hdk hkg hL hR
      have hT : ∃ c, c < C.gates.length ∧ (k = c ∨ InCone n C k c) ∧ (c = g ∨ BelowF G C c) := by
        refine ⟨C.output - n, by omega, Or.inr ?_, Or.inr h_out_below_gate⟩
        have hc := h_cone k hk
        rcases hc.2 with hout | ⟨_, hinc⟩
        · exfalso
          apply hdk
          intro x hx
          exact h_out_below x (by rw [hout]; exact hx)
        · exact hinc
      obtain ⟨c, hc_eq⟩ : ∃ c, c = Nat.find hT := ⟨_, rfl⟩
      have hc_spec : c < C.gates.length ∧ (k = c ∨ InCone n C k c) ∧ (c = g ∨ BelowF G C c) :=
        hc_eq ▸ Nat.find_spec hT
      have hc_min : ∀ j < c, ¬ (j < C.gates.length ∧ (k = j ∨ InCone n C k j) ∧ (j = g ∨ BelowF G C j)) :=
        fun j hj => Nat.find_min hT (hc_eq ▸ hj)
      rcases hc_spec with ⟨hc_lt, hc_reach, hc_end⟩
      have h_sub : ∀ j < c, (k = j ∨ InCone n C k j) → varSet n C g (n + k) ⊆ varSet n C g (n + j) := by
        intro j
        induction j using Nat.strongRecOn with
        | ind j ih =>
          intro hjc hjr
          rcases hjr with hkj | hinc
          · rw [hkj]
          · have hjlt : j < C.gates.length := inCone_lt_len hinc
            have hj_not : ¬ (j = g ∨ BelowF G C j) := fun h => hc_min j hjc ⟨hjlt, Or.inr hinc, h⟩
            have hjg : j ≠ g := fun h => hj_not (Or.inl h)
            rw [inCone_iff hjlt] at hinc
            rcases hinc with ⟨w, hwm, hwn, hwlt, hsub⟩
            have hwn' : w = n + (w - n) := by omega
            have h1 := ih (w - n) (by omega) (by omega) hsub
            rw [varSet_gate hAO g j hjlt hjg]
            rw [gate_inputs_eq hAO hjlt] at hwm
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hwm
            rcases hwm with rfl | rfl
            · exact Finset.Subset.trans h1 (by rw [← hwn']; exact Finset.subset_union_left)
            · exact Finset.Subset.trans h1 (by rw [← hwn']; exact Finset.subset_union_right)
      have hck : k ≠ c := by
        intro heq
        rcases hc_end with hcg | hbf
        · exact hkg (heq.trans hcg)
        · exact hdk (heq ▸ hbf)
      have hc_inc : InCone n C k c := hc_reach.resolve_left hck
      rw [inCone_iff hc_lt] at hc_inc
      rcases hc_inc with ⟨w, hwm, hwn, hwlt, hsub⟩
      have hwn' : w = n + (w - n) := by omega
      have h_k_le : k ≤ w - n := by
        rcases hsub with hkw | hinc'
        · omega
        · have := inCone_lt hinc'; omega
      have h_sub_w : varSet n C g (n + k) ⊆ varSet n C g w := by
        rw [hwn']
        exact h_sub (w - n) (by omega) hsub
      have hwL : ∃ uL ∈ varSet n C g w, s uL = s v := by
        rcases hL with ⟨u, hu, hs⟩; exact ⟨u, h_sub_w hu, hs⟩
      have hwR : ∃ uR ∈ varSet n C g w, s uR ≠ s v := by
        rcases hR with ⟨u, hu, hs⟩; exact ⟨u, h_sub_w hu, hs⟩
      have hdw : ¬ BelowF G C (w - n) := fun hbf =>
        hc_min (w - n) (by omega) ⟨by omega, hsub, Or.inr hbf⟩
      rcases hc_end with hcg | hbf
      · rw [hcg] at hwm
        rcases hg_in w hwm with rfl | rfl
        · rcases hwR with ⟨uR, huR, hsR⟩
          exact (hsR (hA_L uR huR)).elim
        · omega
      · exfalso
        rcases hAO.1 _ (gateAt_mem hc_lt) with hop | hop
        · have hcg : c ≠ g := fun heq => hg_dirty (heq ▸ hbf)
          rw [gate_inputs_eq hAO hc_lt] at hwm
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hwm
          rcases hwm with rfl | rfl
          · exact h_clean_and_no_two_sided c hc_lt hop hcg 0 ⟨hwL, hwR⟩
          · exact h_clean_and_no_two_sided c hc_lt hop hcg 1 ⟨hwL, hwR⟩
        · rw [gate_inputs_eq hAO hc_lt] at hwm
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hwm
          rcases hwm with rfl | rfl
          · exact hdw (h_clean_or_inputs c hc_lt hbf hop 0).2.2
          · exact hdw (h_clean_or_inputs c hc_lt hbf hop 1).2.2
    have h_del_wval_dirty : ∀ (r : ℕ), r < n + g →
        ∀ w < n + C.gates.length, ¬ WireBelowF G C w → ∀ x : Fin n → Bool,
          wval (delCircuit n C g r) x (delMap n g r w) = true ↔
            (usesG n C g w = true ∧ wval C x r = true) ∨ (∃ u ∈ varSet n C g w, x u = true) := by
      intro r hr
      have hAO' := delCircuit_isAO2 hAO hg_lt hr
      intro w
      induction w using Nat.strongRecOn with
      | ind w ih =>
        intro hw hdw x
        by_cases hlt : w < n + g
        · have hm : delMap n g r w = w := by simp [delMap, hlt]
          rw [hm, delCircuit_wval_lt hAO hg_lt hr x w hlt, h_wval_dirty w hw hdw x, usesG_lt_g hAO g w hlt]
          simp
        · by_cases hwg : w = n + g
          · subst hwg
            have hm : delMap n g r (n + g) = r := by simp [delMap]
            rw [hm, delCircuit_wval_lt hAO hg_lt hr x r hr, usesG_g, varSet_g]
            simp
          · have hk : w - n < C.gates.length := by omega
            have hkg : w - n ≠ g := by omega
            have hwn : w = n + (w - n) := by omega
            have hdk : ¬ BelowF G C (w - n) := fun hbf => hdw (by rw [hwn]; exact hbf)
            have hop : (gateAt C (w - n)).op = GateOp.or := h_dirty_or (w - n) hk hdk hkg
            have hdm : delMap n g r w = n + delGateMap g (w - n) := by
              conv_lhs => rw [hwn]
              exact delMap_gate n g r (w - n) hkg
            have hk' : delGateMap g (w - n) < (delCircuit n C g r).gates.length := by
              rw [delCircuit_len]; unfold delGateMap; split_ifs <;> omega
            have hgate : (gateAt (delCircuit n C g r) (delGateMap g (w - n))).op = GateOp.or := by
              rw [delCircuit_gateAt_src hg_lt hk hkg, hop]
            have h0lt : opnd C (w - n) 0 < w := by have := opnd_lt hAO hk 0; omega
            have h1lt : opnd C (w - n) 1 < w := by have := opnd_lt hAO hk 1; omega
            have ih0 := ih _ h0lt (by omega) (h_dirty_inputs (w - n) hk hdk 0) x
            have ih1 := ih _ h1lt (by omega) (h_dirty_inputs (w - n) hk hdk 1) x
            rw [hdm, wval_gate_or hAO' x hk' hgate, Bool.or_eq_true,
              delCircuit_opnd hAO hg_lt hk hkg 0, delCircuit_opnd hAO hg_lt hk hkg 1, ih0, ih1]
            conv_rhs => rw [hwn, usesG_gate hAO g (w - n) hk hkg, varSet_gate hAO g (w - n) hk hkg]
            simp only [Bool.or_eq_true, Finset.mem_union, or_and_right, exists_or]
            exact or_and_or_iff
    have h_solve_Z1_wire : ∀ (m : Fin n) (r : ℕ),
        (∀ z ∈ Z, z = m) → r < n + g →
        (∀ x, gateVal n C g x = true → wval C x r = true) →
        (∀ x, wval C x r = true → x m = true → graphFun G ∅ x = true) →
        ∃ D : Circuit, IsAO2 n D ∧ D.size ≤ C.size ∧
          circuitFun n D = graphFun G ∅ ∧
          ∀ k < D.gates.length, (gateAt D k).op = GateOp.and → BelowF G D k := by
      intro m r hZm hr hge_r h_rm_below
      let D := delCircuit n C g r
      have hAO' := delCircuit_isAO2 hAO hg_lt hr
      have h_and_bf : ∀ a < C.gates.length, (gateAt C a).op = GateOp.and → a ≠ g →
          BelowF G D (delGateMap g a) := by
        intro a ha hop hag x hDx
        have ha' : delGateMap g a < D.gates.length := by
          rw [delCircuit_len]; unfold delGateMap; split_ifs <;> omega
        have hgate : (gateAt D (delGateMap g a)).op = GateOp.and := by
          rw [delCircuit_gateAt_src hg_lt ha hag, hop]
        change wval D x (n + delGateMap g a) = true at hDx
        rw [wval_gate_and hAO' x ha' hgate, Bool.and_eq_true,
          delCircuit_opnd hAO hg_lt ha hag 0, delCircuit_opnd hAO hg_lt ha hag 1] at hDx
        have hd0 : ¬ WireBelowF G C (opnd C a 0) := h_no_imp a ha hop _ (opnd_mem hAO ha 0)
        have hd1 : ¬ WireBelowF G C (opnd C a 1) := h_no_imp a ha hop _ (opnd_mem hAO ha 1)
        have h0 := (h_del_wval_dirty r hr _ (by have := opnd_lt hAO ha 0; omega) hd0 x).mp hDx.1
        have h1 := (h_del_wval_dirty r hr _ (by have := opnd_lt hAO ha 1; omega) hd1 x).mp hDx.2
        rcases h0 with ⟨hu0, hrx⟩ | ⟨u0, hu0, hxu0⟩
        · have hu1f : usesG n C g (opnd C a 1) = false := by
            cases h : usesG n C g (opnd C a 1)
            · rfl
            · exact (h_and_not_both_g a ha hop hag ⟨hu0, h⟩).elim
          rcases h1 with ⟨hu1t, _⟩ | ⟨z, hz, hxz⟩
          · rw [hu1f] at hu1t; cases hu1t
          · have hzm : z = m := hZm z ((h_mem_zSet z).mpr ⟨a, ha, hop, hag, Or.inl ⟨hu0, hz⟩⟩)
            exact h_rm_below x hrx (hzm ▸ hxz)
        · rcases h1 with ⟨hu1, hrx⟩ | ⟨u1, hu1, hxu1⟩
          · have hzm : u0 = m := hZm u0 ((h_mem_zSet u0).mpr ⟨a, ha, hop, hag, Or.inr ⟨hu1, hu0⟩⟩)
            exact h_rm_below x hrx (hzm ▸ hxu0)
          · apply h_clean_and a ha hop hag x
            change wval C x (n + a) = true
            rw [wval_gate_and hAO x ha hop, Bool.and_eq_true]
            exact ⟨(h_wval_dirty _ (by have := opnd_lt hAO ha 0; omega) hd0 x).mpr (Or.inr ⟨u0, hu0, hxu0⟩),
                   (h_wval_dirty _ (by have := opnd_lt hAO ha 1; omega) hd1 x).mpr (Or.inr ⟨u1, hu1, hxu1⟩)⟩
      have h_all_bf : ∀ k < C.gates.length, BelowF G C k → BelowF G D (delGateMap g k) := by
        intro k
        induction k using Nat.strongRecOn with
        | ind k ih =>
          intro hk hbf
          have hkg : k ≠ g := fun heq => hg_dirty (heq ▸ hbf)
          rcases hAO.1 _ (gateAt_mem hk) with hop | hop
          · exact h_and_bf k hk hop hkg
          · intro x hDx
            have hk' : delGateMap g k < D.gates.length := by
              rw [delCircuit_len]; unfold delGateMap; split_ifs <;> omega
            have hgate : (gateAt D (delGateMap g k)).op = GateOp.or := by
              rw [delCircuit_gateAt_src hg_lt hk hkg, hop]
            change wval D x (n + delGateMap g k) = true at hDx
            rw [wval_gate_or hAO' x hk' hgate, Bool.or_eq_true,
              delCircuit_opnd hAO hg_lt hk hkg 0, delCircuit_opnd hAO hg_lt hk hkg 1] at hDx
            have hi0 := h_clean_or_inputs k hk hbf hop 0
            have hi1 := h_clean_or_inputs k hk hbf hop 1
            have hne0 : opnd C k 0 - n ≠ g := fun heq => hg_dirty (heq ▸ hi0.2.2)
            have hne1 : opnd C k 1 - n ≠ g := fun heq => hg_dirty (heq ▸ hi1.2.2)
            have heq0 : opnd C k 0 = n + (opnd C k 0 - n) := by omega
            have heq1 : opnd C k 1 = n + (opnd C k 1 - n) := by omega
            rcases hDx with h0 | h1
            · rw [heq0, delMap_gate n g r _ hne0] at h0
              exact ih _ hi0.2.1 (by omega) hi0.2.2 x h0
            · rw [heq1, delMap_gate n g r _ hne1] at h1
              exact ih _ hi1.2.1 (by omega) hi1.2.2 x h1
      refine ⟨D, hAO', delCircuit_size n C g r, ?_, ?_⟩
      · funext x
        have h_out_ne : C.output - n ≠ g := by omega
        have h_out_eq : C.output = n + (C.output - n) := by omega
        have h_Dout : circuitFun n D x = gateVal n D (delGateMap g (C.output - n)) x := by
          change wval D x (delMap n g r C.output) = wval D x (n + delGateMap g (C.output - n))
          conv_lhs => rw [h_out_eq]
          rw [delMap_gate n g r _ h_out_ne]
        cases hDx : circuitFun n D x with
        | true =>
          rw [h_Dout] at hDx
          exact (h_all_bf (C.output - n) (by omega) h_out_below_gate x hDx).symm
        | false =>
          cases hFx : graphFun G ∅ x with
          | false => rfl
          | true =>
            have hCx : wval C x C.output = true := by
              change circuitFun n C x = true
              rw [h_eq]; exact hFx
            have hDt : circuitFun n D x = true :=
              delCircuit_wval_ge hAO hg_lt hr x (hge_r x) C.output (by omega) hCx
            rw [hDx] at hDt; cases hDt
      · intro k' hk' hop'
        rw [delCircuit_len] at hk'
        let src := if k' < g then k' else k' + 1
        have hsrc_lt : src < C.gates.length := by dsimp [src]; split_ifs <;> omega
        have hsrc_ne : src ≠ g := by dsimp [src]; split_ifs <;> omega
        have hdgm : delGateMap g src = k' := by dsimp [src, delGateMap]; split_ifs <;> omega
        have hop : (gateAt C src).op = GateOp.and := by
          rw [← hdgm, delCircuit_gateAt_src hg_lt hsrc_lt hsrc_ne] at hop'
          exact hop'
        rw [← hdgm]
        exact h_and_bf src hsrc_lt hop hsrc_ne
    by_cases hZ1 : Z.card ≤ 1
    · rcases h_zSet_nonempty with ⟨m, hmZ⟩
      have hZm : ∀ z ∈ Z, z = m := fun z hz => Finset.card_le_one.mp hZ1 z hz m hmZ
      by_cases hAm : ∀ u ∈ A, G.Adj u m
      · apply h_solve_Z1_wire m aW hZm haW_lt
        · intro x hgx; rw [hg_ab, Bool.and_eq_true] at hgx; exact hgx.1
        · intro x hrx hxm
          rcases (haW_val x).mp hrx with ⟨u, hu, hxu⟩
          exact (graphFun_iff x).mpr ⟨u, m, hAm u hu, hxu, hxm⟩
      · push_neg at hAm
        rcases hAm with ⟨u0, hu0A, hu0m⟩
        have hBL_m : ∀ w ∈ B, s w = s v → G.Adj w m := by
          intro w hwB hsw
          have htri : graphFun G ∅ (tripleInput u0 w m) = true := by
            apply h_zSet_below m hmZ (tripleInput u0 w m)
            · rw [hg_AB]
              exact ⟨⟨u0, hu0A, by simp [tripleInput]⟩, ⟨w, hwB, by simp [tripleInput]⟩⟩
            · simp [tripleInput]
          rw [graphFun_tripleInput_iff] at htri
          rcases htri with hadj | hadj | hadj
          · exact (h_bip u0 w hadj ((hA_L u0 hu0A).trans hsw.symm)).elim
          · exact (hu0m hadj).elim
          · exact hadj
        have hm_not_B : m ∉ B := by
          intro hmB
          have hp : graphFun G ∅ (pairInput u0 m) = true := by
            apply h_zSet_below m hmZ (pairInput u0 m)
            · rw [hg_AB]
              exact ⟨⟨u0, hu0A, by simp [pairInput]⟩, ⟨m, hmB, by simp [pairInput]⟩⟩
            · simp [pairInput]
          exact hu0m ((graphFun_pairInput_iff G u0 m).mp hp)
        by_cases hB_L : ∀ w ∈ B, s w = s v
        · apply h_solve_Z1_wire m bW hZm hbW_lt
          · intro x hgx; rw [hg_ab, Bool.and_eq_true] at hgx; exact hgx.2
          · intro x hrx hxm
            rcases (hbW_val x).mp hrx with ⟨w, hw, hxw⟩
            exact (graphFun_iff x).mpr ⟨w, m, hBL_m w hw (hB_L w hw), hxw, hxm⟩
        · push_neg at hB_L
          rcases hB_L with ⟨wR, hwRB, hwRs⟩
          let C1 := restrictTwoSided G C s v g
          have hAO1 : IsAO2 n C1 := restrictTwoSided_isAO2 hAO s v g
          have hg_lt1 : g < C1.gates.length := by rw [restrictTwoSided_len]; exact hg_lt
          let D := delCircuit n C1 g bW
          have hAO' := delCircuit_isAO2 hAO1 hg_lt1 hbW_lt
          have h_no_ts_reads_ts : ∀ k < C.gates.length, k ≠ g →
              ¬ isTwoSided G C s v g (n + k) → ∀ b : Fin 2, ¬ isTwoSided G C s v g (opnd C k b) := by
            intro k hk hkg hnts b hts
            rcases hts with ⟨_, hdw, hL, hR⟩
            by_cases hbf : BelowF G C k
            · rcases hAO.1 _ (gateAt_mem hk) with hop | hop
              · exact h_clean_and_no_two_sided k hk hop hkg b ⟨hL, hR⟩
              · have hi := h_clean_or_inputs k hk hbf hop b
                apply hdw
                have : opnd C k b = n + (opnd C k b - n) := by omega
                rw [this]; exact hi.2.2
            · apply hnts
              refine ⟨by omega, hbf, ?_, ?_⟩
              · rw [varSet_gate hAO g k hk hkg]
                rcases hL with ⟨u, hu, hs⟩
                fin_cases b
                · exact ⟨u, Finset.mem_union_left _ hu, hs⟩
                · exact ⟨u, Finset.mem_union_right _ hu, hs⟩
              · rw [varSet_gate hAO g k hk hkg]
                rcases hR with ⟨u, hu, hs⟩
                fin_cases b
                · exact ⟨u, Finset.mem_union_left _ hu, hs⟩
                · exact ⟨u, Finset.mem_union_right _ hu, hs⟩
          have h_C1_eq_C : ∀ w < n + g, ¬ isTwoSided G C s v g w →
              ∀ x : Fin n → Bool, wval C1 x w = wval C x w := by
            intro w
            induction w using Nat.strongRecOn with
            | ind w ih =>
              intro hw hnts x
              by_cases hlt : w < n
              · rw [wval_input C1 x w hlt, wval_input C x w hlt]
              · have hk : w - n < C.gates.length := by omega
                have hkg : w - n ≠ g := by omega
                have hwn : w = n + (w - n) := by omega
                have hnts' : ¬ isTwoSided G C s v g (n + (w - n)) := by rwa [← hwn]
                have hgt : gateAt C1 (w - n) = gateAt C (w - n) := by
                  rw [restrictTwoSided_gateAt G C s v g (w - n) hk]
                  split_ifs with hcond
                  · exfalso; exact hnts' ⟨by omega, hcond.1, hcond.2.1, hcond.2.2⟩
                  · rfl
                have h0lt : opnd C (w - n) 0 < w := by have := opnd_lt hAO hk 0; omega
                have h1lt : opnd C (w - n) 1 < w := by have := opnd_lt hAO hk 1; omega
                have h0nts := h_no_ts_reads_ts (w - n) hk hkg hnts' 0
                have h1nts := h_no_ts_reads_ts (w - n) hk hkg hnts' 1
                have hop0 : opnd C1 (w - n) 0 = opnd C (w - n) 0 := by unfold opnd; rw [hgt]
                have hop1 : opnd C1 (w - n) 1 = opnd C (w - n) 1 := by unfold opnd; rw [hgt]
                have hk1 : w - n < C1.gates.length := by rw [restrictTwoSided_len]; exact hk
                rw [hwn]
                rcases hAO.1 _ (gateAt_mem hk) with hop | hop
                · rw [wval_gate_and hAO1 x hk1 (by rw [hgt]; exact hop), wval_gate_and hAO x hk hop,
                    hop0, hop1, ih _ h0lt (by omega) h0nts x, ih _ h1lt (by omega) h1nts x]
                · rw [wval_gate_or hAO1 x hk1 (by rw [hgt]; exact hop), wval_gate_or hAO x hk hop,
                    hop0, hop1, ih _ h0lt (by omega) h0nts x, ih _ h1lt (by omega) h1nts x]
          have h_C1_ts_bounds : ∀ w < n + g, isTwoSided G C s v g w → ∀ x : Fin n → Bool,
              (wval C1 x w = true → x v = true ∨ ∃ u ∈ varSet n C g w, s u = s v ∧ x u = true) ∧
              ((∃ u ∈ varSet n C g w, s u = s v ∧ x u = true) → wval C1 x w = true) := by
            intro w
            induction w using Nat.strongRecOn with
            | ind w ih =>
              intro hw hts x
              have hge_n : n ≤ w := by
                by_contra hlt
                rcases hts with ⟨_, _, ⟨uL, huL, hsL⟩, ⟨uR, huR, hsR⟩⟩
                rw [varSet_input n C g w (by omega)] at huL huR
                simp only [Finset.mem_singleton] at huL huR
                subst huL; subst huR
                exact hsR hsL
              have hk : w - n < C.gates.length := by omega
              have hkg : w - n ≠ g := by omega
              have hwn : w = n + (w - n) := by omega
              have hdk : ¬ BelowF G C (w - n) := fun hbf => hts.2.1 (by rw [hwn]; exact hbf)
              have hop : (gateAt C (w - n)).op = GateOp.or := h_dirty_or (w - n) hk hdk hkg
              have hk1 : w - n < C1.gates.length := by rw [restrictTwoSided_len]; exact hk
              have hgt : gateAt C1 (w - n) = ⟨GateOp.or, (gateAt C (w - n)).inputs.map (restrictMap C s v g)⟩ := by
                rw [restrictTwoSided_gateAt G C s v g (w - n) hk]
                have hcond : ¬ BelowF G C (w - n) ∧ (∃ u ∈ varSet n C g (n + (w - n)), s u = s v) ∧
                    (∃ u ∈ varSet n C g (n + (w - n)), s u ≠ s v) := by
                  rw [← hwn]; exact ⟨hdk, hts.2.2.1, hts.2.2.2⟩
                simp [hcond, hop]
              have hop_eq : (gateAt C1 (w - n)).op = GateOp.or := by rw [hgt]
              have hop0 : opnd C1 (w - n) 0 = restrictMap C s v g (opnd C (w - n) 0) := by
                unfold opnd; rw [hgt, gate_inputs_eq hAO hk]; rfl
              have hop1 : opnd C1 (w - n) 1 = restrictMap C s v g (opnd C (w - n) 1) := by
                unfold opnd; rw [hgt, gate_inputs_eq hAO hk]; rfl
              have h_branch : ∀ b : Fin 2,
                  (wval C1 x (restrictMap C s v g (opnd C (w - n) b)) = true →
                    x v = true ∨ ∃ u ∈ varSet n C g (opnd C (w - n) b), s u = s v ∧ x u = true) ∧
                  ((∃ u ∈ varSet n C g (opnd C (w - n) b), s u = s v ∧ x u = true) →
                    wval C1 x (restrictMap C s v g (opnd C (w - n) b)) = true) := by
                intro b
                set uW := opnd C (w - n) b
                have huW_lt : uW < w := by have := opnd_lt hAO hk b; omega
                have huW_d : ¬ WireBelowF G C uW := h_dirty_inputs (w - n) hk hdk b
                have huW_val : wval C x uW = true ↔ ∃ u ∈ varSet n C g uW, x u = true := by
                  have h := h_wval_dirty uW (by omega) huW_d x
                  rw [usesG_lt_g hAO g uW (by omega)] at h
                  simpa using h
                unfold restrictMap
                by_cases hR : ∀ u ∈ varSet n C g uW, s u ≠ s v
                · rw [ite_eq_left_iff.mpr (fun hn => (hn hR).elim)]
                  constructor
                  · intro hv1; rw [wval_input C1 x v.val v.isLt] at hv1; exact Or.inl hv1
                  · rintro ⟨u, hu, hsu, _⟩; exact (hR u hu hsu).elim
                · rw [ite_eq_right_iff.mpr (fun hy => (hR hy).elim)]
                  push_neg at hR
                  rcases hR with ⟨uL, huL, hsL⟩
                  by_cases hR2 : ∃ uR ∈ varSet n C g uW, s uR ≠ s v
                  · exact ih uW huW_lt (by omega) ⟨by omega, huW_d, ⟨uL, huL, hsL⟩, hR2⟩ x
                  · push_neg at hR2
                    have hnts_u : ¬ isTwoSided G C s v g uW := by
                      rintro ⟨_, _, _, ⟨uR, huR, hsR⟩⟩; exact hsR (hR2 uR huR)
                    rw [h_C1_eq_C uW (by omega) hnts_u x, huW_val]
                    constructor
                    · rintro ⟨u, hu, hxu⟩; exact Or.inr ⟨u, hu, hR2 u hu, hxu⟩
                    · rintro ⟨u, hu, _, hxu⟩; exact ⟨u, hu, hxu⟩
              have hb0 := h_branch 0
              have hb1 := h_branch 1
              rw [hwn, wval_gate_or hAO1 x hk1 hop_eq, Bool.or_eq_true, hop0, hop1,
                varSet_gate hAO g (w - n) hk hkg]
              constructor
              · rintro (h0 | h1)
                · rcases hb0.1 h0 with hv1 | ⟨u, hu, hsu, hxu⟩
                  · exact Or.inl hv1
                  · exact Or.inr ⟨u, Finset.mem_union_left _ hu, hsu, hxu⟩
                · rcases hb1.1 h1 with hv1 | ⟨u, hu, hsu, hxu⟩
                  · exact Or.inl hv1
                  · exact Or.inr ⟨u, Finset.mem_union_right _ hu, hsu, hxu⟩
              · rintro ⟨u, hu, hsu, hxu⟩
                rcases Finset.mem_union.mp hu with hu0 | hu1
                · exact Or.inl (hb0.2 ⟨u, hu0, hsu, hxu⟩)
                · exact Or.inr (hb1.2 ⟨u, hu1, hsu, hxu⟩)
          have h_C1_bW : ∀ x : Fin n → Bool, wval C1 x bW = true ↔ ∃ w ∈ B, s w = s v ∧ x w = true := by
            intro x
            have hts_b : isTwoSided G C s v g bW := ⟨by omega, hbW_d, ⟨v, hv_B, rfl⟩, ⟨wR, hwRB, hwRs⟩⟩
            have hb := h_C1_ts_bounds bW hbW_lt hts_b x
            constructor
            · intro h1
              rcases hb.1 h1 with hv1 | h2
              · exact ⟨v, hv_B, rfl, hv1⟩
              · exact h2
            · exact hb.2
          have h_D_dirty : ∀ w < n + C.gates.length, ¬ WireBelowF G C w → ¬ isTwoSided G C s v g w →
              ∀ x : Fin n → Bool,
                wval D x (delMap n g bW w) = true ↔
                  (usesG n C g w = true ∧ wval C1 x bW = true) ∨ (∃ u ∈ varSet n C g w, x u = true) := by
            intro w
            induction w using Nat.strongRecOn with
            | ind w ih =>
              intro hw hdw hnts x
              by_cases hlt : w < n + g
              · have hm : delMap n g bW w = w := by simp [delMap, hlt]
                rw [hm, delCircuit_wval_lt hAO1 hg_lt1 hbW_lt x w hlt, h_C1_eq_C w hlt hnts x,
                  h_wval_dirty w hw hdw x, usesG_lt_g hAO g w hlt]
                simp
              · by_cases hwg : w = n + g
                · subst hwg
                  have hm : delMap n g bW (n + g) = bW := by simp [delMap]
                  rw [hm, delCircuit_wval_lt hAO1 hg_lt1 hbW_lt x bW hbW_lt, usesG_g, varSet_g]
                  simp
                · have hk : w - n < C.gates.length := by omega
                  have hkg : w - n ≠ g := by omega
                  have hwn : w = n + (w - n) := by omega
                  have hdk : ¬ BelowF G C (w - n) := fun hbf => hdw (by rw [hwn]; exact hbf)
                  have hop : (gateAt C (w - n)).op = GateOp.or := h_dirty_or (w - n) hk hdk hkg
                  have hnts' : ¬ isTwoSided G C s v g (n + (w - n)) := by rwa [← hwn]
                  have hgt1 : gateAt C1 (w - n) = gateAt C (w - n) := by
                    rw [restrictTwoSided_gateAt G C s v g (w - n) hk]
                    split_ifs with hcond
                    · exfalso; exact hnts' ⟨by omega, hcond.1, hcond.2.1, hcond.2.2⟩
                    · rfl
                  have hdm : delMap n g bW w = n + delGateMap g (w - n) := by
                    conv_lhs => rw [hwn]
                    exact delMap_gate n g bW (w - n) hkg
                  have hk1 : w - n < C1.gates.length := by rw [restrictTwoSided_len]; exact hk
                  have hk' : delGateMap g (w - n) < D.gates.length := by
                    rw [delCircuit_len, restrictTwoSided_len]; unfold delGateMap; split_ifs <;> omega
                  have hgate : (gateAt D (delGateMap g (w - n))).op = GateOp.or := by
                    rw [delCircuit_gateAt_src hg_lt1 hk1 hkg, hgt1, hop]
                  have hop0 : opnd D (delGateMap g (w - n)) 0 = delMap n g bW (opnd C (w - n) 0) := by
                    rw [delCircuit_opnd hAO1 hg_lt1 hk1 hkg 0]; unfold opnd; rw [hgt1]
                  have hop1 : opnd D (delGateMap g (w - n)) 1 = delMap n g bW (opnd C (w - n) 1) := by
                    rw [delCircuit_opnd hAO1 hg_lt1 hk1 hkg 1]; unfold opnd; rw [hgt1]
                  have h0lt : opnd C (w - n) 0 < w := by have := opnd_lt hAO hk 0; omega
                  have h1lt : opnd C (w - n) 1 < w := by have := opnd_lt hAO hk 1; omega
                  have ih0 := ih _ h0lt (by omega) (h_dirty_inputs (w - n) hk hdk 0)
                    (h_no_ts_reads_ts (w - n) hk hkg hnts' 0) x
                  have ih1 := ih _ h1lt (by omega) (h_dirty_inputs (w - n) hk hdk 1)
                    (h_no_ts_reads_ts (w - n) hk hkg hnts' 1) x
                  rw [hdm, wval_gate_or hAO' x hk' hgate, Bool.or_eq_true, hop0, hop1, ih0, ih1]
                  conv_rhs => rw [hwn, usesG_gate hAO g (w - n) hk hkg, varSet_gate hAO g (w - n) hk hkg]
                  simp only [Bool.or_eq_true, Finset.mem_union, or_and_right, exists_or]
                  exact or_and_or_iff
          have h_C1_clean : ∀ k < C.gates.length, BelowF G C k → gateAt C1 k = gateAt C k := by
            intro k hk hbf
            rw [restrictTwoSided_gateAt G C s v g k hk]
            simp [hbf]
          have h_and_bf : ∀ a < C.gates.length, (gateAt C a).op = GateOp.and → a ≠ g →
              BelowF G D (delGateMap g a) := by
            intro a ha hop hag x hDx
            have ha1 : a < C1.gates.length := by rw [restrictTwoSided_len]; exact ha
            have ha' : delGateMap g a < D.gates.length := by
              rw [delCircuit_len, restrictTwoSided_len]; unfold delGateMap; split_ifs <;> omega
            have hgt1 := h_C1_clean a ha (h_clean_and a ha hop hag)
            have hgate : (gateAt D (delGateMap g a)).op = GateOp.and := by
              rw [delCircuit_gateAt_src hg_lt1 ha1 hag, hgt1, hop]
            have hop0 : opnd D (delGateMap g a) 0 = delMap n g bW (opnd C a 0) := by
              rw [delCircuit_opnd hAO1 hg_lt1 ha1 hag 0]; unfold opnd; rw [hgt1]
            have hop1 : opnd D (delGateMap g a) 1 = delMap n g bW (opnd C a 1) := by
              rw [delCircuit_opnd hAO1 hg_lt1 ha1 hag 1]; unfold opnd; rw [hgt1]
            change wval D x (n + delGateMap g a) = true at hDx
            rw [wval_gate_and hAO' x ha' hgate, Bool.and_eq_true, hop0, hop1] at hDx
            have hd0 : ¬ WireBelowF G C (opnd C a 0) := h_no_imp a ha hop _ (opnd_mem hAO ha 0)
            have hd1 : ¬ WireBelowF G C (opnd C a 1) := h_no_imp a ha hop _ (opnd_mem hAO ha 1)
            have hnts_a : ¬ isTwoSided G C s v g (n + a) := fun h => h.2.1 (h_clean_and a ha hop hag)
            have h0 := (h_D_dirty _ (by have := opnd_lt hAO ha 0; omega) hd0
              (h_no_ts_reads_ts a ha hag hnts_a 0) x).mp hDx.1
            have h1 := (h_D_dirty _ (by have := opnd_lt hAO ha 1; omega) hd1
              (h_no_ts_reads_ts a ha hag hnts_a 1) x).mp hDx.2
            rcases h0 with ⟨hu0, hbx⟩ | ⟨u0, hu0, hxu0⟩
            · have hu1f : usesG n C g (opnd C a 1) = false := by
                cases h : usesG n C g (opnd C a 1)
                · rfl
                · exact (h_and_not_both_g a ha hop hag ⟨hu0, h⟩).elim
              rcases h1 with ⟨hu1t, _⟩ | ⟨z, hz, hxz⟩
              · rw [hu1f] at hu1t; cases hu1t
              · have hzm : z = m := hZm z ((h_mem_zSet z).mpr ⟨a, ha, hop, hag, Or.inl ⟨hu0, hz⟩⟩)
                rcases (h_C1_bW x).mp hbx with ⟨w, hwB, hsw, hxw⟩
                exact (graphFun_iff x).mpr ⟨w, m, hBL_m w hwB hsw, hxw, hzm ▸ hxz⟩
            · rcases h1 with ⟨hu1, hbx⟩ | ⟨u1, hu1, hxu1⟩
              · have hzm : u0 = m := hZm u0 ((h_mem_zSet u0).mpr ⟨a, ha, hop, hag, Or.inr ⟨hu1, hu0⟩⟩)
                rcases (h_C1_bW x).mp hbx with ⟨w, hwB, hsw, hxw⟩
                exact (graphFun_iff x).mpr ⟨w, m, hBL_m w hwB hsw, hxw, hzm ▸ hxu0⟩
              · apply h_clean_and a ha hop hag x
                change wval C x (n + a) = true
                rw [wval_gate_and hAO x ha hop, Bool.and_eq_true]
                exact ⟨(h_wval_dirty _ (by have := opnd_lt hAO ha 0; omega) hd0 x).mpr (Or.inr ⟨u0, hu0, hxu0⟩),
                       (h_wval_dirty _ (by have := opnd_lt hAO ha 1; omega) hd1 x).mpr (Or.inr ⟨u1, hu1, hxu1⟩)⟩
          have h_all_bf : ∀ k < C.gates.length, BelowF G C k → BelowF G D (delGateMap g k) := by
            intro k
            induction k using Nat.strongRecOn with
            | ind k ih =>
              intro hk hbf
              have hkg : k ≠ g := fun heq => hg_dirty (heq ▸ hbf)
              rcases hAO.1 _ (gateAt_mem hk) with hop | hop
              · exact h_and_bf k hk hop hkg
              · intro x hDx
                have hk1 : k < C1.gates.length := by rw [restrictTwoSided_len]; exact hk
                have hk' : delGateMap g k < D.gates.length := by
                  rw [delCircuit_len, restrictTwoSided_len]; unfold delGateMap; split_ifs <;> omega
                have hgt1 := h_C1_clean k hk hbf
                have hgate : (gateAt D (delGateMap g k)).op = GateOp.or := by
                  rw [delCircuit_gateAt_src hg_lt1 hk1 hkg, hgt1, hop]
                have hop0 : opnd D (delGateMap g k) 0 = delMap n g bW (opnd C k 0) := by
                  rw [delCircuit_opnd hAO1 hg_lt1 hk1 hkg 0]; unfold opnd; rw [hgt1]
                have hop1 : opnd D (delGateMap g k) 1 = delMap n g bW (opnd C k 1) := by
                  rw [delCircuit_opnd hAO1 hg_lt1 hk1 hkg 1]; unfold opnd; rw [hgt1]
                change wval D x (n + delGateMap g k) = true at hDx
                rw [wval_gate_or hAO' x hk' hgate, Bool.or_eq_true, hop0, hop1] at hDx
                have hi0 := h_clean_or_inputs k hk hbf hop 0
                have hi1 := h_clean_or_inputs k hk hbf hop 1
                have hne0 : opnd C k 0 - n ≠ g := fun heq => hg_dirty (heq ▸ hi0.2.2)
                have hne1 : opnd C k 1 - n ≠ g := fun heq => hg_dirty (heq ▸ hi1.2.2)
                have heq0 : opnd C k 0 = n + (opnd C k 0 - n) := by omega
                have heq1 : opnd C k 1 = n + (opnd C k 1 - n) := by omega
                rcases hDx with h0 | h1
                · rw [heq0, delMap_gate n g bW _ hne0] at h0
                  exact ih _ hi0.2.1 (by omega) hi0.2.2 x h0
                · rw [heq1, delMap_gate n g bW _ hne1] at h1
                  exact ih _ hi1.2.1 (by omega) hi1.2.2 x h1
          have h_edge_keep : ∀ p q : Fin n, G.Adj p q → s p = s v →
              ∀ k < C.gates.length, BelowF G C k →
                gateVal n C k (pairInput p q) = true → gateVal n D (delGateMap g k) (pairInput p q) = true := by
            intro p q hpq hsp k
            have hsq : s q ≠ s v := fun heq => h_bip p q hpq (hsp.trans heq.symm)
            induction k using Nat.strongRecOn with
            | ind k ih =>
              intro hk hbf hCk
              have hkg : k ≠ g := fun heq => hg_dirty (heq ▸ hbf)
              have hk1 : k < C1.gates.length := by rw [restrictTwoSided_len]; exact hk
              have hk' : delGateMap g k < D.gates.length := by
                rw [delCircuit_len, restrictTwoSided_len]; unfold delGateMap; split_ifs <;> omega
              have hgt1 := h_C1_clean k hk hbf
              have hop0 : opnd D (delGateMap g k) 0 = delMap n g bW (opnd C k 0) := by
                rw [delCircuit_opnd hAO1 hg_lt1 hk1 hkg 0]; unfold opnd; rw [hgt1]
              have hop1 : opnd D (delGateMap g k) 1 = delMap n g bW (opnd C k 1) := by
                rw [delCircuit_opnd hAO1 hg_lt1 hk1 hkg 1]; unfold opnd; rw [hgt1]
              rcases hAO.1 _ (gateAt_mem hk) with hop | hop
              · have hgate : (gateAt D (delGateMap g k)).op = GateOp.and := by
                  rw [delCircuit_gateAt_src hg_lt1 hk1 hkg, hgt1, hop]
                change wval C (pairInput p q) (n + k) = true at hCk
                rw [wval_gate_and hAO _ hk hop, Bool.and_eq_true] at hCk
                change wval D (pairInput p q) (n + delGateMap g k) = true
                rw [wval_gate_and hAO' _ hk' hgate, Bool.and_eq_true, hop0, hop1]
                have hd0 : ¬ WireBelowF G C (opnd C k 0) := h_no_imp k hk hop _ (opnd_mem hAO hk 0)
                have hd1 : ¬ WireBelowF G C (opnd C k 1) := h_no_imp k hk hop _ (opnd_mem hAO hk 1)
                have hnts_k : ¬ isTwoSided G C s v g (n + k) := fun h => h.2.1 hbf
                have h0 := (h_wval_dirty _ (by have := opnd_lt hAO hk 0; omega) hd0 _).mp hCk.1
                have h1 := (h_wval_dirty _ (by have := opnd_lt hAO hk 1; omega) hd1 _).mp hCk.2
                have h_g_to_b : (∃ z ∈ Z, pairInput p q z = true) →
                    gateVal n C g (pairInput p q) = true → wval C1 (pairInput p q) bW = true := by
                  rintro ⟨z, hzZ, hpqz⟩ hgx
                  have hzm : z = m := hZm z hzZ
                  rw [hzm] at hpqz
                  simp only [pairInput, decide_eq_true_eq] at hpqz
                  have hqm : q = m := by
                    rcases hpqz with hmp | hmq
                    · exact (h_zSet_color m hmZ (hmp ▸ hsp)).elim
                    · exact hmq.symm
                  rw [hqm] at hgx ⊢
                  rcases ((hg_AB (pairInput p m)).mp hgx).2 with ⟨w, hwB, hpqw⟩
                  simp only [pairInput, decide_eq_true_eq] at hpqw
                  rcases hpqw with hwp | hwm
                  · exact (h_C1_bW (pairInput p m)).mpr ⟨w, hwB, hwp ▸ hsp, by simp [pairInput, hwp]⟩
                  · exact (hm_not_B (hwm ▸ hwB)).elim
                rw [h_D_dirty _ (by have := opnd_lt hAO hk 0; omega) hd0 (h_no_ts_reads_ts k hk hkg hnts_k 0),
                  h_D_dirty _ (by have := opnd_lt hAO hk 1; omega) hd1 (h_no_ts_reads_ts k hk hkg hnts_k 1)]
                rcases h0 with ⟨hu0, hgx⟩ | h0s
                · have hu1f : usesG n C g (opnd C k 1) = false := by
                    cases h : usesG n C g (opnd C k 1)
                    · rfl
                    · exact (h_and_not_both_g k hk hop hkg ⟨hu0, h⟩).elim
                  rcases h1 with ⟨hu1t, _⟩ | ⟨z, hz, hpqz⟩
                  · rw [hu1f] at hu1t; cases hu1t
                  · have hzZ : z ∈ Z := (h_mem_zSet z).mpr ⟨k, hk, hop, hkg, Or.inl ⟨hu0, hz⟩⟩
                    exact ⟨Or.inl ⟨hu0, h_g_to_b ⟨z, hzZ, hpqz⟩ hgx⟩, Or.inr ⟨z, hz, hpqz⟩⟩
                · rcases h1 with ⟨hu1, hgx⟩ | h1s
                  · rcases h0s with ⟨z, hz, hpqz⟩
                    have hzZ : z ∈ Z := (h_mem_zSet z).mpr ⟨k, hk, hop, hkg, Or.inr ⟨hu1, hz⟩⟩
                    exact ⟨Or.inr ⟨z, hz, hpqz⟩, Or.inl ⟨hu1, h_g_to_b ⟨z, hzZ, hpqz⟩ hgx⟩⟩
                  · exact ⟨Or.inr h0s, Or.inr h1s⟩
              · have hgate : (gateAt D (delGateMap g k)).op = GateOp.or := by
                  rw [delCircuit_gateAt_src hg_lt1 hk1 hkg, hgt1, hop]
                change wval C (pairInput p q) (n + k) = true at hCk
                rw [wval_gate_or hAO _ hk hop, Bool.or_eq_true] at hCk
                change wval D (pairInput p q) (n + delGateMap g k) = true
                rw [wval_gate_or hAO' _ hk' hgate, Bool.or_eq_true, hop0, hop1]
                have hi0 := h_clean_or_inputs k hk hbf hop 0
                have hi1 := h_clean_or_inputs k hk hbf hop 1
                have hne0 : opnd C k 0 - n ≠ g := fun heq => hg_dirty (heq ▸ hi0.2.2)
                have hne1 : opnd C k 1 - n ≠ g := fun heq => hg_dirty (heq ▸ hi1.2.2)
                have heq0 : opnd C k 0 = n + (opnd C k 0 - n) := by omega
                have heq1 : opnd C k 1 = n + (opnd C k 1 - n) := by omega
                rcases hCk with h0 | h1
                · left
                  rw [heq0, delMap_gate n g bW _ hne0]
                  exact ih _ hi0.2.1 (by omega) hi0.2.2
                    (by change wval C (pairInput p q) (n + (opnd C k 0 - n)) = true; rw [← heq0]; exact h0)
                · right
                  rw [heq1, delMap_gate n g bW _ hne1]
                  exact ih _ hi1.2.1 (by omega) hi1.2.2
                    (by change wval C (pairInput p q) (n + (opnd C k 1 - n)) = true; rw [← heq1]; exact h1)
          have h_Dout : ∀ x, circuitFun n D x = gateVal n D (delGateMap g (C.output - n)) x := by
            intro x
            change wval D x (delMap n g bW C.output) = wval D x (n + delGateMap g (C.output - n))
            have h_out_ne : C.output - n ≠ g := by omega
            have h_out_eq : C.output = n + (C.output - n) := by omega
            conv_lhs => rw [h_out_eq]
            rw [delMap_gate n g bW _ h_out_ne]
          refine ⟨D, hAO', by rw [Circuit.size, delCircuit_len, restrictTwoSided_len]; exact Nat.sub_le _ _, ?_, ?_⟩
          · apply circuitFun_eq_graphFun_of hAO'
            · intro x hx
              rw [h_Dout] at hx
              exact h_all_bf (C.output - n) (by omega) h_out_below_gate x hx
            · intro p q hpq
              have hCpq : gateVal n C (C.output - n) (pairInput p q) = true := by
                have h1 : circuitFun n C (pairInput p q) = true := by
                  rw [h_eq]; exact (graphFun_pairInput_iff G p q).mpr hpq
                change wval C (pairInput p q) C.output = true at h1
                have : C.output = n + (C.output - n) := by omega
                rw [this] at h1; exact h1
              by_cases hsp : s p = s v
              · rw [h_Dout]
                exact h_edge_keep p q hpq hsp (C.output - n) (by omega) h_out_below_gate hCpq
              · have hsq : s q = s v := bool_eq_of_ne_ne (h_bip p q hpq) hsp
                have hsym : pairInput p q = pairInput q p := by
                  funext t; simp [pairInput, or_comm]
                rw [hsym, h_Dout]
                exact h_edge_keep q p hpq.symm hsq (C.output - n) (by omega) h_out_below_gate (hsym ▸ hCpq)
          · intro k' hk' hop'
            rw [delCircuit_len, restrictTwoSided_len] at hk'
            let src := if k' < g then k' else k' + 1
            have hsrc_lt : src < C.gates.length := by dsimp [src]; split_ifs <;> omega
            have hsrc_ne : src ≠ g := by dsimp [src]; split_ifs <;> omega
            have hsrc1 : src < C1.gates.length := by rw [restrictTwoSided_len]; exact hsrc_lt
            have hdgm : delGateMap g src = k' := by dsimp [src, delGateMap]; split_ifs <;> omega
            have hop1 : (gateAt C1 src).op = GateOp.and := by
              rw [← hdgm, delCircuit_gateAt_src hg_lt1 hsrc1 hsrc_ne] at hop'
              exact hop'
            have hop : (gateAt C src).op = GateOp.and := by
              rw [restrictTwoSided_gateAt G C s v g src hsrc_lt] at hop1
              split_ifs at hop1 <;> exact hop1
            rw [← hdgm]
            exact h_and_bf src hsrc_lt hop hsrc_ne
    · have hZ2 : 1 < Z.card := by omega
      have hAB_inter : ∀ u ∈ A, u ∈ B → u = v := by
        intro u huA huB
        by_contra huv
        rcases Finset.one_lt_card.mp hZ2 with ⟨z1, hz1, z2, hz2, hz12⟩
        have hadj_u : ∀ z ∈ Z, G.Adj u z := by
          intro z hz
          rw [← graphFun_pairInput_iff G u z]
          apply h_zSet_below z hz (pairInput u z)
          · rw [hg_AB]
            exact ⟨⟨u, huA, by simp [pairInput]⟩, ⟨u, huB, by simp [pairInput]⟩⟩
          · simp [pairInput]
        exact hz12 (noFourCycle_unique h_c4 huv (hadj_u z1 hz1) (h_zSet_adj_v z1 hz1)
          (hadj_u z2 hz2) (h_zSet_adj_v z2 hz2))
      by_cases hBZ : ∃ m ∈ B, m ∈ Z
      · rcases hBZ with ⟨m, hmB, hmZ⟩
        by_cases hA_only_v : ∀ u ∈ A, u = v
        · let D := delCircuit n C g v.val
          have hvl : v.val < n + g := by omega
          have hAO' := delCircuit_isAO2 hAO hg_lt hvl
          have hg_eq_v : ∀ x, gateVal n C g x = true ↔ wval C x v.val = true := by
            intro x
            rw [hg_AB, wval_input C x v.val v.isLt]
            constructor
            · rintro ⟨⟨u, huA, hxu⟩, _⟩
              rw [hA_only_v u huA] at hxu; exact hxu
            · intro hxv
              exact ⟨⟨v, hv_A, hxv⟩, ⟨v, hv_B, hxv⟩⟩
          refine ⟨D, hAO', delCircuit_size n C g v.val, ?_, ?_⟩
          · funext x
            have hle_out := delCircuit_wval_le hAO hg_lt hvl x (hg_eq_v x).mpr C.output (by omega)
            have hge_out := delCircuit_wval_ge hAO hg_lt hvl x (hg_eq_v x).mp C.output (by omega)
            cases hDx : circuitFun n D x with
            | true =>
              have hCx : circuitFun n C x = true := hle_out hDx
              rw [h_eq] at hCx; exact hCx.symm
            | false =>
              cases hFx : graphFun G ∅ x with
              | false => rfl
              | true =>
                have hCx : circuitFun n C x = true := by rw [h_eq]; exact hFx
                have hDt : circuitFun n D x = true := hge_out hCx
                rw [hDx] at hDt; cases hDt
          · intro k' hk' hop' x hDx
            rw [delCircuit_len] at hk'
            let src := if k' < g then k' else k' + 1
            have hsrc_lt : src < C.gates.length := by dsimp [src]; split_ifs <;> omega
            have hsrc_ne : src ≠ g := by dsimp [src]; split_ifs <;> omega
            have hdgm : delGateMap g src = k' := by dsimp [src, delGateMap]; split_ifs <;> omega
            have hop : (gateAt C src).op = GateOp.and := by
              rw [← hdgm, delCircuit_gateAt_src hg_lt hsrc_lt hsrc_ne] at hop'
              exact hop'
            apply h_clean_and src hsrc_lt hop hsrc_ne x
            apply delCircuit_wval_le hAO hg_lt hvl x (hg_eq_v x).mpr (n + src) (by omega)
            rw [delMap_gate n g v.val src hsrc_ne, hdgm]
            exact hDx
        · push_neg at hA_only_v
          rcases hA_only_v with ⟨u0, hu0A, hu0v⟩
          have hAm : ∀ u ∈ A, G.Adj u m := by
            intro u huA
            rw [← graphFun_pairInput_iff G u m]
            apply h_zSet_below m hmZ (pairInput u m)
            · rw [hg_AB]
              exact ⟨⟨u, huA, by simp [pairInput]⟩, ⟨m, hmB, by simp [pairInput]⟩⟩
            · simp [pairInput]
          have hBZ_uniq : ∀ m' ∈ B, m' ∈ Z → m' = m := by
            intro m' hm'B hm'Z
            have hu0m' : G.Adj u0 m' := by
              rw [← graphFun_pairInput_iff G u0 m']
              apply h_zSet_below m' hm'Z (pairInput u0 m')
              · rw [hg_AB]
                exact ⟨⟨u0, hu0A, by simp [pairInput]⟩, ⟨m', hm'B, by simp [pairInput]⟩⟩
              · simp [pairInput]
            exact noFourCycle_unique h_c4 hu0v hu0m' (h_zSet_adj_v m' hm'Z)
              (hAm u0 hu0A) (h_zSet_adj_v m hmZ)
          have hms : s m ≠ s v := h_zSet_color m hmZ
          have hbW_ge : n ≤ bW := by
            by_contra hlt
            have h1 := hv_B
            have h2 := hmB
            dsimp [B] at h1 h2
            rw [varSet_input n C g bW (by omega)] at h1 h2
            simp only [Finset.mem_singleton] at h1 h2
            subst h1; subst h2
            exact hms rfl
          let jb := bW - n
          have hbW_eq : bW = n + jb := by omega
          have hjb_lt : jb < g := by omega
          have haW_ne : aW ≠ n + jb := by
            intro heq
            have : m ∈ A := by
              dsimp [A]; rw [heq, ← hbW_eq]; exact hmB
            exact hms (hA_L m this)
          have hno_jb : ∀ k < C.gates.length, k ≠ g → n + jb ∉ (gateAt C k).inputs := by
            intro k hk hkg hmem
            have hjk : jb < k := by
              have := hAO.2.1 k hk (n + jb) hmem; omega
            by_cases hbf : BelowF G C k
            · rcases hAO.1 _ (gateAt_mem hk) with hop | hop
              · rw [gate_inputs_eq hAO hk] at hmem
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
                rcases hmem with heq | heq
                · exact h_clean_and_no_two_sided k hk hop hkg 0
                    ⟨⟨v, by rw [← heq, ← hbW_eq]; exact hv_B, rfl⟩,
                     ⟨m, by rw [← heq, ← hbW_eq]; exact hmB, hms⟩⟩
                · exact h_clean_and_no_two_sided k hk hop hkg 1
                    ⟨⟨v, by rw [← heq, ← hbW_eq]; exact hv_B, rfl⟩,
                     ⟨m, by rw [← heq, ← hbW_eq]; exact hmB, hms⟩⟩
              · rw [gate_inputs_eq hAO hk] at hmem
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
                rcases hmem with heq | heq
                · have hi := h_clean_or_inputs k hk hbf hop 0
                  rw [← heq] at hi
                  apply hbW_d
                  rw [hbW_eq]
                  have : n + jb - n = jb := by omega
                  rw [this] at hi
                  exact hi.2.2
                · have hi := h_clean_or_inputs k hk hbf hop 1
                  rw [← heq] at hi
                  apply hbW_d
                  rw [hbW_eq]
                  have : n + jb - n = jb := by omega
                  rw [this] at hi
                  exact hi.2.2
            · have hsub : B ⊆ varSet n C g (n + k) := by
                rw [varSet_gate hAO g k hk hkg]
                rw [gate_inputs_eq hAO hk] at hmem
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
                rcases hmem with heq | heq
                · rw [← heq, ← hbW_eq]; exact Finset.subset_union_left
                · rw [← heq, ← hbW_eq]; exact Finset.subset_union_right
              have hle := h_two_sided_le_b k hk hbf hkg ⟨v, hsub hv_B, rfl⟩ ⟨m, hsub hmB, hms⟩
              omega
          let D := rewriteCircuit n C jb g aW v m
          have hAO' := rewriteCircuit_isAO2 v m hAO hjb_lt hg_lt haW_lt haW_ne hno_jb
          have hle_g : ∀ x, (x v || (wval C x aW && x m)) = true → gateVal n C g x = true := by
            intro x hx
            rw [Bool.or_eq_true, Bool.and_eq_true] at hx
            rw [hg_AB]
            rcases hx with hxv | ⟨haW_t, hxm⟩
            · exact ⟨⟨v, hv_A, hxv⟩, ⟨v, hv_B, hxv⟩⟩
            · exact ⟨(haW_val x).mp haW_t, ⟨m, hmB, hxm⟩⟩
          have h_D_dirty : ∀ w < n + C.gates.length, ¬ WireBelowF G C w → w ≠ n + jb →
              ∀ x : Fin n → Bool,
                wval D x (remapC n jb g w) = true ↔
                  (usesG n C g w = true ∧ (x v || (wval C x aW && x m)) = true) ∨
                  (∃ u ∈ varSet n C g w, x u = true) := by
            intro w
            induction w using Nat.strongRecOn with
            | ind w ih =>
              intro hw hdw hwne x
              by_cases hlt : w < n + g
              · rw [rewriteCircuit_wval_lt_g hAO hjb_lt hg_lt haW_lt haW_ne hno_jb x w hlt hwne,
                  h_wval_dirty w hw hdw x, usesG_lt_g hAO g w hlt]
                simp
              · by_cases hwg : w = n + g
                · subst hwg
                  have hm : remapC n jb g (n + g) = n + g := by unfold remapC; split_ifs <;> omega
                  rw [hm, usesG_g, varSet_g]
                  change gateVal n D g x = true ↔ _
                  rw [rewriteCircuit_wval_g hAO hjb_lt hg_lt haW_lt haW_ne hno_jb x]
                  simp
                · have hk : w - n < C.gates.length := by omega
                  have hkg : w - n ≠ g := by omega
                  have hwn : w = n + (w - n) := by omega
                  have hdk : ¬ BelowF G C (w - n) := fun hbf => hdw (by rw [hwn]; exact hbf)
                  have hop : (gateAt C (w - n)).op = GateOp.or := h_dirty_or (w - n) hk hdk hkg
                  have hm : remapC n jb g w = n + (w - n) := by unfold remapC; split_ifs <;> omega
                  have hi : w - n < D.gates.length := by rw [rewriteCircuit_len]; exact hk
                  have hgt : gateAt D (w - n) =
                      ⟨GateOp.or, (gateAt C (w - n)).inputs.map (remapC n jb g)⟩ := by
                    rw [rewriteCircuit_gateAt hk]
                    have h1 : ¬ w - n < jb := by omega
                    have h2 : ¬ w - n + 1 < g := by omega
                    have h3 : w - n + 1 ≠ g := by omega
                    simp [h1, h2, h3, hkg, hop]
                  have hop_eq : (gateAt D (w - n)).op = GateOp.or := by rw [hgt]
                  have hop0 : opnd D (w - n) 0 = remapC n jb g (opnd C (w - n) 0) := by
                    unfold opnd; rw [hgt, gate_inputs_eq hAO hk]; rfl
                  have hop1 : opnd D (w - n) 1 = remapC n jb g (opnd C (w - n) 1) := by
                    unfold opnd; rw [hgt, gate_inputs_eq hAO hk]; rfl
                  have h0lt : opnd C (w - n) 0 < w := by have := opnd_lt hAO hk 0; omega
                  have h1lt : opnd C (w - n) 1 < w := by have := opnd_lt hAO hk 1; omega
                  have h0ne : opnd C (w - n) 0 ≠ n + jb :=
                    fun heq => hno_jb (w - n) hk hkg (heq ▸ opnd_mem hAO hk 0)
                  have h1ne : opnd C (w - n) 1 ≠ n + jb :=
                    fun heq => hno_jb (w - n) hk hkg (heq ▸ opnd_mem hAO hk 1)
                  have ih0 := ih _ h0lt (by omega) (h_dirty_inputs (w - n) hk hdk 0) h0ne x
                  have ih1 := ih _ h1lt (by omega) (h_dirty_inputs (w - n) hk hdk 1) h1ne x
                  rw [hm, wval_gate_or hAO' x hi hop_eq, Bool.or_eq_true, hop0, hop1, ih0, ih1]
                  conv_rhs => rw [hwn, usesG_gate hAO g (w - n) hk hkg, varSet_gate hAO g (w - n) hk hkg]
                  simp only [Bool.or_eq_true, Finset.mem_union, or_and_right, exists_or]
                  exact or_and_or_iff
          have h_edge_keep : ∀ p q : Fin n, G.Adj p q → s p = s v →
              ∀ k < C.gates.length, BelowF G C k →
                gateVal n C k (pairInput p q) = true →
                gateVal n D (remapCGate jb g k) (pairInput p q) = true := by
            intro p q hpq hsp k
            have hsq : s q ≠ s v := fun heq => h_bip p q hpq (hsp.trans heq.symm)
            induction k using Nat.strongRecOn with
            | ind k ih =>
              intro hk hbf hCk
              have hkg : k ≠ g := fun heq => hg_dirty (heq ▸ hbf)
              have hkjb : k ≠ jb := fun heq => hbW_d (by rw [hbW_eq, ← heq]; exact hbf)
              by_cases hlt : k < g
              · have h1 := rewriteCircuit_wval_lt_g (v := v) (m := m) hAO hjb_lt hg_lt haW_lt haW_ne hno_jb
                  (pairInput p q) (n + k) (by omega) (by omega)
                rw [remapC_gate n jb g k hkjb] at h1
                change wval D (pairInput p q) (n + remapCGate jb g k) = true
                rw [h1]; exact hCk
              · have hrm : remapCGate jb g k = k := by unfold remapCGate; split_ifs <;> omega
                rw [hrm]
                have hi : k < D.gates.length := by rw [rewriteCircuit_len]; exact hk
                have hgt : gateAt D k = ⟨(gateAt C k).op, (gateAt C k).inputs.map (remapC n jb g)⟩ := by
                  rw [rewriteCircuit_gateAt hk]
                  have h1 : ¬ k < jb := by omega
                  have h2 : ¬ k + 1 < g := by omega
                  have h3 : k + 1 ≠ g := by omega
                  simp [h1, h2, h3, hkg]
                have hop0 : opnd D k 0 = remapC n jb g (opnd C k 0) := by
                  unfold opnd; rw [hgt, gate_inputs_eq hAO hk]; rfl
                have hop1 : opnd D k 1 = remapC n jb g (opnd C k 1) := by
                  unfold opnd; rw [hgt, gate_inputs_eq hAO hk]; rfl
                have h0ne : opnd C k 0 ≠ n + jb := fun heq => hno_jb k hk hkg (heq ▸ opnd_mem hAO hk 0)
                have h1ne : opnd C k 1 ≠ n + jb := fun heq => hno_jb k hk hkg (heq ▸ opnd_mem hAO hk 1)
                rcases hAO.1 _ (gateAt_mem hk) with hop | hop
                · have hgate : (gateAt D k).op = GateOp.and := by rw [hgt, hop]
                  change wval C (pairInput p q) (n + k) = true at hCk
                  rw [wval_gate_and hAO _ hk hop, Bool.and_eq_true] at hCk
                  change wval D (pairInput p q) (n + k) = true
                  rw [wval_gate_and hAO' _ hi hgate, Bool.and_eq_true, hop0, hop1]
                  have hd0 : ¬ WireBelowF G C (opnd C k 0) := h_no_imp k hk hop _ (opnd_mem hAO hk 0)
                  have hd1 : ¬ WireBelowF G C (opnd C k 1) := h_no_imp k hk hop _ (opnd_mem hAO hk 1)
                  have h0 := (h_wval_dirty _ (by have := opnd_lt hAO hk 0; omega) hd0 _).mp hCk.1
                  have h1 := (h_wval_dirty _ (by have := opnd_lt hAO hk 1; omega) hd1 _).mp hCk.2
                  have h_g_to_new : (∃ z ∈ Z, pairInput p q z = true) →
                      gateVal n C g (pairInput p q) = true →
                      (pairInput p q v || (wval C (pairInput p q) aW && pairInput p q m)) = true := by
                    rintro ⟨z, hzZ, hpqz⟩ hgx
                    simp only [pairInput, decide_eq_true_eq] at hpqz
                    have hzq : z = q := by
                      rcases hpqz with rfl | rfl
                      · exact (h_zSet_color z hzZ hsp).elim
                      · rfl
                    have hqZ : q ∈ Z := hzq ▸ hzZ
                    by_cases hpv : p = v
                    · subst hpv; simp [pairInput]
                    · rcases (hg_AB (pairInput p q)).mp hgx with ⟨⟨u, huA, hpqu⟩, ⟨w, hwB, hpqw⟩⟩
                      simp only [pairInput, decide_eq_true_eq] at hpqu hpqw
                      have hpA : p ∈ A := by
                        rcases hpqu with rfl | huq
                        · exact huA
                        · exact (hsq (huq ▸ hA_L u huA)).elim
                      have hp_not_B : p ∉ B := fun hpB => hpv (hAB_inter p hpA hpB)
                      have hqB : q ∈ B := by
                        rcases hpqw with rfl | rfl
                        · exact (hp_not_B hwB).elim
                        · exact hwB
                      have hqm : q = m := hBZ_uniq q hqB hqZ
                      rw [hqm, Bool.or_eq_true, Bool.and_eq_true]
                      right
                      exact ⟨(haW_val _).mpr ⟨p, hpA, by simp [pairInput]⟩, by simp [pairInput]⟩
                  rw [h_D_dirty _ (by have := opnd_lt hAO hk 0; omega) hd0 h0ne,
                    h_D_dirty _ (by have := opnd_lt hAO hk 1; omega) hd1 h1ne]
                  rcases h0 with ⟨hu0, hgx⟩ | h0s
                  · have hu1f : usesG n C g (opnd C k 1) = false := by
                      cases h : usesG n C g (opnd C k 1)
                      · rfl
                      · exact (h_and_not_both_g k hk hop hkg ⟨hu0, h⟩).elim
                    rcases h1 with ⟨hu1t, _⟩ | ⟨z, hz, hpqz⟩
                    · rw [hu1f] at hu1t; cases hu1t
                    · have hzZ : z ∈ Z := (h_mem_zSet z).mpr ⟨k, hk, hop, hkg, Or.inl ⟨hu0, hz⟩⟩
                      exact ⟨Or.inl ⟨hu0, h_g_to_new ⟨z, hzZ, hpqz⟩ hgx⟩, Or.inr ⟨z, hz, hpqz⟩⟩
                  · rcases h1 with ⟨hu1, hgx⟩ | h1s
                    · rcases h0s with ⟨z, hz, hpqz⟩
                      have hzZ : z ∈ Z := (h_mem_zSet z).mpr ⟨k, hk, hop, hkg, Or.inr ⟨hu1, hz⟩⟩
                      exact ⟨Or.inr ⟨z, hz, hpqz⟩, Or.inl ⟨hu1, h_g_to_new ⟨z, hzZ, hpqz⟩ hgx⟩⟩
                    · exact ⟨Or.inr h0s, Or.inr h1s⟩
                · have hgate : (gateAt D k).op = GateOp.or := by rw [hgt, hop]
                  change wval C (pairInput p q) (n + k) = true at hCk
                  rw [wval_gate_or hAO _ hk hop, Bool.or_eq_true] at hCk
                  change wval D (pairInput p q) (n + k) = true
                  rw [wval_gate_or hAO' _ hi hgate, Bool.or_eq_true, hop0, hop1]
                  have hi0 := h_clean_or_inputs k hk hbf hop 0
                  have hi1 := h_clean_or_inputs k hk hbf hop 1
                  have heq0 : opnd C k 0 = n + (opnd C k 0 - n) := by omega
                  have heq1 : opnd C k 1 = n + (opnd C k 1 - n) := by omega
                  have hne0 : opnd C k 0 - n ≠ jb := by omega
                  have hne1 : opnd C k 1 - n ≠ jb := by omega
                  rcases hCk with h0 | h1
                  · left
                    rw [heq0, remapC_gate n jb g _ hne0]
                    exact ih _ hi0.2.1 (by omega) hi0.2.2
                      (by change wval C (pairInput p q) (n + (opnd C k 0 - n)) = true; rw [← heq0]; exact h0)
                  · right
                    rw [heq1, remapC_gate n jb g _ hne1]
                    exact ih _ hi1.2.1 (by omega) hi1.2.2
                      (by change wval C (pairInput p q) (n + (opnd C k 1 - n)) = true; rw [← heq1]; exact h1)
          refine ⟨D, hAO', rewriteCircuit_size n C jb g aW v m, ?_, ?_⟩
          · apply circuitFun_eq_graphFun_of hAO'
            · intro x hx
              have hrm_out : remapC n jb g C.output = C.output := by
                unfold remapC; split_ifs <;> omega
              have hCx : wval C x C.output = true :=
                rewriteCircuit_wval_le hAO hjb_lt hg_lt haW_lt haW_ne hno_jb x (hle_g x)
                  C.output (by omega) (by omega) (by rw [hrm_out]; exact hx)
              exact h_out_below x hCx
            · intro p q hpq
              have hCpq : gateVal n C (C.output - n) (pairInput p q) = true := by
                have h1 : circuitFun n C (pairInput p q) = true := by
                  rw [h_eq]; exact (graphFun_pairInput_iff G p q).mpr hpq
                change wval C (pairInput p q) C.output = true at h1
                have : C.output = n + (C.output - n) := by omega
                rw [this] at h1; exact h1
              have hDout : ∀ y, circuitFun n D y = gateVal n D (remapCGate jb g (C.output - n)) y := by
                intro y
                have hrm : remapCGate jb g (C.output - n) = C.output - n := by
                  unfold remapCGate; split_ifs <;> omega
                rw [hrm]
                change wval D y C.output = wval D y (n + (C.output - n))
                have : C.output = n + (C.output - n) := by omega
                conv_lhs => rw [this]
              by_cases hsp : s p = s v
              · rw [hDout]
                exact h_edge_keep p q hpq hsp (C.output - n) (by omega) h_out_below_gate hCpq
              · have hsq : s q = s v := bool_eq_of_ne_ne (h_bip p q hpq) hsp
                have hsym : pairInput p q = pairInput q p := by
                  funext t; simp [pairInput, or_comm]
                rw [hsym, hDout]
                exact h_edge_keep q p hpq.symm hsq (C.output - n) (by omega) h_out_below_gate (hsym ▸ hCpq)
          · intro i hi hop x hDx
            rw [rewriteCircuit_len] at hi
            rw [rewriteCircuit_gateAt hi] at hop
            split_ifs at hop with h1 h2 h3 h4
            · apply h_clean_and i hi hop (by omega) x
              apply rewriteCircuit_wval_le hAO hjb_lt hg_lt haW_lt haW_ne hno_jb x (hle_g x) (n + i) (by omega) (by omega)
              have hm : remapC n jb g (n + i) = n + i := by unfold remapC; split_ifs <;> omega
              rw [hm]; exact hDx
            · apply h_clean_and (i + 1) (by omega) hop (by omega) x
              apply rewriteCircuit_wval_le hAO hjb_lt hg_lt haW_lt haW_ne hno_jb x (hle_g x) (n + (i + 1)) (by omega) (by omega)
              have hm : remapC n jb g (n + (i + 1)) = n + i := by unfold remapC; split_ifs <;> omega
              rw [hm]; exact hDx
            · have hig : i = g - 1 := by omega
              subst hig
              rw [rewriteCircuit_wval_and hAO hjb_lt hg_lt haW_lt haW_ne hno_jb x, Bool.and_eq_true] at hDx
              rcases (haW_val x).mp hDx.1 with ⟨u, huA, hxu⟩
              exact (graphFun_iff x).mpr ⟨u, m, hAm u huA, hxu, hDx.2⟩
            · apply h_clean_and i hi hop h4 x
              apply rewriteCircuit_wval_le hAO hjb_lt hg_lt haW_lt haW_ne hno_jb x (hle_g x) (n + i) (by omega) (by omega)
              have hm : remapC n jb g (n + i) = n + i := by unfold remapC; split_ifs <;> omega
              rw [hm]; exact hDx
      · push_neg at hBZ
        let D := delCircuit n C g v.val
        have hvl : v.val < n + g := by omega
        have hAO' := delCircuit_isAO2 hAO hg_lt hvl
        have hle_v : ∀ x, wval C x v.val = true → gateVal n C g x = true := by
          intro x hxv
          rw [wval_input C x v.val v.isLt] at hxv
          rw [hg_AB]
          exact ⟨⟨v, hv_A, hxv⟩, ⟨v, hv_B, hxv⟩⟩
        have h_edge_keep : ∀ p q : Fin n, G.Adj p q → s p = s v →
            ∀ k < C.gates.length, BelowF G C k →
              gateVal n C k (pairInput p q) = true →
              gateVal n D (delGateMap g k) (pairInput p q) = true := by
          intro p q hpq hsp k
          have hsq : s q ≠ s v := fun heq => h_bip p q hpq (hsp.trans heq.symm)
          induction k using Nat.strongRecOn with
          | ind k ih =>
            intro hk hbf hCk
            have hkg : k ≠ g := fun heq => hg_dirty (heq ▸ hbf)
            have hk' : delGateMap g k < D.gates.length := by
              rw [delCircuit_len]; unfold delGateMap; split_ifs <;> omega
            rcases hAO.1 _ (gateAt_mem hk) with hop | hop
            · have hgate : (gateAt D (delGateMap g k)).op = GateOp.and := by
                rw [delCircuit_gateAt_src hg_lt hk hkg, hop]
              change wval C (pairInput p q) (n + k) = true at hCk
              rw [wval_gate_and hAO _ hk hop, Bool.and_eq_true] at hCk
              change wval D (pairInput p q) (n + delGateMap g k) = true
              rw [wval_gate_and hAO' _ hk' hgate, Bool.and_eq_true,
                delCircuit_opnd hAO hg_lt hk hkg 0, delCircuit_opnd hAO hg_lt hk hkg 1]
              have hd0 : ¬ WireBelowF G C (opnd C k 0) := h_no_imp k hk hop _ (opnd_mem hAO hk 0)
              have hd1 : ¬ WireBelowF G C (opnd C k 1) := h_no_imp k hk hop _ (opnd_mem hAO hk 1)
              have h0 := (h_wval_dirty _ (by have := opnd_lt hAO hk 0; omega) hd0 _).mp hCk.1
              have h1 := (h_wval_dirty _ (by have := opnd_lt hAO hk 1; omega) hd1 _).mp hCk.2
              have h_g_to_v : (∃ z ∈ Z, pairInput p q z = true) →
                  gateVal n C g (pairInput p q) = true → wval C (pairInput p q) v.val = true := by
                rintro ⟨z, hzZ, hpqz⟩ hgx
                simp only [pairInput, decide_eq_true_eq] at hpqz
                have hzq : z = q := by
                  rcases hpqz with rfl | rfl
                  · exact (h_zSet_color z hzZ hsp).elim
                  · rfl
                have hqZ : q ∈ Z := hzq ▸ hzZ
                rcases (hg_AB (pairInput p q)).mp hgx with ⟨⟨u, huA, hpqu⟩, ⟨w, hwB, hpqw⟩⟩
                simp only [pairInput, decide_eq_true_eq] at hpqu hpqw
                have hpA : p ∈ A := by
                  rcases hpqu with rfl | huq
                  · exact huA
                  · exact (hsq (huq ▸ hA_L u huA)).elim
                have hpB : p ∈ B := by
                  rcases hpqw with rfl | hwq
                  · exact hwB
                  · exact (hBZ q (hwq ▸ hwB) hqZ).elim
                have hpv : p = v := hAB_inter p hpA hpB
                subst hpv
                rw [wval_input C _ p.val p.isLt]
                simp [pairInput]
              rw [h_del_wval_dirty v.val hvl _ (by have := opnd_lt hAO hk 0; omega) hd0,
                h_del_wval_dirty v.val hvl _ (by have := opnd_lt hAO hk 1; omega) hd1]
              rcases h0 with ⟨hu0, hgx⟩ | h0s
              · have hu1f : usesG n C g (opnd C k 1) = false := by
                  cases h : usesG n C g (opnd C k 1)
                  · rfl
                  · exact (h_and_not_both_g k hk hop hkg ⟨hu0, h⟩).elim
                rcases h1 with ⟨hu1t, _⟩ | ⟨z, hz, hpqz⟩
                · rw [hu1f] at hu1t; cases hu1t
                · have hzZ : z ∈ Z := (h_mem_zSet z).mpr ⟨k, hk, hop, hkg, Or.inl ⟨hu0, hz⟩⟩
                  exact ⟨Or.inl ⟨hu0, h_g_to_v ⟨z, hzZ, hpqz⟩ hgx⟩, Or.inr ⟨z, hz, hpqz⟩⟩
              · rcases h1 with ⟨hu1, hgx⟩ | h1s
                · rcases h0s with ⟨z, hz, hpqz⟩
                  have hzZ : z ∈ Z := (h_mem_zSet z).mpr ⟨k, hk, hop, hkg, Or.inr ⟨hu1, hz⟩⟩
                  exact ⟨Or.inr ⟨z, hz, hpqz⟩, Or.inl ⟨hu1, h_g_to_v ⟨z, hzZ, hpqz⟩ hgx⟩⟩
                · exact ⟨Or.inr h0s, Or.inr h1s⟩
            · have hgate : (gateAt D (delGateMap g k)).op = GateOp.or := by
                rw [delCircuit_gateAt_src hg_lt hk hkg, hop]
              change wval C (pairInput p q) (n + k) = true at hCk
              rw [wval_gate_or hAO _ hk hop, Bool.or_eq_true] at hCk
              change wval D (pairInput p q) (n + delGateMap g k) = true
              rw [wval_gate_or hAO' _ hk' hgate, Bool.or_eq_true,
                delCircuit_opnd hAO hg_lt hk hkg 0, delCircuit_opnd hAO hg_lt hk hkg 1]
              have hi0 := h_clean_or_inputs k hk hbf hop 0
              have hi1 := h_clean_or_inputs k hk hbf hop 1
              have hne0 : opnd C k 0 - n ≠ g := fun heq => hg_dirty (heq ▸ hi0.2.2)
              have hne1 : opnd C k 1 - n ≠ g := fun heq => hg_dirty (heq ▸ hi1.2.2)
              have heq0 : opnd C k 0 = n + (opnd C k 0 - n) := by omega
              have heq1 : opnd C k 1 = n + (opnd C k 1 - n) := by omega
              rcases hCk with h0 | h1
              · left
                rw [heq0, delMap_gate n g v.val _ hne0]
                exact ih _ hi0.2.1 (by omega) hi0.2.2
                  (by change wval C (pairInput p q) (n + (opnd C k 0 - n)) = true; rw [← heq0]; exact h0)
              · right
                rw [heq1, delMap_gate n g v.val _ hne1]
                exact ih _ hi1.2.1 (by omega) hi1.2.2
                  (by change wval C (pairInput p q) (n + (opnd C k 1 - n)) = true; rw [← heq1]; exact h1)
        refine ⟨D, hAO', delCircuit_size n C g v.val, ?_, ?_⟩
        · apply circuitFun_eq_graphFun_of hAO'
          · intro x hx
            exact h_out_below x (delCircuit_wval_le hAO hg_lt hvl x (hle_v x) C.output (by omega) hx)
          · intro p q hpq
            have hCpq : gateVal n C (C.output - n) (pairInput p q) = true := by
              have h1 : circuitFun n C (pairInput p q) = true := by
                rw [h_eq]; exact (graphFun_pairInput_iff G p q).mpr hpq
              change wval C (pairInput p q) C.output = true at h1
              have : C.output = n + (C.output - n) := by omega
              rw [this] at h1; exact h1
            have hDout : ∀ y, circuitFun n D y = gateVal n D (delGateMap g (C.output - n)) y := by
              intro y
              change wval D y (delMap n g v.val C.output) = wval D y (n + delGateMap g (C.output - n))
              have h_out_ne : C.output - n ≠ g := by omega
              have h_out_eq : C.output = n + (C.output - n) := by omega
              conv_lhs => rw [h_out_eq]
              rw [delMap_gate n g v.val _ h_out_ne]
            by_cases hsp : s p = s v
            · rw [hDout]
              exact h_edge_keep p q hpq hsp (C.output - n) (by omega) h_out_below_gate hCpq
            · have hsq : s q = s v := bool_eq_of_ne_ne (h_bip p q hpq) hsp
              have hsym : pairInput p q = pairInput q p := by
                funext t; simp [pairInput, or_comm]
              rw [hsym, hDout]
              exact h_edge_keep q p hpq.symm hsq (C.output - n) (by omega) h_out_below_gate (hsym ▸ hCpq)
        · intro k' hk' hop' x hDx
          rw [delCircuit_len] at hk'
          let src := if k' < g then k' else k' + 1
          have hsrc_lt : src < C.gates.length := by dsimp [src]; split_ifs <;> omega
          have hsrc_ne : src ≠ g := by dsimp [src]; split_ifs <;> omega
          have hdgm : delGateMap g src = k' := by dsimp [src, delGateMap]; split_ifs <;> omega
          have hop : (gateAt C src).op = GateOp.and := by
            rw [← hdgm, delCircuit_gateAt_src hg_lt hsrc_lt hsrc_ne] at hop'
            exact hop'
          apply h_clean_and src hsrc_lt hop hsrc_ne x
          apply delCircuit_wval_le hAO hg_lt hvl x (hle_v x) (n + src) (by omega)
          rw [delMap_gate n g v.val src hsrc_ne, hdgm]
          exact hDx
  by_cases h0L : ∀ u ∈ varSet n C g (opnd C g 0), s u = s v
  · exact h_solve_ordered (opnd C g 0) (opnd C g 1) h_g_op0_lt h_g_op1_lt h_g_op0_dirty h_g_op1_dirty
      (fun x => wval_gate_and hAO x hg_lt hg_and)
      (fun w hw => by
        rw [gate_inputs_eq hAO hg_lt] at hw
        simpa using hw)
      h0L
  · have h1L : ∀ w ∈ varSet n C g (opnd C g 1), s w = s v := by
      push_neg at h0L
      rcases h0L with ⟨u, hu, hsu⟩
      intro w hw
      by_contra hsw
      rcases h_zSet_nonempty with ⟨z, hzZ⟩
      have hsz := h_zSet_color z hzZ
      have htri : graphFun G ∅ (tripleInput u w z) = true := by
        apply h_zSet_below z hzZ (tripleInput u w z)
        · rw [h_g_val]
          exact ⟨⟨u, hu, by simp [tripleInput]⟩, ⟨w, hw, by simp [tripleInput]⟩⟩
        · simp [tripleInput]
      rw [graphFun_tripleInput_iff] at htri
      rcases htri with hadj | hadj | hadj
      · exact h_bip u w hadj (bool_eq_of_ne_ne (Ne.symm hsu) (Ne.symm hsw))
      · exact h_bip u z hadj (bool_eq_of_ne_ne (Ne.symm hsu) (Ne.symm hsz))
      · exact h_bip w z hadj (bool_eq_of_ne_ne (Ne.symm hsw) (Ne.symm hsz))
    exact h_solve_ordered (opnd C g 1) (opnd C g 0) h_g_op1_lt h_g_op0_lt h_g_op1_dirty h_g_op0_dirty
      (fun x => (wval_gate_and hAO x hg_lt hg_and).trans (Bool.and_comm _ _))
      (fun w hw => by
        rw [gate_inputs_eq hAO hg_lt] at hw
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        exact hw.symm)
      h1L

end PEqualNP.Outside.L_meta_2056_aux.TwoDirty.SingletonReduction


namespace PEqualNP.Outside.L_meta_2056_aux.TwoDirty

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.Core
  PEqualNP.EdgeOwnership PEqualNP.SplitCount
open FlatSumPlane OneDirtyPlane

lemma plane_edge_count : plane.edgeFinset.card = 52 := by decide +kernel

lemma plane_vertex_cover (S : Finset (Fin 26)) (cover : plane.IsVertexCover ↑S) : 13 ≤ S.card := by
  classical
  let label : Fin 26 → Fin 13 := fun c =>
    if h : c.val < 13 then ⟨c.val, h⟩ else -⟨c.val - 13, by omega⟩
  have hp : ∀ p : Fin 13, label (Fin.castAdd 13 p) = p := by decide
  have hl : ∀ p : Fin 13, label (Fin.natAdd 13 (-p)) = p := by decide
  have sub : (Finset.univ : Finset (Fin 13)) ⊆ S.image label := by
    intro p _
    rcases cover (adj_diag p) with h | h
    · exact Finset.mem_image.mpr ⟨Fin.castAdd 13 p, h, hp p⟩
    · exact Finset.mem_image.mpr ⟨Fin.natAdd 13 (-p), h, hl p⟩
  have h1 := Finset.card_le_card sub
  have h2 : (S.image label).card ≤ S.card := Finset.card_image_le
  simp only [Finset.card_univ, Fintype.card_fin] at h1
  omega

lemma plane_unit_false : ∀ p : Fin 26, graphFun plane ∅ (unitInput p) = false := by
  decide +kernel

lemma all_clean_lower (C : Circuit) (ao : IsAO2 26 C)
    (correct : circuitFun 26 C = graphFun plane ∅)
    (clean : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → BelowF plane C j) :
    64 ≤ C.size := by
  obtain ⟨S, cover, hbound⟩ := AllCleanBudget.all_clean_budget plane C (0 : Fin 26)
    plane_no_four ao correct clean
  have hcard := plane_vertex_cover S cover
  rw [plane_edge_count] at hbound
  omega

theorem normalized_at_most_one_dirty_lower (C : Circuit)
    (ao : IsAO2 26 C) (correct : circuitFun 26 C = graphFun plane ∅)
    (fixed : IsLiftFixedPoint plane C)
    (live : ∀ k < C.gates.length, InOutputCone 26 C k)
    (operands : OneDirtyReduction.NoSoundOperands plane C)
    (one : ∀ i < C.gates.length, ∀ j < C.gates.length,
      (gateAt C i).op = GateOp.and → (gateAt C j).op = GateOp.and →
      ¬ BelowF plane C i → ¬ BelowF plane C j → i = j) :
    64 ≤ C.size := by
  classical
  by_cases singleton : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ∀ p : Fin 26, gateVal 26 C k (unitInput p) = false
  · exact OneDirtyPlane.normalized_at_most_one_dirty_lower C ao correct fixed live operands singleton one
  · push_neg at singleton
    obtain ⟨g, hg, ha, p, hp⟩ := singleton
    have hit : gateVal 26 C g (unitInput p) = true := by
      cases h : gateVal 26 C g (unitInput p) <;> simp_all
    have dirty : ¬ BelowF plane C g := by
      intro h
      have bad := h (unitInput p) hit
      rw [plane_unit_false] at bad
      cases bad
    have clean : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → k ≠ g → BelowF plane C k := by
      intro k hk hkand hkg
      by_contra hkd
      exact hkg (one k hk g hg hkand ha hkd dirty)
    obtain ⟨D, hD, hs, hF, hclean⟩ := SingletonReduction.main 26 plane C
      (fun u => decide (u.val < 13)) g plane_bip plane_no_four ao correct fixed
      operands live hg ha dirty clean ⟨p, hit⟩
    exact (all_clean_lower D hD hF hclean).trans hs

theorem normalized_small_two_dirty (C : Circuit)
    (ao : IsAO2 26 C) (correct : circuitFun 26 C = graphFun plane ∅)
    (fixed : IsLiftFixedPoint plane C)
    (live : ∀ k < C.gates.length, InOutputCone 26 C k)
    (operands : OneDirtyReduction.NoSoundOperands plane C)
    (small : C.size ≤ 63) :
    ∃ i j : ℕ, i < C.gates.length ∧ j < C.gates.length ∧ i ≠ j ∧
      (gateAt C i).op = GateOp.and ∧ (gateAt C j).op = GateOp.and ∧
      ¬ BelowF plane C i ∧ ¬ BelowF plane C j := by
  classical
  by_contra h
  have one : ∀ i < C.gates.length, ∀ j < C.gates.length,
      (gateAt C i).op = GateOp.and → (gateAt C j).op = GateOp.and →
      ¬ BelowF plane C i → ¬ BelowF plane C j → i = j := by
    intro i hi j hj ha hb hd he
    by_contra hne
    exact h ⟨i, j, hi, hj, hne, ha, hb, hd, he⟩
  have bound := normalized_at_most_one_dirty_lower C ao correct fixed live operands one
  omega

end PEqualNP.Outside.L_meta_2056_aux.TwoDirty
