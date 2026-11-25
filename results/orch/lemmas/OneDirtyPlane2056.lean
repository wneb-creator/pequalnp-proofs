import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2056_aux.OneDirtyReduction.Support

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

end PEqualNP.Outside.L_meta_2056_aux.OneDirtyReduction.Support


namespace PEqualNP.Outside.L_meta_2056_aux.OneDirtyReduction
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

end PEqualNP.Outside.L_meta_2056_aux.OneDirtyReduction

namespace PEqualNP.Outside.L_meta_2056_aux.OneDirtyReduction
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.SplitCount
  PEqualNP.Core PEqualNP.Outside.L_meta_2056_aux.OneDirtyReduction.Support

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

end PEqualNP.Outside.L_meta_2056_aux.OneDirtyReduction
namespace PEqualNP.Outside.L_meta_2056_aux.OneDirtyReduction
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.SplitCount
  PEqualNP.Core PEqualNP.Outside.L_meta_2056_aux.OneDirtyReduction.Support
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

end PEqualNP.Outside.L_meta_2056_aux.OneDirtyReduction
namespace PEqualNP.Outside.L_meta_2056_aux.OneDirtyReduction
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.SplitCount
  PEqualNP.Core PEqualNP.Outside.L_meta_2056_aux.OneDirtyReduction.Support

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

end PEqualNP.Outside.L_meta_2056_aux.OneDirtyReduction
namespace PEqualNP.Outside.L_meta_2056_aux.OneDirtyReduction
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.SplitCount
  PEqualNP.Core PEqualNP.Outside.L_meta_2056_aux.OneDirtyReduction.Support
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

end PEqualNP.Outside.L_meta_2056_aux.OneDirtyReduction
namespace PEqualNP.Outside.L_meta_2056_aux.OneDirtyReduction
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.SplitCount
  PEqualNP.Core PEqualNP.Outside.L_meta_2056_aux.OneDirtyReduction.Support
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

end PEqualNP.Outside.L_meta_2056_aux.OneDirtyReduction
namespace PEqualNP.Outside.L_meta_2056_aux.OneDirtyReduction
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.SplitCount
  PEqualNP.Core PEqualNP.Outside.L_meta_2056_aux.OneDirtyReduction.Support

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
end PEqualNP.Outside.L_meta_2056_aux.OneDirtyReduction
namespace PEqualNP.Outside.L_meta_2056_aux.OneDirtyReduction
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.SplitCount
  PEqualNP.Core PEqualNP.Outside.L_meta_2056_aux.OneDirtyReduction.Support

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

end PEqualNP.Outside.L_meta_2056_aux.OneDirtyReduction
namespace PEqualNP.Outside.L_meta_2056_aux.OneDirtyReduction
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.SplitCount
  PEqualNP.Core PEqualNP.Outside.L_meta_2056_aux.OneDirtyReduction.Support
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

end PEqualNP.Outside.L_meta_2056_aux.OneDirtyReduction
namespace PEqualNP.Outside.L_meta_2056_aux.OneDirtyReduction
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.SplitCount
  PEqualNP.Core PEqualNP.Outside.L_meta_2056_aux.OneDirtyReduction.Support
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

end PEqualNP.Outside.L_meta_2056_aux.OneDirtyReduction
namespace PEqualNP.Outside.L_meta_2056_aux.OneDirtyReduction
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.SplitCount
  PEqualNP.Core PEqualNP.Outside.L_meta_2056_aux.OneDirtyReduction.Support
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

end PEqualNP.Outside.L_meta_2056_aux.OneDirtyReduction
namespace PEqualNP.Outside.L_meta_2056_aux.OneDirtyReduction
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.SplitCount
  PEqualNP.Core PEqualNP.Outside.L_meta_2056_aux.OneDirtyReduction.Support
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

end PEqualNP.Outside.L_meta_2056_aux.OneDirtyReduction
namespace PEqualNP.Outside.L_meta_2056_aux.OneDirtyReduction
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.SplitCount
  PEqualNP.Core PEqualNP.Outside.L_meta_2056_aux.OneDirtyReduction.Support
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

end PEqualNP.Outside.L_meta_2056_aux.OneDirtyReduction
namespace PEqualNP.Outside.L_meta_2056_aux.OneDirtyReduction
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.SplitCount
  PEqualNP.Core PEqualNP.Outside.L_meta_2056_aux.OneDirtyReduction.Support
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

end PEqualNP.Outside.L_meta_2056_aux.OneDirtyReduction
namespace PEqualNP.Outside.L_meta_2056_aux.OneDirtyReduction
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.SplitCount
  PEqualNP.Core PEqualNP.Outside.L_meta_2056_aux.OneDirtyReduction.Support
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

end PEqualNP.Outside.L_meta_2056_aux.OneDirtyReduction

namespace PEqualNP.Outside.L_meta_2056_aux.FlatSumPlane

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

end PEqualNP.Outside.L_meta_2056_aux.FlatSumPlane


namespace PEqualNP.Outside.L_meta_2056_aux.OneDirtyPlane

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.Core
  PEqualNP.EdgeOwnership PEqualNP.SplitCount
open PEqualNP.Outside.L_meta_2056_aux.FlatSumPlane

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
  apply PEqualNP.Outside.L_meta_2056_aux.FlatSumPlane.main C ao
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
    (operands : PEqualNP.Outside.L_meta_2056_aux.OneDirtyReduction.NoSoundOperands plane C)
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
    have model : PEqualNP.Outside.L_meta_2056_aux.OneDirtyReduction.Model 26 plane C g :=
      ⟨ao, correct, fixed, live, operands, singleton, hg, ha, hn, clean⟩
    obtain ⟨D, hD, hs, hF, hflat⟩ :=
      PEqualNP.Outside.L_meta_2056_aux.OneDirtyReduction.complete model plane_no_four
        (fun u => decide (u.val < 13)) plane_bip
    exact (flat_lower D hD hF hflat).trans hs
  · apply flat_lower C ao correct
    intro i hi j hj ha hb hc
    have clean : BelowF plane C i := by
      by_contra h
      exact hd ⟨i, hi, ha, h⟩
    have ho := (PEqualNP.Outside.L_meta_2056_aux.OneDirtyReduction.sound_ancestor
      ao fixed live operands clean hj hc).1
    rw [hb] at ho
    cases ho

end PEqualNP.Outside.L_meta_2056_aux.OneDirtyPlane
