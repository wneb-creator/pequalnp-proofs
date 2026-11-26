import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4970

namespace SeparatingTrace

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

abbrev Test (n : ℕ) := (Fin n → Bool) → Prop

def binary (b : Bool) (u v : ℕ) : Gate :=
  ⟨if b then .and else .or, [u, v]⟩

def combine {n} (b : Bool) (p q : Test n) : Test n :=
  fun x => if b then p x ∧ q x else p x ∨ q x

def step (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (n : ℕ) (gs : List Gate) (i : ℕ) : Test n :=
  fun x => ((gs.foldl step (List.ofFn x)).getD i false) = true

lemma length_fold (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [List.foldl, ih, step]; omega

lemma old_wire {n gs i} (hi : i < n + gs.length) (g : Gate) :
    W n (gs ++ [g]) i = W n gs i := by
  funext x
  have hl := length_fold gs (List.ofFn x)
  simp only [List.length_ofFn] at hl
  simp [W, List.foldl_append, step, List.getD, List.getElem?_append_left (hl ▸ hi : i < (gs.foldl step (List.ofFn x)).length)]

lemma new_wire (n) (gs : List Gate) (b u v) :
    W n (gs ++ [binary b u v]) (n + gs.length) =
      combine b (W n gs u) (W n gs v) := by
  funext x
  have hl := length_fold gs (List.ofFn x)
  simp only [List.length_ofFn] at hl
  cases b <;> simp [W, List.foldl_append, step, binary, GateOp.eval, combine,
    ← hl, List.getD]

def Layout (n : ℕ) (gs : List Gate) : Prop :=
  ∀ i (hi : i < gs.length), ∃ b u v, gs[i] = binary b u v ∧ u < n+i ∧ v < n+i

lemma layout_of {n} {C : Circuit} (h : IsAO2 n C) : Layout n C.gates := by
  intro i hi
  have hm := List.getElem_mem (l := C.gates) hi
  obtain ⟨u,v, huv⟩ := List.length_eq_two.mp (h.2.2 _ hm)
  have hat : gateAt C i = C.gates[i] := by simp [gateAt, List.getD, hi]
  have hr := h.2.1 i hi
  rw [hat, huv] at hr
  obtain ho | ho := h.1 _ hm
  · exact ⟨true,u,v, by cases hg : C.gates[i] with | mk o l => simp_all [binary],
      hr u (by simp), hr v (by simp)⟩
  · exact ⟨false,u,v, by cases hg : C.gates[i] with | mk o l => simp_all [binary],
      hr u (by simp), hr v (by simp)⟩

lemma old_wire_append {n : ℕ} (gs hs : List Gate) {i : ℕ}
    (hi : i < n + gs.length) : W n (gs ++ hs) i = W n gs i := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, old_wire (by simp; omega), ih]

lemma orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [PEqualNP.CleanedNonEdge.orStep]
    omega

lemma orSets_length (n : ℕ) (C : Circuit) :
    (PEqualNP.CleanedNonEdge.orSets n C).length = C.gates.length := by
  unfold PEqualNP.CleanedNonEdge.orSets
  rw [orSets_len]; simp

lemma orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (PEqualNP.CleanedNonEdge.orStep n (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD k [] =
          (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD k [] := by
      intro k hk
      simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
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
      · have e2 : (PEqualNP.CleanedNonEdge.orStep n
            (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD (w - n) []) := by
          simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
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
      · have e2 : (PEqualNP.CleanedNonEdge.orStep n
            (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
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
    · have e0 : (PEqualNP.CleanedNonEdge.orStep n
          (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD j [] = [] := by
        simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma orSets_mem_iff (n : ℕ) (C : Circuit) (k x : ℕ) (hk : k < C.gates.length) :
    x ∈ (PEqualNP.CleanedNonEdge.orSets n C).getD k [] ↔ x = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
        x ∈ (PEqualNP.CleanedNonEdge.orSets n C).getD (w - n) []) := by
  have h := orSets_char n C.gates x k
  unfold PEqualNP.CleanedNonEdge.orSets gateAt
  rw [h]
  constructor
  · rintro ⟨_, h3⟩; exact h3
  · intro h3; exact ⟨hk, h3⟩

lemma orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    PEqualNP.CleanedNonEdge.OrReaches n C (n + k) g ↔ k < C.gates.length ∧
      (g = k ∨ ((gateAt C k).op = GateOp.or ∧
        ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ PEqualNP.CleanedNonEdge.OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold PEqualNP.CleanedNonEdge.OrReaches PEqualNP.CleanedNonEdge.orSets gateAt
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

lemma orReaches_self (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    PEqualNP.CleanedNonEdge.OrReaches n C (n + j) j :=
  (orReaches_iff n C j j).mpr ⟨hj, Or.inl rfl⟩

lemma orReaches_step (n : ℕ) (C : Circuit) (j i g : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hi : i ∈ (gateAt C j).inputs) (hlt : i < n + j)
    (h : PEqualNP.CleanedNonEdge.OrReaches n C i g) :
    PEqualNP.CleanedNonEdge.OrReaches n C (n + j) g :=
  (orReaches_iff n C j g).mpr ⟨hj, Or.inr ⟨hop, i, hi, hlt, h⟩⟩

lemma orReaches_bound (n : ℕ) (C : Circuit) (g : ℕ) :
    ∀ w : ℕ, PEqualNP.CleanedNonEdge.OrReaches n C w g → n + g ≤ w ∧ w < n + C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hr
    have hnw : n ≤ w := hr.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp hr
    rcases h3 with h3 | ⟨_, i, _, hlt, hri⟩
    · omega
    · have := ih i hlt hri
      omega

lemma orReaches_trans (n : ℕ) (C : Circuit) (k g : ℕ) (hkg : PEqualNP.CleanedNonEdge.OrReaches n C (n + k) g) :
    ∀ w : ℕ, PEqualNP.CleanedNonEdge.OrReaches n C w k → PEqualNP.CleanedNonEdge.OrReaches n C w g := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hr
    have hnw : n ≤ w := hr.1
    obtain ⟨m, rfl⟩ : ∃ m, w = n + m := ⟨w - n, by omega⟩
    obtain ⟨hm, h3⟩ := (orReaches_iff n C m k).mp hr
    rcases h3 with h3 | ⟨hop, i, hi, hlt, hri⟩
    · rw [← h3]; exact hkg
    · exact orReaches_step n C m i g hm hop hi hlt (ih i hlt hri)

lemma orIn_mem_filter {α : Type} (p : α → Prop) (d : DecidablePred p) (s : Finset α) (a : α) :
    a ∈ @Finset.filter α p d s ↔ a ∈ s ∧ p a :=
  @Finset.mem_filter α p d s a

lemma mem_orIn (n : ℕ) (C : Circuit) (w : ℕ) (i : Fin n) :
    i ∈ PEqualNP.TopForm.orIn n C w ↔ ((i : ℕ) = w ∨ ∃ k < C.gates.length,
      PEqualNP.CleanedNonEdge.OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧
        (i : ℕ) ∈ (gateAt C k).inputs) := by
  unfold PEqualNP.TopForm.orIn
  exact ⟨fun h => ((orIn_mem_filter _ _ _ _).1 h).2,
    fun h => (orIn_mem_filter _ _ _ _).2 ⟨Finset.mem_univ _, h⟩⟩

lemma orIn_self (n : ℕ) (C : Circuit) (i : Fin n) : i ∈ PEqualNP.TopForm.orIn n C i :=
  (mem_orIn n C i i).mpr (Or.inl rfl)

lemma orIn_up (n : ℕ) (C : Circuit) (j i : ℕ) (a : Fin n) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hi : i ∈ (gateAt C j).inputs) (hlt : i < n + j)
    (h : a ∈ PEqualNP.TopForm.orIn n C i) : a ∈ PEqualNP.TopForm.orIn n C (n + j) := by
  rw [mem_orIn] at h ⊢
  right
  rcases h with h | ⟨k, hk, hr, hopk, hin⟩
  · exact ⟨j, hj, orReaches_self n C j hj, hop, by rw [h]; exact hi⟩
  · exact ⟨k, hk, orReaches_step n C j i k hj hop hi hlt hr, hopk, hin⟩


lemma orIn_input (n : ℕ) (C : Circuit) (w : ℕ) (hw : w < n) :
    orIn n C w = {⟨w, hw⟩} := by
  ext i
  rw [mem_orIn, Finset.mem_singleton]
  constructor
  · rintro (he | ⟨j, hj, hr, ho, hi⟩)
    · exact Fin.ext he
    · have := hr.1
      omega
  · intro he
    exact Or.inl (congrArg Fin.val he)

lemma orIn_gate (n : ℕ) (C : Circuit) (hC : ReadsBack n C)
    (j : ℕ) (hj : j < C.gates.length) :
    orIn n C (n + j) = @ite (Finset (Fin n)) ((gateAt C j).op = .or) (Classical.propDecidable _)
      ((gateAt C j).inputs.toFinset.biUnion (orIn n C)) ∅ := by
  classical
  ext a
  rw [mem_orIn]
  by_cases hop : (gateAt C j).op = .or
  · simp only [hop, ↓reduceIte, Finset.mem_biUnion]
    constructor
    · rintro (he | ⟨k, hk, hr, hok, hai⟩)
      · have := a.isLt
        omega
      · rcases (orReaches_iff n C j k).mp hr with ⟨_, he | ⟨_, w, hw, hlt, hrw⟩⟩
        · subst k
          exact ⟨a.val, List.mem_toFinset.mpr hai, orIn_self n C a⟩
        · exact ⟨w, List.mem_toFinset.mpr hw,
            (mem_orIn n C w a).mpr (Or.inr ⟨k, hk, hrw, hok, hai⟩)⟩
    · rintro ⟨w, hw, haw⟩
      have hw' := List.mem_toFinset.mp hw
      exact (mem_orIn n C (n+j) a).mp
        (orIn_up n C j w a hj hop hw' (hC j hj w hw') haw)
  · simp only [hop, ↓reduceIte]
    simp only [Finset.notMem_empty, iff_false]
    rintro (he | ⟨k, hk, hr, hok, hai⟩)
    · have := a.isLt
      omega
    · rcases (orReaches_iff n C j k).mp hr with ⟨_, he | ⟨ho, _⟩⟩
      · subst k
        exact hop hok
      · exact hop ho

lemma W_input {n : ℕ} (gs : List Gate) (i : Fin n) (x : Fin n → Bool) :
    W n gs i x ↔ x i = true := by
  change W n ([] ++ gs) i x ↔ x i = true
  rw [old_wire_append [] gs i.isLt]
  simp [W, List.getD]

lemma W_gate {n : ℕ} {C : Circuit} (hC : IsAO2 n C) (j : ℕ)
    (hj : j < C.gates.length) :
    ∃ b u v, gateAt C j = binary b u v ∧ u < n + j ∧ v < n + j ∧
      W n C.gates (n+j) = combine b (W n C.gates u) (W n C.gates v) := by
  obtain ⟨b,u,v,hg,hu,hv⟩ := layout_of hC j hj
  refine ⟨b,u,v,by simpa [gateAt,List.getD,hj] using hg,hu,hv,?_⟩
  have hlen : (C.gates.take j).length = j := by simp [List.length_take, Nat.min_eq_left hj.le]
  have hsplit : C.gates = (C.gates.take j ++ [binary b u v]) ++ C.gates.drop (j+1) := by
    rw [← hg, List.append_assoc]
    rw [List.singleton_append, ← List.drop_eq_getElem_cons hj, List.take_append_drop]
  have hroot : W n C.gates (n+j) = W n (C.gates.take j ++ [binary b u v]) (n+j) := by
    conv_lhs => rw [hsplit]
    exact old_wire_append _ _ (by simp [hlen])
  have hchild (w : ℕ) (hw : w < n+j) : W n C.gates w = W n (C.gates.take j) w := by
    conv_lhs => rw [← List.take_append_drop j C.gates]
    exact old_wire_append _ _ (by simpa [hlen] using hw)
  have hnew := new_wire n (C.gates.take j) b u v
  rw [hlen] at hnew
  rw [hroot, hnew, ← hchild u hu, ← hchild v hv]

lemma separating_trace {n : ℕ} (C : Circuit) (hC : IsAO2 n C)
    (x y : Fin n → Bool) :
    ∀ w, w < n + C.gates.length → W n C.gates w x → ¬ W n C.gates w y →
      ∃ i : Fin n, x i = true ∧ y i = false ∧
        (i ∈ orIn n C w ∨ ∃ j < C.gates.length,
          (gateAt C j).op = .and ∧ ∃ z ∈ (gateAt C j).inputs,
            i ∈ orIn n C z ∧ ¬ W n C.gates z y) := by
  classical
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hx hy
    by_cases hin : w < n
    · let i : Fin n := ⟨w, hin⟩
      have hix : x i = true := (W_input C.gates i x).mp hx
      have hiy : y i = false := by
        cases h : y i with
        | false => rfl
        | true => exact False.elim (hy ((W_input C.gates i y).mpr h))
      exact ⟨i, hix, hiy, Or.inl (orIn_self n C i)⟩
    · obtain ⟨j, rfl⟩ : ∃ j, w = n+j := ⟨w-n, by omega⟩
      have hj : j < C.gates.length := by omega
      obtain ⟨b,u,v,hgate,hu,hv,heval⟩ := W_gate hC j hj
      have choose_child : ∃ z, z ∈ [u,v] ∧ z < n+j ∧
          W n C.gates z x ∧ ¬ W n C.gates z y := by
        rw [heval] at hx hy
        cases b with
        | false =>
          have hxx : W n C.gates u x ∨ W n C.gates v x := by simpa [combine] using hx
          have hyy : ¬ W n C.gates u y ∧ ¬ W n C.gates v y := by
            simpa [combine, not_or] using hy
          rcases hxx with h | h
          · exact ⟨u, by simp, hu, h, hyy.1⟩
          · exact ⟨v, by simp, hv, h, hyy.2⟩
        | true =>
          have hxx : W n C.gates u x ∧ W n C.gates v x := by simpa [combine] using hx
          have hyy : ¬ W n C.gates u y ∨ ¬ W n C.gates v y :=
            not_and_or.mp (by simpa [combine] using hy)
          rcases hyy with h | h
          · exact ⟨u, by simp, hu, hxx.1, h⟩
          · exact ⟨v, by simp, hv, hxx.2, h⟩
      obtain ⟨z,hzm,hzlt,hzx,hzy⟩ := choose_child
      obtain ⟨i,hix,hiy,hraw | hslot⟩ := ih z hzlt (hzlt.trans hw) hzx hzy
      · refine ⟨i,hix,hiy,?_⟩
        have hmem : z ∈ (gateAt C j).inputs := by simpa [hgate,binary] using hzm
        cases b with
        | false =>
          exact Or.inl (orIn_up n C j z i hj (by simp [hgate,binary]) hmem hzlt hraw)
        | true =>
          exact Or.inr ⟨j,hj,by simp [hgate,binary],z,hmem,hraw,hzy⟩
      · exact ⟨i,hix,hiy,Or.inr hslot⟩

lemma orIn_semantics {n : ℕ} (C : Circuit) (hC : IsAO2 n C)
    (x : Fin n → Bool) :
    ∀ w, w < n + C.gates.length → ∀ i ∈ orIn n C w,
      x i = true → W n C.gates w x := by
  classical
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw i hi hix
    by_cases hin : w < n
    · rw [orIn_input n C w hin, Finset.mem_singleton] at hi
      subst i
      exact (W_input C.gates ⟨w,hin⟩ x).mpr hix
    · obtain ⟨j,rfl⟩ : ∃ j, w = n+j := ⟨w-n,by omega⟩
      have hj : j < C.gates.length := by omega
      obtain ⟨b,u,v,hgate,hu,hv,heval⟩ := W_gate hC j hj
      have hr := orIn_gate n C hC.2.1 j hj
      rw [hr] at hi
      cases b with
      | true => simp [hgate,binary] at hi
      | false =>
        have hmem : i ∈ orIn n C u ∨ i ∈ orIn n C v := by
          simpa [hgate,binary] using hi
        rw [heval]
        change W n C.gates u x ∨ W n C.gates v x
        exact hmem.elim
          (fun h => Or.inl (ih u hu (hu.trans hw) i h hix))
          (fun h => Or.inr (ih v hv (hv.trans hw) i h hix))

lemma separating_slot {n : ℕ} (C : Circuit) (hC : IsAO2 n C)
    (x y : Fin n → Bool) (i : Fin n) (w : ℕ)
    (hw : w < n + C.gates.length)
    (hx : W n C.gates w x) (hy : ¬ W n C.gates w y)
    (hunique : ∀ k, x k = true → y k = false → k = i)
    (hsingle : ¬ W n C.gates w (fun k => decide (k = i))) :
    ∃ j < C.gates.length, (gateAt C j).op = .and ∧
      ∃ z ∈ (gateAt C j).inputs, i ∈ orIn n C z ∧ ¬ W n C.gates z y := by
  obtain ⟨k,hkx,hky,hraw | hslot⟩ := separating_trace C hC x y w hw hx hy
  · have hki := hunique k hkx hky
    subst k
    exact False.elim (hsingle (orIn_semantics C hC _ w hw i hraw (by simp)))
  · exact hunique k hkx hky ▸ hslot

lemma slot_members_false {n : ℕ} (C : Circuit) (hC : IsAO2 n C)
    (y : Fin n → Bool) (z : ℕ) (hz : z < n + C.gates.length)
    (hfalse : ¬ W n C.gates z y) : ∀ i ∈ orIn n C z, y i = false := by
  intro i hi
  cases h : y i with
  | false => rfl
  | true => exact False.elim (hfalse (orIn_semantics C hC y z hz i hi h))

lemma orIn_colour_equal {n : ℕ} (C : Circuit) (hC : IsAO2 n C)
    (colour : ℕ → Bool) (hT : PEqualNP.TwoColour.tCount n C colour = 0)
    (w : ℕ) (hw : w < n + C.gates.length)
    (i k : Fin n) (hi : i ∈ orIn n C w) (hk : k ∈ orIn n C w) :
    colour i = colour k := by
  classical
  by_cases hin : w < n
  · rw [orIn_input n C w hin, Finset.mem_singleton] at hi hk
    rw [hi, hk]
  · obtain ⟨j,rfl⟩ : ∃ j, w = n+j := ⟨w-n,by omega⟩
    have hj : j < C.gates.length := by omega
    have hor : (gateAt C j).op = .or := by
      by_contra hop
      rw [orIn_gate n C hC.2.1 j hj] at hi
      simp [hop] at hi
    have hempty : PEqualNP.TwoColour.twoColour n C colour = ∅ :=
      Finset.card_eq_zero.mp hT
    have hnone : ¬ PEqualNP.TwoColour.IsTwoColour n C colour j := by
      intro hm
      have hmem : j ∈ PEqualNP.TwoColour.twoColour n C colour :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hm⟩
      rw [hempty] at hmem
      exact Finset.notMem_empty _ hmem
    cases hci : colour i <;> cases hck : colour k
    · rfl
    · exact False.elim (hnone ⟨hj,hor,⟨i,hi,hci⟩,⟨k,hk,hck⟩⟩)
    · exact False.elim (hnone ⟨hj,hor,⟨k,hk,hck⟩,⟨i,hi,hci⟩⟩)
    · rfl

def operand (C : Circuit) (j : ℕ) (s : Fin 2) : ℕ :=
  (gateAt C j).inputs.getD s 0

lemma operand_mem {n : ℕ} (C : Circuit) (hC : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) (s : Fin 2) :
    operand C j s ∈ (gateAt C j).inputs := by
  have heq : gateAt C j = C.gates[j] := by simp [gateAt,List.getD,hj]
  have hlen : (gateAt C j).inputs.length = 2 := by
    rw [heq]
    exact hC.2.2 _ (List.getElem_mem hj)
  have hs : s.val < (gateAt C j).inputs.length := by simpa [hlen] using s.isLt
  simp [operand,List.getD,hs]

lemma operand_lt {n : ℕ} (C : Circuit) (hC : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) (s : Fin 2) :
    operand C j s < n + j :=
  hC.2.1 j hj _ (operand_mem C hC j hj s)

lemma separating_indexed_slot {n : ℕ} (C : Circuit) (hC : IsAO2 n C)
    (x y : Fin n → Bool) (i : Fin n) (w : ℕ)
    (hw : w < n + C.gates.length)
    (hx : W n C.gates w x) (hy : ¬ W n C.gates w y)
    (hunique : ∀ k, x k = true → y k = false → k = i)
    (hsingle : ¬ W n C.gates w (fun k => decide (k = i))) :
    ∃ j < C.gates.length, (gateAt C j).op = .and ∧
      ∃ s : Fin 2, operand C j s < n+j ∧
        i ∈ orIn n C (operand C j s) ∧ ¬ W n C.gates (operand C j s) y := by
  obtain ⟨j,hj,hop,z,hzm,hi,hfalse⟩ := separating_slot C hC x y i w hw hx hy hunique hsingle
  obtain ⟨k,hk,hkz⟩ := List.getElem_of_mem hzm
  have heq : gateAt C j = C.gates[j] := by simp [gateAt,List.getD,hj]
  have hlen : (gateAt C j).inputs.length = 2 := by
    rw [heq]
    exact hC.2.2 _ (List.getElem_mem hj)
  let s : Fin 2 := ⟨k,by omega⟩
  have hs : operand C j s = z := by simp [operand,List.getD,s,hk,hkz]
  refine ⟨j,hj,hop,s,operand_lt C hC j hj s,?_,?_⟩
  · simpa [hs] using hi
  · simpa [hs] using hfalse

end SeparatingTrace

namespace StrongTrace
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4970.SeparatingTrace

lemma and_operand_true {n : ℕ} (C : Circuit) (hC : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = .and)
    (x : Fin n → Bool) (hpos : W n C.gates (n+j) x) (s : Fin 2) :
    W n C.gates (operand C j s) x := by
  obtain ⟨b,u,v,hgate,hu,hv,heval⟩ := W_gate hC j hj
  have hb : b = true := by cases b <;> simp_all [binary]
  subst b
  have hboth : W n C.gates u x ∧ W n C.gates v x := by
    rw [heval] at hpos
    simpa [combine] using hpos
  have hs : operand C j s = u ∨ operand C j s = v := by
    simpa [hgate, binary] using operand_mem C hC j hj s
  exact hs.elim (fun h => h.symm ▸ hboth.1) (fun h => h.symm ▸ hboth.2)

end StrongTrace

namespace H3BoundedTrace

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4970.SeparatingTrace

lemma separating_trace_bounded {n : ℕ} (C : Circuit) (hC : IsAO2 n C)
    (x y : Fin n → Bool) :
    ∀ w, w < n + C.gates.length → W n C.gates w x → ¬ W n C.gates w y →
      ∃ i : Fin n, x i = true ∧ y i = false ∧
        (i ∈ orIn n C w ∨ ∃ j < C.gates.length,
          (gateAt C j).op = .and ∧ n+j ≤ w ∧ W n C.gates (n+j) x ∧
          ∃ z ∈ (gateAt C j).inputs,
            i ∈ orIn n C z ∧ ¬ W n C.gates z y) := by
  classical
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hx hy
    by_cases hin : w < n
    · let i : Fin n := ⟨w, hin⟩
      have hix : x i = true := (W_input C.gates i x).mp hx
      have hiy : y i = false := by
        cases h : y i with
        | false => rfl
        | true => exact False.elim (hy ((W_input C.gates i y).mpr h))
      exact ⟨i, hix, hiy, Or.inl (orIn_self n C i)⟩
    · obtain ⟨j, rfl⟩ : ∃ j, w = n+j := ⟨w-n, by omega⟩
      have hj : j < C.gates.length := by omega
      obtain ⟨b,u,v,hgate,hu,hv,heval⟩ := W_gate hC j hj
      have choose_child : ∃ z, z ∈ [u,v] ∧ z < n+j ∧
          W n C.gates z x ∧ ¬ W n C.gates z y := by
        rw [heval] at hx hy
        cases b with
        | false =>
          have hxx : W n C.gates u x ∨ W n C.gates v x := by
            simpa [combine] using hx
          have hyy : ¬ W n C.gates u y ∧ ¬ W n C.gates v y := by
            simpa [combine, not_or] using hy
          rcases hxx with h | h
          · exact ⟨u, by simp, hu, h, hyy.1⟩
          · exact ⟨v, by simp, hv, h, hyy.2⟩
        | true =>
          have hxx : W n C.gates u x ∧ W n C.gates v x := by
            simpa [combine] using hx
          have hyy : ¬ W n C.gates u y ∨ ¬ W n C.gates v y :=
            not_and_or.mp (by simpa [combine] using hy)
          rcases hyy with h | h
          · exact ⟨u, by simp, hu, hxx.1, h⟩
          · exact ⟨v, by simp, hv, hxx.2, h⟩
      obtain ⟨z,hzm,hzlt,hzx,hzy⟩ := choose_child
      obtain ⟨i,hix,hiy,hraw | hslot⟩ := ih z hzlt (hzlt.trans hw) hzx hzy
      · refine ⟨i,hix,hiy,?_⟩
        have hmem : z ∈ (gateAt C j).inputs := by simpa [hgate,binary] using hzm
        cases b with
        | false =>
          exact Or.inl (orIn_up n C j z i hj (by simp [hgate,binary]) hmem hzlt hraw)
        | true =>
          exact Or.inr ⟨j,hj,by simp [hgate,binary],le_rfl,hx,z,hmem,hraw,hzy⟩
      · obtain ⟨k,hk,hop,hkz,hpos,u,hum,hraw,hneg⟩ := hslot
        exact ⟨i,hix,hiy,Or.inr
          ⟨k,hk,hop,hkz.trans hzlt.le,hpos,u,hum,hraw,hneg⟩⟩

/-- Strong raw-slot eligibility, with no retained path-to-output hypothesis. -/
def Eligible {n : ℕ} (C : Circuit) (x y : Fin n → Bool)
    (i : Fin n) (j : ℕ) (s : Fin 2) : Prop :=
  j < C.gates.length ∧ (gateAt C j).op = .and ∧
    W n C.gates (n+j) x ∧ i ∈ orIn n C (operand C j s) ∧
    ¬ W n C.gates (operand C j s) y

lemma eligible_parent_false {n : ℕ} (C : Circuit) (hC : IsAO2 n C)
    (x y : Fin n → Bool) (i : Fin n) (j : ℕ) (s : Fin 2)
    (he : Eligible C x y i j s) : ¬ W n C.gates (n+j) y := by
  intro hy
  exact he.2.2.2.2 (StrongTrace.and_operand_true C hC j he.1 he.2.1 y hy s)

lemma raw_or_eligible_bounded {n : ℕ} (C : Circuit) (hC : IsAO2 n C)
    (x y : Fin n → Bool) (i : Fin n)
    (hunique : ∀ k, x k = true → y k = false → k = i)
    (w : ℕ) (hw : w < n + C.gates.length)
    (hx : W n C.gates w x) (hy : ¬ W n C.gates w y) :
    i ∈ orIn n C w ∨ ∃ j s, n+j ≤ w ∧ Eligible C x y i j s := by
  obtain ⟨k,hkx,hky,hraw | hslot⟩ := separating_trace_bounded C hC x y w hw hx hy
  · exact Or.inl (hunique k hkx hky ▸ hraw)
  · obtain ⟨j,hj,hop,hjw,hpos,z,hzm,hr,hneg⟩ := hslot
    obtain ⟨t,ht,htz⟩ := List.getElem_of_mem hzm
    have heq : gateAt C j = C.gates[j] := by simp [gateAt,List.getD,hj]
    have hlen : (gateAt C j).inputs.length = 2 := by
      rw [heq]
      exact hC.2.2 _ (List.getElem_mem hj)
    let s : Fin 2 := ⟨t,by omega⟩
    have hs : operand C j s = z := by simp [operand,List.getD,s,ht,htz]
    refine Or.inr ⟨j,s,hjw,hj,hop,hpos,?_,?_⟩
    · simpa [hs,hunique k hkx hky] using hr
    · simpa [hs] using hneg

lemma eligible_before_distinguishing_and {n : ℕ} (C : Circuit) (hC : IsAO2 n C)
    (x y : Fin n → Bool) (i : Fin n)
    (hunique : ∀ k, x k = true → y k = false → k = i)
    (j : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = .and)
    (hx : W n C.gates (n+j) x) (hy : ¬ W n C.gates (n+j) y) :
    ∃ k s, k ≤ j ∧ Eligible C x y i k s := by
  obtain hraw | ⟨k,s,hkw,he⟩ := raw_or_eligible_bounded C hC x y i hunique
    (n+j) (by omega) hx hy
  · rw [orIn_gate n C hC.2.1 j hj] at hraw
    simp [hop] at hraw
  · exact ⟨k,s,by omega,he⟩

/-- Uniqueness of strong eligibility makes its gate the first AND
    distinguishing the positive assignment from the chosen negative baseline. -/
lemma earlier_and_true_on_baseline {n : ℕ} (C : Circuit) (hC : IsAO2 n C)
    (x y : Fin n → Bool) (i : Fin n)
    (hunique : ∀ k, x k = true → y k = false → k = i)
    (g : ℕ) (t : Fin 2)
    (hslot : ∀ k s, Eligible C x y i k s → k = g ∧ s = t)
    (j : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = .and)
    (hjg : j < g) (hx : W n C.gates (n+j) x) :
    W n C.gates (n+j) y := by
  by_contra hy
  obtain ⟨k,s,hkj,he⟩ := eligible_before_distinguishing_and C hC x y i hunique
    j hj hop hx hy
  have hkg := (hslot k s he).1
  omega

/-- At the unique eligible gate the other operand is true on the baseline. -/
lemma other_operand_true_on_baseline {n : ℕ} (C : Circuit) (hC : IsAO2 n C)
    (x y : Fin n → Bool) (i : Fin n)
    (hunique : ∀ k, x k = true → y k = false → k = i)
    (g : ℕ) (t : Fin 2) (hg : Eligible C x y i g t)
    (hslot : ∀ k s, Eligible C x y i k s → k = g ∧ s = t)
    (s : Fin 2) (hst : s ≠ t) :
    W n C.gates (operand C g s) y := by
  by_contra hy
  have hslt := operand_lt C hC g hg.1 s
  have hsvalid : operand C g s < n + C.gates.length :=
    hslt.trans (Nat.add_lt_add_left hg.1 n)
  have hx := StrongTrace.and_operand_true C hC g hg.1 hg.2.1 x hg.2.2.1 s
  obtain hraw | ⟨k,u,hkw,he⟩ := raw_or_eligible_bounded C hC x y i hunique
    (operand C g s) hsvalid hx hy
  · have he : Eligible C x y i g s := ⟨hg.1,hg.2.1,hg.2.2.1,hraw,hy⟩
    exact hst (hslot g s he).2
  · have hkg := (hslot k u he).1
    omega

end H3BoundedTrace


end PEqualNP.Outside.L_meta_4970
