import PNPAccepted6659
namespace PEqualNP.Outside.L_meta_6659_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def surgery_binaryCount (gs : List Gate) : ℕ :=
  (gs.filter (fun g => decide (2 ≤ g.inputs.length))).length

lemma surgery_binaryCount_cons (g : Gate) (gs : List Gate) :
    surgery_binaryCount (g :: gs) =
      surgery_binaryCount gs + if 2 ≤ g.inputs.length then 1 else 0 := by
  by_cases h : 2 ≤ g.inputs.length <;> simp [surgery_binaryCount,h]

lemma surgery_step_count (n : ℕ) (st : List Ref × Dag) (g : Gate) :
    (na_step n st g).2.length ≤
      st.2.length + if 2 ≤ g.inputs.length then 1 else 0 := by
  cases h : g.inputs with
  | nil => simp [na_step,h]
  | cons a rest =>
    cases rest with
    | nil => simp [na_step,h]
    | cons b rest =>
      simp only [na_step,h]
      split <;> simp

lemma surgery_fold_count (n : ℕ) (gs : List Gate) (st : List Ref × Dag) :
    (gs.foldl (na_step n) st).2.length ≤ st.2.length + surgery_binaryCount gs := by
  induction gs generalizing st with
  | nil => simp [surgery_binaryCount]
  | cons g gs ih =>
    have step := surgery_step_count n st g
    have tail := ih (na_step n st g)
    rw [List.foldl_cons,surgery_binaryCount_cons]
    omega

lemma surgery_binaryCount_le (gs : List Gate) : surgery_binaryCount gs ≤ gs.length := by
  induction gs with
  | nil => simp [surgery_binaryCount]
  | cons g gs ih =>
    rw [surgery_binaryCount_cons,List.length_cons]
    split <;> omega

lemma surgery_binaryCount_lt (gs : List Gate)
    (short : ∃ g ∈ gs, g.inputs.length ≤ 1) : surgery_binaryCount gs < gs.length := by
  induction gs with
  | nil => simp at short
  | cons g gs ih =>
    rw [surgery_binaryCount_cons,List.length_cons]
    by_cases hg : 2 ≤ g.inputs.length
    · have hs : ∃ k ∈ gs, k.inputs.length ≤ 1 := by
        obtain ⟨k,hk,hlen⟩ := short
        rcases List.mem_cons.mp hk with rfl | hk
        · omega
        · exact ⟨k,hk,hlen⟩
      have := ih hs
      simp only [hg,ite_true]
      omega
    · have := surgery_binaryCount_le gs
      simp only [hg,ite_false]
      omega

lemma surgery_strict_of_monotone2 {n : ℕ} (C : Circuit) (hmono : Monotone2 C) :
    (∃ b : Bool, ∀ x : Fin n → Bool, C.eval (List.ofFn x) = b) ∨
    (∃ i : Fin n, ∀ x : Fin n → Bool, C.eval (List.ofFn x) = x i) ∨
    (∃ D : Dag, Strict n D ∧ D ≠ [] ∧ D.length ≤ surgery_binaryCount C.gates ∧
      ∀ x : Fin n → Bool, val D x (outW n D) = C.eval (List.ofFn x)) := by
  have h0 : na_Good n ((List.range n).map Sum.inr, ([] : Dag)) := by
    refine ⟨fun j hj => absurd hj (by simp),?_⟩
    intro r hr
    simp only [List.mem_map,List.mem_range] at hr
    obtain ⟨k,hk,rfl⟩ := hr
    simpa [na_ok] using hk
  obtain ⟨⟨hS,hok⟩,_,hsem⟩ := na_fold_spec n C.gates hmono _ h0
  have hcost := surgery_fold_count n C.gates ((List.range n).map Sum.inr, ([] : Dag))
  generalize C.gates.foldl (na_step n) ((List.range n).map Sum.inr, ([] : Dag)) = st
    at hS hok hsem hcost
  obtain ⟨m,D⟩ := st
  dsimp only at hS hok hsem hcost
  have hev : ∀ x : Fin n → Bool,
      C.eval (List.ofFn x) = refVal (wl D (List.ofFn x)) (na_look m C.output) := by
    intro x
    rw [na_look_val,hsem x (List.ofFn x) (na_init n x)]
    rfl
  have hk := na_look_ok _ m hok C.output
  rcases hr : na_look m C.output with b | k
  · exact Or.inl ⟨b,fun x => by rw [hev x,hr]; rfl⟩
  · rw [hr] at hk
    have hk' : k < n + D.length := hk
    by_cases hkn : k < n
    · exact Or.inr (Or.inl ⟨⟨k,hkn⟩,fun x => by rw [hev x,hr]; exact val_input D x k hkn⟩)
    · have hl : (D.take (k-n+1)).length = k-n+1 := by
        rw [List.length_take]
        omega
      refine Or.inr (Or.inr ⟨D.take (k-n+1),na_strict_take hS _,?_,?_,fun x => ?_⟩)
      · intro h
        rw [h] at hl
        simp at hl
      · rw [hl]
        simp only [List.length_nil,Nat.zero_add] at hcost
        omega
      · have ho : outW n (D.take (k-n+1)) = k := by unfold outW; rw [hl]; omega
        rw [ho,val_take D x (k-n+1) k (by omega) (by omega),hev x,hr]
        rfl

lemma surgery_one_short_gate {n : ℕ} (C : Circuit) (hmono : Monotone2 C)
    (short : ∃ g ∈ C.gates, g.inputs.length ≤ 1) :
    (∃ b : Bool, ∀ x : Fin n → Bool, C.eval (List.ofFn x) = b) ∨
    (∃ i : Fin n, ∀ x : Fin n → Bool, C.eval (List.ofFn x) = x i) ∨
    (∃ D : Dag, Strict n D ∧ D ≠ [] ∧ D.length < C.size ∧
      ∀ x : Fin n → Bool, val D x (outW n D) = C.eval (List.ofFn x)) := by
  rcases surgery_strict_of_monotone2 C hmono with constant | input | ⟨D,hS,hne,hlen,hval⟩
  · exact Or.inl constant
  · exact Or.inr (Or.inl input)
  · exact Or.inr (Or.inr ⟨D,hS,hne,lt_of_le_of_lt hlen (surgery_binaryCount_lt _ short),hval⟩)

end PEqualNP.Outside.L_meta_6659_aux
