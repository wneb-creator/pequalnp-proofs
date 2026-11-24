import PEqualNP.MetaComplexity.L649
import PEqualNP.MetaComplexity.Helpers.LowMergeWires

/-!
# Theorem A at line-degree 3: card 09 (Statement R1), conjecture until checked

Card 09 of the line-degree-3 skeleton, from the recorded statements of L-meta-270, L-meta-669 and
L-meta-738 taken as hypotheses. `card09_R1_of` takes cards 07 (pruning) and 08 (an unreached
input is not read) as explicit hypotheses, statements verbatim from the skeleton; both cards are
proved here (`card07_prune`, `card08_unreached`), and `card09_R1` is the card with the statement
of the skeleton. No monotonicity card is used: the identity of L-meta-738 at one line missing a
point already makes the point-only part false at that point.
-/

namespace PEqualNP.MetaComplexity.Deg3
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-! ## Recorded statements taken as hypotheses (verbatim from the hub) -/

/-- The recorded statement of L-meta-270 (checked by an outside proof; not imported). -/
def H270 : Prop := ∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (S i).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true ↔ p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (S i).card) → ∑ i : Fin m, c i ≤ C.size

/-- The recorded statement of L-meta-669 (checked by an outside proof; not imported). -/
def H669 : Prop := ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (T Z : Finset (Fin n)), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (r : ℕ → ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ gates'.length ≤ gates.length ∧ ∀ o : ℕ, (∃ x y : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else y i))) → ∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', r o⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i))

/-- The recorded statement of L-meta-738 (Lemma TR; open). -/
def H738 : Prop := ∀ (P1 L1 : ℕ) (C1 : PEqualNP.CircuitLowerBounds.Circuit) (N1 : Finset (Fin L1)), PEqualNP.CircuitLowerBounds.IsMonotoneCircuit C1 → (∀ g1 ∈ C1.gates, g1.inputs.length ≤ 2) → PEqualNP.CircuitLowerBounds.HasLineDegree (P1 + L1) (Finset.Ico P1 (P1 + L1)) C1 1 → (∀ j1 : Fin C1.gates.length, Relation.ReflTransGen (fun a1 b1 : ℕ => a1 < b1 ∧ ∃ i1 : Fin C1.gates.length, b1 = P1 + L1 + i1.val ∧ a1 ∈ (C1.gates.get i1).inputs) (P1 + L1 + j1.val) C1.output) → (∀ w1 : Fin L1, w1 ∈ N1 ↔ Relation.ReflTransGen (fun r1 s1 : ℕ => r1 < s1 ∧ ∃ k1 : Fin C1.gates.length, s1 = P1 + L1 + k1.val ∧ r1 ∈ (C1.gates.get k1).inputs) (P1 + w1.val) C1.output) → ∃ (D1 : PEqualNP.CircuitLowerBounds.Circuit) (T1 : Finset (Fin L1)) (o1 : Fin L1 → ℕ), PEqualNP.CircuitLowerBounds.IsMonotoneCircuit D1 ∧ (∀ h1 ∈ D1.gates, h1.inputs.length ≤ 2) ∧ D1.size + N1.card ≤ C1.size + 1 ∧ ∀ (x1 : Fin P1 → Bool) (y1 : Fin L1 → Bool), C1.eval (List.ofFn x1 ++ List.ofFn y1) = (C1.eval (List.ofFn x1 ++ List.ofFn (fun v1 : Fin L1 => false)) || decide (∃ u1 : Fin L1, y1 u1 = true ∧ (u1 ∈ T1 ∨ (D1.wires (List.ofFn x1)).getD (o1 u1) false = true)))

/-! ## Card 07 (pruning to the cone of one wire) -/

section Prune

variable {α : Type}

/-- The fold behind `Circuit.wires` and `Circuit.lineDegrees`, for any value type. -/
def d3r1Fold (δ : α) (Φ : GateOp → List α → α) (gs : List Gate) (init : List α) : List α :=
  gs.foldl (fun w g => w ++ [Φ g.op (g.inputs.map fun i => w.getD i δ)]) init

theorem d3r1Fold_snoc (δ : α) (Φ : GateOp → List α → α) (gs : List Gate) (g : Gate)
    (init : List α) :
    d3r1Fold δ Φ (gs ++ [g]) init = d3r1Fold δ Φ gs init ++
      [Φ g.op (g.inputs.map fun i => (d3r1Fold δ Φ gs init).getD i δ)] := by
  simp only [d3r1Fold, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem d3r1Fold_length (δ : α) (Φ : GateOp → List α → α) (gs : List Gate) (init : List α) :
    (d3r1Fold δ Φ gs init).length = init.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [d3r1Fold]
  | append_singleton gs g ih => rw [d3r1Fold_snoc]; simp [ih]; omega

theorem d3r1Fold_lt (δ : α) (Φ : GateOp → List α → α) (gs : List Gate) (init : List α)
    (i : ℕ) (h : i < init.length) : (d3r1Fold δ Φ gs init).getD i δ = init.getD i δ := by
  induction gs using List.reverseRecOn with
  | nil => simp [d3r1Fold]
  | append_singleton gs g ih =>
    rw [d3r1Fold_snoc, List.getD_append _ _ _ _ (by rw [d3r1Fold_length]; omega), ih]

theorem d3r1Fold_ge (δ : α) (Φ : GateOp → List α → α) (gs : List Gate) (init : List α)
    (i : ℕ) (h : init.length + gs.length ≤ i) : (d3r1Fold δ Φ gs init).getD i δ = δ := by
  rw [List.getD_eq_default _ _ (by rw [d3r1Fold_length]; exact h)]

theorem d3r1Fold_gate (δ : α) (Φ : GateOp → List α → α) (gs : List Gate) (init : List α) :
    ∀ (j : ℕ) (hj : j < gs.length), (d3r1Fold δ Φ gs init).getD (init.length + j) δ =
      Φ gs[j].op (gs[j].inputs.map fun i =>
        if i < init.length + j then (d3r1Fold δ Φ gs init).getD i δ else δ) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hl := d3r1Fold_length δ Φ gs init
    rw [d3r1Fold_snoc]
    by_cases hjl : j < gs.length
    · rw [List.getD_append _ _ _ _ (by omega), ih j hjl]
      simp only [List.getElem_append_left hjl]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < init.length + j
      · rw [if_pos hi, if_pos hi, List.getD_append _ _ _ _ (by omega)]
      · simp only [hi, if_false]
    · have hje : j = gs.length := by simp at hj; omega
      subst hje
      rw [List.getD_append_right _ _ _ _ (by omega)]
      simp only [List.getElem_append_right (Nat.le_refl _), hl, Nat.sub_self,
        List.getD_cons_zero, List.getElem_cons_zero]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < init.length + gs.length
      · rw [if_pos hi, List.getD_append _ _ _ _ (by omega)]
      · simp only [hi, if_false]
        rw [List.getD_eq_default _ _ (by omega)]

end Prune

/-- The number of indices below `t` kept by `κ`. -/
def d3r1Rank (κ : ℕ → Bool) (t : ℕ) : ℕ := ((List.range t).filter κ).length

theorem d3r1_range_split (κ : ℕ → Bool) (s t : ℕ) (h : s ≤ t) :
    (List.range t).filter κ = (List.range s).filter κ ++ (List.range' s (t - s)).filter κ := by
  rw [← List.filter_append]
  congr 1
  rw [List.range_eq_range', List.range_eq_range']
  have := @List.range'_append_1 0 s (t - s)
  simp only [Nat.zero_add] at this
  rw [this]
  congr 1
  omega

theorem d3r1_rank_lt (κ : ℕ → Bool) (s t : ℕ) (hst : s < t) (hs : κ s = true) :
    d3r1Rank κ s < d3r1Rank κ t := by
  unfold d3r1Rank
  rw [d3r1_range_split κ s t hst.le, List.length_append]
  obtain ⟨m, hm⟩ : ∃ m, t - s = m + 1 := ⟨t - s - 1, by omega⟩
  rw [hm, List.range'_succ, List.filter_cons_of_pos hs]
  simp

theorem d3r1_L_get (κ : ℕ → Bool) (len t : ℕ) (ht : t < len) (hk : κ t = true) :
    ((List.range len).filter κ)[d3r1Rank κ t]? = some t := by
  rw [d3r1_range_split κ t len ht.le]
  unfold d3r1Rank
  rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  obtain ⟨m, hm⟩ : ∃ m, len - t = m + 1 := ⟨len - t - 1, by omega⟩
  rw [hm, List.range'_succ, List.filter_cons_of_pos hk]
  simp

theorem d3r1_L_back (κ : ℕ → Bool) (len r : ℕ) (hr : r < ((List.range len).filter κ).length) :
    κ ((List.range len).filter κ)[r] = true ∧ ((List.range len).filter κ)[r] < len ∧
      d3r1Rank κ ((List.range len).filter κ)[r] = r := by
  have hm : ((List.range len).filter κ)[r] ∈ (List.range len).filter κ := List.getElem_mem hr
  have hm2 := List.mem_filter.mp hm
  have hlt := List.mem_range.mp hm2.1
  refine ⟨hm2.2, hlt, ?_⟩
  have hg := d3r1_L_get κ len _ hlt hm2.2
  rw [List.getElem?_eq_some_iff] at hg
  obtain ⟨hb, he⟩ := hg
  have hnd : ((List.range len).filter κ).Nodup := (List.nodup_range).filter _
  exact (hnd.getElem_inj_iff).mp he

/-- The new index of a wire after pruning. -/
def d3r1New (n : ℕ) (κ : ℕ → Bool) (top u : ℕ) : ℕ :=
  if u < n then u else if κ (u - n) then n + d3r1Rank κ (u - n) else n + top

/-- The number of kept gates. -/
def d3r1Top (κ : ℕ → Bool) (gs : List Gate) : ℕ := ((List.range gs.length).filter κ).length

/-- The gate `t` after pruning: reads below it are renumbered, a read at or above it reads itself
(the value `false` and degree `0`, as before). -/
def d3r1PGate (n : ℕ) (κ : ℕ → Bool) (gs : List Gate) (t : ℕ) : Gate :=
  { op := (gs.getD t ⟨GateOp.and, []⟩).op,
    inputs := (gs.getD t ⟨GateOp.and, []⟩).inputs.map fun a =>
      if a < n + t then d3r1New n κ (d3r1Top κ gs) a else n + d3r1Rank κ t }

/-- The kept gates, in order. -/
def d3r1Pruned (n : ℕ) (κ : ℕ → Bool) (gs : List Gate) : List Gate :=
  ((List.range gs.length).filter κ).map (d3r1PGate n κ gs)

theorem d3r1_pruned_length (n : ℕ) (κ : ℕ → Bool) (gs : List Gate) :
    (d3r1Pruned n κ gs).length = d3r1Top κ gs := by
  simp [d3r1Pruned, d3r1Top]

theorem d3r1_pruned_get (n : ℕ) (κ : ℕ → Bool) (gs : List Gate) (t : ℕ) (ht : t < gs.length)
    (hk : κ t = true) : ∃ h : d3r1Rank κ t < (d3r1Pruned n κ gs).length,
      (d3r1Pruned n κ gs)[d3r1Rank κ t] = d3r1PGate n κ gs t := by
  have hg := d3r1_L_get κ gs.length t ht hk
  rw [List.getElem?_eq_some_iff] at hg
  obtain ⟨hb, he⟩ := hg
  refine ⟨by simpa [d3r1Pruned] using hb, ?_⟩
  simp [d3r1Pruned, he]

theorem d3r1_new_lt (n : ℕ) (κ : ℕ → Bool) (top a t : ℕ) (hat : a < n + t)
    (ha : a < n ∨ κ (a - n) = true) : d3r1New n κ top a < n + d3r1Rank κ t := by
  unfold d3r1New
  by_cases han : a < n
  · rw [if_pos han]; omega
  · have hk := ha.resolve_left han
    rw [if_neg han, if_pos hk]
    have := d3r1_rank_lt κ (a - n) t (by omega) hk
    omega

/-- Pruning keeps the value of every kept wire, for any fold of the shape of `Circuit.wires`. -/
theorem d3r1_prune_val {α : Type} (δ : α) (Φ : GateOp → List α → α) (init : List α) (n : ℕ)
    (hn : init.length = n) (gs : List Gate) (κ : ℕ → Bool)
    (hκ : ∀ t, κ t = true → t < gs.length)
    (hcl : ∀ (t : ℕ) (ht : t < gs.length), κ t = true → ∀ a ∈ gs[t].inputs, n ≤ a → a < n + t →
      κ (a - n) = true) :
    ∀ u, (u < n ∨ κ (u - n) = true) →
      (d3r1Fold δ Φ (d3r1Pruned n κ gs) init).getD (d3r1New n κ (d3r1Top κ gs) u) δ =
        (d3r1Fold δ Φ gs init).getD u δ := by
  subst hn
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu
    by_cases hun : u < init.length
    · simp only [d3r1New, hun, if_true]
      rw [d3r1Fold_lt _ _ _ _ _ hun, d3r1Fold_lt _ _ _ _ _ hun]
    · have hk : κ (u - init.length) = true := hu.resolve_left hun
      obtain ⟨t, rfl⟩ : ∃ t, u = init.length + t := ⟨u - init.length, by omega⟩
      simp only [Nat.add_sub_cancel_left] at hk
      have ht := hκ t hk
      have hnew : d3r1New init.length κ (d3r1Top κ gs) (init.length + t) =
          init.length + d3r1Rank κ t := by
        simp [d3r1New, hk]
      obtain ⟨hb, hpr⟩ := d3r1_pruned_get init.length κ gs t ht hk
      rw [hnew, d3r1Fold_gate _ _ _ _ _ hb, d3r1Fold_gate _ _ _ _ t ht, hpr]
      have hg : gs.getD t ⟨GateOp.and, []⟩ = gs[t] := List.getD_eq_getElem _ _ ht
      simp only [d3r1PGate, hg, List.map_map]
      congr 1
      apply List.map_congr_left
      intro a ha
      simp only [Function.comp]
      by_cases hat : a < init.length + t
      · have hA : a < init.length ∨ κ (a - init.length) = true := by
          by_cases han : a < init.length
          · exact Or.inl han
          · exact Or.inr (hcl t ht hk a ha (by omega) hat)
        rw [if_pos hat, if_pos (d3r1_new_lt _ _ _ a t hat hA), if_pos hat]
        exact ih a hat hA
      · simp only [hat, if_false, lt_irrefl]

/-- The value at the output wire is kept, whether or not that wire is a kept gate. -/
theorem d3r1_prune_out {α : Type} (δ : α) (Φ : GateOp → List α → α) (init : List α) (n : ℕ)
    (hn : init.length = n) (gs : List Gate) (κ : ℕ → Bool) (o : ℕ)
    (hκ : ∀ t, κ t = true → t < gs.length)
    (hcl : ∀ (t : ℕ) (ht : t < gs.length), κ t = true → ∀ a ∈ gs[t].inputs, n ≤ a → a < n + t →
      κ (a - n) = true)
    (ho : n ≤ o → o < n + gs.length → κ (o - n) = true) :
    (d3r1Fold δ Φ (d3r1Pruned n κ gs) init).getD (d3r1New n κ (d3r1Top κ gs) o) δ =
      (d3r1Fold δ Φ gs init).getD o δ := by
  by_cases hA : o < n ∨ κ (o - n) = true
  · exact d3r1_prune_val δ Φ init n hn gs κ hκ hcl o hA
  · have hon : n ≤ o := by omega
    have hk : κ (o - n) = false := by simpa using (fun h => hA (Or.inr h))
    have hol : n + gs.length ≤ o := by
      by_contra h
      rw [ho hon (by omega)] at hk
      exact Bool.noConfusion hk
    have hnew : d3r1New n κ (d3r1Top κ gs) o = n + d3r1Top κ gs := by
      simp [d3r1New, hk, show ¬ o < n by omega]
    rw [hnew, d3r1Fold_ge _ _ _ _ _ (by rw [hn, d3r1_pruned_length]),
      d3r1Fold_ge _ _ _ _ _ (by omega)]

/-- The read relation of a gate list on `n` inputs, as in the cards. -/
def d3r1R (gs : List Gate) (n : ℕ) : ℕ → ℕ → Prop := fun a1 b1 =>
  a1 < b1 ∧ ∃ i1 : Fin gs.length, b1 = n + i1.val ∧ a1 ∈ (gs.get i1).inputs

/-- Every wire of the cone still reaches the output after pruning. -/
theorem d3r1_prune_reach (n : ℕ) (gs : List Gate) (o : ℕ) (κ : ℕ → Bool)
    (hiff : ∀ t, κ t = true ↔ t < gs.length ∧ Relation.ReflTransGen (d3r1R gs n) (n + t) o) :
    ∀ c, Relation.ReflTransGen (d3r1R gs n) c o →
      Relation.ReflTransGen (d3r1R (d3r1Pruned n κ gs) n) (d3r1New n κ (d3r1Top κ gs) c)
        (d3r1New n κ (d3r1Top κ gs) o) := by
  intro c hc
  induction hc using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | @head c d hcd hdo ih =>
    obtain ⟨hlt, i1, hd, hmem⟩ := hcd
    subst hd
    have hk : κ i1 = true := (hiff i1).mpr ⟨i1.2, hdo⟩
    have hnew : d3r1New n κ (d3r1Top κ gs) (n + i1.val) = n + d3r1Rank κ i1 := by
      simp [d3r1New, hk]
    obtain ⟨hb, hpr⟩ := d3r1_pruned_get n κ gs i1 i1.2 hk
    have hA : c < n ∨ κ (c - n) = true := by
      by_cases hcn : c < n
      · exact Or.inl hcn
      · right
        apply (hiff _).mpr
        refine ⟨by omega, ?_⟩
        rw [show n + (c - n) = c by omega]
        exact Relation.ReflTransGen.head ⟨hlt, i1, rfl, hmem⟩ hdo
    refine Relation.ReflTransGen.head ⟨?_, ⟨d3r1Rank κ i1, hb⟩, hnew, ?_⟩ ih
    · rw [hnew]; exact d3r1_new_lt n κ _ c i1 hlt hA
    · simp only [List.get_eq_getElem, hpr, d3r1PGate]
      rw [List.getD_eq_getElem _ _ i1.2]
      exact List.mem_map.mpr ⟨c, by simpa using hmem, if_pos hlt⟩

attribute [local instance] lineDegreeGateOpDecEq in
/-- The gate rule of `Circuit.lineDegrees`. -/
def d3r1DegOp (op : GateOp) (l : List ℕ) : ℕ := if op = GateOp.and then l.sum else l.foldr max 0

theorem d3r1_lineDegrees_eq (C : Circuit) (n : ℕ) (marked : Finset ℕ) :
    C.lineDegrees n marked =
      d3r1Fold 0 d3r1DegOp C.gates ((List.range n).map fun i => if i ∈ marked then 1 else 0) := rfl

theorem d3r1_wires_eq (C : Circuit) (x : List Bool) :
    C.wires x = d3r1Fold false GateOp.eval C.gates x := rfl

/-- CARD 07 (pruning). The cone of one wire, as a circuit in which every gate reaches the output:
same function, no larger, AND/OR of fan-in two, no larger line-degree. -/
theorem card07_prune : ∀ (n : ℕ) (marked : Finset ℕ) (C : Circuit) (o : ℕ), IsMonotoneCircuit C →
    (∀ g ∈ C.gates, g.inputs.length ≤ 2) →
    ∃ H : Circuit, IsMonotoneCircuit H ∧ (∀ g ∈ H.gates, g.inputs.length ≤ 2) ∧ H.size ≤ C.size ∧
      H.lineDeg n marked ≤ (C.lineDegrees n marked).getD o 0 ∧
      (∀ x : Fin n → Bool, circuitFun n H x = (C.wires (List.ofFn x)).getD o false) ∧
      ∀ j : Fin H.gates.length, Relation.ReflTransGen (fun a1 b1 : ℕ => a1 < b1 ∧
        ∃ i1 : Fin H.gates.length, b1 = n + i1.val ∧ a1 ∈ (H.gates.get i1).inputs)
        (n + j.val) H.output := by
  intro n marked C o hm hf
  classical
  let κ : ℕ → Bool := fun t =>
    decide (t < C.gates.length ∧ Relation.ReflTransGen (d3r1R C.gates n) (n + t) o)
  have hiff : ∀ t, κ t = true ↔
      t < C.gates.length ∧ Relation.ReflTransGen (d3r1R C.gates n) (n + t) o := by
    intro t; simp [κ]
  have hκ : ∀ t, κ t = true → t < C.gates.length := fun t h => ((hiff t).mp h).1
  have hcl : ∀ (t : ℕ) (ht : t < C.gates.length), κ t = true → ∀ a ∈ C.gates[t].inputs,
      n ≤ a → a < n + t → κ (a - n) = true := by
    intro t ht hk a ha han hat
    apply (hiff _).mpr
    refine ⟨by omega, ?_⟩
    rw [show n + (a - n) = a by omega]
    exact Relation.ReflTransGen.head ⟨hat, ⟨t, ht⟩, rfl, by simpa using ha⟩ ((hiff t).mp hk).2
  have ho : n ≤ o → o < n + C.gates.length → κ (o - n) = true := by
    intro h1 h2
    apply (hiff _).mpr
    refine ⟨by omega, ?_⟩
    rw [show n + (o - n) = o by omega]
  have hmemP : ∀ g ∈ d3r1Pruned n κ C.gates, ∃ t, ∃ ht : t < C.gates.length,
      g = d3r1PGate n κ C.gates t := by
    intro g hg
    simp only [d3r1Pruned, List.mem_map, List.mem_filter, List.mem_range] at hg
    obtain ⟨t, ⟨ht, _⟩, rfl⟩ := hg
    exact ⟨t, ht, rfl⟩
  refine ⟨⟨d3r1Pruned n κ C.gates, d3r1New n κ (d3r1Top κ C.gates) o⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨t, ht, rfl⟩ := hmemP g hg
    simp only [d3r1PGate]
    rw [List.getD_eq_getElem _ _ ht]
    exact hm _ (List.getElem_mem ht)
  · intro g hg
    obtain ⟨t, ht, rfl⟩ := hmemP g hg
    simp only [d3r1PGate, List.length_map]
    rw [List.getD_eq_getElem _ _ ht]
    exact hf _ (List.getElem_mem ht)
  · show (d3r1Pruned n κ C.gates).length ≤ C.gates.length
    rw [d3r1_pruned_length]
    unfold d3r1Top
    exact le_trans (List.length_filter_le _ _) (by simp)
  · unfold Circuit.lineDeg
    rw [d3r1_lineDegrees_eq, d3r1_lineDegrees_eq]
    exact le_of_eq (d3r1_prune_out 0 d3r1DegOp _ n (by simp) C.gates κ o hκ hcl ho)
  · intro x
    show (Circuit.wires _ (List.ofFn x)).getD _ false = _
    rw [d3r1_wires_eq, d3r1_wires_eq]
    exact d3r1_prune_out false GateOp.eval _ n (by simp) C.gates κ o hκ hcl ho
  · intro j
    have hj : j.val < ((List.range C.gates.length).filter κ).length := by
      have := j.2
      simp only [d3r1_pruned_length] at this
      exact this
    obtain ⟨hk, ht, hr⟩ := d3r1_L_back κ C.gates.length j.val hj
    have hreach := d3r1_prune_reach n C.gates o κ hiff
      (n + ((List.range C.gates.length).filter κ)[j.val]) ((hiff _).mp hk).2
    have hnew : d3r1New n κ (d3r1Top κ C.gates) (n + ((List.range C.gates.length).filter κ)[j.val])
        = n + j.val := by
      simp [d3r1New, hk, hr]
    rw [hnew] at hreach
    exact hreach

/-! ## Card 08 -/

/-- A wire that the input `j` does not reach has the same value on two inputs that differ only
at `j`. -/
theorem d3r1_unreached_wire (n : ℕ) (C : Circuit) (j : ℕ) (x y : Fin n → Bool)
    (hxy : ∀ i : Fin n, i.val ≠ j → x i = y i) : ∀ v : ℕ,
    ¬ Relation.ReflTransGen (fun a1 b1 : ℕ => a1 < b1 ∧
        ∃ i1 : Fin C.gates.length, b1 = n + i1.val ∧ a1 ∈ (C.gates.get i1).inputs) j v →
    (C.wires (List.ofFn x)).getD v false = (C.wires (List.ofFn y)).getD v false := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    intro hnr
    by_cases hvn : v < n
    · have hvj : v ≠ j := by
        intro h; subst h; exact hnr Relation.ReflTransGen.refl
      rw [LowMergeProof.wires_input _ _ _ (by simpa using hvn),
        LowMergeProof.wires_input _ _ _ (by simpa using hvn)]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp [hvn, hxy ⟨v, hvn⟩ hvj]
    · by_cases hvl : v < n + C.gates.length
      · obtain ⟨t, rfl⟩ : ∃ t, v = n + t := ⟨v - n, by omega⟩
        have ht : t < C.gates.length := by omega
        have e1 := LowMergeProof.wires_gate C (List.ofFn x) t ht
        have e2 := LowMergeProof.wires_gate C (List.ofFn y) t ht
        simp only [List.length_ofFn] at e1 e2
        rw [e1, e2]
        congr 1
        apply List.map_congr_left
        intro a ha
        unfold LowMergeProof.rd
        by_cases hav : a < n + t
        · rw [if_pos hav, if_pos hav]
          apply ih a hav
          intro hr
          apply hnr
          refine Relation.ReflTransGen.tail hr ⟨hav, ⟨t, ht⟩, rfl, ?_⟩
          simpa using ha
        · simp only [hav, if_false]
      · rw [List.getD_eq_default _ _ (by rw [LowMergeProof.wires_length]; simp; omega),
          List.getD_eq_default _ _ (by rw [LowMergeProof.wires_length]; simp; omega)]

/-- CARD 08 (an input that does not reach the output is not read). -/
theorem card08_unreached : ∀ (n : ℕ) (C : Circuit) (j : ℕ) (x y : Fin n → Bool),
    (∀ i : Fin n, i.val ≠ j → x i = y i) →
    ¬ Relation.ReflTransGen (fun a1 b1 : ℕ => a1 < b1 ∧
        ∃ i1 : Fin C.gates.length, b1 = n + i1.val ∧ a1 ∈ (C.gates.get i1).inputs) j C.output →
    circuitFun n C x = circuitFun n C y := by
  intro n C j x y hxy hnr
  exact d3r1_unreached_wire n C j x y hxy C.output hnr

/-! ## Card 09 from cards 07 and 08 -/

/-- Splitting an input of `N + N` wires into points and lines. -/
theorem d3r1_ofFn_addCases {N : ℕ} (x y : Fin N → Bool) :
    List.ofFn (Fin.addCases (motive := fun _ => Bool) x y) = List.ofFn x ++ List.ofFn y :=
  List.ofFn_fin_append x y

/-- CARD 09 (Statement R1) from card 07 (pruning) and card 08 (an unreached input is not read),
both taken as hypotheses with the statements of the skeleton. -/
theorem card09_R1_of :
    (∀ (n : ℕ) (marked : Finset ℕ) (C : Circuit) (o : ℕ), IsMonotoneCircuit C →
      (∀ g ∈ C.gates, g.inputs.length ≤ 2) →
      ∃ H : Circuit, IsMonotoneCircuit H ∧ (∀ g ∈ H.gates, g.inputs.length ≤ 2) ∧ H.size ≤ C.size ∧
        H.lineDeg n marked ≤ (C.lineDegrees n marked).getD o 0 ∧
        (∀ x : Fin n → Bool, circuitFun n H x = (C.wires (List.ofFn x)).getD o false) ∧
        ∀ j : Fin H.gates.length, Relation.ReflTransGen (fun a1 b1 : ℕ => a1 < b1 ∧
          ∃ i1 : Fin H.gates.length, b1 = n + i1.val ∧ a1 ∈ (H.gates.get i1).inputs)
          (n + j.val) H.output) →
    (∀ (n : ℕ) (C : Circuit) (j : ℕ) (x y : Fin n → Bool),
      (∀ i : Fin n, i.val ≠ j → x i = y i) →
      ¬ Relation.ReflTransGen (fun a1 b1 : ℕ => a1 < b1 ∧
          ∃ i1 : Fin C.gates.length, b1 = n + i1.val ∧ a1 ∈ (C.gates.get i1).inputs) j C.output →
      circuitFun n C x = circuitFun n C y) →
    ∀ (N q k : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (H : Circuit),
    H270 → H669 → H738 →
    (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
    2 ≤ q → 1 ≤ k → k + 1 ≤ q →
    (∀ l : Fin N, (Finset.univ.filter (fun p : Fin N => I p l)).card = q) →
    (∀ p : Fin N, ∃ u : Fin N, ¬ I p u) →
    Monotone2 H → HasLineDegree (N + N) (Finset.Ico N (N + N)) H 1 →
    (∀ (w : Fin N) (T : Finset (Fin N)), T.card ≤ k →
      (circuitFun (N + N) H
        (Fin.addCases (motive := fun _ => Bool) (fun p => decide (p ∈ T)) (fun l => decide (l = w))) = true ↔
        ∃ p ∈ T, I p w)) →
    N * k + N ≤ H.size + 1 := by
  intro h07 h08 N q k I _ H h270 h669 h738 hI hq hk1 hk2 hl hmiss hmono hdeg hR
  classical
  -- the hypothesis on inputs given as functions
  have hR' : ∀ (w : Fin N) (x : Fin N → Bool),
      (Finset.univ.filter (fun p : Fin N => x p = true)).card ≤ k →
      (circuitFun (N + N) H
        (Fin.addCases (motive := fun _ => Bool) x (fun l => decide (l = w))) = true ↔
        ∃ p, x p = true ∧ I p w) := by
    intro w x hx
    have hxe : (fun p => decide (p ∈ Finset.univ.filter (fun p : Fin N => x p = true))) = x := by
      funext p; simp
    have := hR w _ hx
    rw [hxe] at this
    rw [this]; simp
  have hm : IsMonotoneCircuit H := fun g hg => by
    have := (hmono g hg).1
    simpa using this
  have hf : ∀ g ∈ H.gates, g.inputs.length ≤ 2 := fun g hg => (hmono g hg).2
  obtain ⟨H', hm', hf', hs', hd', hfun', hreach'⟩ := h07 (N + N) (Finset.Ico N (N + N)) H H.output hm hf
  have hfun : ∀ z, circuitFun (N + N) H' z = circuitFun (N + N) H z := fun z => hfun' z
  have hd1 : HasLineDegree (N + N) (Finset.Ico N (N + N)) H' 1 := le_trans hd' hdeg
  obtain ⟨D1, T1, o1, hDm, hDf, hDs, hDid⟩ := h738 N N H'
    (Finset.univ.filter (fun w1 : Fin N => Relation.ReflTransGen (fun r1 s1 : ℕ => r1 < s1 ∧
      ∃ k1 : Fin H'.gates.length, s1 = N + N + k1.val ∧ r1 ∈ (H'.gates.get k1).inputs)
      (N + w1.val) H'.output))
    hm' hf' hd1 hreach' (fun w1 => by simp)
  set phi : Fin N → (Fin N → Bool) → Bool :=
    fun u x => (D1.wires (List.ofFn x)).getD (o1 u) false with hphi
  -- the identity of L-meta-738, on the inputs of `H`
  have hid : ∀ (x y : Fin N → Bool),
      circuitFun (N + N) H (Fin.addCases (motive := fun _ => Bool) x y) =
        (circuitFun (N + N) H (Fin.addCases (motive := fun _ => Bool) x (fun _ => false)) ||
          decide (∃ u1 : Fin N, y u1 = true ∧ (u1 ∈ T1 ∨ phi u1 x = true))) := by
    intro x y
    rw [← hfun, ← hfun]
    unfold circuitFun
    rw [d3r1_ofFn_addCases, d3r1_ofFn_addCases]
    exact hDid x y
  have hid1 : ∀ (x : Fin N → Bool) (w : Fin N),
      circuitFun (N + N) H (Fin.addCases (motive := fun _ => Bool) x (fun l => decide (l = w))) =
        (circuitFun (N + N) H (Fin.addCases (motive := fun _ => Bool) x (fun _ => false)) ||
          decide (w ∈ T1 ∨ phi w x = true)) := by
    intro x w
    have hiff : (∃ u1 : Fin N, decide (u1 = w) = true ∧ (u1 ∈ T1 ∨ phi u1 x = true)) ↔
        (w ∈ T1 ∨ phi w x = true) := by
      constructor
      · rintro ⟨u, hu, h⟩
        simp only [decide_eq_true_eq] at hu
        subst hu
        exact h
      · intro h
        exact ⟨w, by simp, h⟩
    rw [hid x]
    simp only [hiff]
  let e0 : Fin N → Bool := fun _ => false
  let ep : Fin N → Fin N → Bool := fun p q => decide (q = p)
  have hc0 : (Finset.univ.filter (fun p : Fin N => e0 p = true)).card ≤ k := by simp [e0]
  have hcp : ∀ p, (Finset.univ.filter (fun q : Fin N => ep p q = true)).card ≤ k := by
    intro p
    have : Finset.univ.filter (fun q : Fin N => ep p q = true) = {p} := by
      ext q; simp [ep]
    rw [this, Finset.card_singleton]
    exact hk1
  -- no line is in T1
  have hT1 : ∀ w, w ∉ T1 := by
    intro w hw
    have h0 : circuitFun (N + N) H
        (Fin.addCases (motive := fun _ => Bool) e0 (fun l => decide (l = w))) ≠ true := by
      intro hh
      rw [hR' w e0 hc0] at hh
      revert hh
      rintro ⟨p, hp, _⟩
      simp [e0] at hp
    apply h0
    rw [hid1 e0 w]
    simp [hw]
  -- the point-only part is false at a single point
  have hHp0 : ∀ p, circuitFun (N + N) H
      (Fin.addCases (motive := fun _ => Bool) (ep p) (fun _ => false)) = false := by
    intro p
    obtain ⟨u, hu⟩ := hmiss p
    have h0 : circuitFun (N + N) H
        (Fin.addCases (motive := fun _ => Bool) (ep p) (fun l => decide (l = u))) ≠ true := by
      intro hh
      rw [hR' u (ep p) (hcp p)] at hh
      revert hh
      rintro ⟨p', hp', hI'⟩
      simp [ep] at hp'
      subst hp'
      exact hu hI'
    rw [hid1 (ep p) u] at h0
    cases h : circuitFun (N + N) H (Fin.addCases (motive := fun _ => Bool) (ep p) (fun _ => false))
    · rfl
    · rw [h] at h0; simp at h0
  -- the line coefficients
  have hphi_on : ∀ p w, I p w → phi w (ep p) = true := by
    intro p w hpw
    have h1 := (hR' w (ep p) (hcp p)).mpr ⟨p, by simp [ep], hpw⟩
    rw [hid1 (ep p) w, hHp0 p] at h1
    simpa [hT1 w] using h1
  have hphi_off : ∀ (w : Fin N) (x : Fin N → Bool),
      (Finset.univ.filter (fun p : Fin N => x p = true)).card ≤ k →
      (∀ p, x p = true → ¬ I p w) → phi w x = false := by
    intro w x hx hoff
    have h0 : circuitFun (N + N) H
        (Fin.addCases (motive := fun _ => Bool) x (fun l => decide (l = w))) ≠ true := by
      intro hh
      rw [hR' w x hx] at hh
      revert hh
      rintro ⟨p, hp, hI'⟩
      exact hoff p hp hI'
    rw [hid1 x w] at h0
    cases h : phi w x
    · rfl
    · rw [h] at h0; simp at h0
  -- every line reaches the output of the pruned circuit
  have hN1 : ∀ w : Fin N, Relation.ReflTransGen (fun r1 s1 : ℕ => r1 < s1 ∧
      ∃ k1 : Fin H'.gates.length, s1 = N + N + k1.val ∧ r1 ∈ (H'.gates.get k1).inputs)
      (N + w.val) H'.output := by
    intro w
    by_contra hnr
    have hpos : 0 < (Finset.univ.filter (fun p : Fin N => I p w)).card := by
      rw [hl w]; omega
    obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    have h8 := h08 (N + N) H' (N + w.val)
      (Fin.addCases (motive := fun _ => Bool) (ep p) (fun l => decide (l = w)))
      (Fin.addCases (motive := fun _ => Bool) (ep p) (fun _ => false)) (by
        intro i hi
        induction i using Fin.addCases with
        | left a => simp
        | right b =>
          have hb : b ≠ w := by
            intro h; apply hi; subst h; rfl
          rw [Fin.addCases_right, Fin.addCases_right]
          exact decide_eq_false hb) hnr
    rw [hfun, hfun, hHp0 p] at h8
    have h1 := (hR' w (ep p) (hcp p)).mpr ⟨p, by simp [ep], hp⟩
    rw [h8] at h1
    exact Bool.false_ne_true h1
  have hN1c : (Finset.univ.filter (fun w1 : Fin N => Relation.ReflTransGen (fun r1 s1 : ℕ =>
      r1 < s1 ∧ ∃ k1 : Fin H'.gates.length, s1 = N + N + k1.val ∧ r1 ∈ (H'.gates.get k1).inputs)
      (N + w1.val) H'.output)).card = N := by
    rw [Finset.filter_true_of_mem (fun w _ => hN1 w)]
    simp
  rw [hN1c] at hDs
  -- gates of exactly two wires (L-meta-669 with nothing fixed)
  obtain ⟨gates', r, hg', hlen, heq⟩ := h669 N D1.gates ∅ ∅ (fun g hg => ⟨hDm g hg, hDf g hg⟩)
  have hempty : ∀ x : Fin N → Bool, (fun i : Fin N => if i ∈ (∅ : Finset (Fin N)) then true
      else if i ∈ (∅ : Finset (Fin N)) then false else x i) = x := by
    intro x; funext i; simp
  have hev : ∀ (w : Fin N) (x : Fin N → Bool),
      Circuit.eval ⟨gates', r (o1 w)⟩ (List.ofFn x) = phi w x := by
    intro w x
    have hpos : 0 < (Finset.univ.filter (fun p : Fin N => I p w)).card := by
      rw [hl w]; omega
    obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    have h := heq (o1 w) ⟨ep p, e0, by
      rw [hempty, hempty]
      change phi w (ep p) ≠ phi w e0
      rw [hphi_on p w hp, hphi_off w e0 hc0 (fun p h => by simp [e0] at h)]
      simp⟩ x
    rw [h, hempty]
    rfl
  -- L-meta-270 on the points of each line
  have h2 := h270 N N k (fun w => Finset.univ.filter (fun p : Fin N => I p w)) ⟨gates', 0⟩
    (fun w => r (o1 w)) (fun _ => k)
    (by
      intro i j hij
      rw [Finset.card_le_one]
      intro a ha b hb
      simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      by_contra hab
      exact hI a b i j hab hij ⟨ha.1, ha.2, hb.1, hb.2⟩)
    (fun i => by rw [hl i]; exact hq)
    hg'
    (by
      intro i p
      change Circuit.eval ⟨gates', r (o1 i)⟩ (List.ofFn (ep p)) = true ↔ _
      rw [hev i (ep p)]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        by_contra hpi
        rw [hphi_off i (ep p) (hcp p) (by
          intro p' hp' hI'; simp [ep] at hp'; subst hp'; exact hpi hI')] at h
        exact Bool.false_ne_true h
      · intro hpi
        exact hphi_on p i hpi)
    (by
      intro i x hx hoff
      change Circuit.eval ⟨gates', r (o1 i)⟩ (List.ofFn x) = false
      rw [hev i x]
      apply hphi_off i x hx
      intro p hp hI'
      have := hoff p (by simp [hI'])
      rw [this] at hp
      exact Bool.false_ne_true hp)
    (fun _ => le_rfl)
    (fun i => by rw [hl i]; exact hk2)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h2
  unfold Circuit.size at h2 hDs hs' ⊢
  have : gates'.length ≤ D1.gates.length := hlen
  nlinarith

/-! ## Card 09 -/

/-- CARD 09 (Statement R1, from the recorded 270, 669 and 738). A fan-in-two AND/OR circuit of
line-degree at most 1 equal to the line sum on every input with one line and at most k points has
at least N k + N - 1 gates. Proof plan: prune (card 07) to the cone; every line reaches it (card 08,
with a point of the line and a line missing that point); H738 gives D on the points with
size(D) + N <= size + 1 and the line coefficients o_w (no line in T1: H is false at (empty, e_w));
H669 with nothing fixed gives gates of exactly two wires for the non-constant wires o_w (true at a
point of w, false at no point); H270 with S_w = points of w, c_w = k (k <= q - 1). -/
theorem card09_R1 : ∀ (N q k : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (H : Circuit),
    H270 → H669 → H738 →
    (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
    2 ≤ q → 1 ≤ k → k + 1 ≤ q →
    (∀ l : Fin N, (Finset.univ.filter (fun p : Fin N => I p l)).card = q) →
    (∀ p : Fin N, ∃ u : Fin N, ¬ I p u) →
    Monotone2 H → HasLineDegree (N + N) (Finset.Ico N (N + N)) H 1 →
    (∀ (w : Fin N) (T : Finset (Fin N)), T.card ≤ k →
      (circuitFun (N + N) H
        (Fin.addCases (motive := fun _ => Bool) (fun p => decide (p ∈ T)) (fun l => decide (l = w))) = true ↔
        ∃ p ∈ T, I p w)) →
    N * k + N ≤ H.size + 1 :=
  card09_R1_of card07_prune card08_unreached

end PEqualNP.MetaComplexity.Deg3
