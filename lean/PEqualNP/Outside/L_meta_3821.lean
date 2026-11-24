import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3821_aux.Pruning

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

variable {α : Type}

def d3r1Fold (δ : α) (Φ : GateOp → List α → α) (gs : List Gate) (init : List α) : List α :=
  gs.foldl (fun w g => w ++ [Φ g.op (g.inputs.map fun i => w.getD i δ)]) init

lemma d3r1Fold_snoc (δ : α) (Φ : GateOp → List α → α) (gs : List Gate) (g : Gate)
    (init : List α) :
    d3r1Fold δ Φ (gs ++ [g]) init = d3r1Fold δ Φ gs init ++
      [Φ g.op (g.inputs.map fun i => (d3r1Fold δ Φ gs init).getD i δ)] := by
  simp only [d3r1Fold, List.foldl_append, List.foldl_cons, List.foldl_nil]

lemma d3r1Fold_length (δ : α) (Φ : GateOp → List α → α) (gs : List Gate) (init : List α) :
    (d3r1Fold δ Φ gs init).length = init.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [d3r1Fold]
  | append_singleton gs g ih => rw [d3r1Fold_snoc]; simp [ih]; omega

lemma d3r1Fold_lt (δ : α) (Φ : GateOp → List α → α) (gs : List Gate) (init : List α)
    (i : ℕ) (h : i < init.length) : (d3r1Fold δ Φ gs init).getD i δ = init.getD i δ := by
  induction gs using List.reverseRecOn with
  | nil => simp [d3r1Fold]
  | append_singleton gs g ih =>
    rw [d3r1Fold_snoc, List.getD_append _ _ _ _ (by rw [d3r1Fold_length]; omega), ih]

lemma d3r1Fold_ge (δ : α) (Φ : GateOp → List α → α) (gs : List Gate) (init : List α)
    (i : ℕ) (h : init.length + gs.length ≤ i) : (d3r1Fold δ Φ gs init).getD i δ = δ := by
  rw [List.getD_eq_default _ _ (by rw [d3r1Fold_length]; exact h)]

lemma d3r1Fold_gate (δ : α) (Φ : GateOp → List α → α) (gs : List Gate) (init : List α) :
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
      · rw [ite_eq_left hi, ite_eq_left hi, List.getD_append _ _ _ _ (by omega)]
      · simp only [hi, ite_false]
    · have hje : j = gs.length := by simp at hj; omega
      subst hje
      rw [List.getD_append_right _ _ _ _ (by omega)]
      simp only [List.getElem_append_right (Nat.le_refl _), hl, Nat.sub_self,
        List.getD_cons_zero, List.getElem_cons_zero]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < init.length + gs.length
      · rw [ite_eq_left hi, List.getD_append _ _ _ _ (by omega)]
      · simp only [hi, ite_false]
        rw [List.getD_eq_default _ _ (by omega)]


def d3r1Rank (κ : ℕ → Bool) (t : ℕ) : ℕ := ((List.range t).filter κ).length

lemma d3r1_range_split (κ : ℕ → Bool) (s t : ℕ) (h : s ≤ t) :
    (List.range t).filter κ = (List.range s).filter κ ++ (List.range' s (t - s)).filter κ := by
  rw [← List.filter_append]
  congr 1
  rw [List.range_eq_range', List.range_eq_range']
  have := @List.range'_append_1 0 s (t - s)
  simp only [Nat.zero_add] at this
  rw [this]
  congr 1
  omega

lemma d3r1_rank_lt (κ : ℕ → Bool) (s t : ℕ) (hst : s < t) (hs : κ s = true) :
    d3r1Rank κ s < d3r1Rank κ t := by
  unfold d3r1Rank
  rw [d3r1_range_split κ s t hst.le, List.length_append]
  obtain ⟨m, hm⟩ : ∃ m, t - s = m + 1 := ⟨t - s - 1, by omega⟩
  rw [hm, List.range'_succ, List.filter_cons_of_pos hs]
  simp

lemma d3r1_L_get (κ : ℕ → Bool) (len t : ℕ) (ht : t < len) (hk : κ t = true) :
    ((List.range len).filter κ)[d3r1Rank κ t]? = some t := by
  rw [d3r1_range_split κ t len ht.le]
  unfold d3r1Rank
  rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  obtain ⟨m, hm⟩ : ∃ m, len - t = m + 1 := ⟨len - t - 1, by omega⟩
  rw [hm, List.range'_succ, List.filter_cons_of_pos hk]
  simp

lemma d3r1_L_back (κ : ℕ → Bool) (len r : ℕ) (hr : r < ((List.range len).filter κ).length) :
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

def d3r1New (n : ℕ) (κ : ℕ → Bool) (top u : ℕ) : ℕ :=
  if u < n then u else if κ (u - n) then n + d3r1Rank κ (u - n) else n + top

def d3r1Top (κ : ℕ → Bool) (gs : List Gate) : ℕ := ((List.range gs.length).filter κ).length

def d3r1PGate (n : ℕ) (κ : ℕ → Bool) (gs : List Gate) (t : ℕ) : Gate :=
  { op := (gs.getD t ⟨GateOp.and, []⟩).op,
    inputs := (gs.getD t ⟨GateOp.and, []⟩).inputs.map fun a =>
      if a < n + t then d3r1New n κ (d3r1Top κ gs) a else n + d3r1Rank κ t }

def d3r1Pruned (n : ℕ) (κ : ℕ → Bool) (gs : List Gate) : List Gate :=
  ((List.range gs.length).filter κ).map (d3r1PGate n κ gs)

lemma d3r1_pruned_length (n : ℕ) (κ : ℕ → Bool) (gs : List Gate) :
    (d3r1Pruned n κ gs).length = d3r1Top κ gs := by
  simp [d3r1Pruned, d3r1Top]

lemma d3r1_pruned_get (n : ℕ) (κ : ℕ → Bool) (gs : List Gate) (t : ℕ) (ht : t < gs.length)
    (hk : κ t = true) : ∃ h : d3r1Rank κ t < (d3r1Pruned n κ gs).length,
      (d3r1Pruned n κ gs)[d3r1Rank κ t] = d3r1PGate n κ gs t := by
  have hg := d3r1_L_get κ gs.length t ht hk
  rw [List.getElem?_eq_some_iff] at hg
  obtain ⟨hb, he⟩ := hg
  refine ⟨by simpa [d3r1Pruned] using hb, ?_⟩
  simp [d3r1Pruned, he]

lemma d3r1_new_lt (n : ℕ) (κ : ℕ → Bool) (top a t : ℕ) (hat : a < n + t)
    (ha : a < n ∨ κ (a - n) = true) : d3r1New n κ top a < n + d3r1Rank κ t := by
  unfold d3r1New
  by_cases han : a < n
  · rw [ite_eq_left han]; omega
  · have hk := ha.resolve_left han
    rw [ite_eq_right han, ite_eq_left hk]
    have := d3r1_rank_lt κ (a - n) t (by omega) hk
    omega

lemma d3r1_prune_val {α : Type} (δ : α) (Φ : GateOp → List α → α) (init : List α) (n : ℕ)
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
    · simp only [d3r1New, hun, ite_true]
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
        rw [ite_eq_left hat, ite_eq_left (d3r1_new_lt _ _ _ a t hat hA), ite_eq_left hat]
        exact ih a hat hA
      · simp only [hat, ite_false, lt_irrefl]

lemma d3r1_prune_out {α : Type} (δ : α) (Φ : GateOp → List α → α) (init : List α) (n : ℕ)
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

lemma pruned_fanInTwo (n : ℕ) (C : Circuit) (κ : ℕ → Bool) (hfan : FanInTwo C) :
    FanInTwo ⟨d3r1Pruned n κ C.gates, d3r1New n κ (d3r1Top κ C.gates) C.output⟩ := by
  intro g hg
  simp only [d3r1Pruned, List.mem_map, List.mem_filter, List.mem_range] at hg
  obtain ⟨t, ⟨ht, _⟩, rfl⟩ := hg
  have h := hfan C.gates[t] (List.getElem_mem ht)
  simpa only [d3r1PGate, List.getD_eq_getElem _ _ ht, List.length_map] using h

lemma prune_certificate (n : ℕ) (C : Circuit) (κ : ℕ → Bool) (hfan : FanInTwo C)
    (hκ : ∀ t, κ t = true → t < C.gates.length)
    (hcl : ∀ (t : ℕ) (ht : t < C.gates.length), κ t = true →
      ∀ a ∈ C.gates[t].inputs, n ≤ a → a < n + t → κ (a - n) = true)
    (ho : n ≤ C.output → C.output < n + C.gates.length → κ (C.output - n) = true) :
    ∃ D : Circuit, FanInTwo D ∧ D.size = d3r1Top κ C.gates ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  refine ⟨⟨d3r1Pruned n κ C.gates,
    d3r1New n κ (d3r1Top κ C.gates) C.output⟩, pruned_fanInTwo n C κ hfan,
    d3r1_pruned_length n κ C.gates, ?_⟩
  intro x
  exact d3r1_prune_out false GateOp.eval (List.ofFn x) n (by simp)
    C.gates κ C.output hκ hcl ho


lemma prune_deleted_count (n : ℕ) (C : Circuit) (κ : ℕ → Bool) (hfan : FanInTwo C)
    (hκ : ∀ t, κ t = true → t < C.gates.length)
    (hcl : ∀ (t : ℕ) (ht : t < C.gates.length), κ t = true →
      ∀ a ∈ C.gates[t].inputs, n ≤ a → a < n + t → κ (a - n) = true)
    (ho : n ≤ C.output → C.output < n + C.gates.length → κ (C.output - n) = true) :
    ∃ D : Circuit, FanInTwo D ∧
      D.size + ((List.range C.size).filter (fun t => !(κ t))).length = C.size ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  obtain ⟨D, hD, hsize, heval⟩ := prune_certificate n C κ hfan hκ hcl ho
  refine ⟨D, hD, ?_, heval⟩
  rw [hsize]
  change ((List.range C.size).filter κ).length +
    ((List.range C.size).filter (fun t => !(κ t))).length = C.size
  have h := List.length_eq_length_filter_add (l := List.range C.size) κ
  simpa using h.symm


lemma prune_removed_set (n : ℕ) (C : Circuit) (S : Finset ℕ) (hfan : FanInTwo C)
    (hS : ∀ t ∈ S, t < C.gates.length)
    (hcl : ∀ (t : ℕ) (ht : t < C.gates.length), t ∉ S →
      ∀ a ∈ C.gates[t].inputs, n ≤ a → a < n + t → a - n ∉ S)
    (ho : n ≤ C.output → C.output < n + C.gates.length → C.output - n ∉ S) :
    ∃ D : Circuit, FanInTwo D ∧ D.size + S.card = C.size ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  let κ : ℕ → Bool := fun t => decide (t < C.gates.length ∧ t ∉ S)
  have hκ (t : ℕ) : κ t = true ↔ t < C.gates.length ∧ t ∉ S := by simp [κ]
  obtain ⟨D, hD, hsize, heval⟩ := prune_deleted_count n C κ hfan
    (fun t ht => ((hκ t).mp ht).1)
    (by
      intro t ht hkeep a ha han hat
      exact (hκ _).mpr ⟨by omega, hcl t ht ((hκ t).mp hkeep).2 a ha han hat⟩)
    (by
      intro hon hol
      exact (hκ _).mpr ⟨by omega, ho hon hol⟩)
  have hlist : ((List.range C.size).filter (fun t => !(κ t))).toFinset = S := by
    ext t
    simp only [List.mem_toFinset, List.mem_filter, List.mem_range]
    constructor
    · rintro ⟨ht, hk⟩
      by_contra hn
      have hk' : κ t = true := (hκ t).mpr ⟨ht, hn⟩
      simp [hk'] at hk
    · intro ht
      refine ⟨hS t ht, ?_⟩
      simp [κ, ht]
  have hcount := List.toFinset_card_of_nodup
    ((List.nodup_range (n := C.size)).filter (fun t => !(κ t)))
  rw [hlist] at hcount
  refine ⟨D, hD, ?_, heval⟩
  rwa [← hcount] at hsize


lemma prune_dead_cone (n : ℕ) (C : Circuit) (S : Finset ℕ) (hfan : FanInTwo C)
    (hS : ∀ t ∈ S, t < C.gates.length)
    (hdead : ∀ p ∈ S, ∀ (q : ℕ) (hq : q < C.gates.length),
      p < q → n + p ∈ C.gates[q].inputs → q ∈ S)
    (ho : ∀ p ∈ S, C.output ≠ n + p) :
    ∃ D : Circuit, FanInTwo D ∧ D.size + S.card = C.size ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  apply prune_removed_set n C S hfan hS
  · intro t ht hkeep a ha han hat hremoved
    apply hkeep
    exact hdead (a - n) hremoved t ht (by omega) (by simpa [Nat.add_sub_of_le han] using ha)
  · intro hon _ hremoved
    exact ho (C.output - n) hremoved (by omega)

end PEqualNP.Outside.L_meta_3821_aux.Pruning
