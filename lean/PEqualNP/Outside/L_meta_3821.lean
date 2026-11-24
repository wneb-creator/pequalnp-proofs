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


def falseGate : Gate := ⟨.or, []⟩

def replaceWithFalse (C : Circuit) (p : ℕ) : Circuit :=
  ⟨C.gates.set p falseGate, C.output⟩

lemma replaceWithFalse_size (C : Circuit) (p : ℕ) :
    (replaceWithFalse C p).size = C.size := by
  simp [replaceWithFalse, Circuit.size]

lemma replaceWithFalse_fanInTwo (C : Circuit) (p : ℕ) (hfan : FanInTwo C) :
    FanInTwo (replaceWithFalse C p) := by
  intro g hg
  rcases List.mem_or_eq_of_mem_set hg with hg | rfl
  · exact hfan g hg
  · simp [falseGate]

lemma fold_replace_gate (gs : List Gate) (p : ℕ) (hp : p < gs.length)
    (g : Gate) (x : List Bool)
    (heq : g.op.eval (g.inputs.map fun i => (d3r1Fold false GateOp.eval (gs.take p) x).getD i false) =
      gs[p].op.eval (gs[p].inputs.map fun i =>
        (d3r1Fold false GateOp.eval (gs.take p) x).getD i false)) :
    d3r1Fold false GateOp.eval (gs.set p g) x = d3r1Fold false GateOp.eval gs x := by
  have hsplit : gs = gs.take p ++ gs[p] :: gs.drop (p + 1) := by
    rw [← List.drop_eq_getElem_cons hp, List.take_append_drop]
  unfold d3r1Fold
  rw [List.set_eq_take_append_cons_drop, ite_eq_left hp]
  conv_rhs => rw [hsplit]
  simp only [List.foldl_append, List.foldl_cons]
  exact congrArg (fun w => (gs.drop (p + 1)).foldl
    (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w)
    (congrArg (fun b => d3r1Fold false GateOp.eval (gs.take p) x ++ [b]) heq)

lemma replaceAndFalse_wires (C : Circuit) (p i j : ℕ) (hp : p < C.gates.length)
    (hg : C.gates[p] = ⟨.and, [i, j]⟩) (x : List Bool)
    (hz : (d3r1Fold false GateOp.eval (C.gates.take p) x).getD i false = false) :
    (replaceWithFalse C p).wires x = C.wires x := by
  apply fold_replace_gate C.gates p hp falseGate x
  simp only [falseGate, hg, GateOp.eval, List.map_cons, List.map_nil,
    List.all_cons, List.all_nil, List.any_nil, id_eq]
  rw [hz]
  rfl

lemma replaceAndFalse_eval (C : Circuit) (p i j : ℕ) (hp : p < C.gates.length)
    (hg : C.gates[p] = ⟨.and, [i, j]⟩) (x : List Bool)
    (hz : (d3r1Fold false GateOp.eval (C.gates.take p) x).getD i false = false) :
    (replaceWithFalse C p).eval x = C.eval x := by
  simp only [Circuit.eval, replaceAndFalse_wires C p i j hp hg x hz]
  rfl


lemma prune_private_and (n : ℕ) (C : Circuit) (p i j : ℕ) (S : Finset ℕ)
    (P : (Fin n → Bool) → Prop) (hfan : FanInTwo C) (hp : p < C.gates.length)
    (hg : C.gates[p] = ⟨.and, [i, j]⟩)
    (hS : ∀ t ∈ S, t < p)
    (hprivate : ∀ (q : ℕ) (hq : q < C.gates.length), q ∉ S → q ≠ p →
      ∀ a ∈ C.gates[q].inputs, n ≤ a → a < n + q → a - n ∉ S)
    (ho : n ≤ C.output → C.output < n + C.gates.length → C.output - n ∉ S)
    (hz : ∀ x : Fin n → Bool, P x →
      (d3r1Fold false GateOp.eval (C.gates.take p) (List.ofFn x)).getD i false = false) :
    ∃ D : Circuit, FanInTwo D ∧ D.size + S.card = C.size ∧
      ∀ x : Fin n → Bool, P x → D.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  obtain ⟨D, hD, hsize, heval⟩ := prune_removed_set n (replaceWithFalse C p) S
    (replaceWithFalse_fanInTwo C p hfan)
    (by
      intro t ht
      simpa only [replaceWithFalse, List.length_set] using lt_trans (hS t ht) hp)
    (by
      intro q hq hkeep a ha han haq
      by_cases hqp : q = p
      · subst q
        simp only [replaceWithFalse, List.getElem_set_self, falseGate, List.not_mem_nil] at ha
      · have hq' : q < C.gates.length := by
          simpa only [replaceWithFalse, List.length_set] using hq
        have hgate : (replaceWithFalse C p).gates[q] = C.gates[q] := by
          exact List.getElem_set_ne (Ne.symm hqp) hq
        rw [hgate] at ha
        exact hprivate q hq' hkeep hqp a ha han haq)
    (by
      intro hon hol
      exact ho hon (by simpa only [replaceWithFalse, List.length_set] using hol))
  refine ⟨D, hD, ?_, ?_⟩
  · simpa only [replaceWithFalse_size] using hsize
  · intro x hx
    exact (heval x).trans (replaceAndFalse_eval C p i j hp hg (List.ofFn x) (hz x hx))


def aliasGate (n : ℕ) (r : ℕ → ℕ) (t : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map fun a => if a < n + t then r a else a⟩

def aliasGates (n : ℕ) (r : ℕ → ℕ) (gs : List Gate) : List Gate :=
  gs.zipIdx.map fun z => aliasGate n r z.2 z.1

def aliasCircuit (n : ℕ) (C : Circuit) (r : ℕ → ℕ) : Circuit :=
  ⟨aliasGates n r C.gates, r C.output⟩

lemma aliasGates_length (n : ℕ) (r : ℕ → ℕ) (gs : List Gate) :
    (aliasGates n r gs).length = gs.length := by simp [aliasGates]

lemma aliasGates_get (n : ℕ) (r : ℕ → ℕ) (gs : List Gate) (t : ℕ)
    (ht : t < (aliasGates n r gs).length) :
    (aliasGates n r gs)[t] = aliasGate n r t (gs[t]'(by simpa [aliasGates] using ht)) := by
  simp [aliasGates, List.getElem_zipIdx]

lemma aliasCircuit_fanInTwo (n : ℕ) (C : Circuit) (r : ℕ → ℕ) (hfan : FanInTwo C) :
    FanInTwo (aliasCircuit n C r) := by
  intro g hg
  obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.mp hg
  simp only [aliasCircuit] at ht ⊢
  rw [aliasGates_get n r C.gates t ht]
  have ht' : t < C.gates.length := by simpa [aliasCircuit, aliasGates] using ht
  simpa only [aliasGate, List.length_map] using hfan C.gates[t] (List.getElem_mem ht')

lemma aliasGates_values (n : ℕ) (gs : List Gate) (r : ℕ → ℕ) (x : List Bool)
    (hx : x.length = n) (hr : ∀ a, r a ≤ a)
    (heq : ∀ a, (d3r1Fold false GateOp.eval gs x).getD (r a) false =
      (d3r1Fold false GateOp.eval gs x).getD a false) :
    ∀ u, (d3r1Fold false GateOp.eval (aliasGates n r gs) x).getD u false =
      (d3r1Fold false GateOp.eval gs x).getD u false := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    by_cases hun : u < n
    · rw [d3r1Fold_lt _ _ _ _ _ (by omega), d3r1Fold_lt _ _ _ _ _ (by omega)]
    · by_cases hul : u < n + gs.length
      · obtain ⟨t, rfl⟩ : ∃ t, u = n + t := ⟨u - n, by omega⟩
        have ht : t < gs.length := by omega
        have ht' : t < (aliasGates n r gs).length := by simpa [aliasGates] using ht
        have hleft := d3r1Fold_gate false GateOp.eval (aliasGates n r gs) x t ht'
        have hright := d3r1Fold_gate false GateOp.eval gs x t ht
        rw [hx] at hleft hright
        rw [hleft, hright, aliasGates_get n r gs t ht']
        simp only [aliasGate, List.map_map]
        congr 1
        apply List.map_congr_left
        intro a _
        simp only [Function.comp_apply]
        by_cases hat : a < n + t
        · have hrat : r a < n + t := lt_of_le_of_lt (hr a) hat
          rw [ite_eq_left hat, ite_eq_left (by omega), ite_eq_left (by omega)]
          exact (ih (r a) hrat).trans (heq a)
        · rw [ite_eq_right hat, ite_eq_right (by omega), ite_eq_right (by omega)]
      · rw [d3r1Fold_ge _ _ _ _ _ (by rw [aliasGates_length]; omega),
          d3r1Fold_ge _ _ _ _ _ (by omega)]

lemma aliasCircuit_eval (n : ℕ) (C : Circuit) (r : ℕ → ℕ) (x : Fin n → Bool)
    (hr : ∀ a, r a ≤ a)
    (heq : ∀ a, (C.wires (List.ofFn x)).getD (r a) false =
      (C.wires (List.ofFn x)).getD a false) :
    (aliasCircuit n C r).eval (List.ofFn x) = C.eval (List.ofFn x) := by
  exact (aliasGates_values n C.gates r (List.ofFn x) (by simp) hr heq (r C.output)).trans
    (heq C.output)


lemma alias_prune (n : ℕ) (C : Circuit) (r : ℕ → ℕ) (S : Finset ℕ)
    (P : (Fin n → Bool) → Prop) (hfan : FanInTwo C) (hr : ∀ a, r a ≤ a)
    (hS : ∀ t ∈ S, t < C.gates.length)
    (hcl : ∀ (t : ℕ) (ht : t < C.gates.length), t ∉ S →
      ∀ a ∈ C.gates[t].inputs, a < n + t → n ≤ r a → r a - n ∉ S)
    (ho : n ≤ r C.output → r C.output < n + C.gates.length → r C.output - n ∉ S)
    (heq : ∀ x : Fin n → Bool, P x → ∀ a,
      (C.wires (List.ofFn x)).getD (r a) false = (C.wires (List.ofFn x)).getD a false) :
    ∃ D : Circuit, FanInTwo D ∧ D.size + S.card = C.size ∧
      ∀ x : Fin n → Bool, P x → D.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  obtain ⟨D, hD, hsize, hev⟩ := prune_removed_set n (aliasCircuit n C r) S
    (aliasCircuit_fanInTwo n C r hfan)
    (by intro t ht; simpa only [aliasCircuit, aliasGates_length] using hS t ht)
    (by
      intro t ht hkeep a ha han hat
      change a ∈ (aliasGates n r C.gates)[t].inputs at ha
      rw [aliasGates_get n r C.gates t ht] at ha
      obtain ⟨b, hb, hba⟩ := List.mem_map.mp ha
      by_cases hbt : b < n + t
      · have hba' : r b = a := by simpa only [ite_eq_left hbt] using hba
        subst a
        simp only [ite_eq_left hbt] at han ⊢
        exact hcl t (by simpa only [aliasCircuit, aliasGates_length] using ht)
          hkeep b hb hbt han
      · have hba' : b = a := by simpa only [ite_eq_right hbt] using hba
        omega)
    (by
      intro hon hol
      exact ho hon (by simpa only [aliasCircuit, aliasGates_length] using hol))
  refine ⟨D, hD, ?_, ?_⟩
  · simpa only [Circuit.size, aliasCircuit, aliasGates_length] using hsize
  · intro x hx
    exact (hev x).trans (aliasCircuit_eval n C r x hr (heq x hx))

def bypassPair (n p q i w a : ℕ) : ℕ :=
  if a = n + q then (if w = n + p then i else w) else if a = n + p then i else a

lemma bypassPair_le (n p q i w : ℕ) (hi : i < n) (_hpq : p < q) (hw : w < n + q) :
    ∀ a, bypassPair n p q i w a ≤ a := by
  intro a
  unfold bypassPair
  split_ifs <;> omega

lemma bypassPair_ne_left (n p q i w a : ℕ) (hi : i < n) :
    bypassPair n p q i w a ≠ n + p := by
  unfold bypassPair
  split_ifs <;> omega

lemma bypassPair_ne_right (n p q i w a : ℕ) (hi : i < n) (hw : w < n + q) :
    bypassPair n p q i w a ≠ n + q := by
  unfold bypassPair
  split_ifs <;> omega

lemma bypassPair_values (n p q i w : ℕ) (v : ℕ → Bool)
    (hp : v (n + p) = v i) (hq : v (n + q) = v w) :
    ∀ a, v (bypassPair n p q i w a) = v a := by
  intro a
  unfold bypassPair
  split_ifs with haq hwp hap
  · subst a
    rw [hwp] at hq
    exact (hq.trans hp).symm
  · subst a
    exact hq.symm
  · subst a
    exact hp.symm
  · rfl


lemma bypassPair_outside (n p q i w a : ℕ) (S : Finset ℕ) (hi : i < n)
    (hwS : n ≤ w → w - n ∉ S) (haS : n ≤ a → a - n ∉ S) :
    n ≤ bypassPair n p q i w a → bypassPair n p q i w a - n ∉ S := by
  unfold bypassPair
  split_ifs
  · omega
  · exact hwS
  · omega
  · exact haS

lemma private_pair_saving (n : ℕ) (C : Circuit) (p q i w : ℕ) (S : Finset ℕ)
    (P : (Fin n → Bool) → Prop) (hfan : FanInTwo C) (hp : p < C.gates.length)
    (hpq : p < q) (hq : q < C.gates.length) (hi : i < n) (hw : w < n + q)
    (hS : ∀ t ∈ S, t < p)
    (hprivate : ∀ (t : ℕ) (ht : t < C.gates.length), t ∉ S → t ≠ p →
      ∀ a ∈ C.gates[t].inputs, n ≤ a → a < n + t → a - n ∉ S)
    (hwS : n ≤ w → w - n ∉ S)
    (ho : n ≤ C.output → C.output < n + C.gates.length → C.output - n ∉ S)
    (hvp : ∀ x : Fin n → Bool, P x → (C.wires (List.ofFn x)).getD (n + p) false =
      (C.wires (List.ofFn x)).getD i false)
    (hvq : ∀ x : Fin n → Bool, P x → (C.wires (List.ofFn x)).getD (n + q) false =
      (C.wires (List.ofFn x)).getD w false) :
    ∃ D : Circuit, FanInTwo D ∧ D.size + S.card + 2 = C.size ∧
      ∀ x : Fin n → Bool, P x → D.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  let T : Finset ℕ := insert p (insert q S)
  let r : ℕ → ℕ := bypassPair n p q i w
  have hpn : p ∉ S := by intro hm; have := hS p hm; omega
  have hqn : q ∉ S := by intro hm; have := hS q hm; omega
  have hTcard : T.card = S.card + 2 := by simp [T, hpn, hqn, ne_of_lt hpq]
  have routside (a : ℕ) (ha : n ≤ a → a - n ∉ S) (hra : n ≤ r a) : r a - n ∉ T := by
    have hleft := bypassPair_ne_left n p q i w a hi
    have hright := bypassPair_ne_right n p q i w a hi hw
    have hrest := bypassPair_outside n p q i w a S hi hwS ha hra
    simp only [T, Finset.mem_insert]
    intro hm
    rcases hm with hm | hm | hm
    · exact hleft (by change bypassPair n p q i w a - n = p at hm; change n ≤ bypassPair n p q i w a at hra; omega)
    · exact hright (by change bypassPair n p q i w a - n = q at hm; change n ≤ bypassPair n p q i w a at hra; omega)
    · exact hrest hm
  obtain ⟨D, hD, hsize, hev⟩ := alias_prune n C r T P hfan
    (bypassPair_le n p q i w hi hpq hw)
    (by
      intro t ht
      simp only [T, Finset.mem_insert] at ht
      rcases ht with rfl | rfl | ht
      · exact hp
      · exact hq
      · exact lt_trans (hS t ht) hp)
    (by
      intro t ht hkeep a ha hat hra
      apply routside a _ hra
      intro han
      apply hprivate t ht
      · intro hm; exact hkeep (by simp [T, hm])
      · intro hm; subst t; exact hkeep (by simp [T])
      · exact ha
      · exact han
      · exact hat)
    (by
      intro hra _
      apply routside C.output _ hra
      intro hon hm
      have hs := hS (C.output - n) hm
      exact ho hon (by omega) hm)
    (by
      intro x hx
      exact bypassPair_values n p q i w
        (fun a => (C.wires (List.ofFn x)).getD a false) (hvp x hx) (hvq x hx))
  refine ⟨D, hD, ?_, hev⟩
  rw [hTcard] at hsize
  omega


lemma private_and_or_saving (n : ℕ) (C : Circuit) (p q i j w : ℕ) (S : Finset ℕ)
    (P : (Fin n → Bool) → Prop) (hfan : FanInTwo C) (hp : p < C.gates.length)
    (hpq : p < q) (hq : q < C.gates.length) (hi : i < n) (hw : w < n + q)
    (hgp : C.gates[p] = ⟨.and, [i, j]⟩)
    (hgq : C.gates[q] = ⟨.or, [n + p, w]⟩)
    (hS : ∀ t ∈ S, t < p)
    (hprivate : ∀ (t : ℕ) (ht : t < C.gates.length), t ∉ S → t ≠ p →
      ∀ a ∈ C.gates[t].inputs, n ≤ a → a < n + t → a - n ∉ S)
    (ho : n ≤ C.output → C.output < n + C.gates.length → C.output - n ∉ S)
    (hz : ∀ x : Fin n → Bool, P x → x ⟨i, hi⟩ = false) :
    ∃ D : Circuit, FanInTwo D ∧ D.size + S.card + 2 = C.size ∧
      ∀ x : Fin n → Bool, P x → D.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  have hqn : q ∉ S := by intro hm; have := hS q hm; omega
  have hwS : n ≤ w → w - n ∉ S := by
    intro hwn
    exact hprivate q hq hqn (ne_of_gt hpq) w (by rw [hgq]; simp) hwn hw
  have hzero (x : Fin n → Bool) (hx : P x) :
      (C.wires (List.ofFn x)).getD i false = false := by
    change (d3r1Fold false GateOp.eval C.gates (List.ofFn x)).getD i false = false
    rw [d3r1Fold_lt _ _ _ _ _ (by simpa using hi)]
    simpa [List.getD_eq_getElem?_getD, hi] using hz x hx
  have hpzero (x : Fin n → Bool) (hx : P x) :
      (C.wires (List.ofFn x)).getD (n + p) false = false := by
    have hv := d3r1Fold_gate false GateOp.eval C.gates (List.ofFn x) p hp
    simp only [List.length_ofFn, hgp, GateOp.eval, List.map_cons, List.map_nil,
      List.all_cons, List.all_nil, id_eq] at hv
    change (d3r1Fold false GateOp.eval C.gates (List.ofFn x)).getD (n + p) false = false
    rw [hv, ite_eq_left (by omega)]
    change ((C.wires (List.ofFn x)).getD i false && _) = false
    rw [hzero x hx]
    rfl
  apply private_pair_saving n C p q i w S P hfan hp hpq hq hi hw hS hprivate hwS ho
  · intro x hx
    rw [hpzero x hx, hzero x hx]
  · intro x hx
    have hv := d3r1Fold_gate false GateOp.eval C.gates (List.ofFn x) q hq
    simp only [List.length_ofFn, hgq, GateOp.eval, List.map_cons, List.map_nil,
      List.any_cons, List.any_nil, id_eq] at hv
    change (d3r1Fold false GateOp.eval C.gates (List.ofFn x)).getD (n + q) false = _
    rw [hv, ite_eq_left (by omega), ite_eq_left hw]
    change ((C.wires (List.ofFn x)).getD (n + p) false || _) = _
    rw [hpzero x hx]
    simp only [Bool.false_or, Bool.or_false]
    rfl

lemma private_and_or_four (n : ℕ) (C : Circuit) (p q i j w : ℕ) (S : Finset ℕ)
    (P : (Fin n → Bool) → Prop) (hfan : FanInTwo C) (hp : p < C.gates.length)
    (hpq : p < q) (hq : q < C.gates.length) (hi : i < n) (hw : w < n + q)
    (hgp : C.gates[p] = ⟨.and, [i, j]⟩)
    (hgq : C.gates[q] = ⟨.or, [n + p, w]⟩)
    (hS : ∀ t ∈ S, t < p) (hcard : S.card = 2)
    (hprivate : ∀ (t : ℕ) (ht : t < C.gates.length), t ∉ S → t ≠ p →
      ∀ a ∈ C.gates[t].inputs, n ≤ a → a < n + t → a - n ∉ S)
    (ho : n ≤ C.output → C.output < n + C.gates.length → C.output - n ∉ S)
    (hz : ∀ x : Fin n → Bool, P x → x ⟨i, hi⟩ = false) :
    ∃ D : Circuit, FanInTwo D ∧ D.size + 4 = C.size ∧
      ∀ x : Fin n → Bool, P x → D.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  obtain ⟨D, hD, hsize, hev⟩ := private_and_or_saving n C p q i j w S P hfan hp hpq hq hi hw
    hgp hgq hS hprivate ho hz
  exact ⟨D, hD, by omega, hev⟩


namespace StarCover

open Finset

def Covers (S : Finset (Fin 10)) : Prop :=
  ∀ i : Fin 5,
    (Fin.castAdd 5 i ∈ S ∨ Fin.castAdd 5 (i + (1 : Fin 5)) ∈ S) ∧
    (Fin.castAdd 5 i ∈ S ∨ Fin.natAdd 5 i ∈ S) ∧
    (Fin.natAdd 5 i ∈ S ∨ Fin.natAdd 5 (i + (2 : Fin 5)) ∈ S)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
lemma cover_card : ∀ S : Finset (Fin 10), Covers S → 6 ≤ S.card := by
  unfold Covers
  decide +kernel

def endpoints (e : Fin 3 × Fin 5) : Fin 10 × Fin 10 :=
  if e.1 = 0 then (Fin.castAdd 5 e.2, Fin.castAdd 5 (e.2 + 1))
  else if e.1 = 1 then (Fin.castAdd 5 e.2, Fin.natAdd 5 e.2)
  else (Fin.natAdd 5 e.2, Fin.natAdd 5 (e.2 + 2))

lemma assigned_centers_cover (c : Fin 3 × Fin 5 → Fin 10)
    (hc : ∀ e, c e = (endpoints e).1 ∨ c e = (endpoints e).2) :
    Covers (Finset.univ.image c) := by
  intro i
  have mem (e : Fin 3 × Fin 5) : c e ∈ Finset.univ.image c :=
    Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩
  have edge (e : Fin 3 × Fin 5) :
      (endpoints e).1 ∈ Finset.univ.image c ∨ (endpoints e).2 ∈ Finset.univ.image c := by
    rcases hc e with h | h
    · exact Or.inl (h ▸ mem e)
    · exact Or.inr (h ▸ mem e)
  exact ⟨by simpa [endpoints] using edge (0, i),
    by simpa [endpoints] using edge (1, i),
    by simpa [endpoints] using edge (2, i)⟩

lemma assigned_star_cost (c : Fin 3 × Fin 5 → Fin 10)
    (hc : ∀ e, c e = (endpoints e).1 ∨ c e = (endpoints e).2) :
    20 ≤ 15 + (Finset.univ.image c).card - 1 := by
  have := cover_card _ (assigned_centers_cover c hc)
  omega

end StarCover

end PEqualNP.Outside.L_meta_3821_aux.Pruning
