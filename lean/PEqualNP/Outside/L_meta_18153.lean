import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18153

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

theorem run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
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

theorem mono (gs : List Gate) (x y : List Bool) (hl : x.length = y.length)
    (h : ∀ i, x.getD i false = true → y.getD i false = true)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ i, (run gs x).getD i false = true → (run gs y).getD i false = true := by
  induction gs using List.reverseRecOn with
  | nil => intro i hi; exact h i hi
  | append_singleton gs g ih =>
    intro i hi
    have ih' := ih (fun g hg' => hg g (by simp [hg']))
    have l1 := run_length gs x
    have l2 := run_length gs y
    rw [run_snoc] at hi ⊢
    rcases Nat.lt_trichotomy i (x.length + gs.length) with hlt | heq | hgt
    · rw [getD_lt _ _ _ (by omega)] at hi ⊢; exact ih' i hi
    · have e1 : i = (run gs x).length := by omega
      have e2 : i = (run gs y).length := by omega
      have hi' : g.op.eval (g.inputs.map fun i => (run gs x).getD i false) = true := by
        rw [← getD_at (run gs x) (g.op.eval (g.inputs.map fun i => (run gs x).getD i false)), ← e1]
        exact hi
      rw [e2, getD_at]
      rcases hg g (by simp) with ho | ho
      · rw [ho] at hi' ⊢
        simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id] at hi' ⊢
        exact fun q hq => ih' q (hi' q hq)
      · rw [ho] at hi' ⊢
        simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id] at hi' ⊢
        obtain ⟨q, h1, h2⟩ := hi'
        exact ⟨q, h1, ih' q h2⟩
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hi; cases hi

theorem det : ∀ (gs : List Gate) (N : ℕ), (∀ g ∈ gs, g.inputs.length ≤ 2) → ∀ S : Finset ℕ, ∃ S' : Finset ℕ, S'.card ≤ S.card + gs.length ∧
    ∀ x y : List Bool, x.length = N → y.length = N → (∀ w ∈ S', x.getD w false = y.getD w false) → ∀ w ∈ S, (run gs x).getD w false = (run gs y).getD w false := by
  intro gs
  induction gs with
  | nil => intro N _ S; exact ⟨S, by simp, fun x y _ _ h => h⟩
  | cons g gs ih =>
    intro N hg S
    obtain ⟨T, hT, hd⟩ := ih (N + 1) (fun g' h' => hg g' (List.mem_cons_of_mem _ h')) S
    have step : ∀ x y : List Bool, x.length = N → y.length = N → (∀ w ∈ T, w ≠ N → x.getD w false = y.getD w false) →
        (N ∈ T → ∀ w ∈ g.inputs, x.getD w false = y.getD w false) → ∀ w ∈ S, (run (g :: gs) x).getD w false = (run (g :: gs) y).getD w false := by
      intro x y hx hy h1 h2
      refine hd (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) (y ++ [g.op.eval (g.inputs.map fun i => y.getD i false)]) (by simp [hx]) (by simp [hy]) ?_
      intro w hw
      rcases Nat.lt_trichotomy w N with h | h | h
      · rw [getD_lt _ _ _ (by omega), getD_lt _ _ _ (by omega)]
        exact h1 w hw (by omega)
      · subst h
        have e1 : (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]).getD w false = g.op.eval (g.inputs.map fun i => x.getD i false) := by
          rw [← hx]; exact getD_at _ _
        have e2 : (y ++ [g.op.eval (g.inputs.map fun i => y.getD i false)]).getD w false = g.op.eval (g.inputs.map fun i => y.getD i false) := by
          rw [← hy]; exact getD_at _ _
        rw [e1, e2, List.map_congr_left fun i hi => h2 hw i hi]
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    by_cases hN : N ∈ T
    · refine ⟨T.erase N ∪ g.inputs.toFinset, ?_, fun x y hx hy h => step x y hx hy (fun w hw hne => h w ?_) (fun _ w hw => h w ?_)⟩
      · have e1 := Finset.card_union_le (T.erase N) g.inputs.toFinset
        have e2 := Finset.card_erase_add_one hN
        have e3 := List.toFinset_card_le g.inputs
        have e4 := hg g List.mem_cons_self
        simp only [List.length_cons]
        omega
      · exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hne, hw⟩)
      · exact Finset.mem_union_right _ (List.mem_toFinset.2 hw)
    · refine ⟨T, by simp only [List.length_cons]; omega, fun x y hx hy h => step x y hx hy (fun w hw _ => h w hw) (fun h' => absurd h' hN)⟩

def rv (w : List Bool) : Bool ⊕ ℕ → Bool
  | .inl b => b
  | .inr t => w.getD t false

def fok (g : Gate) : Prop := (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

theorem rv_ext (hs e : List Gate) (y : List Bool) (r : Bool ⊕ ℕ) (h : ∀ t, r = .inr t → t < y.length + hs.length) :
    rv (run (hs ++ e) y) r = rv (run hs y) r := by
  rcases r with b | t
  · rfl
  · exact run_prefix _ _ _ _ (h t rfl)

theorem emit (N : ℕ) (hs : List Gate) (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (rs : List (Bool ⊕ ℕ)) (hl : rs.length ≤ 2) (hv : ∀ r ∈ rs, ∀ t, r = .inr t → t < N + hs.length) :
    ∃ (r : Bool ⊕ ℕ) (e : List Gate), e.length ≤ 1 ∧ (∀ g ∈ e, fok g) ∧ (∀ t, r = .inr t → t < N + hs.length + e.length) ∧
      ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
  have keep : ∀ r : Bool ⊕ ℕ, (∀ t, r = .inr t → t < N + hs.length) → (∀ y : List Bool, y.length = N → rv (run hs y) r = op.eval (rs.map (rv (run hs y)))) →
      ∃ (r : Bool ⊕ ℕ) (e : List Gate), e.length ≤ 1 ∧ (∀ g ∈ e, fok g) ∧ (∀ t, r = .inr t → t < N + hs.length + e.length) ∧
        ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
    intro r h1 h2
    exact ⟨r, [], by simp, by simp, by simpa using h1, fun y hy => by rw [List.append_nil]; exact h2 y hy⟩
  have add : ∀ g : Gate, fok g → (∀ y : List Bool, y.length = N → g.op.eval (g.inputs.map fun i => (run hs y).getD i false) = op.eval (rs.map (rv (run hs y)))) →
      ∃ (r : Bool ⊕ ℕ) (e : List Gate), e.length ≤ 1 ∧ (∀ g ∈ e, fok g) ∧ (∀ t, r = .inr t → t < N + hs.length + e.length) ∧
        ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
    intro g h1 h2
    refine ⟨.inr (N + hs.length), [g], by simp, by simpa using h1, ?_, fun y hy => ?_⟩
    · intro t ht
      cases ht
      simp
    · have : N + hs.length = (run hs y).length := by rw [run_length, hy]
      simp only [rv]
      rw [run_snoc, this, getD_at]
      exact h2 y hy
  rcases rs with _ | ⟨r, _ | ⟨s, _ | ⟨u, rs⟩⟩⟩
  · rcases hop with rfl | rfl
    · exact keep (.inl true) (by simp) (by intro y _; rfl)
    · exact keep (.inl false) (by simp) (by intro y _; rfl)
  · have hr := hv r (by simp)
    rcases hop with rfl | rfl
    · exact keep r hr (by intro y _; simp [GateOp.eval])
    · exact keep r hr (by intro y _; simp [GateOp.eval])
  · have hr := hv r (by simp)
    have hs' := hv s (by simp)
    rcases hop with rfl | rfl
    · rcases r with b | t
      · cases b
        · exact keep (.inl false) (by simp) (by intro y _; simp [GateOp.eval, rv])
        · exact keep s hs' (by intro y _; simp [GateOp.eval, rv])
      · rcases s with b | q
        · cases b
          · exact keep (.inl false) (by simp) (by intro y _; simp [GateOp.eval, rv])
          · exact keep (.inr t) hr (by intro y _; simp [GateOp.eval, rv])
        · exact add ⟨GateOp.and, [t, q]⟩ ⟨by simp, by simp⟩ (by intro y _; simp [GateOp.eval, rv])
    · rcases r with b | t
      · cases b
        · exact keep s hs' (by intro y _; simp [GateOp.eval, rv])
        · exact keep (.inl true) (by simp) (by intro y _; simp [GateOp.eval, rv])
      · rcases s with b | q
        · cases b
          · exact keep (.inr t) hr (by intro y _; simp [GateOp.eval, rv])
          · exact keep (.inl true) (by simp) (by intro y _; simp [GateOp.eval, rv])
        · exact add ⟨GateOp.or, [t, q]⟩ ⟨by simp, by simp⟩ (by intro y _; simp [GateOp.eval, rv])
  · simp at hl

theorem engine3 {X : Type} (n M : ℕ) (C : Circuit) (src tgt : X → List Bool) (hsrc : ∀ x, (src x).length = n) (htgt : ∀ x, (tgt x).length = M) (F : Finset ℕ)
    (hC : PEqualNP.MetaComplexity.Monotone2 C)
    (h0 : ∀ w < n, (∃ b, ∀ x, (src x).getD w false = b) ∨ ∃ t, t < M ∧ ∀ x, (src x).getD w false = (tgt x).getD t false)
    (hne : ¬∃ b, ∀ x, C.eval (src x) = b)
    (hF : ∀ j ∈ F, j < C.gates.length ∧ ((∃ b, ∀ x, (run C.gates (src x)).getD (n + j) false = b) ∨
      ∃ w < n + j, ∀ x, (run C.gates (src x)).getD (n + j) false = (run C.gates (src x)).getD w false)) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ D.size + F.card ≤ C.size ∧ ∀ x, D.eval (tgt x) = C.eval (src x) := by
  classical
  have key : ∀ k, k ≤ C.gates.length → ∃ (hs : List Gate) (m : ℕ → Bool ⊕ ℕ), (∀ g ∈ hs, fok g) ∧ hs.length + (F.filter fun j => j < k).card ≤ k ∧
      (∀ w t, w < n + k → m w = .inr t → t < M + hs.length) ∧
      ∀ x : X, ∀ w < n + k, (run C.gates (src x)).getD w false = rv (run hs (tgt x)) (m w) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨[], fun w => if h : ∃ t, t < M ∧ ∀ x, (src x).getD w false = (tgt x).getD t false then .inr h.choose else if hb : ∃ b, ∀ x, (src x).getD w false = b then .inl hb.choose else .inl false, by simp, by simp, ?_, ?_⟩
      · intro w t hw ht
        beta_reduce at ht
        split_ifs at ht with h1 h2
        cases ht
        simpa using h1.choose_spec.1
      · intro x w hw
        simp only [Nat.add_zero] at hw
        rw [run_input _ _ _ (by rw [hsrc]; exact hw)]
        beta_reduce
        split_ifs with h1 h2
        · exact h1.choose_spec.2 x
        · exact h2.choose_spec x
        · rcases h0 w hw with h | h
          · exact absurd h h2
          · exact absurd h h1
    | succ k ih =>
      intro hk
      obtain ⟨hs, m, h1, h2, h3, h4⟩ := ih (by omega)
      have hk' : k < C.gates.length := by omega
      have fin : ∀ (r : Bool ⊕ ℕ) (e : List Gate), (∀ g ∈ e, fok g) → (∀ t, r = .inr t → t < M + hs.length + e.length) → e.length + (if k ∈ F then 1 else 0) ≤ 1 →
          (∀ x : X, (run C.gates (src x)).getD (n + k) false = rv (run (hs ++ e) (tgt x)) r) →
          ∃ (hs : List Gate) (m : ℕ → Bool ⊕ ℕ), (∀ g ∈ hs, fok g) ∧ hs.length + (F.filter fun j => j < k + 1).card ≤ k + 1 ∧
      (∀ w t, w < n + (k + 1) → m w = .inr t → t < M + hs.length) ∧
      ∀ x : X, ∀ w < n + (k + 1), (run C.gates (src x)).getD w false = rv (run hs (tgt x)) (m w) := by
        intro r e he hr hlen hval
        refine ⟨hs ++ e, Function.update m (n + k) r, ?_, ?_, ?_, ?_⟩
        · intro g hg
          rcases List.mem_append.1 hg with hg | hg
          · exact h1 g hg
          · exact he g hg
        · have e1 : (F.filter fun j => j < k + 1) ⊆ (F.filter fun j => j < k) ∪ (if k ∈ F then {k} else ∅) := by
            intro j hj
            rw [Finset.mem_filter] at hj
            rcases Nat.lt_or_ge j k with h | h
            · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hj.1, h⟩)
            · have : j = k := by omega
              subst this
              rw [if_pos hj.1]; simp
          have e2 := (Finset.card_le_card e1).trans (Finset.card_union_le _ _)
          rw [List.length_append]
          by_cases hkF : k ∈ F
          · rw [if_pos hkF] at e2 hlen
            rw [Finset.card_singleton] at e2
            omega
          · rw [if_neg hkF] at e2 hlen
            rw [Finset.card_empty] at e2
            omega
        · intro w t hw ht
          rw [List.length_append]
          by_cases hwe : w = n + k
          · subst hwe; rw [Function.update_self] at ht
            have := hr t ht; omega
          · rw [Function.update_of_ne hwe] at ht
            have := h3 w t (by omega) ht; omega
        · intro x w hw
          by_cases hwe : w = n + k
          · subst hwe; rw [Function.update_self]; exact hval x
          · rw [Function.update_of_ne hwe, h4 x w (by omega)]
            refine (rv_ext hs e (tgt x) (m w) fun t ht => ?_).symm
            have := h3 w t (by omega) ht
            rw [htgt]; exact this
      by_cases hkF : k ∈ F
      · rcases (hF k hkF).2 with ⟨b, hb⟩ | ⟨w, hw, hb⟩
        · exact fin (.inl b) [] (by simp) (by simp) (by simp [hkF]) (fun x => hb x)
        · refine fin (m w) [] (by simp) (fun t ht => by simpa using h3 w t hw ht) (by simp [hkF]) (fun x => ?_)
          rw [List.append_nil, ← h4 x w hw]
          exact hb x
      · have hg := hC _ (List.getElem_mem hk')
        have hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or := by simpa using hg.1
        let m' : ℕ → Bool ⊕ ℕ := fun i => if i < n + k then m i else .inl false
        obtain ⟨r, e, e1, e2, e3, e4⟩ := emit M hs C.gates[k].op hop (C.gates[k].inputs.map m') (by rw [List.length_map]; exact hg.2) (by
          intro r hr t ht
          obtain ⟨i, _, rfl⟩ := List.mem_map.1 hr
          simp only [m'] at ht
          split_ifs at ht with h
          exact h3 i t h ht)
        refine fin r e e2 e3 (by simp [hkF]; exact e1) (fun x => ?_)
        rw [e4 _ (htgt x)]
        have rg := run_gate C.gates (src x) k hk'
        rw [hsrc] at rg
        rw [rg, List.map_map]
        congr 1
        refine List.map_congr_left fun i _ => ?_
        simp only [Function.comp, m']
        split_ifs with h
        · exact h4 x i h
        · rfl
  obtain ⟨hs, m, h1, h2, h3, h4⟩ := key C.gates.length le_rfl
  have hFc : (F.filter fun j => j < C.gates.length) = F := Finset.filter_true_of_mem fun j hj => (hF j hj).1
  rw [hFc] at h2
  have hout : C.output < n + C.gates.length := by
    by_contra h
    refine hne ⟨false, fun x => ?_⟩
    change (run C.gates (src x)).getD C.output false = false
    rw [List.getD_eq_default _ _ (by rw [run_length, hsrc]; omega)]
  have hev : ∀ x, C.eval (src x) = rv (run hs (tgt x)) (m C.output) := fun x => h4 x _ hout
  rcases hm : m C.output with b | t
  · exact absurd ⟨b, fun x => by rw [hev, hm]; rfl⟩ hne
  · refine ⟨⟨hs, t⟩, ?_, h2, fun x => ?_⟩
    · intro g hg
      exact ⟨by simpa using (h1 g hg).1, (h1 g hg).2⟩
    · have := hev x
      rw [hm] at this
      exact this.symm

def rd (A B : ℕ → ℕ) (k w : ℕ) : Prop := A k = w ∨ B k = w

def pt (n u v : ℕ) : ℕ → Bool := fun k => decide (k = u ∨ k = n + v)

def Tg (n m : ℕ) (A B : ℕ → ℕ) (An : ℕ → Bool) (i j : ℕ) : Prop :=
  i < n ∧ j < m ∧ An j = false ∧ ((A j = i ∧ B j = n + i) ∨ (A j = n + i ∧ B j = i)) ∧
    ∀ k < m, (rd A B k i ∨ rd A B k (n + i)) → k = j

def Kill (n : ℕ) (V : (ℕ → Bool) → ℕ → Bool) (i j : ℕ) : Prop :=
  (∃ b, ∀ u v, u < n → v < n → u ≠ i → v ≠ i → V (pt n u v) (n + n + j) = b) ∨
    ∃ w < n + n + j, ∀ u v, u < n → v < n → u ≠ i → v ≠ i → V (pt n u v) (n + n + j) = V (pt n u v) w

theorem core (n : ℕ) (hn : 3 ≤ n) (m : ℕ) (A B : ℕ → ℕ) (An : ℕ → Bool) (V : (ℕ → Bool) → ℕ → Bool) (o : ℕ)
    (hA : ∀ j < m, A j < n + n + j) (hB : ∀ j < m, B j < n + n + j) (hAB : ∀ j < m, A j ≠ B j)
    (v0 : ∀ P k, k < n + n → V P k = P k)
    (v1 : ∀ P j, j < m → V P (n + n + j) = if An j = true then V P (A j) && V P (B j) else V P (A j) || V P (B j))
    (ho : o < n + n + m)
    (hf : ∀ u v, u < n → v < n → V (pt n u v) o = decide (u ≠ v))
    (irr : ∀ j < m, ∀ w < n + n + j, ¬∀ u v, u < n → v < n → V (pt n u v) (n + n + j) = V (pt n u v) w) :
    ∃ i < n, ∃ a b c, a < m ∧ b < m ∧ c < m ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ Kill n V i a ∧ Kill n V i b ∧ Kill n V i c := by
  classical
  have mono : ∀ (P Q : ℕ → Bool), (∀ k, P k = true → Q k = true) → ∀ w < n + n + m, V P w = true → V Q w = true := by
    intro P Q hPQ w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw h
      by_cases hwn : w < n + n
      · rw [v0 _ _ hwn] at h ⊢; exact hPQ _ h
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + n + j := ⟨w - (n + n), by omega⟩
        have hj : j < m := by omega
        have a1 := hA j hj
        have b1 := hB j hj
        rw [v1 _ _ hj] at h ⊢
        split_ifs at h ⊢ with hAn
        · rw [Bool.and_eq_true] at h ⊢
          exact ⟨ih _ a1 (by omega) h.1, ih _ b1 (by omega) h.2⟩
        · rw [Bool.or_eq_true] at h ⊢
          exact h.imp (ih _ a1 (by omega)) (ih _ b1 (by omega))
  have rep : ∀ (Hd : ℕ → Prop) (P Q : ℕ → Bool), (∀ k < n + n, ¬Hd k → P k = Q k) →
      (∀ j < m, ¬Hd (n + n + j) → (Hd (A j) ∨ Hd (B j)) → V P (n + n + j) = V Q (n + n + j)) →
      ∀ w < n + n + m, ¬Hd w → V P w = V Q w := by
    intro Hd P Q h1 h2 w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw hH
      by_cases hwn : w < n + n
      · rw [v0 _ _ hwn, v0 _ _ hwn]; exact h1 _ hwn hH
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + n + j := ⟨w - (n + n), by omega⟩
        have hj : j < m := by omega
        have a1 := hA j hj
        have b1 := hB j hj
        by_cases hr : Hd (A j) ∨ Hd (B j)
        · exact h2 j hj hH hr
        · rw [not_or] at hr
          rw [v1 _ _ hj, v1 _ _ hj, ih _ a1 (by omega) hr.1, ih _ b1 (by omega) hr.2]
  have row1 : ∀ u < n, V (fun k => decide (k = u)) o = false := by
    intro u hu
    by_contra h
    have h1 := mono (fun k => decide (k = u)) (pt n u u) (by
      intro k hk
      have : k = u := by simpa using hk
      simp [pt, this]) o ho (by simpa using h)
    rw [hf u u hu hu] at h1
    simp at h1
  have col1 : ∀ v < n, V (fun k => decide (k = n + v)) o = false := by
    intro v hv
    by_contra h
    have h1 := mono (fun k => decide (k = n + v)) (pt n v v) (by
      intro k hk
      have : k = n + v := by simpa using hk
      simp [pt, this]) o ho (by simpa using h)
    rw [hf v v hv hv] at h1
    simp at h1
  obtain ⟨jo, hjo, rfl⟩ : ∃ jo, jo < m ∧ o = n + n + jo := by
    by_cases h : o < n + n
    · exfalso
      by_cases h2 : o < n
      · have := hf o o h2 h2
        rw [v0 _ _ h] at this
        simp [pt] at this
      · have := hf (o - n) (o - n) (by omega) (by omega)
        rw [v0 _ _ h] at this
        have e : o = n + (o - n) := by omega
        simp only [pt, ← e] at this
        simp at this
    · exact ⟨o - (n + n), by omega, by omega⟩
  let Z : ℕ → ℕ → Prop := fun i w => ∀ u v, u < n → v < n → u ≠ i → v ≠ i → V (pt n u v) w = false
  have zr : ∀ i < n, Z i i := by
    intro i hi u v hu hv hui hvi
    rw [v0 _ _ (by omega)]
    simp only [pt, decide_eq_false_iff_not, not_or]
    omega
  have zc : ∀ i < n, Z i (n + i) := by
    intro i hi u v hu hv hui hvi
    rw [v0 _ _ (by omega)]
    simp only [pt, decide_eq_false_iff_not, not_or]
    omega
  have kr : ∀ i j w, j < m → rd A B j w → Z i w → Kill n V i j := by
    intro i j w hj hr hz
    have a1 := hA j hj
    have b1 := hB j hj
    by_cases hAn : An j = true
    · left
      refine ⟨false, fun u v hu hv hui hvi => ?_⟩
      rw [v1 _ _ hj, if_pos hAn]
      rcases hr with rfl | rfl
      · rw [hz u v hu hv hui hvi]; rfl
      · rw [hz u v hu hv hui hvi, Bool.and_false]
    · right
      rcases hr with rfl | rfl
      · refine ⟨B j, b1, fun u v hu hv hui hvi => ?_⟩
        rw [v1 _ _ hj, if_neg hAn, hz u v hu hv hui hvi, Bool.false_or]
      · refine ⟨A j, a1, fun u v hu hv hui hvi => ?_⟩
        rw [v1 _ _ hj, if_neg hAn, hz u v hu hv hui hvi, Bool.or_false]
  have zor : ∀ i j, j < m → An j = false → Z i (A j) → Z i (B j) → Z i (n + n + j) := by
    intro i j hj hAn h1 h2 u v hu hv hui hvi
    rw [v1 _ _ hj, if_neg (by simp [hAn]), h1 u v hu hv hui hvi, h2 u v hu hv hui hvi]; rfl
  have orii : ∀ i j, i < n → j < m → An j = false → (rd A B j i ∨ rd A B j (n + i)) → V (pt n i i) (n + n + j) = true := by
    intro i j hi hj hAn hr
    have p1 : V (pt n i i) i = true := by rw [v0 _ _ (by omega)]; simp [pt]
    have p2 : V (pt n i i) (n + i) = true := by rw [v0 _ _ (by omega)]; simp [pt]
    rw [v1 _ _ hj, if_neg (by simp [hAn]), Bool.or_eq_true]
    rcases hr with (h | h) | (h | h)
    · exact Or.inl (by rw [h]; exact p1)
    · exact Or.inr (by rw [h]; exact p1)
    · exact Or.inl (by rw [h]; exact p2)
    · exact Or.inr (by rw [h]; exact p2)
  have notout : ∀ i j, i < n → j < m → An j = false → (rd A B j i ∨ rd A B j (n + i)) → j ≠ jo := by
    rintro i j hi hj hAn hr rfl
    have h1 := orii i j hi hj hAn hr
    rw [hf i i hi hi] at h1
    simp at h1
  have seesC : ∀ i < n, ∃ P Q : ℕ → Bool, (∀ k, k ≠ n + i → P k = Q k) ∧ P i = false ∧ Q i = false ∧ V P (n + n + jo) ≠ V Q (n + n + jo) := by
    intro i hi
    obtain ⟨u, hu, hui⟩ : ∃ u < n, u ≠ i := by
      by_cases h : i = 0
      · exact ⟨1, by omega, by omega⟩
      · exact ⟨0, by omega, by omega⟩
    refine ⟨pt n u i, fun k => decide (k = u), ?_, ?_, ?_, ?_⟩
    · intro k hk; simp [pt, hk]
    · simp only [pt, decide_eq_false_iff_not, not_or]; omega
    · simp only [decide_eq_false_iff_not]; omega
    · rw [hf u i hu hi, row1 u hu]; simp [hui]
  have seesR : ∀ i < n, ∃ P Q : ℕ → Bool, (∀ k, k ≠ i → P k = Q k) ∧ P (n + i) = false ∧ Q (n + i) = false ∧ V P (n + n + jo) ≠ V Q (n + n + jo) := by
    intro i hi
    obtain ⟨v, hv, hvi⟩ : ∃ v < n, v ≠ i := by
      by_cases h : i = 0
      · exact ⟨1, by omega, by omega⟩
      · exact ⟨0, by omega, by omega⟩
    refine ⟨pt n i v, fun k => decide (k = n + v), ?_, ?_, ?_, ?_⟩
    · intro k hk; simp [pt, hk]
    · simp only [pt, decide_eq_false_iff_not, not_or]; omega
    · simp only [decide_eq_false_iff_not]; omega
    · rw [hf i v hi hv, col1 v hv]; simp [Ne.symm hvi]
  have raw : ∀ (i x y h g : ℕ), i < n → ((x = i ∧ y = n + i) ∨ (x = n + i ∧ y = i)) → h < m → g < m → h ≠ g → rd A B h x → rd A B g x →
      (∀ a, rd A B h a → a < n + n ∨ ∃ i' j, a = n + n + j ∧ Tg n m A B An i' j) →
      (∃ P Q : ℕ → Bool, (∀ k, k ≠ y → P k = Q k) ∧ P x = false ∧ Q x = false ∧ V P (n + n + jo) ≠ V Q (n + n + jo)) →
      ∃ i < n, ∃ a b c, a < m ∧ b < m ∧ c < m ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ Kill n V i a ∧ Kill n V i b ∧ Kill n V i c := by
    intro i x y h g hi hxy hh hg hhg rhx rgx hat hsee
    have zx : Z i x := by rcases hxy with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> [exact zr _ hi; exact zc _ hi]
    have zy : Z i y := by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> [exact zc _ hi; exact zr _ hi]
    have hxN : x < n + n := by rcases hxy with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
    have hyN : y < n + n := by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> omega
    have hne : x ≠ y := by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
    by_cases h3 : ∃ k < m, (rd A B k x ∨ rd A B k y) ∧ k ≠ h ∧ k ≠ g
    · obtain ⟨k, hk, hr, k1, k2⟩ := h3
      refine ⟨i, hi, h, g, k, hh, hg, hk, hhg, Ne.symm k1, Ne.symm k2, kr i h x hh rhx zx, kr i g x hg rgx zx, ?_⟩
      exact hr.elim (fun r => kr i k x hk r zx) (fun r => kr i k y hk r zy)
    push Not at h3
    have only : ∀ k < m, (rd A B k x ∨ rd A B k y) → k = h ∨ k = g := by
      intro k hk hr
      by_contra hc
      rw [not_or] at hc
      exact hc.2 (h3 k hk hr hc.1)
    obtain ⟨P, Q, pq, px, qx, hdiff⟩ := hsee
    have both : ∀ k < m, rd A B k x → rd A B k y → (A k = x ∧ B k = y) ∨ (A k = y ∧ B k = x) := by
      intro k _ h1 h2
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
      · exact absurd (h1.symm.trans h2) hne
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr ⟨h2, h1⟩
      · exact absurd (h1.symm.trans h2) hne
    have andv : ∀ k < m, An k = true → rd A B k x → ∀ W : ℕ → Bool, W x = false → V W (n + n + k) = false := by
      intro k hk hAn hr W hW
      rw [v1 _ _ hk, if_pos hAn]
      rcases hr with hr | hr
      · rw [hr, v0 _ _ hxN, hW]; rfl
      · rw [hr, v0 _ _ hxN, hW, Bool.and_false]
    have orxy : ∀ k < m, An k = false → (rd A B k x ∧ rd A B k y) → k ≠ jo := by
      intro k hk hAn hr
      refine notout i k hi hk hAn ?_
      rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl hr.1
      · exact Or.inl hr.2
    have zgate : ∀ k < m, An k = false → rd A B k x → rd A B k y → Z i (n + n + k) := by
      intro k hk hAn r1 r2
      rcases both k hk r1 r2 with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact zor i k hk hAn (by rw [e1]; exact zx) (by rw [e2]; exact zy)
      · exact zor i k hk hAn (by rw [e1]; exact zy) (by rw [e2]; exact zx)
    by_cases rhy : rd A B h y
    · by_cases rgy : rd A B g y
      ·
        have hops : An h ≠ An g := by
          intro e
          have same : ∀ W, V W (n + n + h) = V W (n + n + g) := by
            intro W
            rw [v1 _ _ hh, v1 _ _ hg, e]
            rcases both h hh rhx rhy with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases both g hg rgx rgy with ⟨e3, e4⟩ | ⟨e3, e4⟩ <;> rw [e1, e2, e3, e4] <;>
              cases V W x <;> cases V W y <;> cases An g <;> rfl
          rcases Nat.lt_or_gt_of_ne hhg with hlt | hlt
          · exact irr g hg (n + n + h) (by omega) fun u v _ _ => (same _).symm
          · exact irr h hh (n + n + g) (by omega) fun u v _ _ => same _
        obtain ⟨p, q, hp, hq, hpq, pAn, qAn, rpx, rpy, rqx, rqy, hset⟩ : ∃ p q, p < m ∧ q < m ∧ p ≠ q ∧ An p = false ∧ An q = true ∧ rd A B p x ∧ rd A B p y ∧ rd A B q x ∧ rd A B q y ∧ (∀ k, k = h ∨ k = g → k = p ∨ k = q) := by
          cases e1 : An h with
          | false =>
            have e2 : An g = true := by
              cases e2 : An g with
              | true => rfl
              | false => exact absurd (e1.trans e2.symm) hops
            exact ⟨h, g, hh, hg, hhg, e1, e2, rhx, rhy, rgx, rgy, fun k hk => hk⟩
          | true =>
            have e2 : An g = false := by
              cases e2 : An g with
              | false => rfl
              | true => exact absurd (e1.trans e2.symm) hops
            exact ⟨g, h, hg, hh, Ne.symm hhg, e2, e1, rgx, rgy, rhx, rhy, fun k hk => hk.symm⟩
        have hrd : ∃ k < m, rd A B k (n + n + p) := by
          by_contra hno
          push Not at hno
          refine hdiff (rep (fun w => w = y ∨ w = n + n + p) P Q (fun k _ hk => pq k fun e => hk (Or.inl e)) ?_ _ (by omega) ?_)
          · intro j hj hjH hr
            have hjp : j ≠ p := fun e => hjH (Or.inr (by rw [e]))
            have : rd A B j y := by
              rcases hr with (e | e) | (e | e)
              · exact Or.inl e
              · exact absurd (Or.inl e) (hno j hj)
              · exact Or.inr e
              · exact absurd (Or.inr e) (hno j hj)
            have hjq : j = q := by
              rcases hset j (only j hj (Or.inr this)) with e | e
              · exact absurd e hjp
              · exact e
            subst hjq
            rw [andv j hj qAn rqx P px, andv j hj qAn rqx Q qx]
          · rintro (e | e)
            · omega
            · exact orxy p hp pAn ⟨rpx, rpy⟩ (by omega)
        obtain ⟨k, hk, hr⟩ := hrd
        have ar : ∀ c < m, rd A B c x → rd A B c y → ¬rd A B c (n + n + p) := by
          intro c hc c1 c2 c3
          rcases both c hc c1 c2 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases c3 with e3 | e3 <;> omega
        refine ⟨i, hi, p, q, k, hp, hq, hk, hpq, ?_, ?_, kr i p x hp rpx zx, kr i q x hq rqx zx, kr i k _ hk hr (zgate p hp pAn rpx rpy)⟩
        · rintro rfl; exact ar _ hp rpx rpy hr
        · rintro rfl; exact ar _ hq rqx rqy hr
      ·
        have oy : ∀ k < m, rd A B k y → k = h := by
          intro k hk r
          rcases only k hk (Or.inr r) with e | e
          · exact e
          · subst e; exact absurd r rgy
        cases hAn : An h with
        | true =>
          exfalso
          refine hdiff (rep (fun w => w = y) P Q (fun k _ hk => pq k hk) ?_ _ (by omega) (by omega))
          intro j hj _ hr
          have : j = h := oy j hj hr
          subst this
          rw [andv j hj hAn rhx P px, andv j hj hAn rhx Q qx]
        | false =>
          have hrd : ∃ k < m, rd A B k (n + n + h) := by
            by_contra hno
            push Not at hno
            refine hdiff (rep (fun w => w = y ∨ w = n + n + h) P Q (fun k _ hk => pq k fun e => hk (Or.inl e)) ?_ _ (by omega) ?_)
            · intro j hj hjH hr
              exfalso
              have : rd A B j y := by
                rcases hr with (e | e) | (e | e)
                · exact Or.inl e
                · exact absurd (Or.inl e) (hno j hj)
                · exact Or.inr e
                · exact absurd (Or.inr e) (hno j hj)
              exact hjH (Or.inr (by rw [oy j hj this]))
            · rintro (e | e)
              · omega
              · exact orxy h hh hAn ⟨rhx, rhy⟩ (by omega)
          by_cases hother : ∃ k < m, rd A B k (n + n + h) ∧ k ≠ g
          · obtain ⟨k, hk, hr, hkg⟩ := hother
            refine ⟨i, hi, h, g, k, hh, hg, hk, hhg, ?_, Ne.symm hkg, kr i h x hh rhx zx, kr i g x hg rgx zx, kr i k _ hk hr (zgate h hh hAn rhx rhy)⟩
            rintro rfl
            have a1 := hA h hh
            have b1 := hB h hh
            rcases hr with e | e <;> omega
          · exfalso
            push Not at hother
            obtain ⟨k, hk, hr⟩ := hrd
            have hkg := hother k hk hr
            subst hkg
            have hhk : h < k := by
              have a1 := hA k hk
              have b1 := hB k hk
              rcases hr with e | e <;> omega
            have ops : (A k = x ∧ B k = n + n + h) ∨ (A k = n + n + h ∧ B k = x) := by
              rcases rgx with e1 | e1 <;> rcases hr with e2 | e2
              · omega
              · exact Or.inl ⟨e1, e2⟩
              · exact Or.inr ⟨e2, e1⟩
              · omega
            have hhv : ∀ W, V W (n + n + h) = (V W x || V W y) := by
              intro W
              rw [v1 _ _ hh, if_neg (by simp [hAn])]
              rcases both h hh rhx rhy with ⟨e1, e2⟩ | ⟨e1, e2⟩
              · rw [e1, e2]
              · rw [e1, e2, Bool.or_comm]
            cases hAk : An k with
            | true =>
              refine irr k hk x (by omega) fun u v _ _ => ?_
              rw [v1 _ _ hk, if_pos hAk]
              rcases ops with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2, hhv] <;> cases V (pt n u v) x <;> cases V (pt n u v) y <;> rfl
            | false =>
              refine irr k hk (n + n + h) (by omega) fun u v _ _ => ?_
              rw [v1 _ _ hk, if_neg (by simp [hAk])]
              rcases ops with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2, hhv] <;> cases V (pt n u v) x <;> cases V (pt n u v) y <;> rfl
    ·
      have oy : ∀ k < m, rd A B k y → k = g := by
        intro k hk r
        rcases only k hk (Or.inr r) with e | e
        · subst e; exact absurd r rhy
        · exact e
      have rgy : rd A B g y := by
        by_contra hno
        refine hdiff (rep (fun w => w = y) P Q (fun k _ hk => pq k hk) ?_ _ (by omega) (by omega))
        intro j hj _ hr
        exfalso
        have := oy j hj hr
        subst this
        exact hno hr
      cases hAn : An g with
      | true =>
        exfalso
        refine hdiff (rep (fun w => w = y) P Q (fun k _ hk => pq k hk) ?_ _ (by omega) (by omega))
        intro j hj _ hr
        have : j = g := oy j hj hr
        subst this
        rw [andv j hj hAn rgx P px, andv j hj hAn rgx Q qx]
      | false =>
        have hrd : ∃ k < m, rd A B k (n + n + g) := by
          by_contra hno
          push Not at hno
          refine hdiff (rep (fun w => w = y ∨ w = n + n + g) P Q (fun k _ hk => pq k fun e => hk (Or.inl e)) ?_ _ (by omega) ?_)
          · intro j hj hjH hr
            exfalso
            have : rd A B j y := by
              rcases hr with (e | e) | (e | e)
              · exact Or.inl e
              · exact absurd (Or.inl e) (hno j hj)
              · exact Or.inr e
              · exact absurd (Or.inr e) (hno j hj)
            exact hjH (Or.inr (by rw [oy j hj this]))
          · rintro (e | e)
            · omega
            · exact orxy g hg hAn ⟨rgx, rgy⟩ (by omega)
        obtain ⟨k, hk, hr⟩ := hrd
        refine ⟨i, hi, h, g, k, hh, hg, hk, hhg, ?_, ?_, kr i h x hh rhx zx, kr i g x hg rgx zx, kr i k _ hk hr (zgate g hg hAn rgx rgy)⟩
        · rintro rfl
          rcases hat _ hr with e | ⟨i', j, e, hT⟩
          · omega
          · have hjg : j = g := by omega
            subst hjg
            obtain ⟨_, _, _, hops, hex⟩ := hT
            have hx' : x = i' ∨ x = n + i' := by
              rcases hops with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases rgx with e3 | e3 <;> omega
            have : h = j := by
              refine hex h hh ?_
              rcases hx' with rfl | rfl
              · exact Or.inl rhx
              · exact Or.inr rhx
            exact hhg this
        · rintro rfl
          have a1 := hA g hg
          have b1 := hB g hg
          rcases hr with e | e <;> omega
  by_contra hG
  have hexT : ∃ j, j < m ∧ ¬∃ i, Tg n m A B An i j := by
    refine ⟨jo, hjo, ?_⟩
    rintro ⟨i, hi, hj, hAn, hops, _⟩
    refine notout i jo hi hj hAn ?_ rfl
    rcases hops with ⟨e, _⟩ | ⟨_, e⟩
    · exact Or.inl (Or.inl e)
    · exact Or.inl (Or.inr e)
  obtain ⟨hh, hhT⟩ := Nat.find_spec hexT
  have hmin : ∀ j, j < Nat.find hexT → ∃ i, Tg n m A B An i j := by
    intro j hj
    by_contra hc
    exact Nat.find_min hexT hj ⟨by omega, hc⟩
  generalize Nat.find hexT = h at hh hhT hmin
  clear hexT
  have hAh := hA h hh
  have hBh := hB h hh
  have hat : ∀ a, rd A B h a → a < n + n ∨ ∃ i' j, a = n + n + j ∧ Tg n m A B An i' j := by
    intro a ha
    by_cases h1 : a < n + n
    · exact Or.inl h1
    · right
      have : a < n + n + h := by rcases ha with e | e <;> omega
      obtain ⟨i, hi⟩ := hmin (a - (n + n)) (by omega)
      exact ⟨i, a - (n + n), by omega, hi⟩
  have Tne : ∀ i j, Tg n m A B An i j → j ≠ h := by
    rintro i j hT rfl
    exact hhT ⟨i, hT⟩
  have Tno : ∀ i j, Tg n m A B An i j → j ≠ jo := by
    rintro i j ⟨hi, hj, hAn, hops, _⟩
    refine notout i j hi hj hAn ?_
    rcases hops with ⟨e, _⟩ | ⟨_, e⟩
    · exact Or.inl (Or.inl e)
    · exact Or.inl (Or.inr e)
  have VT : ∀ i j, Tg n m A B An i j → ∀ W : ℕ → Bool, V W (n + n + j) = (W i || W (n + i)) := by
    rintro i j ⟨hi, hj, hAn, hops, _⟩ W
    rw [v1 _ _ hj, if_neg (by simp [hAn])]
    rcases hops with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1, e2, v0 _ _ (by omega), v0 _ _ (by omega)]
    · rw [e1, e2, v0 _ _ (by omega), v0 _ _ (by omega), Bool.or_comm]
  have sole : ∀ a, rd A B h a → ∀ k < m, rd A B k a → k = h := by
    intro a ha k hk hr
    by_contra hkh
    apply hG
    rcases hat a ha with h1 | ⟨i, j, rfl, hT⟩
    · by_cases h2 : a < n
      · exact raw a a (n + a) h k h2 (Or.inl ⟨rfl, rfl⟩) hh hk (Ne.symm hkh) ha hr hat (seesC a h2)
      · have e : a = n + (a - n) := by omega
        exact raw (a - n) a (a - n) h k (by omega) (Or.inr ⟨e, rfl⟩) hh hk (Ne.symm hkh) ha hr hat (by
          have := seesR (a - n) (by omega)
          rwa [← e] at this)
    · obtain ⟨hi, hj, hAn, hops, hex⟩ := hT
      have zA : Z i (A j) := by rcases hops with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> [exact zr i hi; exact zc i hi]
      have zB : Z i (B j) := by rcases hops with ⟨_, e⟩ | ⟨_, e⟩ <;> rw [e] <;> [exact zc i hi; exact zr i hi]
      have zj := zor i j hj hAn zA zB
      refine ⟨i, hi, j, h, k, hj, hh, hk, Tne i j ⟨hi, hj, hAn, hops, hex⟩, ?_, Ne.symm hkh, kr i j _ hj (Or.inl rfl) zA, kr i h _ hh ha zj, kr i k _ hk hr zj⟩
      rintro rfl
      have a1 := hA j hj
      have b1 := hB j hj
      rcases hr with e | e <;> omega
  have fin : ∀ (Hd : ℕ → Prop) (P Q : ℕ → Bool), (∀ k < n + n, ¬Hd k → P k = Q k) →
      (∀ j < m, ¬Hd (n + n + j) → (Hd (A j) ∨ Hd (B j)) → j = h) → V P (n + n + h) = V Q (n + n + h) → ¬Hd (n + n + jo) →
      V P (n + n + jo) = V Q (n + n + jo) := by
    intro Hd P Q h1 h2 h3 h4
    refine rep Hd P Q h1 (fun j hj hjH hr => ?_) _ (by omega) h4
    rw [h2 j hj hjH hr]; exact h3
  have hVh : ∀ W, V W (n + n + h) = if An h = true then V W (A h) && V W (B h) else V W (A h) || V W (B h) := fun W => v1 W h hh
  have ra : rd A B h (A h) := Or.inl rfl
  have rb : rd A B h (B h) := Or.inr rfl
  have sa := sole _ ra
  have sb := sole _ rb
  have hab := hAB h hh
  have atom : ∀ a, rd A B h a → (∃ i < n, a = i) ∨ (∃ i < n, a = n + i) ∨ ∃ i j, a = n + n + j ∧ Tg n m A B An i j := by
    intro a ha
    rcases hat a ha with h1 | h1
    · by_cases h2 : a < n
      · exact Or.inl ⟨a, h2, rfl⟩
      · exact Or.inr (Or.inl ⟨a - n, by omega, by omega⟩)
    · exact Or.inr (Or.inr h1)
  have third : ∀ i j, i < n → j < n → ∃ v < n, v ≠ i ∧ v ≠ j := by
    intro i j _ _
    by_cases h0 : 0 ≠ i ∧ 0 ≠ j
    · exact ⟨0, by omega, h0.1, h0.2⟩
    · by_cases h1 : 1 ≠ i ∧ 1 ≠ j
      · exact ⟨1, by omega, h1.1, h1.2⟩
      · refine ⟨2, by omega, ?_, ?_⟩ <;> omega
  rcases atom _ ra with ⟨i, hi, ea⟩ | ⟨i, hi, ea⟩ | ⟨i, ja, ea, hTa⟩
  · rcases atom _ rb with ⟨j, hj, eb⟩ | ⟨j, hj, eb⟩ | ⟨j, jb, eb, hTb⟩
    · by_cases hij : i = j
      · subst hij
        exact hab (ea.trans eb.symm)
      · obtain ⟨v, hv, hvi, hvj⟩ := third i j hi hj
        cases hAn : An h with
        | true =>
          let P : ℕ → Bool := fun k => decide (k = i ∨ k = n + v)
          let Q : ℕ → Bool := fun k => decide (k = n + v)
          have va : V P (i) = true := by rw [v0 _ _ (by omega)]; exact (show P (i) = true from by show decide ((i) = i ∨ (i) = n + v) = true; rw [decide_eq_true_eq] <;> omega)
          have vb : V P (j) = false := by rw [v0 _ _ (by omega)]; exact (show P (j) = false from by show decide ((j) = i ∨ (j) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)
          have ua : V Q (i) = false := by rw [v0 _ _ (by omega)]; exact (show Q (i) = false from by show decide ((i) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)
          have ub : V Q (j) = false := by rw [v0 _ _ (by omega)]; exact (show Q (j) = false from by show decide ((j) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)
          have hfin := fin (fun w => w = i) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf i v hi hv).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := col1 v hv
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = i ∨ k = n + v) = decide (k = n + v)
            have hH2 : ¬(k = i) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬(n + n + k = i) := hkH
            have hr2 : ∃ w, rd A B k w ∧ (w = i) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with rfl
            · exact sa k hk (by rw [ea]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : n + n + jo = i := hH
            omega
        | false =>
          let P : ℕ → Bool := fun k => decide (k = i ∨ k = n + i)
          let Q : ℕ → Bool := fun k => decide (k = j ∨ k = n + i)
          have va : V P (i) = true := by rw [v0 _ _ (by omega)]; exact (show P (i) = true from by show decide ((i) = i ∨ (i) = n + i) = true; rw [decide_eq_true_eq] <;> omega)
          have vb : V P (j) = false := by rw [v0 _ _ (by omega)]; exact (show P (j) = false from by show decide ((j) = i ∨ (j) = n + i) = false; rw [decide_eq_false_iff_not] <;> omega)
          have ua : V Q (i) = false := by rw [v0 _ _ (by omega)]; exact (show Q (i) = false from by show decide ((i) = j ∨ (i) = n + i) = false; rw [decide_eq_false_iff_not] <;> omega)
          have ub : V Q (j) = true := by rw [v0 _ _ (by omega)]; exact (show Q (j) = true from by show decide ((j) = j ∨ (j) = n + i) = true; rw [decide_eq_true_eq] <;> omega)
          have hfin := fin (fun w => w = i ∨ w = j) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = false := (hf i i hi hi).trans (by simp)
            have f2 : V Q (n + n + jo) = true := (hf j i hj hi).trans (by simp <;> omega)
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = i ∨ k = n + i) = decide (k = j ∨ k = n + i)
            have hH2 : ¬(k = i ∨ k = j) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬(n + n + k = i ∨ n + n + k = j) := hkH
            have hr2 : ∃ w, rd A B k w ∧ (w = i ∨ w = j) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with rfl | rfl
            · exact sa k hk (by rw [ea]; exact hw)
            · exact sb k hk (by rw [eb]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : n + n + jo = i ∨ n + n + jo = j := hH
            omega
    · by_cases hij : i = j
      · subst hij
        cases hAn : An h with
        | false =>
          refine hhT ⟨i, hi, hh, hAn, Or.inl ⟨ea, eb⟩, fun k hk hr => ?_⟩
          rcases hr with hr | hr
          · exact sa k hk (by rw [ea]; exact hr)
          · exact sb k hk (by rw [eb]; exact hr)
        | true =>
          obtain ⟨P, Q, pq, px, qx, hdiff⟩ := seesC i hi
          refine hdiff (fin (fun w => w = n + i) P Q (fun k _ hk => pq k hk) ?_ ?_ (by omega))
          · intro k hk _ hr
            exact sb k hk (by rw [eb]; exact hr)
          · rw [hVh, hVh, if_pos hAn, if_pos hAn, ea, eb, v0 _ i (by omega), v0 _ i (by omega), px, qx]
            simp
      · obtain ⟨v, hv, hvi, hvj⟩ := third i j hi hj
        cases hAn : An h with
        | true =>
          let P : ℕ → Bool := fun k => decide (k = i ∨ k = n + v)
          let Q : ℕ → Bool := fun k => decide (k = n + v)
          have va : V P (i) = true := by rw [v0 _ _ (by omega)]; exact (show P (i) = true from by show decide ((i) = i ∨ (i) = n + v) = true; rw [decide_eq_true_eq] <;> omega)
          have vb : V P (n + j) = false := by rw [v0 _ _ (by omega)]; exact (show P (n + j) = false from by show decide ((n + j) = i ∨ (n + j) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)
          have ua : V Q (i) = false := by rw [v0 _ _ (by omega)]; exact (show Q (i) = false from by show decide ((i) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)
          have ub : V Q (n + j) = false := by rw [v0 _ _ (by omega)]; exact (show Q (n + j) = false from by show decide ((n + j) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)
          have hfin := fin (fun w => w = i) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf i v hi hv).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := col1 v hv
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = i ∨ k = n + v) = decide (k = n + v)
            have hH2 : ¬(k = i) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬(n + n + k = i) := hkH
            have hr2 : ∃ w, rd A B k w ∧ (w = i) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with rfl
            · exact sa k hk (by rw [ea]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : n + n + jo = i := hH
            omega
        | false =>
          let P : ℕ → Bool := fun k => decide (k = i ∨ k = n + j)
          let Q : ℕ → Bool := fun k => decide (k = i)
          have va : V P (i) = true := by rw [v0 _ _ (by omega)]; exact (show P (i) = true from by show decide ((i) = i ∨ (i) = n + j) = true; rw [decide_eq_true_eq] <;> omega)
          have vb : V P (n + j) = true := by rw [v0 _ _ (by omega)]; exact (show P (n + j) = true from by show decide ((n + j) = i ∨ (n + j) = n + j) = true; rw [decide_eq_true_eq] <;> omega)
          have ua : V Q (i) = true := by rw [v0 _ _ (by omega)]; exact (show Q (i) = true from by show decide ((i) = i) = true; rw [decide_eq_true_eq] <;> omega)
          have ub : V Q (n + j) = false := by rw [v0 _ _ (by omega)]; exact (show Q (n + j) = false from by show decide ((n + j) = i) = false; rw [decide_eq_false_iff_not] <;> omega)
          have hfin := fin (fun w => w = i ∨ w = n + j) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf i j hi hj).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := row1 i hi
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = i ∨ k = n + j) = decide (k = i)
            have hH2 : ¬(k = i ∨ k = n + j) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬(n + n + k = i ∨ n + n + k = n + j) := hkH
            have hr2 : ∃ w, rd A B k w ∧ (w = i ∨ w = n + j) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with rfl | rfl
            · exact sa k hk (by rw [ea]; exact hw)
            · exact sb k hk (by rw [eb]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : n + n + jo = i ∨ n + n + jo = n + j := hH
            omega
    · have hj := hTb.1
      have xb := hTb.2.2.2.2
      by_cases hij : i = j
      · subst hij
        exact Tne i jb hTb (xb h hh (Or.inl (by rw [← ea]; exact ra))).symm
      · obtain ⟨v, hv, hvi, hvj⟩ := third i j hi hj
        cases hAn : An h with
        | true =>
          let P : ℕ → Bool := fun k => decide (k = i ∨ k = n + v)
          let Q : ℕ → Bool := fun k => decide (k = n + v)
          have va : V P (i) = true := by rw [v0 _ _ (by omega)]; exact (show P (i) = true from by show decide ((i) = i ∨ (i) = n + v) = true; rw [decide_eq_true_eq] <;> omega)
          have vb : V P (n + n + jb) = false := by rw [VT j jb hTb P, (show P (j) = false from by show decide ((j) = i ∨ (j) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega), (show P (n + j) = false from by show decide ((n + j) = i ∨ (n + j) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have ua : V Q (i) = false := by rw [v0 _ _ (by omega)]; exact (show Q (i) = false from by show decide ((i) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)
          have ub : V Q (n + n + jb) = false := by rw [VT j jb hTb Q, (show Q (j) = false from by show decide ((j) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega), (show Q (n + j) = false from by show decide ((n + j) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have hfin := fin (fun w => w = i) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf i v hi hv).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := col1 v hv
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = i ∨ k = n + v) = decide (k = n + v)
            have hH2 : ¬(k = i) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬(n + n + k = i) := hkH
            have hr2 : ∃ w, rd A B k w ∧ (w = i) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with rfl
            · exact sa k hk (by rw [ea]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : n + n + jo = i := hH
            omega
        | false =>
          let P : ℕ → Bool := fun k => decide (k = i ∨ k = n + j)
          let Q : ℕ → Bool := fun k => decide (k = i)
          have va : V P (i) = true := by rw [v0 _ _ (by omega)]; exact (show P (i) = true from by show decide ((i) = i ∨ (i) = n + j) = true; rw [decide_eq_true_eq] <;> omega)
          have vb : V P (n + n + jb) = true := by rw [VT j jb hTb P, (show P (j) = false from by show decide ((j) = i ∨ (j) = n + j) = false; rw [decide_eq_false_iff_not] <;> omega), (show P (n + j) = true from by show decide ((n + j) = i ∨ (n + j) = n + j) = true; rw [decide_eq_true_eq] <;> omega)]; rfl
          have ua : V Q (i) = true := by rw [v0 _ _ (by omega)]; exact (show Q (i) = true from by show decide ((i) = i) = true; rw [decide_eq_true_eq] <;> omega)
          have ub : V Q (n + n + jb) = false := by rw [VT j jb hTb Q, (show Q (j) = false from by show decide ((j) = i) = false; rw [decide_eq_false_iff_not] <;> omega), (show Q (n + j) = false from by show decide ((n + j) = i) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have hfin := fin (fun w => w = i ∨ (w = j ∨ w = n + j ∨ w = n + n + jb)) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf i j hi hj).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := row1 i hi
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = i ∨ k = n + j) = decide (k = i)
            have hH2 : ¬(k = i ∨ (k = j ∨ k = n + j ∨ k = n + n + jb)) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬(n + n + k = i ∨ (n + n + k = j ∨ n + n + k = n + j ∨ n + n + k = n + n + jb)) := hkH
            have hr2 : ∃ w, rd A B k w ∧ (w = i ∨ (w = j ∨ w = n + j ∨ w = n + n + jb)) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with rfl | (rfl | rfl | rfl)
            · exact sa k hk (by rw [ea]; exact hw)
            · exfalso; have := xb k hk (Or.inl hw); omega
            · exfalso; have := xb k hk (Or.inr hw); omega
            · exact sb k hk (by rw [eb]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : n + n + jo = i ∨ (n + n + jo = j ∨ n + n + jo = n + j ∨ n + n + jo = n + n + jb) := hH
            have := Tno j jb hTb
            omega
  · rcases atom _ rb with ⟨j, hj, eb⟩ | ⟨j, hj, eb⟩ | ⟨j, jb, eb, hTb⟩
    · by_cases hij : i = j
      · subst hij
        cases hAn : An h with
        | false =>
          refine hhT ⟨i, hi, hh, hAn, Or.inr ⟨ea, eb⟩, fun k hk hr => ?_⟩
          rcases hr with hr | hr
          · exact sb k hk (by rw [eb]; exact hr)
          · exact sa k hk (by rw [ea]; exact hr)
        | true =>
          obtain ⟨P, Q, pq, px, qx, hdiff⟩ := seesC i hi
          refine hdiff (fin (fun w => w = n + i) P Q (fun k _ hk => pq k hk) ?_ ?_ (by omega))
          · intro k hk _ hr
            exact sa k hk (by rw [ea]; exact hr)
          · rw [hVh, hVh, if_pos hAn, if_pos hAn, ea, eb, v0 _ i (by omega), v0 _ i (by omega), px, qx]
            simp
      · obtain ⟨v, hv, hvi, hvj⟩ := third i j hi hj
        cases hAn : An h with
        | true =>
          let P : ℕ → Bool := fun k => decide (k = v ∨ k = n + i)
          let Q : ℕ → Bool := fun k => decide (k = v)
          have va : V P (n + i) = true := by rw [v0 _ _ (by omega)]; exact (show P (n + i) = true from by show decide ((n + i) = v ∨ (n + i) = n + i) = true; rw [decide_eq_true_eq] <;> omega)
          have vb : V P (j) = false := by rw [v0 _ _ (by omega)]; exact (show P (j) = false from by show decide ((j) = v ∨ (j) = n + i) = false; rw [decide_eq_false_iff_not] <;> omega)
          have ua : V Q (n + i) = false := by rw [v0 _ _ (by omega)]; exact (show Q (n + i) = false from by show decide ((n + i) = v) = false; rw [decide_eq_false_iff_not] <;> omega)
          have ub : V Q (j) = false := by rw [v0 _ _ (by omega)]; exact (show Q (j) = false from by show decide ((j) = v) = false; rw [decide_eq_false_iff_not] <;> omega)
          have hfin := fin (fun w => w = n + i) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf v i hv hi).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := row1 v hv
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = v ∨ k = n + i) = decide (k = v)
            have hH2 : ¬(k = n + i) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬(n + n + k = n + i) := hkH
            have hr2 : ∃ w, rd A B k w ∧ (w = n + i) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with rfl
            · exact sa k hk (by rw [ea]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : n + n + jo = n + i := hH
            omega
        | false =>
          let P : ℕ → Bool := fun k => decide (k = j ∨ k = n + i)
          let Q : ℕ → Bool := fun k => decide (k = j)
          have va : V P (n + i) = true := by rw [v0 _ _ (by omega)]; exact (show P (n + i) = true from by show decide ((n + i) = j ∨ (n + i) = n + i) = true; rw [decide_eq_true_eq] <;> omega)
          have vb : V P (j) = true := by rw [v0 _ _ (by omega)]; exact (show P (j) = true from by show decide ((j) = j ∨ (j) = n + i) = true; rw [decide_eq_true_eq] <;> omega)
          have ua : V Q (n + i) = false := by rw [v0 _ _ (by omega)]; exact (show Q (n + i) = false from by show decide ((n + i) = j) = false; rw [decide_eq_false_iff_not] <;> omega)
          have ub : V Q (j) = true := by rw [v0 _ _ (by omega)]; exact (show Q (j) = true from by show decide ((j) = j) = true; rw [decide_eq_true_eq] <;> omega)
          have hfin := fin (fun w => w = n + i ∨ w = j) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf j i hj hi).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := row1 j hj
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = j ∨ k = n + i) = decide (k = j)
            have hH2 : ¬(k = n + i ∨ k = j) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬(n + n + k = n + i ∨ n + n + k = j) := hkH
            have hr2 : ∃ w, rd A B k w ∧ (w = n + i ∨ w = j) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with rfl | rfl
            · exact sa k hk (by rw [ea]; exact hw)
            · exact sb k hk (by rw [eb]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : n + n + jo = n + i ∨ n + n + jo = j := hH
            omega
    · by_cases hij : i = j
      · subst hij
        exact hab (ea.trans eb.symm)
      · obtain ⟨v, hv, hvi, hvj⟩ := third i j hi hj
        cases hAn : An h with
        | true =>
          let P : ℕ → Bool := fun k => decide (k = v ∨ k = n + i)
          let Q : ℕ → Bool := fun k => decide (k = v)
          have va : V P (n + i) = true := by rw [v0 _ _ (by omega)]; exact (show P (n + i) = true from by show decide ((n + i) = v ∨ (n + i) = n + i) = true; rw [decide_eq_true_eq] <;> omega)
          have vb : V P (n + j) = false := by rw [v0 _ _ (by omega)]; exact (show P (n + j) = false from by show decide ((n + j) = v ∨ (n + j) = n + i) = false; rw [decide_eq_false_iff_not] <;> omega)
          have ua : V Q (n + i) = false := by rw [v0 _ _ (by omega)]; exact (show Q (n + i) = false from by show decide ((n + i) = v) = false; rw [decide_eq_false_iff_not] <;> omega)
          have ub : V Q (n + j) = false := by rw [v0 _ _ (by omega)]; exact (show Q (n + j) = false from by show decide ((n + j) = v) = false; rw [decide_eq_false_iff_not] <;> omega)
          have hfin := fin (fun w => w = n + i) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf v i hv hi).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := row1 v hv
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = v ∨ k = n + i) = decide (k = v)
            have hH2 : ¬(k = n + i) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬(n + n + k = n + i) := hkH
            have hr2 : ∃ w, rd A B k w ∧ (w = n + i) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with rfl
            · exact sa k hk (by rw [ea]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : n + n + jo = n + i := hH
            omega
        | false =>
          let P : ℕ → Bool := fun k => decide (k = i ∨ k = n + i)
          let Q : ℕ → Bool := fun k => decide (k = i ∨ k = n + j)
          have va : V P (n + i) = true := by rw [v0 _ _ (by omega)]; exact (show P (n + i) = true from by show decide ((n + i) = i ∨ (n + i) = n + i) = true; rw [decide_eq_true_eq] <;> omega)
          have vb : V P (n + j) = false := by rw [v0 _ _ (by omega)]; exact (show P (n + j) = false from by show decide ((n + j) = i ∨ (n + j) = n + i) = false; rw [decide_eq_false_iff_not] <;> omega)
          have ua : V Q (n + i) = false := by rw [v0 _ _ (by omega)]; exact (show Q (n + i) = false from by show decide ((n + i) = i ∨ (n + i) = n + j) = false; rw [decide_eq_false_iff_not] <;> omega)
          have ub : V Q (n + j) = true := by rw [v0 _ _ (by omega)]; exact (show Q (n + j) = true from by show decide ((n + j) = i ∨ (n + j) = n + j) = true; rw [decide_eq_true_eq] <;> omega)
          have hfin := fin (fun w => w = n + i ∨ w = n + j) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = false := (hf i i hi hi).trans (by simp)
            have f2 : V Q (n + n + jo) = true := (hf i j hi hj).trans (by simp <;> omega)
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = i ∨ k = n + i) = decide (k = i ∨ k = n + j)
            have hH2 : ¬(k = n + i ∨ k = n + j) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬(n + n + k = n + i ∨ n + n + k = n + j) := hkH
            have hr2 : ∃ w, rd A B k w ∧ (w = n + i ∨ w = n + j) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with rfl | rfl
            · exact sa k hk (by rw [ea]; exact hw)
            · exact sb k hk (by rw [eb]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : n + n + jo = n + i ∨ n + n + jo = n + j := hH
            omega
    · have hj := hTb.1
      have xb := hTb.2.2.2.2
      by_cases hij : i = j
      · subst hij
        exact Tne i jb hTb (xb h hh (Or.inr (by rw [← ea]; exact ra))).symm
      · obtain ⟨v, hv, hvi, hvj⟩ := third i j hi hj
        cases hAn : An h with
        | true =>
          let P : ℕ → Bool := fun k => decide (k = v ∨ k = n + i)
          let Q : ℕ → Bool := fun k => decide (k = v)
          have va : V P (n + i) = true := by rw [v0 _ _ (by omega)]; exact (show P (n + i) = true from by show decide ((n + i) = v ∨ (n + i) = n + i) = true; rw [decide_eq_true_eq] <;> omega)
          have vb : V P (n + n + jb) = false := by rw [VT j jb hTb P, (show P (j) = false from by show decide ((j) = v ∨ (j) = n + i) = false; rw [decide_eq_false_iff_not] <;> omega), (show P (n + j) = false from by show decide ((n + j) = v ∨ (n + j) = n + i) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have ua : V Q (n + i) = false := by rw [v0 _ _ (by omega)]; exact (show Q (n + i) = false from by show decide ((n + i) = v) = false; rw [decide_eq_false_iff_not] <;> omega)
          have ub : V Q (n + n + jb) = false := by rw [VT j jb hTb Q, (show Q (j) = false from by show decide ((j) = v) = false; rw [decide_eq_false_iff_not] <;> omega), (show Q (n + j) = false from by show decide ((n + j) = v) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have hfin := fin (fun w => w = n + i) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf v i hv hi).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := row1 v hv
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = v ∨ k = n + i) = decide (k = v)
            have hH2 : ¬(k = n + i) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬(n + n + k = n + i) := hkH
            have hr2 : ∃ w, rd A B k w ∧ (w = n + i) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with rfl
            · exact sa k hk (by rw [ea]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : n + n + jo = n + i := hH
            omega
        | false =>
          let P : ℕ → Bool := fun k => decide (k = j ∨ k = n + i)
          let Q : ℕ → Bool := fun k => decide (k = n + i)
          have va : V P (n + i) = true := by rw [v0 _ _ (by omega)]; exact (show P (n + i) = true from by show decide ((n + i) = j ∨ (n + i) = n + i) = true; rw [decide_eq_true_eq] <;> omega)
          have vb : V P (n + n + jb) = true := by rw [VT j jb hTb P, (show P (j) = true from by show decide ((j) = j ∨ (j) = n + i) = true; rw [decide_eq_true_eq] <;> omega), (show P (n + j) = false from by show decide ((n + j) = j ∨ (n + j) = n + i) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have ua : V Q (n + i) = true := by rw [v0 _ _ (by omega)]; exact (show Q (n + i) = true from by show decide ((n + i) = n + i) = true; rw [decide_eq_true_eq] <;> omega)
          have ub : V Q (n + n + jb) = false := by rw [VT j jb hTb Q, (show Q (j) = false from by show decide ((j) = n + i) = false; rw [decide_eq_false_iff_not] <;> omega), (show Q (n + j) = false from by show decide ((n + j) = n + i) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have hfin := fin (fun w => w = n + i ∨ (w = j ∨ w = n + j ∨ w = n + n + jb)) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf j i hj hi).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := col1 i hi
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = j ∨ k = n + i) = decide (k = n + i)
            have hH2 : ¬(k = n + i ∨ (k = j ∨ k = n + j ∨ k = n + n + jb)) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬(n + n + k = n + i ∨ (n + n + k = j ∨ n + n + k = n + j ∨ n + n + k = n + n + jb)) := hkH
            have hr2 : ∃ w, rd A B k w ∧ (w = n + i ∨ (w = j ∨ w = n + j ∨ w = n + n + jb)) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with rfl | (rfl | rfl | rfl)
            · exact sa k hk (by rw [ea]; exact hw)
            · exfalso; have := xb k hk (Or.inl hw); omega
            · exfalso; have := xb k hk (Or.inr hw); omega
            · exact sb k hk (by rw [eb]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : n + n + jo = n + i ∨ (n + n + jo = j ∨ n + n + jo = n + j ∨ n + n + jo = n + n + jb) := hH
            have := Tno j jb hTb
            omega
  · rcases atom _ rb with ⟨j, hj, eb⟩ | ⟨j, hj, eb⟩ | ⟨j, jb, eb, hTb⟩
    · have hi := hTa.1
      have xa := hTa.2.2.2.2
      by_cases hij : i = j
      · subst hij
        exact Tne i ja hTa (xa h hh (Or.inl (by rw [← eb]; exact rb))).symm
      · obtain ⟨v, hv, hvi, hvj⟩ := third i j hi hj
        cases hAn : An h with
        | true =>
          let P : ℕ → Bool := fun k => decide (k = i ∨ k = n + v)
          let Q : ℕ → Bool := fun k => decide (k = n + v)
          have va : V P (n + n + ja) = true := by rw [VT i ja hTa P, (show P (i) = true from by show decide ((i) = i ∨ (i) = n + v) = true; rw [decide_eq_true_eq] <;> omega), (show P (n + i) = false from by show decide ((n + i) = i ∨ (n + i) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have vb : V P (j) = false := by rw [v0 _ _ (by omega)]; exact (show P (j) = false from by show decide ((j) = i ∨ (j) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)
          have ua : V Q (n + n + ja) = false := by rw [VT i ja hTa Q, (show Q (i) = false from by show decide ((i) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega), (show Q (n + i) = false from by show decide ((n + i) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have ub : V Q (j) = false := by rw [v0 _ _ (by omega)]; exact (show Q (j) = false from by show decide ((j) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)
          have hfin := fin (fun w => (w = i ∨ w = n + i ∨ w = n + n + ja)) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf i v hi hv).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := col1 v hv
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = i ∨ k = n + v) = decide (k = n + v)
            have hH2 : ¬((k = i ∨ k = n + i ∨ k = n + n + ja)) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬((n + n + k = i ∨ n + n + k = n + i ∨ n + n + k = n + n + ja)) := hkH
            have hr2 : ∃ w, rd A B k w ∧ ((w = i ∨ w = n + i ∨ w = n + n + ja)) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with (rfl | rfl | rfl)
            · exfalso; have := xa k hk (Or.inl hw); omega
            · exfalso; have := xa k hk (Or.inr hw); omega
            · exact sa k hk (by rw [ea]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : (n + n + jo = i ∨ n + n + jo = n + i ∨ n + n + jo = n + n + ja) := hH
            have := Tno i ja hTa
            omega
        | false =>
          let P : ℕ → Bool := fun k => decide (k = j ∨ k = n + i)
          let Q : ℕ → Bool := fun k => decide (k = j)
          have va : V P (n + n + ja) = true := by rw [VT i ja hTa P, (show P (i) = false from by show decide ((i) = j ∨ (i) = n + i) = false; rw [decide_eq_false_iff_not] <;> omega), (show P (n + i) = true from by show decide ((n + i) = j ∨ (n + i) = n + i) = true; rw [decide_eq_true_eq] <;> omega)]; rfl
          have vb : V P (j) = true := by rw [v0 _ _ (by omega)]; exact (show P (j) = true from by show decide ((j) = j ∨ (j) = n + i) = true; rw [decide_eq_true_eq] <;> omega)
          have ua : V Q (n + n + ja) = false := by rw [VT i ja hTa Q, (show Q (i) = false from by show decide ((i) = j) = false; rw [decide_eq_false_iff_not] <;> omega), (show Q (n + i) = false from by show decide ((n + i) = j) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have ub : V Q (j) = true := by rw [v0 _ _ (by omega)]; exact (show Q (j) = true from by show decide ((j) = j) = true; rw [decide_eq_true_eq] <;> omega)
          have hfin := fin (fun w => (w = i ∨ w = n + i ∨ w = n + n + ja) ∨ w = j) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf j i hj hi).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := row1 j hj
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = j ∨ k = n + i) = decide (k = j)
            have hH2 : ¬((k = i ∨ k = n + i ∨ k = n + n + ja) ∨ k = j) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬((n + n + k = i ∨ n + n + k = n + i ∨ n + n + k = n + n + ja) ∨ n + n + k = j) := hkH
            have hr2 : ∃ w, rd A B k w ∧ ((w = i ∨ w = n + i ∨ w = n + n + ja) ∨ w = j) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with (rfl | rfl | rfl) | rfl
            · exfalso; have := xa k hk (Or.inl hw); omega
            · exfalso; have := xa k hk (Or.inr hw); omega
            · exact sa k hk (by rw [ea]; exact hw)
            · exact sb k hk (by rw [eb]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : (n + n + jo = i ∨ n + n + jo = n + i ∨ n + n + jo = n + n + ja) ∨ n + n + jo = j := hH
            have := Tno i ja hTa
            omega
    · have hi := hTa.1
      have xa := hTa.2.2.2.2
      by_cases hij : i = j
      · subst hij
        exact Tne i ja hTa (xa h hh (Or.inr (by rw [← eb]; exact rb))).symm
      · obtain ⟨v, hv, hvi, hvj⟩ := third i j hi hj
        cases hAn : An h with
        | true =>
          let P : ℕ → Bool := fun k => decide (k = i ∨ k = n + v)
          let Q : ℕ → Bool := fun k => decide (k = n + v)
          have va : V P (n + n + ja) = true := by rw [VT i ja hTa P, (show P (i) = true from by show decide ((i) = i ∨ (i) = n + v) = true; rw [decide_eq_true_eq] <;> omega), (show P (n + i) = false from by show decide ((n + i) = i ∨ (n + i) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have vb : V P (n + j) = false := by rw [v0 _ _ (by omega)]; exact (show P (n + j) = false from by show decide ((n + j) = i ∨ (n + j) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)
          have ua : V Q (n + n + ja) = false := by rw [VT i ja hTa Q, (show Q (i) = false from by show decide ((i) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega), (show Q (n + i) = false from by show decide ((n + i) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have ub : V Q (n + j) = false := by rw [v0 _ _ (by omega)]; exact (show Q (n + j) = false from by show decide ((n + j) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)
          have hfin := fin (fun w => (w = i ∨ w = n + i ∨ w = n + n + ja)) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf i v hi hv).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := col1 v hv
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = i ∨ k = n + v) = decide (k = n + v)
            have hH2 : ¬((k = i ∨ k = n + i ∨ k = n + n + ja)) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬((n + n + k = i ∨ n + n + k = n + i ∨ n + n + k = n + n + ja)) := hkH
            have hr2 : ∃ w, rd A B k w ∧ ((w = i ∨ w = n + i ∨ w = n + n + ja)) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with (rfl | rfl | rfl)
            · exfalso; have := xa k hk (Or.inl hw); omega
            · exfalso; have := xa k hk (Or.inr hw); omega
            · exact sa k hk (by rw [ea]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : (n + n + jo = i ∨ n + n + jo = n + i ∨ n + n + jo = n + n + ja) := hH
            have := Tno i ja hTa
            omega
        | false =>
          let P : ℕ → Bool := fun k => decide (k = i ∨ k = n + j)
          let Q : ℕ → Bool := fun k => decide (k = n + j)
          have va : V P (n + n + ja) = true := by rw [VT i ja hTa P, (show P (i) = true from by show decide ((i) = i ∨ (i) = n + j) = true; rw [decide_eq_true_eq] <;> omega), (show P (n + i) = false from by show decide ((n + i) = i ∨ (n + i) = n + j) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have vb : V P (n + j) = true := by rw [v0 _ _ (by omega)]; exact (show P (n + j) = true from by show decide ((n + j) = i ∨ (n + j) = n + j) = true; rw [decide_eq_true_eq] <;> omega)
          have ua : V Q (n + n + ja) = false := by rw [VT i ja hTa Q, (show Q (i) = false from by show decide ((i) = n + j) = false; rw [decide_eq_false_iff_not] <;> omega), (show Q (n + i) = false from by show decide ((n + i) = n + j) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have ub : V Q (n + j) = true := by rw [v0 _ _ (by omega)]; exact (show Q (n + j) = true from by show decide ((n + j) = n + j) = true; rw [decide_eq_true_eq] <;> omega)
          have hfin := fin (fun w => (w = i ∨ w = n + i ∨ w = n + n + ja) ∨ w = n + j) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf i j hi hj).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := col1 j hj
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = i ∨ k = n + j) = decide (k = n + j)
            have hH2 : ¬((k = i ∨ k = n + i ∨ k = n + n + ja) ∨ k = n + j) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬((n + n + k = i ∨ n + n + k = n + i ∨ n + n + k = n + n + ja) ∨ n + n + k = n + j) := hkH
            have hr2 : ∃ w, rd A B k w ∧ ((w = i ∨ w = n + i ∨ w = n + n + ja) ∨ w = n + j) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with (rfl | rfl | rfl) | rfl
            · exfalso; have := xa k hk (Or.inl hw); omega
            · exfalso; have := xa k hk (Or.inr hw); omega
            · exact sa k hk (by rw [ea]; exact hw)
            · exact sb k hk (by rw [eb]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : (n + n + jo = i ∨ n + n + jo = n + i ∨ n + n + jo = n + n + ja) ∨ n + n + jo = n + j := hH
            have := Tno i ja hTa
            omega
    · have hi := hTa.1
      have hj := hTb.1
      have xa := hTa.2.2.2.2
      have xb := hTb.2.2.2.2
      by_cases hij : i = j
      · subst hij
        exfalso
        have e1 : ja = jb := by
          refine xb ja hTa.2.1 ?_
          rcases hTa.2.2.2.1 with ⟨e, _⟩ | ⟨_, e⟩
          · exact Or.inl (Or.inl e)
          · exact Or.inl (Or.inr e)
        exact hab (by rw [ea, eb, e1])
      · obtain ⟨v, hv, hvi, hvj⟩ := third i j hi hj
        cases hAn : An h with
        | true =>
          let P : ℕ → Bool := fun k => decide (k = i ∨ k = n + v)
          let Q : ℕ → Bool := fun k => decide (k = n + v)
          have va : V P (n + n + ja) = true := by rw [VT i ja hTa P, (show P (i) = true from by show decide ((i) = i ∨ (i) = n + v) = true; rw [decide_eq_true_eq] <;> omega), (show P (n + i) = false from by show decide ((n + i) = i ∨ (n + i) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have vb : V P (n + n + jb) = false := by rw [VT j jb hTb P, (show P (j) = false from by show decide ((j) = i ∨ (j) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega), (show P (n + j) = false from by show decide ((n + j) = i ∨ (n + j) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have ua : V Q (n + n + ja) = false := by rw [VT i ja hTa Q, (show Q (i) = false from by show decide ((i) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega), (show Q (n + i) = false from by show decide ((n + i) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have ub : V Q (n + n + jb) = false := by rw [VT j jb hTb Q, (show Q (j) = false from by show decide ((j) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega), (show Q (n + j) = false from by show decide ((n + j) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have hfin := fin (fun w => (w = i ∨ w = n + i ∨ w = n + n + ja)) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf i v hi hv).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := col1 v hv
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = i ∨ k = n + v) = decide (k = n + v)
            have hH2 : ¬((k = i ∨ k = n + i ∨ k = n + n + ja)) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬((n + n + k = i ∨ n + n + k = n + i ∨ n + n + k = n + n + ja)) := hkH
            have hr2 : ∃ w, rd A B k w ∧ ((w = i ∨ w = n + i ∨ w = n + n + ja)) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with (rfl | rfl | rfl)
            · exfalso; have := xa k hk (Or.inl hw); omega
            · exfalso; have := xa k hk (Or.inr hw); omega
            · exact sa k hk (by rw [ea]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : (n + n + jo = i ∨ n + n + jo = n + i ∨ n + n + jo = n + n + ja) := hH
            have := Tno i ja hTa
            omega
        | false =>
          let P : ℕ → Bool := fun k => decide (k = i ∨ k = n + j)
          let Q : ℕ → Bool := fun k => decide (k = i)
          have va : V P (n + n + ja) = true := by rw [VT i ja hTa P, (show P (i) = true from by show decide ((i) = i ∨ (i) = n + j) = true; rw [decide_eq_true_eq] <;> omega), (show P (n + i) = false from by show decide ((n + i) = i ∨ (n + i) = n + j) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have vb : V P (n + n + jb) = true := by rw [VT j jb hTb P, (show P (j) = false from by show decide ((j) = i ∨ (j) = n + j) = false; rw [decide_eq_false_iff_not] <;> omega), (show P (n + j) = true from by show decide ((n + j) = i ∨ (n + j) = n + j) = true; rw [decide_eq_true_eq] <;> omega)]; rfl
          have ua : V Q (n + n + ja) = true := by rw [VT i ja hTa Q, (show Q (i) = true from by show decide ((i) = i) = true; rw [decide_eq_true_eq] <;> omega), (show Q (n + i) = false from by show decide ((n + i) = i) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have ub : V Q (n + n + jb) = false := by rw [VT j jb hTb Q, (show Q (j) = false from by show decide ((j) = i) = false; rw [decide_eq_false_iff_not] <;> omega), (show Q (n + j) = false from by show decide ((n + j) = i) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have hfin := fin (fun w => (w = i ∨ w = n + i ∨ w = n + n + ja) ∨ (w = j ∨ w = n + j ∨ w = n + n + jb)) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf i j hi hj).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := row1 i hi
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = i ∨ k = n + j) = decide (k = i)
            have hH2 : ¬((k = i ∨ k = n + i ∨ k = n + n + ja) ∨ (k = j ∨ k = n + j ∨ k = n + n + jb)) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬((n + n + k = i ∨ n + n + k = n + i ∨ n + n + k = n + n + ja) ∨ (n + n + k = j ∨ n + n + k = n + j ∨ n + n + k = n + n + jb)) := hkH
            have hr2 : ∃ w, rd A B k w ∧ ((w = i ∨ w = n + i ∨ w = n + n + ja) ∨ (w = j ∨ w = n + j ∨ w = n + n + jb)) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with (rfl | rfl | rfl) | (rfl | rfl | rfl)
            · exfalso; have := xa k hk (Or.inl hw); omega
            · exfalso; have := xa k hk (Or.inr hw); omega
            · exact sa k hk (by rw [ea]; exact hw)
            · exfalso; have := xb k hk (Or.inl hw); omega
            · exfalso; have := xb k hk (Or.inr hw); omega
            · exact sb k hk (by rw [eb]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : (n + n + jo = i ∨ n + n + jo = n + i ∨ n + n + jo = n + n + ja) ∨ (n + n + jo = j ∨ n + n + jo = n + j ∨ n + n + jo = n + n + jb) := hH
            have := Tno i ja hTa
            have := Tno j jb hTb
            omega

def onl (n : ℕ) (Q : ℕ → Bool) : List Bool := (List.range (n + n)).map Q

theorem onl_len (n : ℕ) (Q : ℕ → Bool) : (onl n Q).length = n + n := by simp [onl]

theorem onl_get (n : ℕ) (Q : ℕ → Bool) (k : ℕ) (hk : k < n + n) : (onl n Q).getD k false = Q k := by
  simp [onl, List.getD_eq_getElem?_getD, List.getElem?_range hk]

theorem one_onl (n : ℕ) (u v : Fin n) : PEqualNP.Represents.oneEach u v = onl n (pt n u v) := by
  refine List.ext_getElem (by simp [PEqualNP.Represents.oneEach, onl]) fun k h1 h2 => ?_
  have hk : k < n + n := by simpa [onl] using h2
  simp only [PEqualNP.Represents.oneEach, onl, List.getElem_map, List.getElem_range, pt]
  by_cases h : k < n
  · rw [List.getElem_append_left (by simpa using h)]
    simp only [List.getElem_ofFn, Fin.ext_iff]
    rw [decide_eq_decide]
    have := v.isLt
    omega
  · rw [List.getElem_append_right (by simpa using h)]
    simp only [List.getElem_ofFn, List.length_ofFn, Fin.ext_iff]
    rw [decide_eq_decide]
    have := u.isLt
    omega

theorem vmono (n : ℕ) (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C) (Q R : ℕ → Bool) (h : ∀ k, Q k = true → R k = true) (w : ℕ)
    (hw : (run C.gates (onl n Q)).getD w false = true) : (run C.gates (onl n R)).getD w false = true := by
  refine mono C.gates (onl n Q) (onl n R) (by simp [onl]) ?_ (fun g hg => by simpa using (hC g hg).1) w hw
  intro i hi
  by_cases hin : i < n + n
  · rw [onl_get n _ i hin] at hi ⊢; exact h i hi
  · rw [List.getD_eq_default _ _ (by rw [onl_len]; omega)] at hi; cases hi

theorem two (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C)
    (hf : ∀ u v : Fin 2, C.eval (PEqualNP.Represents.oneEach u v) = decide (u ≠ v)) : 3 ≤ C.size := by
  classical
  obtain ⟨S, hS, hdet⟩ := det C.gates 4 (fun g hg => (hC g hg).2) {C.output}
  have hv : ∀ u v : Fin 2, (run C.gates (onl 2 (pt 2 u v))).getD C.output false = decide (u ≠ v) := by
    intro u v
    rw [← one_onl]; exact hf u v
  have row : ∀ u : Fin 2, (run C.gates (onl 2 fun k => decide (k = (u : ℕ)))).getD C.output false = false := by
    intro u
    by_contra h
    have h1 := vmono 2 C hC (fun k => decide (k = (u : ℕ))) (pt 2 u u) (by
      intro k hk
      have : k = (u : ℕ) := by simpa using hk
      simp [pt, this]) C.output (by simpa using h)
    rw [hv u u] at h1
    simp at h1
  have col : ∀ u : Fin 2, (run C.gates (onl 2 fun k => decide (k = 2 + (u : ℕ)))).getD C.output false = false := by
    intro u
    by_contra h
    have h1 := vmono 2 C hC (fun k => decide (k = 2 + (u : ℕ))) (pt 2 u u) (by
      intro k hk
      have : k = 2 + (u : ℕ) := by simpa using hk
      simp [pt, this]) C.output (by simpa using h)
    rw [hv u u] at h1
    simp at h1
  have see : ∀ (w : ℕ) (Q R : ℕ → Bool), (∀ k, k ≠ w → Q k = R k) → (run C.gates (onl 2 Q)).getD C.output false ≠ (run C.gates (onl 2 R)).getD C.output false → w ∈ S := by
    intro w Q R hQR hne
    by_contra hw
    refine hne (hdet (onl 2 Q) (onl 2 R) (by simp [onl]) (by simp [onl]) (fun i hi => ?_) C.output (by simp))
    by_cases hin : i < 2 + 2
    · rw [onl_get 2 _ i hin, onl_get 2 _ i hin]
      exact hQR i fun e => hw (e ▸ hi)
    · rw [List.getD_eq_default _ _ (by rw [onl_len]; omega), List.getD_eq_default _ _ (by rw [onl_len]; omega)]
  have h0 : 0 ∈ S := see 0 (pt 2 (0 : Fin 2) (1 : Fin 2)) (fun k => decide (k = 2 + ((1 : Fin 2) : ℕ))) (by intro k hk; simp [pt, hk]) (by rw [hv, col]; decide)
  have h1 : 1 ∈ S := see 1 (pt 2 (1 : Fin 2) (0 : Fin 2)) (fun k => decide (k = 2 + ((0 : Fin 2) : ℕ))) (by intro k hk; simp [pt, hk]) (by rw [hv, col]; decide)
  have h2 : 2 ∈ S := see 2 (pt 2 (1 : Fin 2) (0 : Fin 2)) (fun k => decide (k = ((1 : Fin 2) : ℕ))) (by intro k hk; simp [pt, hk]) (by rw [hv, row]; decide)
  have h3 : 3 ∈ S := see 3 (pt 2 (0 : Fin 2) (1 : Fin 2)) (fun k => decide (k = ((0 : Fin 2) : ℕ))) (by intro k hk; simp [pt, hk]) (by rw [hv, row]; decide)
  have hsub : ({0, 1, 2, 3} : Finset ℕ) ⊆ S := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl <;> assumption
  have hc := Finset.card_le_card hsub
  have e : ({0, 1, 2, 3} : Finset ℕ).card = 4 := by decide
  rw [e] at hc
  rw [Finset.card_singleton] at hS
  have : C.size = C.gates.length := rfl
  omega

theorem step3 (k : ℕ) (hk : 2 ≤ k) (C0 : Circuit) (hC0 : PEqualNP.MetaComplexity.Monotone2 C0)
    (hf0 : ∀ u v : Fin (k + 1), C0.eval (PEqualNP.Represents.oneEach u v) = decide (u ≠ v)) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ D.size + 3 ≤ C0.size ∧
      ∀ u v : Fin k, D.eval (PEqualNP.Represents.oneEach u v) = decide (u ≠ v) := by
  classical
  have hex : ∃ s, ∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size = s ∧ ∀ u v : Fin (k + 1), C.eval (PEqualNP.Represents.oneEach u v) = decide (u ≠ v) := ⟨_, C0, hC0, rfl, hf0⟩
  obtain ⟨C, hC, hCs, hf⟩ := Nat.find_spec hex
  have hmin : ∀ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D → (∀ u v : Fin (k + 1), D.eval (PEqualNP.Represents.oneEach u v) = decide (u ≠ v)) → C.size ≤ D.size := by
    intro D h1 h2
    rw [hCs]
    exact Nat.find_min' hex ⟨D, h1, rfl, h2⟩
  have hle : C.size ≤ C0.size := hmin C0 hC0 hf0
  set n := k + 1 with hn
  have hn3 : 3 ≤ n := by omega
  let V : (ℕ → Bool) → ℕ → Bool := fun Q w => (run C.gates (onl n Q)).getD w false
  have hm : C.size = C.gates.length := rfl
  have hV : ∀ u v : Fin n, ∀ w, V (pt n u v) w = (run C.gates (PEqualNP.Represents.oneEach u v)).getD w false := by
    intro u v w
    rw [one_onl]
  have hlen1 : ∀ u v : Fin n, (PEqualNP.Represents.oneEach u v).length = n + n := fun u v => by
    simp only [PEqualNP.Represents.oneEach, List.length_append, List.length_ofFn]
  have nonc : ¬∃ b, ∀ p : Fin n × Fin n, C.eval (PEqualNP.Represents.oneEach p.1 p.2) = b := by
    rintro ⟨b, hb⟩
    have h1 := hb (⟨0, by omega⟩, ⟨0, by omega⟩)
    have h2 := hb (⟨0, by omega⟩, ⟨1, by omega⟩)
    rw [hf] at h1 h2
    rw [← h1] at h2
    simp at h2
  have irr0 : ∀ j < C.gates.length, ¬((∃ b, ∀ p : Fin n × Fin n, (run C.gates (PEqualNP.Represents.oneEach p.1 p.2)).getD (n + n + j) false = b) ∨
      ∃ w < n + n + j, ∀ p : Fin n × Fin n, (run C.gates (PEqualNP.Represents.oneEach p.1 p.2)).getD (n + n + j) false = (run C.gates (PEqualNP.Represents.oneEach p.1 p.2)).getD w false) := by
    intro j hj hbad
    obtain ⟨D, d1, d2, d3⟩ := engine3 (n + n) (n + n) C (fun p : Fin n × Fin n => PEqualNP.Represents.oneEach p.1 p.2) (fun p => PEqualNP.Represents.oneEach p.1 p.2)
      (fun p => hlen1 _ _) (fun p => hlen1 _ _) {j} hC (fun w hw => Or.inr ⟨w, hw, fun _ => rfl⟩) nonc (by
        intro i hi
        have : i = j := by simpa using hi
        subst this
        exact ⟨hj, hbad⟩)
    have := hmin D d1 fun u v => (d3 (u, v)).trans (hf u v)
    rw [Finset.card_singleton] at d2
    omega
  have shape : ∀ j, j < C.gates.length → ∃ a b : ℕ, ∃ c : Bool, a < n + n + j ∧ b < n + n + j ∧ a ≠ b ∧
      ∀ Q, V Q (n + n + j) = if c = true then V Q a && V Q b else V Q a || V Q b := by
    intro j hj
    obtain ⟨hop, hl⟩ := hC _ (List.getElem_mem hj)
    have hop' : C.gates[j].op = GateOp.and ∨ C.gates[j].op = GateOp.or := by simpa using hop
    have rg0 : ∀ l : List Bool, l.length = n + n → (run C.gates l).getD (n + n + j) false = C.gates[j].op.eval (C.gates[j].inputs.map fun i => if i < n + n + j then (run C.gates l).getD i false else false) := by
      intro l hll
      have := run_gate C.gates l j hj
      rw [hll] at this
      exact this
    have bad := irr0 j hj
    generalize hin : C.gates[j].inputs = l at hl rg0
    rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · exact absurd (Or.inl ⟨C.gates[j].op.eval [], fun p => by rw [rg0 _ (hlen1 _ _)]; rfl⟩) bad
    · by_cases ha : a < n + n + j
      · refine absurd (Or.inr ⟨a, ha, fun p => ?_⟩) bad
        rw [rg0 _ (hlen1 _ _)]
        rcases hop' with e | e <;> simp [e, GateOp.eval, ha]
      · refine absurd (Or.inl ⟨false, fun p => ?_⟩) bad
        rw [rg0 _ (hlen1 _ _)]
        rcases hop' with e | e <;> simp [e, GateOp.eval, ha]
    · by_cases ha : a < n + n + j
      · by_cases hb : b < n + n + j
        · by_cases hab : a = b
          · refine absurd (Or.inr ⟨a, ha, fun p => ?_⟩) bad
            rw [rg0 _ (hlen1 _ _), ← hab]
            rcases hop' with e | e <;> simp [e, GateOp.eval, ha]
          · rcases hop' with e | e
            · refine ⟨a, b, true, ha, hb, hab, fun Q => ?_⟩
              have := rg0 (onl n Q) (onl_len n Q)
              rw [e] at this
              simp only [List.map_cons, List.map_nil, if_pos ha, if_pos hb, GateOp.eval, List.all_cons, List.all_nil, id, Bool.and_true] at this
              simpa [V] using this
            · refine ⟨a, b, false, ha, hb, hab, fun Q => ?_⟩
              have := rg0 (onl n Q) (onl_len n Q)
              rw [e] at this
              simp only [List.map_cons, List.map_nil, if_pos ha, if_pos hb, GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false] at this
              simpa [V] using this
        · rcases hop' with e | e
          · refine absurd (Or.inl ⟨false, fun p => ?_⟩) bad
            rw [rg0 _ (hlen1 _ _)]
            simp [e, GateOp.eval, hb]
          · refine absurd (Or.inr ⟨a, ha, fun p => ?_⟩) bad
            rw [rg0 _ (hlen1 _ _)]
            simp [e, GateOp.eval, ha, hb]
      · rcases hop' with e | e
        · refine absurd (Or.inl ⟨false, fun p => ?_⟩) bad
          rw [rg0 _ (hlen1 _ _)]
          simp [e, GateOp.eval, ha]
        · by_cases hb : b < n + n + j
          · refine absurd (Or.inr ⟨b, hb, fun p => ?_⟩) bad
            rw [rg0 _ (hlen1 _ _)]
            simp [e, GateOp.eval, ha, hb]
          · refine absurd (Or.inl ⟨false, fun p => ?_⟩) bad
            rw [rg0 _ (hlen1 _ _)]
            simp [e, GateOp.eval, ha, hb]
    · simp at hl
  choose! A B An hA hB hAB hv1 using shape
  have hout : C.output < n + n + C.gates.length := by
    by_contra h
    refine nonc ⟨false, fun p => ?_⟩
    change (run C.gates (PEqualNP.Represents.oneEach p.1 p.2)).getD C.output false = false
    exact List.getD_eq_default _ _ (by rw [run_length, hlen1]; omega)
  obtain ⟨i, hi, a, b, c, ha, hb, hc, hab, hac, hbc, ka, kb, kc⟩ := core n hn3 C.gates.length A B An V C.output hA hB hAB
    (fun Q w hw => by
      simp only [V]
      rw [run_input _ _ _ (by rw [onl_len]; exact hw), onl_get n Q w hw])
    (fun Q j hj => hv1 j hj Q) hout
    (fun u v hu hv => by
      have := hf ⟨u, hu⟩ ⟨v, hv⟩
      rw [one_onl] at this
      change (run C.gates (onl n (pt n u v))).getD C.output false = _ at this
      simp only [V]
      rw [this]
      simp [Fin.ext_iff])
    (fun j hj w hw hall => irr0 j hj (Or.inr ⟨w, hw, fun p => by rw [← hV, ← hV]; exact hall _ _ p.1.isLt p.2.isLt⟩))
  let ii : Fin (k + 1) := ⟨i, hi⟩
  have hsa : ∀ u : Fin k, ((ii.succAbove u : Fin (k + 1)) : ℕ) ≠ i := fun u h => Fin.succAbove_ne ii u (Fin.ext h)
  have hlen2 : ∀ u v : Fin k, (PEqualNP.Represents.oneEach u v).length = k + k := by intro u v; simp [PEqualNP.Represents.oneEach]
  have kf : ∀ j, Kill n V i j → (∃ b, ∀ p : Fin k × Fin k, (run C.gates (PEqualNP.Represents.oneEach (ii.succAbove p.1) (ii.succAbove p.2))).getD (n + n + j) false = b) ∨
      ∃ w < n + n + j, ∀ p : Fin k × Fin k, (run C.gates (PEqualNP.Represents.oneEach (ii.succAbove p.1) (ii.succAbove p.2))).getD (n + n + j) false = (run C.gates (PEqualNP.Represents.oneEach (ii.succAbove p.1) (ii.succAbove p.2))).getD w false := by
    rintro j (⟨b, h⟩ | ⟨w, hw, h⟩)
    · exact Or.inl ⟨b, fun p => by rw [← hV]; exact h _ _ (Fin.isLt _) (Fin.isLt _) (hsa _) (hsa _)⟩
    · exact Or.inr ⟨w, hw, fun p => by rw [← hV, ← hV]; exact h _ _ (Fin.isLt _) (Fin.isLt _) (hsa _) (hsa _)⟩
  obtain ⟨D, d1, d2, d3⟩ := engine3 (n + n) (k + k) C (fun p : Fin k × Fin k => PEqualNP.Represents.oneEach (ii.succAbove p.1) (ii.succAbove p.2)) (fun p => PEqualNP.Represents.oneEach p.1 p.2)
    (fun p => hlen1 _ _) (fun p => hlen2 _ _) {a, b, c} hC (by
      intro w hw
      by_cases h : w < n
      · by_cases hwi : w = i
        · left
          refine ⟨false, fun p => ?_⟩
          rw [one_onl, onl_get n _ w hw, pt, decide_eq_false_iff_not]
          have := hsa p.1
          omega
        · right
          obtain ⟨u', hu'⟩ := Fin.exists_succAbove_eq (x := (⟨w, h⟩ : Fin (k + 1))) (y := ii) (fun e => hwi (congrArg Fin.val e))
          refine ⟨u', by have := u'.isLt; omega, fun p => ?_⟩
          rw [one_onl, one_onl, onl_get n _ w hw, onl_get k _ _ (by have := u'.isLt; omega)]
          simp only [pt]
          rw [decide_eq_decide]
          have e1 : w = ((ii.succAbove p.1 : Fin (k + 1)) : ℕ) ↔ (u' : ℕ) = p.1 := by
            rw [← show ((ii.succAbove u' : Fin (k + 1)) : ℕ) = w from congrArg Fin.val hu', ← Fin.ext_iff, ← Fin.ext_iff, (Fin.succAbove_right_injective).eq_iff]
          have := u'.isLt
          constructor
          · rintro (e | e)
            · exact Or.inl (e1.1 e)
            · omega
          · rintro (e | e)
            · exact Or.inl (e1.2 e)
            · omega
      · by_cases hwi : w = n + i
        · left
          refine ⟨false, fun p => ?_⟩
          rw [one_onl, onl_get n _ w hw, pt, decide_eq_false_iff_not]
          have := hsa p.2
          have := (ii.succAbove p.1).isLt
          omega
        · right
          obtain ⟨u', hu'⟩ := Fin.exists_succAbove_eq (x := (⟨w - n, by omega⟩ : Fin (k + 1))) (y := ii) (fun e => hwi (by have := congrArg Fin.val e; simp only [ii] at this; omega))
          refine ⟨k + u', by have := u'.isLt; omega, fun p => ?_⟩
          rw [one_onl, one_onl, onl_get n _ w hw, onl_get k _ _ (by have := u'.isLt; omega)]
          simp only [pt]
          rw [decide_eq_decide]
          have e0 : ((ii.succAbove u' : Fin (k + 1)) : ℕ) = w - n := congrArg Fin.val hu'
          have e1 : w - n = ((ii.succAbove p.2 : Fin (k + 1)) : ℕ) ↔ (u' : ℕ) = p.2 := by
            rw [← e0, ← Fin.ext_iff, ← Fin.ext_iff, (Fin.succAbove_right_injective).eq_iff]
          have h1 := u'.isLt
          have h2 := p.1.isLt
          have h3 := (ii.succAbove p.1).isLt
          constructor
          · rintro (e | e)
            · omega
            · have := e1.1 (by omega); omega
          · rintro (e | e)
            · omega
            · have := e1.2 (by omega); omega)
    (by
      rintro ⟨b, hb⟩
      have h1 := hb (⟨0, by omega⟩, ⟨0, by omega⟩)
      have h2 := hb (⟨0, by omega⟩, ⟨1, by omega⟩)
      simp only [hf] at h1 h2
      rw [← h1] at h2
      simp [(Fin.succAbove_right_injective).eq_iff] at h2)
    (by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl | rfl
      · exact ⟨ha, kf _ ka⟩
      · exact ⟨hb, kf _ kb⟩
      · exact ⟨hc, kf _ kc⟩)
  have hcard : ({a, b, c} : Finset ℕ).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]
  rw [hcard] at d2
  refine ⟨D, d1, by omega, fun u v => ?_⟩
  rw [d3 (u, v), hf]
  simp only [ne_eq, (Fin.succAbove_right_injective).eq_iff]

end PEqualNP.Outside.L_meta_18153

open PEqualNP.Outside.L_meta_18153 in
theorem PEqualNP.Outside.L_meta_18153 : (∀ n s : ℕ, PEqualNP.Represents.RepSizeAtMost (fun u v : Fin (n + 1) => decide (u ≠ v)) (s + 3) → PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide (u ≠ v)) s) := by
  rintro n s ⟨C, hC, hs, hf⟩
  rcases Nat.lt_or_ge n 2 with hn | hn
  · refine ⟨⟨[], n + n⟩, ?_, ?_, ?_⟩
    · intro g hg
      simp at hg
    · show 0 ≤ s
      omega
    · intro u v
      have huv : u = v := by
        apply Fin.ext
        have := u.isLt
        have := v.isLt
        omega
      subst huv
      simp only [ne_eq, not_true_eq_false, decide_false]
      show (List.foldl _ (PEqualNP.Represents.oneEach u u) []).getD (n + n) false = false
      simp only [List.foldl_nil]
      exact List.getD_eq_default _ _ (by simp [PEqualNP.Represents.oneEach])
  · obtain ⟨D, d1, d2, d3⟩ := step3 n hn C hC hf
    exact ⟨D, d1, by omega, d3⟩
