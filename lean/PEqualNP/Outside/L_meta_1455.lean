import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1455_aux

open PEqualNP.CircuitLowerBounds

theorem wires_snoc (gs : List Gate) (g : Gate) (o o2 : ℕ) (l : List Bool) :
    Circuit.wires ⟨gs ++ [g], o⟩ l = Circuit.wires ⟨gs, o2⟩ l ++
      [g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨gs, o2⟩ l).getD i false)] := by
  simp [Circuit.wires, List.foldl_append]

theorem wires_length (gs : List Gate) (o : ℕ) (l : List Bool) :
    (Circuit.wires ⟨gs, o⟩ l).length = l.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton gs g ih =>
    rw [wires_snoc gs g o o, List.length_append, ih]
    simp
    omega

theorem foldl_prefix (r : List Gate) : ∀ l : List Bool,
    l <+: r.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) l := by
  induction r with
  | nil => intro l; simp
  | cons g r ih =>
    intro l
    rw [List.foldl_cons]
    exact (List.prefix_append l _).trans (ih _)

theorem wires_prefix (gs r : List Gate) (o o2 : ℕ) (l : List Bool) :
    Circuit.wires ⟨gs, o⟩ l <+: Circuit.wires ⟨gs ++ r, o2⟩ l := by
  simp only [Circuit.wires, List.foldl_append]
  exact foldl_prefix r _

theorem getD_prefix (l1 l2 : List Bool) (h : l1 <+: l2) (i : ℕ) (hi : i < l1.length) :
    l2.getD i false = l1.getD i false := by
  obtain ⟨t, rfl⟩ := h
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem eval_prefix (gs r : List Gate) (o : ℕ) (l : List Bool) (i : ℕ)
    (hi : i < l.length + gs.length) :
    Circuit.eval ⟨gs ++ r, i⟩ l = (Circuit.wires ⟨gs, o⟩ l).getD i false := by
  unfold Circuit.eval
  exact getD_prefix _ _ (wires_prefix gs r o i l) i (by rw [wires_length]; exact hi)

theorem all_mono (f1 f2 : ℕ → Bool) (h : ∀ i, f1 i = true → f2 i = true) (l : List ℕ)
    (h1 : (l.map f1).all id = true) : (l.map f2).all id = true := by
  simp only [List.all_eq_true, List.mem_map] at *
  rintro b ⟨a, ha, rfl⟩
  exact h a (h1 _ ⟨a, ha, rfl⟩)

theorem any_mono (f1 f2 : ℕ → Bool) (h : ∀ i, f1 i = true → f2 i = true) (l : List ℕ)
    (h1 : (l.map f1).any id = true) : (l.map f2).any id = true := by
  simp only [List.any_eq_true, List.mem_map] at *
  obtain ⟨b, ⟨a, ha, rfl⟩, hb⟩ := h1
  exact ⟨_, ⟨a, ha, rfl⟩, h a hb⟩

theorem mono (n : ℕ) (T : Finset (Fin n)) (gates : List Gate) (j : Fin gates.length)
    (hops : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hnot : ∀ i : Fin gates.length, (gates.get i).op = GateOp.not → i = j)
    (htrue : ∀ x : Fin n → Bool, (∀ v ∈ T, x v = false) →
      Circuit.eval ⟨gates, n + (j : ℕ)⟩ (List.ofFn x) = true) :
    ∀ (gs rest : List Gate), gates = gs ++ rest →
    ∀ (w : ℕ) (x y : Fin n → Bool), (∀ v ∈ T, y v = false) → (∀ v : Fin n, x v = true → y v = true) →
      (Circuit.wires ⟨gs, 0⟩ (List.ofFn x)).getD w false = true →
      (Circuit.wires ⟨gs, 0⟩ (List.ofFn y)).getD w false = true := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro rest _ w x y hy hxy h
    simp only [Circuit.wires, List.foldl_nil] at h ⊢
    by_cases hw : w < n
    · simp [List.getD_eq_getElem?_getD, hw] at h ⊢
      exact hxy _ h
    · simp [List.getD_eq_getElem?_getD, hw] at h
  | append_singleton gs g ih =>
    intro rest hg w x y hy hxy h
    have ih' := ih (g :: rest) (by simp [hg])
    have hlen : ∀ z : Fin n → Bool,
        (Circuit.wires ⟨gs, 0⟩ (List.ofFn z)).length = n + gs.length := by
      intro z
      rw [wires_length]
      simp
    rcases lt_trichotomy w (n + gs.length) with hw | hw | hw
    · rw [wires_snoc gs g 0 0] at h ⊢
      rw [List.getD_append _ _ _ _ (by rw [hlen]; exact hw)] at h ⊢
      exact ih' w x y hy hxy h
    · have hgm : g ∈ gates := by rw [hg]; simp
      have hval : ∀ z : Fin n → Bool,
          (Circuit.wires ⟨gs ++ [g], 0⟩ (List.ofFn z)).getD w false =
          g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨gs, 0⟩ (List.ofFn z)).getD i false) := by
        intro z
        rw [wires_snoc gs g 0 0, List.getD_append_right _ _ _ _ (by rw [hlen]; omega), hlen, hw]
        simp
      rcases (hops g hgm).1 with ho | ho | ho
      · rw [hval, ho] at h ⊢
        exact all_mono _ _ (fun i hi => ih' i x y hy hxy hi) _ h
      · rw [hval, ho] at h ⊢
        exact any_mono _ _ (fun i hi => ih' i x y hy hxy hi) _ h
      · have hget : gates[gs.length]? = some g := by rw [hg]; simp
        obtain ⟨hl, hh⟩ := List.getElem?_eq_some_iff.mp hget
        have hj := hnot ⟨gs.length, hl⟩ (by simp [hh, ho])
        have ht := htrue y hy
        rw [← hj] at ht
        simp only [] at ht
        have he := eval_prefix (gs ++ [g]) rest 0 (List.ofFn y) w (by simp; omega)
        rw [← hg, hw] at he
        rw [hw, ← he]
        exact ht
    · rw [wires_snoc gs g 0 0] at h
      rw [List.getD_append_right _ _ _ _ (by rw [hlen]; omega), hlen] at h
      have : w - (n + gs.length) ≠ 0 := by omega
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero this
      rw [hk] at h
      simp at h

theorem gate_val (gs rest : List Gate) (g : Gate) (n : ℕ) (l : List Bool) (hl : l.length = n) :
    Circuit.eval ⟨gs ++ g :: rest, n + gs.length⟩ l =
      g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨gs, 0⟩ l).getD i false) := by
  have he := eval_prefix (gs ++ [g]) rest 0 l (n + gs.length) (by simp; omega)
  rw [List.append_assoc, List.singleton_append] at he
  rw [he, wires_snoc gs g 0 0,
    List.getD_append_right _ _ _ _ (by rw [wires_length]; omega), wires_length, hl]
  simp

end PEqualNP.Outside.L_meta_1455_aux

theorem PEqualNP.Outside.L_meta_1455 : ∀ (n : ℕ) (T : Finset (Fin n)) (gates : List PEqualNP.CircuitLowerBounds.Gate)
    (j : Fin gates.length),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    (∀ x : Fin n → Bool, (∀ v ∈ T, x v = false) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (j : ℕ)⟩ (List.ofFn x) = true) →
    ∀ (g : Fin gates.length) (a b : ℕ), (gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.and →
    (gates.get g).inputs = [a, b] →
    (∀ x : Fin n → Bool, (∀ v ∈ T, x v = false) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (g : ℕ)⟩ (List.ofFn x) = false) →
    (n + (g : ℕ) ≤ a ∨ ∀ x : Fin n → Bool, (∀ v ∈ T, x v = false) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn x) = false) ∨
    (n + (g : ℕ) ≤ b ∨ ∀ x : Fin n → Bool, (∀ v ∈ T, x v = false) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn x) = false) := by
  intro n T gates j hops hnot htrue g a b hop hin hfalse
  by_cases ha : n + (g : ℕ) ≤ a
  · exact Or.inl (Or.inl ha)
  by_cases hb : n + (g : ℕ) ≤ b
  · exact Or.inr (Or.inl hb)
  have hmono : ∀ (w : ℕ) (x y : Fin n → Bool), (∀ v ∈ T, y v = false) →
      (∀ v : Fin n, x v = true → y v = true) →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x) = true →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn y) = true := by
    intro w x y hy hxy h
    exact PEqualNP.Outside.L_meta_1455_aux.mono n T gates j hops hnot htrue gates [] (by simp) w x y hy hxy h
  have htop : ∀ v ∈ T, (fun v : Fin n => !decide (v ∈ T)) v = false := by
    intro v hv
    simp [hv]
  have hle : ∀ x : Fin n → Bool, (∀ v ∈ T, x v = false) →
      ∀ v : Fin n, x v = true → (fun v : Fin n => !decide (v ∈ T)) v = true := by
    intro x hx v hv
    by_cases hvT : v ∈ T
    · rw [hx v hvT] at hv
      cases hv
    · simp [hvT]
  have hdown : ∀ w : ℕ,
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn (fun v : Fin n => !decide (v ∈ T))) = false →
      ∀ x : Fin n → Bool, (∀ v ∈ T, x v = false) →
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x) = false := by
    intro w hw x hx
    by_contra hc
    have h1 := hmono w x _ htop (hle x hx) (by simpa using hc)
    rw [hw] at h1
    cases h1
  have hsplit : gates = gates.take (g : ℕ) ++ gates.get g :: gates.drop ((g : ℕ) + 1) := by
    simp
  have hlen : (gates.take (g : ℕ)).length = (g : ℕ) := by
    simp
  have hv := PEqualNP.Outside.L_meta_1455_aux.gate_val (gates.take (g : ℕ)) (gates.drop ((g : ℕ) + 1))
    (gates.get g) n (List.ofFn (fun v : Fin n => !decide (v ∈ T))) (by simp)
  have hea := PEqualNP.Outside.L_meta_1455_aux.eval_prefix (gates.take (g : ℕ))
    (gates.get g :: gates.drop ((g : ℕ) + 1)) 0 (List.ofFn (fun v : Fin n => !decide (v ∈ T))) a
    (by rw [hlen]; simp; omega)
  have heb := PEqualNP.Outside.L_meta_1455_aux.eval_prefix (gates.take (g : ℕ))
    (gates.get g :: gates.drop ((g : ℕ) + 1)) 0 (List.ofFn (fun v : Fin n => !decide (v ∈ T))) b
    (by rw [hlen]; simp; omega)
  rw [← hsplit] at hv hea heb
  rw [hlen, hfalse _ htop, hop, hin] at hv
  simp only [List.map_cons, List.map_nil, PEqualNP.CircuitLowerBounds.GateOp.eval] at hv
  rw [← hea, ← heb] at hv
  simp only [List.all_cons, List.all_nil, id, Bool.and_true] at hv
  rcases (Bool.and_eq_false_iff.mp hv.symm) with h | h
  · exact Or.inl (Or.inr (hdown a h))
  · exact Or.inr (Or.inr (hdown b h))
