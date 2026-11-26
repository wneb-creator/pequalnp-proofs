import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18107

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

-- Evaluation of a topologically ordered binary circuit.
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

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  exact foldl_getD_gate C.gates x j hj

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

def V (C : Circuit) {N : ℕ} (x : Fin N → Bool) (u : ℕ) : Bool := val C (List.ofFn x) u

def in0 (C : Circuit) (k : ℕ) : ℕ := (gateAt C k).inputs.getD 0 0

def in1 (C : Circuit) (k : ℕ) : ℕ := (gateAt C k).inputs.getD 1 0

lemma V_input (C : Circuit) {N : ℕ} (x : Fin N → Bool) {u : ℕ} (hu : u < N) :
    V C x u = x ⟨u, hu⟩ := by
  unfold V
  rw [val_input (n := N) (by simp) hu]
  simp [List.getD_eq_getElem?_getD, hu]

lemma V_ge (C : Circuit) {N : ℕ} (x : Fin N → Bool) {u : ℕ} (hu : N + C.gates.length ≤ u) :
    V C x u = false := by
  unfold V
  exact val_ge (n := N) (by simp) hu

lemma gate_two {N : ℕ} {C : Circuit} (hAO : PEqualNP.TopForm.IsAO2 N C) {k : ℕ}
    (hk : k < C.gates.length) :
    (gateAt C k).inputs = [in0 C k, in1 C k] ∧ in0 C k < N + k ∧ in1 C k < N + k ∧
      ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) := by
  have hmem : gateAt C k ∈ C.gates := by rw [gateAt_eq hk]; exact List.getElem_mem hk
  have hl := hAO.2.2 _ hmem
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hl
  have hr := hAO.2.1 k hk
  have ha := hr a (by simp [hab])
  have hb := hr b (by simp [hab])
  refine ⟨?_, ?_, ?_, hAO.1 _ hmem⟩
  · simp [in0, in1, hab]
  · simpa [in0, hab] using ha
  · simpa [in1, hab] using hb

lemma V_gate {N : ℕ} {C : Circuit} (hAO : PEqualNP.TopForm.IsAO2 N C) {k : ℕ}
    (hk : k < C.gates.length) (x : Fin N → Bool) :
    V C x (N + k) = (gateAt C k).op.eval [V C x (in0 C k), V C x (in1 C k)] := by
  obtain ⟨h2, ha, hb, _⟩ := gate_two hAO hk
  unfold V
  rw [val_gate (n := N) (by simp) hk, ← gateAt_eq hk, h2]
  simp [ha, hb]

lemma V_and {N : ℕ} {C : Circuit} (hAO : PEqualNP.TopForm.IsAO2 N C) {k : ℕ}
    (hk : k < C.gates.length) (hop : (gateAt C k).op = GateOp.and) (x : Fin N → Bool) :
    V C x (N + k) = (V C x (in0 C k) && V C x (in1 C k)) := by
  rw [V_gate hAO hk, hop]; simp [GateOp.eval]

lemma V_or {N : ℕ} {C : Circuit} (hAO : PEqualNP.TopForm.IsAO2 N C) {k : ℕ}
    (hk : k < C.gates.length) (hop : (gateAt C k).op = GateOp.or) (x : Fin N → Bool) :
    V C x (N + k) = (V C x (in0 C k) || V C x (in1 C k)) := by
  rw [V_gate hAO hk, hop]; simp [GateOp.eval]


-- Each deleted input has a satisfying pair with a surviving input. The
-- first live wire on a sensitized path from the deleted input is an OR.
lemma mono_wire {N : ℕ} {C : Circuit} (ao : IsAO2 N C) {x y : Fin N → Bool}
    (h : ∀ i, x i = true → y i = true) (u : ℕ) :
    V C x u = true → V C y u = true := by
  induction u using Nat.strong_induction_on with
  | ind u ih =>
    intro hx
    by_cases hu : u < N
    · rw [V_input C x hu] at hx
      rw [V_input C y hu]
      exact h _ hx
    by_cases hout : N + C.gates.length ≤ u
    · rw [V_ge C x hout] at hx
      contradiction
    let k := u - N
    have hk : k < C.gates.length := by dsimp [k]; omega
    have he : u = N + k := by dsimp [k]; omega
    obtain ⟨_, ha, hb, hop⟩ := gate_two ao hk
    rcases hop with hand | hor
    · rw [he, V_and ao hk hand, Bool.and_eq_true] at hx ⊢
      exact ⟨ih _ (he ▸ ha) hx.1, ih _ (he ▸ hb) hx.2⟩
    · rw [he, V_or ao hk hor, Bool.or_eq_true] at hx ⊢
      exact hx.imp (ih _ (he ▸ ha)) (ih _ (he ▸ hb))

def loss (C : Circuit) {N : ℕ} (before after : Fin N → Bool) (a b : ℕ) : Prop :=
  V C before a = true ∧ V C after a = false ∧ V C after b = true

def marked (C : Circuit) {N : ℕ} (before after : Fin N → Bool)
    (k : Fin C.gates.length) : Prop :=
  (gateAt C k.val).op = .or ∧
    (loss C before after (in0 C k.val) (in1 C k.val) ∨
      loss C before after (in1 C k.val) (in0 C k.val))

lemma find_marked {N : ℕ} {C : Circuit} (ao : IsAO2 N C)
    {x y before after : Fin N → Bool}
    (hbefore : ∀ i, x i = true → before i = true)
    (hinput : ∀ i, x i = true → y i = false → after i = false)
    (u : ℕ) : V C x u = true → V C y u = false → V C after u = true →
      ∃ k : Fin C.gates.length, marked C before after k := by
  induction u using Nat.strong_induction_on with
  | ind u ih =>
    intro hx hy hz
    by_cases hu : u < N
    · rw [V_input C x hu] at hx
      rw [V_input C y hu] at hy
      rw [V_input C after hu, hinput _ hx hy] at hz
      contradiction
    by_cases hout : N + C.gates.length ≤ u
    · rw [V_ge C x hout] at hx
      contradiction
    let k := u - N
    have hk : k < C.gates.length := by dsimp [k]; omega
    have he : u = N + k := by dsimp [k]; omega
    obtain ⟨_, ha, hb, hop⟩ := gate_two ao hk
    rcases hop with hand | hor
    · rw [he, V_and ao hk hand, Bool.and_eq_true] at hx hz
      rw [he, V_and ao hk hand, Bool.and_eq_false_iff] at hy
      exact hy.elim (fun hy => ih _ (he ▸ ha) hx.1 hy hz.1)
        (fun hy => ih _ (he ▸ hb) hx.2 hy hz.2)
    · rw [he, V_or ao hk hor, Bool.or_eq_true] at hx hz
      rw [he, V_or ao hk hor, Bool.or_eq_false_iff] at hy
      rcases hx with hx | hx
      · cases ha' : V C after (in0 C k)
        · exact ⟨⟨k, hk⟩, hor, Or.inl
            ⟨mono_wire ao hbefore _ hx, ha', hz.resolve_left (by simp [ha'])⟩⟩
        · exact ih _ (he ▸ ha) hx hy.1 ha'
      · cases hb' : V C after (in1 C k)
        · exact ⟨⟨k, hk⟩, hor, Or.inr
            ⟨mono_wire ao hbefore _ hx, hb', hz.resolve_right (by simp [hb'])⟩⟩
        · exact ih _ (he ▸ hb) hx hy.2 hb'

def rank (v : Fin 26) : ℕ :=
  [25, 20, 11, 19, 17, 16, 14, 15, 10, 18, 13, 12, 9,
    24, 8, 5, 4, 23, 7, 2, 3, 1, 0, 22, 6, 21].getD v.val 0

def active (i : ℕ) (v : Fin 26) : Bool := decide (i ≤ rank v)

def point (i : Fin 24) : Fin 13 :=
  [9, 9, 9, 3, 3, 3, 1, 1, 1, 12, 8, 2, 11, 10, 6, 7, 5, 4, 9, 3, 1, 0, 0, 0].getD i.val 0

def line (i : Fin 24) : Fin 13 :=
  [9, 8, 6, 7, 3, 2, 11, 5, 1, 12, 12, 12, 10, 10, 10, 4, 4, 4, 0, 0, 0, 12, 10, 4].getD i.val 0

def survivor (i : Fin 24) : Fin 26 :=
  [9, 9, 9, 3, 3, 3, 1, 1, 1, 25, 25, 25, 23, 23, 23, 17, 17, 17,
    13, 13, 13, 0, 0, 0].getD i.val 0

def inc (p l : Fin 13) : Prop := p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9

def hit (x : Fin 26 → Bool) : Prop :=
  ∃ p l : Fin 13, inc p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true

def pair (i : Fin 24) (v : Fin 26) : Bool :=
  decide (v = Fin.castAdd 13 (point i) ∨ v = Fin.natAdd 13 (line i))

def single (i : Fin 24) (v : Fin 26) : Bool := decide (v = survivor i)

lemma hit_pair (i : Fin 24) : hit (pair i) := by
  have edges : ∀ j : Fin 24, inc (point j) (line j) := by unfold inc; decide
  exact ⟨point i, line i, edges i, by simp [pair], by simp [pair]⟩

lemma no_single (i : Fin 24) : ¬ hit (single i) := by
  rintro ⟨p, l, _, hp, hl⟩
  have hp' := congrArg Fin.val (of_decide_eq_true hp)
  have hl' := congrArg Fin.val (of_decide_eq_true hl)
  change p.val = (survivor i).val at hp'
  change 13 + l.val = (survivor i).val at hl'
  omega

lemma hit_active (i : Fin 24) : hit (active (i.val + 1)) := by
  refine ⟨0, 0, Or.inl rfl, ?_, ?_⟩
  · change decide (i.val + 1 ≤ 25) = true
    exact decide_eq_true (by omega)
  · change decide (i.val + 1 ≤ 24) = true
    exact decide_eq_true (by omega)

-- The same OR cannot survive a second deletion of one of its inputs.
lemma marked_lt_impossible {C : Circuit} (ao : IsAO2 26 C)
    {i j : ℕ} (hij : i < j) {k : Fin C.gates.length}
    (hi : marked C (active i) (active (i + 1)) k)
    (hj : marked C (active j) (active (j + 1)) k) : False := by
  have persist (u : ℕ) {s t : ℕ} (hst : s ≤ t) :
      V C (active t) u = true → V C (active s) u = true :=
    mono_wire ao (fun v hv => decide_eq_true (le_trans hst (of_decide_eq_true hv))) u
  have clash u (h : V C (active (i + 1)) u = false) {t : ℕ} (ht : i + 1 ≤ t)
      (ht' : V C (active t) u = true) : False := by
    have hh := persist u ht ht'
    rw [h] at hh
    contradiction
  rcases hi.2 with hi | hi <;> rcases hj.2 with hj | hj
  · exact clash _ hi.2.1 (by omega) hj.1
  · exact clash _ hi.2.1 (by omega) hj.2.2
  · exact clash _ hi.2.1 (by omega) hj.2.2
  · exact clash _ hi.2.1 (by omega) hj.1

lemma count_or_and (C : Circuit) (ao : IsAO2 26 C)
    (correct : ∀ x, V C x C.output = true ↔ hit x) :
    24 + {i : Fin C.gates.length | (C.gates.get i).op = GateOp.and}.ncard ≤ C.size := by
  classical
  have before : ∀ (i : Fin 24) (v : Fin 26), pair i v = true →
      active i.val v = true := by decide
  have deleted : ∀ (i : Fin 24) (v : Fin 26), pair i v = true → single i v = false →
      active (i.val + 1) v = false := by decide
  have hm (i : Fin 24) : ∃ k, marked C (active i.val) (active (i.val + 1)) k := by
    apply find_marked ao (before i) (deleted i) C.output
    · exact (correct _).mpr (hit_pair i)
    · exact Bool.eq_false_iff.mpr (fun h => no_single i ((correct _).mp h))
    · exact (correct _).mpr (hit_active i)
  choose f hf using hm
  have finj : Function.Injective f := by
    intro i j e
    rcases lt_trichotomy i j with lt | eq | gt
    · exact False.elim (marked_lt_impossible ao lt (hf i) (e ▸ hf j))
    · exact eq
    · exact False.elim (marked_lt_impossible ao gt (hf j) (e ▸ hf i))
  let A : Set (Fin C.gates.length) := {i | (C.gates.get i).op = GateOp.and}
  have disjoint (i : Fin 24) (a : A) : f i ≠ a.val := by
    intro e
    have hor := (hf i).1
    rw [e, gateAt_eq a.val.isLt] at hor
    have hand : (C.gates.get a.val).op = GateOp.and := a.property
    change (C.gates.get a.val).op = GateOp.or at hor
    rw [hand] at hor
    contradiction
  have bound := Fintype.card_le_of_injective (Sum.elim f (fun a : A => a.val)) (by
    intro u v huv
    cases u with
    | inl i =>
      cases v with
      | inl j => exact congrArg Sum.inl (finj huv)
      | inr b => exact False.elim (disjoint i b huv)
    | inr a =>
      cases v with
      | inl j => exact False.elim (disjoint j a huv.symm)
      | inr b => exact congrArg Sum.inr (Subtype.ext huv))
  change 24 + A.ncard ≤ C.gates.length
  simpa only [Fintype.card_sum, Fintype.card_fin, ← Set.ncard_eq_toFinset_card',
    ← Set.toFinset_card] using bound

end PEqualNP.Outside.L_meta_18107

theorem PEqualNP.Outside.L_meta_18107 : have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsAO2 (26 : ℕ) x2 →     (∀ x4 ∈ x2.gates, x4.inputs.Nodup) →       x2.size ≤ (64 : ℕ) →         have x6 : (Fin (26 : ℕ) → Bool) → ℕ → Bool := fun (x6 : Fin (26 : ℕ) → Bool) (x7 : ℕ) => (x2.wires (List.ofFn x6)).getD x7 Bool.false;         (∀ (x7 : Fin (26 : ℕ) → Bool), x6 x7 x2.output = Bool.true ↔ ∃ (x8 : Fin (13 : ℕ)) (x9 : Fin (13 : ℕ)), x1 x8 x9 ∧ x7 (Fin.castAdd (13 : ℕ) x8) = Bool.true ∧ x7 (Fin.natAdd (13 : ℕ) x9) = Bool.true) →           (∀ (x8 x9 : Fin (13 : ℕ)), x1 x8 x9 → ∃ x11 ⊆ Finset.range x2.size, (56 : ℕ) ≤ x11.card ∧ ∀ x12 ∈ x11, ∀ x14 < (26 : ℕ) + x12, ∃ (x16 : Fin (26 : ℕ) → Bool), x16 (Fin.castAdd (13 : ℕ) x8) = Bool.false ∧ x16 (Fin.natAdd (13 : ℕ) x9) = Bool.false ∧ x6 x16 x14 ≠ x6 x16 ((26 : ℕ) + x12)) →             (41 : ℕ) ≤ {x9 : Fin x2.gates.length | (x2.gates.get x9).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard →               have x10 : ℕ → Prop := fun (x10 : ℕ) => Relation.ReflTransGen (fun (x11 x12 : ℕ) => ∃ (x13 : ℕ) (x14 : ℕ) (x15 : PEqualNP.CircuitLowerBounds.Gate), x12 = (26 : ℕ) + x13 ∧ x2.gates[x13]? = Option.some x15 ∧ (x15.inputs = [x11, x14] ∨ x15.inputs = [x14, x11]) ∧ (x15.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ x6 (fun (x16 : Fin (26 : ℕ)) => Decidable.decide (↑x16 = x10)) x14 = Bool.true)) ((13 : ℕ) - x10) x2.output;               x10 (0 : ℕ) ∨ x10 (13 : ℕ) := by
  intro _ C ao _ size _ correct _ count
  have h := PEqualNP.Outside.L_meta_18107.count_or_and C ao correct
  omega
