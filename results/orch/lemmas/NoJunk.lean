import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583.NoJunk

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

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

def oh (N v : ℕ) : Fin N → Bool := fun z => decide (z.val = v)

def th (N u v : ℕ) : Fin N → Bool := fun z => decide (z.val = u ∨ z.val = v)

def S (C : Circuit) (N w : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun v => V C (oh N v) w = true)

def mn (C : Circuit) (N w : ℕ) : ℕ := if h : (S C N w).Nonempty then (S C N w).min' h else 0

def kap (C : Circuit) (N k : ℕ) : ℕ := max (mn C N (in0 C k)) (mn C N (in1 C k))

def adj (n : ℕ) (L : Fin n → Finset (Fin n)) (u v : ℕ) : Prop :=
  ∃ a b : Fin n, a ∈ L b ∧ ((u = a.val ∧ v = n + b.val) ∨ (u = n + b.val ∧ v = a.val))

def stp (C : Circuit) (N : ℕ) (W : Finset ℕ) (u v : ℕ) : Prop :=
  ∃ k < C.gates.length, u = N + k ∧ (gateAt C k).op = GateOp.or ∧ u ∉ W ∧ v ∈ (gateAt C k).inputs

def Rch (C : Circuit) (N : ℕ) (W : Finset ℕ) (v : ℕ) : Prop :=
  Relation.ReflTransGen (stp C N W) C.output v

open Classical in
noncomputable def Aset (C : Circuit) (N : ℕ) (W : Finset ℕ) : Finset ℕ :=
  (Finset.range C.gates.length).filter (fun k => (gateAt C k).op = GateOp.and ∧ Rch C N W (N + k))

open Classical in
noncomputable def Tset (C : Circuit) (N : ℕ) (W : Finset ℕ) : Finset ℕ :=
  (Finset.range C.gates.length).filter
    (fun k => (gateAt C k).op = GateOp.or ∧ N + k ∉ W ∧ Rch C N W (N + k))

open Classical in
noncomputable def Oset (C : Circuit) (N : ℕ) (W : Finset ℕ) : Finset ℕ :=
  (Finset.range C.gates.length).filter (fun k => N + k ∈ W)

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

lemma memS {C : Circuit} {N w v : ℕ} : v ∈ S C N w ↔ v < N ∧ V C (oh N v) w = true := by
  simp [S]

lemma S_or {N : ℕ} {C : Circuit} (hAO : PEqualNP.TopForm.IsAO2 N C) {k : ℕ}
    (hk : k < C.gates.length) (hop : (gateAt C k).op = GateOp.or) (v : ℕ) :
    v ∈ S C N (N + k) ↔ v ∈ S C N (in0 C k) ∨ v ∈ S C N (in1 C k) := by
  simp only [memS, V_or hAO hk hop, Bool.or_eq_true, and_or_left]

lemma mn_mem {C : Circuit} {N w : ℕ} (h : (S C N w).Nonempty) : mn C N w ∈ S C N w := by
  unfold mn; rw [dite_cond_eq_true (eq_true h)]; exact Finset.min'_mem _ _

lemma mn_le {C : Circuit} {N w v : ℕ} (h : v ∈ S C N w) : mn C N w ≤ v := by
  unfold mn; rw [dite_cond_eq_true (eq_true ⟨v, h⟩)]; exact Finset.min'_le _ _ h

def WH (C : Circuit) (N : ℕ) (W : Finset ℕ) : Prop :=
  ∀ w ∈ W, w < N ∨ ∃ k < C.gates.length, w = N + k ∧ (gateAt C k).op = GateOp.or ∧
    ∀ i ∈ (gateAt C k).inputs, i ∈ W

lemma S_input {C : Circuit} {N w : ℕ} (hw : w < N) (v : ℕ) : v ∈ S C N w ↔ v = w := by
  rw [memS, V_input C _ hw]
  simp [oh]
  omega

lemma disj {N : ℕ} {C : Circuit} {W : Finset ℕ} (hAO : PEqualNP.TopForm.IsAO2 N C)
    (hW : WH C N W) : ∀ w ∈ W, (∀ x : Fin N → Bool, V C x w = true ↔
      ∃ z : Fin N, z.val ∈ S C N w ∧ x z = true) ∧ (S C N w).Nonempty := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro hwW
  rcases hW w hwW with hw | ⟨k, hk, rfl, hop, hin⟩
  · refine ⟨fun x => ?_, ⟨w, (S_input hw w).2 rfl⟩⟩
    rw [V_input C x hw]
    constructor
    · intro h; exact ⟨⟨w, hw⟩, (S_input hw w).2 rfl, h⟩
    · rintro ⟨z, hz, hx⟩
      have := (S_input hw _).1 hz
      have e : z = ⟨w, hw⟩ := Fin.ext this
      rw [← e]; exact hx
  · obtain ⟨h2, ha, hb, _⟩ := gate_two hAO hk
    have haW : in0 C k ∈ W := hin _ (by rw [h2]; simp)
    have hbW : in1 C k ∈ W := hin _ (by rw [h2]; simp)
    obtain ⟨IA, NA⟩ := ih _ ha haW
    obtain ⟨IB, _⟩ := ih _ hb hbW
    refine ⟨fun x => ?_, ?_⟩
    · rw [V_or hAO hk hop, Bool.or_eq_true, IA, IB]
      constructor
      · rintro (⟨z, hz, hx⟩ | ⟨z, hz, hx⟩)
        · exact ⟨z, (S_or hAO hk hop _).2 (Or.inl hz), hx⟩
        · exact ⟨z, (S_or hAO hk hop _).2 (Or.inr hz), hx⟩
      · rintro ⟨z, hz, hx⟩
        rcases (S_or hAO hk hop _).1 hz with h | h
        · exact Or.inl ⟨z, h, hx⟩
        · exact Or.inr ⟨z, h, hx⟩
    · obtain ⟨v, hv⟩ := NA
      exact ⟨v, (S_or hAO hk hop _).2 (Or.inl hv)⟩

lemma kill {N : ℕ} {C : Circuit} {W : Finset ℕ} (hAO : PEqualNP.TopForm.IsAO2 N C)
    (hW : WH C N W) : ∀ w ∈ W, ∀ v ∈ S C N w, v ≠ mn C N w →
      ∃ g < C.gates.length, N + g ∈ W ∧ S C N (N + g) ⊆ S C N w ∧ kap C N g = v ∧
        v ≠ mn C N (N + g) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro hwW v hv hne
  rcases hW w hwW with hw | ⟨k, hk, rfl, hop, hin⟩
  · exfalso
    have h1 := (S_input hw _).1 hv
    have h2 := (S_input hw _).1 (mn_mem ⟨v, hv⟩)
    exact hne (h1.trans h2.symm)
  · obtain ⟨h2, ha, hb, _⟩ := gate_two hAO hk
    have haW : in0 C k ∈ W := hin _ (by rw [h2]; simp)
    have hbW : in1 C k ∈ W := hin _ (by rw [h2]; simp)
    have subA : S C N (in0 C k) ⊆ S C N (N + k) :=
      fun z hz => (S_or hAO hk hop _).2 (Or.inl hz)
    have subB : S C N (in1 C k) ⊆ S C N (N + k) :=
      fun z hz => (S_or hAO hk hop _).2 (Or.inr hz)
    by_cases c1 : v ∈ S C N (in0 C k) ∧ v ≠ mn C N (in0 C k)
    · obtain ⟨g, hg, hgW, hsub, hk2, hne2⟩ := ih _ ha haW v c1.1 c1.2
      exact ⟨g, hg, hgW, hsub.trans subA, hk2, hne2⟩
    by_cases c2 : v ∈ S C N (in1 C k) ∧ v ≠ mn C N (in1 C k)
    · obtain ⟨g, hg, hgW, hsub, hk2, hne2⟩ := ih _ hb hbW v c2.1 c2.2
      exact ⟨g, hg, hgW, hsub.trans subB, hk2, hne2⟩
    refine ⟨k, hk, hwW, subset_refl _, ?_, hne⟩
    have hm := mn_mem (C := C) (N := N) (w := N + k) ⟨v, hv⟩
    have hmw := mn_le (C := C) (N := N) (w := N + k) hv
    unfold kap
    rcases (S_or hAO hk hop _).1 hv with h | h
    · have e : v = mn C N (in0 C k) := by
        by_contra h'; exact c1 ⟨h, h'⟩
      have l1 := mn_le (subA (mn_mem ⟨v, h⟩))
      rcases (S_or hAO hk hop _).1 hm with h3 | h3
      · have := mn_le h3; omega
      · have := mn_le h3
        have := mn_le (subB (mn_mem ⟨_, h3⟩))
        omega
    · have e : v = mn C N (in1 C k) := by
        by_contra h'; exact c2 ⟨h, h'⟩
      have l1 := mn_le (subB (mn_mem ⟨v, h⟩))
      rcases (S_or hAO hk hop _).1 hm with h3 | h3
      · have := mn_le h3
        have := mn_le (subA (mn_mem ⟨_, h3⟩))
        omega
      · have := mn_le h3; omega

lemma rch_up {N : ℕ} {C : Circuit} {W : Finset ℕ} (hAO : PEqualNP.TopForm.IsAO2 N C)
    {v : ℕ} (hv : Rch C N W v) (x : Fin N → Bool) (h : V C x v = true) :
    V C x C.output = true := by
  induction hv with
  | refl => exact h
  | tail _ hst ih =>
    obtain ⟨k, hk, rfl, hop, _, hin⟩ := hst
    apply ih
    obtain ⟨h2, _, _, _⟩ := gate_two hAO hk
    rw [V_or hAO hk hop, Bool.or_eq_true]
    rw [h2] at hin
    simp at hin
    rcases hin with rfl | rfl
    · exact Or.inl h
    · exact Or.inr h

lemma nr {N : ℕ} {C : Circuit} {W : Finset ℕ} (hAO : PEqualNP.TopForm.IsAO2 N C)
    (hf0 : ∀ v, V C (oh N v) C.output = false) {u : ℕ} (hu : Rch C N W u) (v : ℕ)
    (h : V C (oh N v) u = true) : False := by
  have := rch_up hAO hu _ h
  rw [hf0 v] at this
  exact Bool.false_ne_true this

lemma rch_notW {N : ℕ} {C : Circuit} {W : Finset ℕ} (hAO : PEqualNP.TopForm.IsAO2 N C)
    (hW : WH C N W) (hf0 : ∀ v, V C (oh N v) C.output = false) {u : ℕ} (hu : Rch C N W u)
    (huW : u ∈ W) : False := by
  obtain ⟨v, hv⟩ := (disj hAO hW u huW).2
  exact nr hAO hf0 hu v (memS.1 hv).2

lemma rch_notIn {N : ℕ} {C : Circuit} {W : Finset ℕ} (hAO : PEqualNP.TopForm.IsAO2 N C)
    (hf0 : ∀ v, V C (oh N v) C.output = false) {u : ℕ} (hu : Rch C N W u) (hlt : u < N) :
    False := by
  apply nr hAO hf0 hu u
  rw [V_input C _ hlt]
  simp [oh]

lemma descend {N : ℕ} {C : Circuit} {W : Finset ℕ} (hAO : PEqualNP.TopForm.IsAO2 N C)
    (hW : WH C N W) (hf0 : ∀ v, V C (oh N v) C.output = false) (x : Fin N → Bool) :
    ∀ u, Rch C N W u → V C x u = true → ∃ k ∈ Aset C N W, V C x (N + k) = true := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
  intro hu hx
  have h1 : N ≤ u := by
    by_contra h; exact rch_notIn hAO hf0 hu (by omega)
  have h2 : u < N + C.gates.length := by
    by_contra h
    rw [V_ge C x (by omega)] at hx
    exact Bool.false_ne_true hx
  obtain ⟨k, rfl⟩ : ∃ k, u = N + k := ⟨u - N, by omega⟩
  have hk : k < C.gates.length := by omega
  obtain ⟨h2, ha, hb, hop⟩ := gate_two hAO hk
  rcases hop with hop | hop
  · refine ⟨k, ?_, hx⟩
    simp [Aset, hk, hop, hu]
  · have hnW : N + k ∉ W := fun h => rch_notW hAO hW hf0 hu h
    rw [V_or hAO hk hop, Bool.or_eq_true] at hx
    rcases hx with hx | hx
    · exact ih _ ha (Relation.ReflTransGen.tail hu ⟨k, hk, rfl, hop, hnW, by rw [h2]; simp⟩) hx
    · exact ih _ hb (Relation.ReflTransGen.tail hu ⟨k, hk, rfl, hop, hnW, by rw [h2]; simp⟩) hx

lemma card_AT {N : ℕ} {C : Circuit} {W : Finset ℕ} (hAO : PEqualNP.TopForm.IsAO2 N C) :
    (Aset C N W).card ≤ (Tset C N W).card + 1 := by
  classical
  have hdis : Disjoint (Aset C N W) (Tset C N W) := by
    rw [Finset.disjoint_left]
    intro k h1 h2
    simp only [Aset, Tset, Finset.mem_filter] at h1 h2
    rw [h1.2.1] at h2
    exact GateOp.noConfusion h2.2.1
  have hsub : Aset C N W ∪ Tset C N W ⊆ insert (C.output - N)
      ((Tset C N W ×ˢ Finset.range 2).image
        (fun p => (gateAt C p.1).inputs.getD p.2 0 - N)) := by
    intro k hk
    have hR : Rch C N W (N + k) := by
      rcases Finset.mem_union.1 hk with h | h
      · simp only [Aset, Finset.mem_filter] at h; exact h.2.2
      · simp only [Tset, Finset.mem_filter] at h; exact h.2.2.2
    rcases Relation.ReflTransGen.cases_tail hR with h | ⟨u, hu, k', hk', rfl, hop, hnW, hin⟩
    · rw [Finset.mem_insert]; left; omega
    · rw [Finset.mem_insert]; right
      rw [Finset.mem_image]
      have hT : k' ∈ Tset C N W := by
        simp only [Tset, Finset.mem_filter, Finset.mem_range]; exact ⟨hk', hop, hnW, hu⟩
      obtain ⟨h2, _, _, _⟩ := gate_two hAO hk'
      rw [h2] at hin
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
      rcases hin with e | e
      · refine ⟨(k', 0), by simp [hT], ?_⟩
        simp only [h2, List.getD_cons_zero]; omega
      · refine ⟨(k', 1), by simp [hT], ?_⟩
        simp only [h2, List.getD_cons_succ, List.getD_cons_zero]; omega
  have c1 := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis] at c1
  have c2 := Finset.card_insert_le (C.output - N) ((Tset C N W ×ˢ Finset.range 2).image
        (fun p => (gateAt C p.1).inputs.getD p.2 0 - N))
  have c3 := Finset.card_image_le (s := Tset C N W ×ˢ Finset.range 2)
    (f := fun p => (gateAt C p.1).inputs.getD p.2 0 - N)
  rw [Finset.card_product, Finset.card_range] at c3
  omega

lemma twoF {n : ℕ} {L : Fin n → Finset (Fin n)} (hI : ∀ b b', b ≠ b' → (L b ∩ L b').card ≤ 1)
    {a a' b b' : Fin n} (ha : a ≠ a') (hb : b ≠ b') (h1 : a ∈ L b) (h2 : a ∈ L b')
    (h3 : a' ∈ L b) (h4 : a' ∈ L b') : False := by
  classical
  have hs : ({a, a'} : Finset (Fin n)) ⊆ L b ∩ L b' := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> simp [*]
  have c := Finset.card_le_card hs
  rw [Finset.card_pair ha] at c
  have := hI b b' hb
  omega

def inc (n : ℕ) (L : Fin n → Finset (Fin n)) (p l : ℕ) : Prop :=
  ∃ a b : Fin n, a ∈ L b ∧ a.val = p ∧ b.val = l

lemma incF {n : ℕ} {L : Fin n → Finset (Fin n)} {p l : ℕ} (h : inc n L p l) (a b : Fin n)
    (ha : a.val = p) (hb : b.val = l) : a ∈ L b := by
  obtain ⟨a1, b1, m, e1, f1⟩ := h
  have x1 : a1 = a := Fin.ext (by omega)
  have x2 : b1 = b := Fin.ext (by omega)
  subst x1 x2
  exact m

lemma twoN {n : ℕ} {L : Fin n → Finset (Fin n)} (hI : ∀ b b', b ≠ b' → (L b ∩ L b').card ≤ 1)
    {p p' l l' : ℕ} (hp : p ≠ p') (hl : l ≠ l') (h1 : inc n L p l) (h2 : inc n L p l')
    (h3 : inc n L p' l) (h4 : inc n L p' l') : False := by
  obtain ⟨a1, b1, m1, e1, f1⟩ := h1
  obtain ⟨a3, b2, m4, e4, f4⟩ := h4
  refine twoF hI (a := a1) (a' := a3) (b := b1) (b' := b2) (by rintro rfl; omega)
    (by rintro rfl; omega) m1 (incF h2 _ _ e1 f4) (incF h3 _ _ e4 f1) m4

lemma adj_symm {n : ℕ} {L : Fin n → Finset (Fin n)} {u v : ℕ} (h : adj n L u v) :
    adj n L v u := by
  obtain ⟨a, b, m, h⟩ := h
  exact ⟨a, b, m, by omega⟩

lemma adj_ne {n : ℕ} {L : Fin n → Finset (Fin n)} {u v : ℕ} (h : adj n L u v) : u ≠ v := by
  obtain ⟨a, b, m, h⟩ := h
  have := a.isLt
  omega

lemma c4 {n : ℕ} {L : Fin n → Finset (Fin n)} (hI : ∀ b b', b ≠ b' → (L b ∩ L b').card ≤ 1)
    {u u' v v' : ℕ} (hu : u ≠ u') (hv : v ≠ v') (h1 : adj n L u v) (h2 : adj n L u v')
    (h3 : adj n L u' v) (h4 : adj n L u' v') : False := by
  obtain ⟨p1, l1, m1, d1⟩ := h1
  obtain ⟨p2, l2, m2, d2⟩ := h2
  obtain ⟨p3, l3, m3, d3⟩ := h3
  obtain ⟨p4, l4, m4, d4⟩ := h4
  have := p1.isLt; have := p2.isLt; have := p3.isLt; have := p4.isLt
  rcases d1 with ⟨e1, f1⟩ | ⟨e1, f1⟩ <;> rcases d2 with ⟨e2, f2⟩ | ⟨e2, f2⟩ <;>
    rcases d3 with ⟨e3, f3⟩ | ⟨e3, f3⟩ <;> rcases d4 with ⟨e4, f4⟩ | ⟨e4, f4⟩ <;>
    first
    | omega
    | exact twoN hI (p := u) (p' := u') (l := v - n) (l' := v' - n) hu (by omega)
        ⟨p1, l1, m1, by omega, by omega⟩ ⟨p2, l2, m2, by omega, by omega⟩
        ⟨p3, l3, m3, by omega, by omega⟩ ⟨p4, l4, m4, by omega, by omega⟩
    | exact twoN hI (p := v) (p' := v') (l := u - n) (l' := u' - n) hv (by omega)
        ⟨p1, l1, m1, by omega, by omega⟩ ⟨p3, l3, m3, by omega, by omega⟩
        ⟨p2, l2, m2, by omega, by omega⟩ ⟨p4, l4, m4, by omega, by omega⟩

def pr (n : ℕ) (e : Fin n × Fin n) (x y : ℕ) : Prop :=
  (x = e.1.val ∧ y = n + e.2.val) ∨ (x = n + e.2.val ∧ y = e.1.val)

lemma pr_inj {n : ℕ} {e e' : Fin n × Fin n} {x y : ℕ} (h : pr n e x y) (h' : pr n e' x y) :
    e = e' := by
  unfold pr at h h'
  have := e.1.isLt; have := e'.1.isLt
  ext <;> omega

lemma pr_swap {n : ℕ} {e : Fin n × Fin n} {x y : ℕ} (h : pr n e x y) : pr n e y x := by
  unfold pr at h ⊢; omega

lemma pr_adj {n : ℕ} {L : Fin n → Finset (Fin n)} {e : Fin n × Fin n} (he : e.1 ∈ L e.2)
    {x y : ℕ} (h : pr n e x y) : adj n L x y := ⟨e.1, e.2, he, h⟩

lemma hf0_of {n : ℕ} {L : Fin n → Finset (Fin n)} {C : Circuit}
    (hf : ∀ x : Fin (n + n) → Bool, circuitFun (n + n) C x = decide (∃ a b : Fin n, a ∈ L b ∧
      x (Fin.castAdd n a) = true ∧ x (Fin.natAdd n b) = true)) (v : ℕ) :
    V C (oh (n + n) v) C.output = false := by
  have e : V C (oh (n + n) v) C.output = circuitFun (n + n) C (oh (n + n) v) := rfl
  rw [e, hf, decide_eq_false_iff_not]
  rintro ⟨a, b, _, h1, h2⟩
  simp [oh] at h1 h2
  have := a.isLt
  omega

lemma and_adj {n : ℕ} {L : Fin n → Finset (Fin n)} {C : Circuit} {W : Finset ℕ}
    (hAO : PEqualNP.TopForm.IsAO2 (n + n) C) (hW : WH C (n + n) W)
    (hA : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ∀ i ∈ (gateAt C k).inputs, i ∈ W)
    (hf : ∀ x : Fin (n + n) → Bool, circuitFun (n + n) C x = decide (∃ a b : Fin n, a ∈ L b ∧
      x (Fin.castAdd n a) = true ∧ x (Fin.natAdd n b) = true))
    {k : ℕ} (hk : k ∈ Aset C (n + n) W) {u v : ℕ} (hu : u ∈ S C (n + n) (in0 C k))
    (hv : v ∈ S C (n + n) (in1 C k)) : adj n L u v := by
  simp only [Aset, Finset.mem_filter, Finset.mem_range] at hk
  obtain ⟨hk, hop, hR⟩ := hk
  obtain ⟨h2, _, _, _⟩ := gate_two hAO hk
  have haW : in0 C k ∈ W := hA k hk hop _ (by rw [h2]; simp)
  have hbW : in1 C k ∈ W := hA k hk hop _ (by rw [h2]; simp)
  have hu' := (memS.1 hu).1
  have hv' := (memS.1 hv).1
  have va : V C (th (n + n) u v) (in0 C k) = true :=
    ((disj hAO hW _ haW).1 _).2 ⟨⟨u, hu'⟩, hu, by simp [th]⟩
  have vb : V C (th (n + n) u v) (in1 C k) = true :=
    ((disj hAO hW _ hbW).1 _).2 ⟨⟨v, hv'⟩, hv, by simp [th]⟩
  have vk : V C (th (n + n) u v) (n + n + k) = true := by
    rw [V_and hAO hk hop, va, vb]; rfl
  have vo := rch_up hAO hR _ vk
  have e : V C (th (n + n) u v) C.output = circuitFun (n + n) C (th (n + n) u v) := rfl
  rw [e, hf, decide_eq_true_iff] at vo
  obtain ⟨a, b, m, h1, h2⟩ := vo
  simp [th] at h1 h2
  have := a.isLt
  exact ⟨a, b, m, by omega⟩

lemma pick {n : ℕ} {L : Fin n → Finset (Fin n)} {C : Circuit} {W : Finset ℕ}
    (hAO : PEqualNP.TopForm.IsAO2 (n + n) C) (hW : WH C (n + n) W)
    (hA : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ∀ i ∈ (gateAt C k).inputs, i ∈ W)
    (hf : ∀ x : Fin (n + n) → Bool, circuitFun (n + n) C x = decide (∃ a b : Fin n, a ∈ L b ∧
      x (Fin.castAdd n a) = true ∧ x (Fin.natAdd n b) = true))
    {e : Fin n × Fin n} (he : e.1 ∈ L e.2) :
    ∃ k ∈ Aset C (n + n) W, ∃ z1 ∈ S C (n + n) (in0 C k), ∃ z2 ∈ S C (n + n) (in1 C k),
      pr n e z1 z2 := by
  have hf0 := hf0_of hf
  set x := th (n + n) e.1.val (n + e.2.val) with hx
  have vo : V C x C.output = true := by
    have e0 : V C x C.output = circuitFun (n + n) C x := rfl
    rw [e0, hf, decide_eq_true_iff]
    exact ⟨e.1, e.2, he, by simp [hx, th], by simp [hx, th]; omega⟩
  obtain ⟨k, hkA, vk⟩ := descend hAO hW hf0 x _ Relation.ReflTransGen.refl vo
  have hkA' := hkA
  simp only [Aset, Finset.mem_filter, Finset.mem_range] at hkA'
  obtain ⟨hk, hop, _⟩ := hkA'
  obtain ⟨h2, _, _, _⟩ := gate_two hAO hk
  have haW : in0 C k ∈ W := hA k hk hop _ (by rw [h2]; simp)
  have hbW : in1 C k ∈ W := hA k hk hop _ (by rw [h2]; simp)
  rw [V_and hAO hk hop, Bool.and_eq_true] at vk
  obtain ⟨z1, hz1, x1⟩ := ((disj hAO hW _ haW).1 x).1 vk.1
  obtain ⟨z2, hz2, x2⟩ := ((disj hAO hW _ hbW).1 x).1 vk.2
  have hne := adj_ne (and_adj (L := L) hAO hW hA hf hkA hz1 hz2)
  simp [hx, th] at x1 x2
  refine ⟨k, hkA, z1, hz1, z2, hz2, ?_⟩
  unfold pr
  omega

lemma oset_or {N : ℕ} {C : Circuit} {W : Finset ℕ} (hW : WH C N W) {k : ℕ}
    (hk : k ∈ Oset C N W) : (gateAt C k).op = GateOp.or := by
  simp only [Oset, Finset.mem_filter, Finset.mem_range] at hk
  rcases hW _ hk.2 with h | ⟨k', _, e, hop, _⟩
  · omega
  · have : k' = k := by omega
    subst this; exact hop

def Good (n : ℕ) (L : Fin n → Finset (Fin n)) (C : Circuit) (W : Finset ℕ)
    (e : Fin n × Fin n) (k : ℕ) : Prop :=
  (k ∈ Aset C (n + n) W ∧ pr n e (mn C (n + n) (in0 C k)) (mn C (n + n) (in1 C k))) ∨
  (k ∈ Oset C (n + n) W ∧ ∃ c, pr n e (kap C (n + n) k) c ∧ adj n L c (mn C (n + n) (n + n + k)) ∧
    kap C (n + n) k ≠ mn C (n + n) (n + n + k))

lemma good_inj {n : ℕ} {L : Fin n → Finset (Fin n)} {C : Circuit} {W : Finset ℕ}
    (hI : ∀ b b', b ≠ b' → (L b ∩ L b').card ≤ 1) (hW : WH C (n + n) W)
    {e e' : Fin n × Fin n} (he : e.1 ∈ L e.2) (he' : e'.1 ∈ L e'.2) {k : ℕ}
    (g1 : Good n L C W e k) (g2 : Good n L C W e' k) : e = e' := by
  rcases g1 with ⟨hA1, p1⟩ | ⟨hO1, c, p1, a1, ne1⟩ <;>
    rcases g2 with ⟨hA2, p2⟩ | ⟨hO2, c', p2, a2, ne2⟩
  · exact pr_inj p1 p2
  · exfalso
    simp only [Aset, Finset.mem_filter] at hA1
    rw [oset_or hW hO2] at hA1
    exact GateOp.noConfusion hA1.2.1
  · exfalso
    simp only [Aset, Finset.mem_filter] at hA2
    rw [oset_or hW hO1] at hA2
    exact GateOp.noConfusion hA2.2.1
  · by_cases hc : c = c'
    · subst hc; exact pr_inj p1 p2
    · exact (c4 hI hc ne1 (adj_symm (pr_adj he p1)) a1 (adj_symm (pr_adj he' p2)) a2).elim

lemma good_ex {n : ℕ} {L : Fin n → Finset (Fin n)} {C : Circuit} {W : Finset ℕ}
    (hAO : PEqualNP.TopForm.IsAO2 (n + n) C) (hW : WH C (n + n) W)
    (hA : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ∀ i ∈ (gateAt C k).inputs, i ∈ W)
    (hf : ∀ x : Fin (n + n) → Bool, circuitFun (n + n) C x = decide (∃ a b : Fin n, a ∈ L b ∧
      x (Fin.castAdd n a) = true ∧ x (Fin.natAdd n b) = true))
    {e : Fin n × Fin n} (he : e.1 ∈ L e.2) : ∃ k, Good n L C W e k := by
  obtain ⟨k, hkA, z1, hz1, z2, hz2, hp⟩ := pick hAO hW hA hf he
  have hkA' := hkA
  simp only [Aset, Finset.mem_filter, Finset.mem_range] at hkA'
  obtain ⟨hk, hop, _⟩ := hkA'
  obtain ⟨h2, _, _, _⟩ := gate_two hAO hk
  have haW : in0 C k ∈ W := hA k hk hop _ (by rw [h2]; simp)
  have hbW : in1 C k ∈ W := hA k hk hop _ (by rw [h2]; simp)
  by_cases c1 : z1 = mn C (n + n) (in0 C k)
  · by_cases c2 : z2 = mn C (n + n) (in1 C k)
    · rw [c1, c2] at hp
      exact ⟨k, Or.inl ⟨hkA, hp⟩⟩
    · obtain ⟨g, hg, hgW, hsub, hkap, hne⟩ := kill hAO hW _ hbW z2 hz2 c2
      have hmem := hsub (mn_mem (disj hAO hW _ hgW).2)
      refine ⟨g, Or.inr ⟨?_, z1, ?_, and_adj hAO hW hA hf hkA hz1 hmem, ?_⟩⟩
      · simp only [Oset, Finset.mem_filter, Finset.mem_range]; exact ⟨hg, hgW⟩
      · rw [hkap]; exact pr_swap hp
      · rw [hkap]; exact hne
  · obtain ⟨g, hg, hgW, hsub, hkap, hne⟩ := kill hAO hW _ haW z1 hz1 c1
    have hmem := hsub (mn_mem (disj hAO hW _ hgW).2)
    refine ⟨g, Or.inr ⟨?_, z2, ?_, adj_symm (and_adj hAO hW hA hf hkA hmem hz2), ?_⟩⟩
    · simp only [Oset, Finset.mem_filter, Finset.mem_range]; exact ⟨hg, hgW⟩
    · rw [hkap]; exact hp
    · rw [hkap]; exact hne

lemma card_E {n : ℕ} {L : Fin n → Finset (Fin n)} {C : Circuit} {W : Finset ℕ}
    (hI : ∀ b b', b ≠ b' → (L b ∩ L b').card ≤ 1)
    (hAO : PEqualNP.TopForm.IsAO2 (n + n) C) (hW : WH C (n + n) W)
    (hA : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ∀ i ∈ (gateAt C k).inputs, i ∈ W)
    (hf : ∀ x : Fin (n + n) → Bool, circuitFun (n + n) C x = decide (∃ a b : Fin n, a ∈ L b ∧
      x (Fin.castAdd n a) = true ∧ x (Fin.natAdd n b) = true)) :
    (PEqualNP.HeptadCover.incidences L).card ≤ (Aset C (n + n) W ∪ Oset C (n + n) W).card := by
  classical
  have memI : ∀ e, e ∈ PEqualNP.HeptadCover.incidences L ↔ e.1 ∈ L e.2 := by
    intro e; simp [PEqualNP.HeptadCover.incidences]
  let f : Fin n × Fin n → ℕ := fun e => if h : ∃ k, Good n L C W e k then h.choose else 0
  have fg : ∀ e, e.1 ∈ L e.2 → Good n L C W e (f e) := by
    intro e he
    have h := good_ex hAO hW hA hf he
    simp only [f, dif_pos h]
    exact h.choose_spec
  apply Finset.card_le_card_of_injOn f
  · intro e he
    have g := fg e ((memI e).1 he)
    rw [Finset.mem_coe, Finset.mem_union]
    rcases g with ⟨h, _⟩ | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr h
  · intro e he e' he' hee
    have he1 := (memI e).1 he
    have he2 := (memI e').1 he'
    have g1 := fg e he1
    have g2 := fg e' he2
    rw [hee] at g1
    exact good_inj hI hW he1 he2 g1 g2

lemma card_n {n : ℕ} {L : Fin n → Finset (Fin n)} {C : Circuit} {W : Finset ℕ}
    (hL : ∀ a : Fin n, a ∈ L a) (hI : ∀ b b', b ≠ b' → (L b ∩ L b').card ≤ 1)
    (hAO : PEqualNP.TopForm.IsAO2 (n + n) C) (hW : WH C (n + n) W)
    (hA : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ∀ i ∈ (gateAt C k).inputs, i ∈ W)
    (hf : ∀ x : Fin (n + n) → Bool, circuitFun (n + n) C x = decide (∃ a b : Fin n, a ∈ L b ∧
      x (Fin.castAdd n a) = true ∧ x (Fin.natAdd n b) = true)) :
    n ≤ (Aset C (n + n) W).card := by
  classical
  let P : Fin n → ℕ → Prop := fun a k => k ∈ Aset C (n + n) W ∧
    ∃ z1 ∈ S C (n + n) (in0 C k), ∃ z2 ∈ S C (n + n) (in1 C k), pr n (a, a) z1 z2
  have ex : ∀ a, ∃ k, P a k := by
    intro a
    obtain ⟨k, hk, z1, h1, z2, h2, hp⟩ := pick hAO hW hA hf (e := (a, a)) (hL a)
    exact ⟨k, hk, z1, h1, z2, h2, hp⟩
  let f : Fin n → ℕ := fun a => (ex a).choose
  have fp : ∀ a, P a (f a) := fun a => (ex a).choose_spec
  have c := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin n)))
    (t := Aset C (n + n) W) f (fun a _ => (fp a).1) (by
      intro a _ a' _ haa
      by_contra hne
      obtain ⟨hk, z1, h1, z2, h2, hp⟩ := fp a
      obtain ⟨_, z1', h1', z2', h2', hp'⟩ := fp a'
      rw [← haa] at h1' h2'
      obtain ⟨p, l, m, d⟩ := and_adj hAO hW hA hf hk h1 h2'
      obtain ⟨p', l', m', d'⟩ := and_adj hAO hW hA hf hk h1' h2
      unfold pr at hp hp'
      simp only at hp hp'
      have := p.isLt; have := p'.isLt; have := a.isLt; have := a'.isLt
      have hne' : a ≠ a' := hne
      have hv : a.val ≠ a'.val := fun h => hne' (Fin.ext h)
      rcases d with ⟨e1, f1⟩ | ⟨e1, f1⟩ <;> rcases d' with ⟨e2, f2⟩ | ⟨e2, f2⟩ <;>
        first
        | omega
        | exact twoF hI hne' hne' (hL a) (incF ⟨p, l, m, rfl, rfl⟩ a a' (by omega) (by omega))
            (incF ⟨p', l', m', rfl, rfl⟩ a' a (by omega) (by omega)) (hL a')
        | exact twoF hI hne' hne' (hL a) (incF ⟨p', l', m', rfl, rfl⟩ a a' (by omega) (by omega))
            (incF ⟨p, l, m, rfl, rfl⟩ a' a (by omega) (by omega)) (hL a'))
  simpa using c

lemma card_all {N : ℕ} {C : Circuit} {W : Finset ℕ} (hW : WH C N W) :
    (Aset C N W).card + (Tset C N W).card + (Oset C N W).card ≤ C.gates.length := by
  classical
  have d1 : Disjoint (Aset C N W) (Tset C N W) := by
    rw [Finset.disjoint_left]
    intro k h1 h2
    simp only [Aset, Tset, Finset.mem_filter] at h1 h2
    rw [h1.2.1] at h2
    exact GateOp.noConfusion h2.2.1
  have d2 : Disjoint (Aset C N W ∪ Tset C N W) (Oset C N W) := by
    rw [Finset.disjoint_left]
    intro k h1 h2
    rcases Finset.mem_union.1 h1 with h | h
    · simp only [Aset, Finset.mem_filter] at h
      rw [oset_or hW h2] at h
      exact GateOp.noConfusion h.2.1
    · simp only [Tset, Finset.mem_filter] at h
      simp only [Oset, Finset.mem_filter] at h2
      exact h.2.2.1 h2.2
  have hs : Aset C N W ∪ Tset C N W ∪ Oset C N W ⊆ Finset.range C.gates.length := by
    intro k hk
    simp only [Finset.mem_union, Aset, Tset, Oset, Finset.mem_filter] at hk
    rcases hk with (h | h) | h <;> exact h.1
  have c := Finset.card_le_card hs
  rw [Finset.card_union_of_disjoint d2, Finset.card_union_of_disjoint d1,
    Finset.card_range] at c
  exact c


lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [PEqualNP.EdgeOwnership.coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (PEqualNP.EdgeOwnership.coneStep n (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []) g).getD k [] =
          (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []).getD k [] := by
      intro k hk
      simp only [PEqualNP.EdgeOwnership.coneStep, List.getD_eq_getElem?_getD]
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
      have e2 : (PEqualNP.EdgeOwnership.coneStep n (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []).getD (w - n) []) := by
        simp only [PEqualNP.EdgeOwnership.coneStep, List.getD_eq_getElem?_getD]
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
    · have e0 : (PEqualNP.EdgeOwnership.coneStep n (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []) g).getD j [] = [] := by
        simp only [PEqualNP.EdgeOwnership.coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    PEqualNP.EdgeOwnership.InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧
      n + k ∈ (gateAt C j).inputs ∧ (i = k ∨ PEqualNP.EdgeOwnership.InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold PEqualNP.EdgeOwnership.InCone PEqualNP.EdgeOwnership.cones gateAt
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

lemma inCone_lt (n : ℕ) (C : Circuit) (a : ℕ) : ∀ c,
    PEqualNP.EdgeOwnership.InCone n C a c → a < c ∧ c < C.gates.length := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro hac
    obtain ⟨hc, k, hk, _, h3⟩ := (inCone_iff n C a c).1 hac
    rcases h3 with h | h
    · exact ⟨by omega, hc⟩
    · have := ih k hk h
      exact ⟨by omega, hc⟩

lemma inCone_trans (n : ℕ) (C : Circuit) (a b : ℕ) : ∀ c,
    PEqualNP.EdgeOwnership.InCone n C a b → PEqualNP.EdgeOwnership.InCone n C b c →
      PEqualNP.EdgeOwnership.InCone n C a c := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro hab hbc
    obtain ⟨hc, k, hk, hw, h3⟩ := (inCone_iff n C b c).1 hbc
    refine (inCone_iff n C a c).2 ⟨hc, k, hk, hw, Or.inr ?_⟩
    rcases h3 with h | h
    · subst h; exact hab
    · exact ih k hk hab h

def Qg (N : ℕ) (C : Circuit) (g : ℕ) : Prop :=
  ∃ k, (gateAt C k).op = GateOp.and ∧ PEqualNP.EdgeOwnership.InCone N C g k

open Classical in
noncomputable def Wset (N : ℕ) (C : Circuit) : Finset ℕ :=
  (Finset.range (N + C.gates.length)).filter (fun w => w < N ∨ Qg N C (w - N))

lemma below_of_junk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hj : PEqualNP.TopForm.junk G C = ∅) (j : ℕ) (hjl : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) : PEqualNP.TopForm.BelowF G C j := by
  intro x hx
  by_contra hF
  have hmem : j ∈ PEqualNP.TopForm.junk G C := by
    unfold PEqualNP.TopForm.junk PEqualNP.TopForm.gatesWhere
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_range.mpr hjl, hop, hjl, x, hx, ?_⟩
    simpa using hF
  rw [hj] at hmem
  exact absurd hmem (Finset.notMem_empty j)

lemma W_props {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (C : Circuit)
    (hAO : PEqualNP.TopForm.IsAO2 N C) (htop : PEqualNP.TopForm.TopForm G C)
    (hj : PEqualNP.TopForm.junk G C = ∅) :
    WH C N (Wset N C) ∧
    (∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ∀ i ∈ (gateAt C k).inputs,
      i ∈ Wset N C) := by
  classical
  obtain ⟨hAOnly, hRB, _⟩ := hAO
  have inp : ∀ k < C.gates.length, ∀ i ∈ (gateAt C k).inputs, N ≤ i →
      PEqualNP.EdgeOwnership.InCone N C (i - N) k := by
    intro k hk i hi hNi
    have hlt := hRB k hk i hi
    refine (inCone_iff N C (i - N) k).2 ⟨hk, i - N, by omega, ?_, Or.inl rfl⟩
    have : N + (i - N) = i := by omega
    rw [this]; exact hi
  refine ⟨?_, ?_⟩
  · intro w hw
    simp only [Wset, Finset.mem_filter, Finset.mem_range] at hw
    obtain ⟨hwr, hw2⟩ := hw
    by_cases hNw : w < N
    · exact Or.inl hNw
    rcases hw2 with h | ⟨k, hk, hc⟩
    · exact Or.inl h
    right
    have hlt2 := inCone_lt N C (w - N) k hc
    have hgl : w - N < C.gates.length := by omega
    have hor : (gateAt C (w - N)).op = GateOp.and ∨ (gateAt C (w - N)).op = GateOp.or := by
      have hm : gateAt C (w - N) ∈ C.gates := by
        rw [gateAt_eq hgl]; exact List.getElem_mem hgl
      exact hAOnly _ hm
    have hop : (gateAt C (w - N)).op = GateOp.or := by
      rcases hor with ho | ho
      · exact absurd hc (htop (w - N) hgl k hlt2.2 ho (below_of_junk G C hj _ hgl ho) hk)
      · exact ho
    refine ⟨w - N, hgl, by omega, hop, ?_⟩
    intro i hi
    have hil := hRB (w - N) hgl i hi
    simp only [Wset, Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    by_cases hNi : i < N
    · exact Or.inl hNi
    · right
      exact ⟨k, hk, inCone_trans N C (i - N) (w - N) k (inp (w - N) hgl i hi (by omega)) hc⟩
  · intro k hk hop i hi
    have hil := hRB k hk i hi
    simp only [Wset, Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    by_cases hNi : i < N
    · exact Or.inl hNi
    · exact Or.inr ⟨k, hop, inp k hk i hi (by omega)⟩

lemma card_n2 {n : ℕ} {L : Fin n → Finset (Fin n)} {C : Circuit} {W : Finset ℕ}
    (σ : Equiv.Perm (Fin n))
    (hL : ∀ a : Fin n, a ∈ L (σ a)) (hI : ∀ b b', b ≠ b' → (L b ∩ L b').card ≤ 1)
    (hAO : PEqualNP.TopForm.IsAO2 (n + n) C) (hW : WH C (n + n) W)
    (hA : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ∀ i ∈ (gateAt C k).inputs, i ∈ W)
    (hf : ∀ x : Fin (n + n) → Bool, circuitFun (n + n) C x = decide (∃ a b : Fin n, a ∈ L b ∧
      x (Fin.castAdd n a) = true ∧ x (Fin.natAdd n b) = true)) :
    n ≤ (Aset C (n + n) W).card := by
  classical
  let P : Fin n → ℕ → Prop := fun a k => k ∈ Aset C (n + n) W ∧
    ∃ z1 ∈ S C (n + n) (in0 C k), ∃ z2 ∈ S C (n + n) (in1 C k), pr n (a, σ a) z1 z2
  have ex : ∀ a, ∃ k, P a k := by
    intro a
    obtain ⟨k, hk, z1, h1, z2, h2, hp⟩ := pick hAO hW hA hf (e := (a, σ a)) (hL a)
    exact ⟨k, hk, z1, h1, z2, h2, hp⟩
  let f : Fin n → ℕ := fun a => (ex a).choose
  have fp : ∀ a, P a (f a) := fun a => (ex a).choose_spec
  have c := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin n)))
    (t := Aset C (n + n) W) f (fun a _ => (fp a).1) (by
      intro a _ a2 _ haa
      by_contra hne
      obtain ⟨hk, z1, h1, z2, h2, hp⟩ := fp a
      obtain ⟨_, y1, g1, y2, g2, hq⟩ := fp a2
      rw [← haa] at g1 g2
      obtain ⟨p, l, m, d⟩ := and_adj hAO hW hA hf hk h1 g2
      obtain ⟨p2, l2, m2, d2⟩ := and_adj hAO hW hA hf hk g1 h2
      unfold pr at hp hq
      simp only at hp hq
      have := p.isLt; have := p2.isLt; have := a.isLt; have := a2.isLt
      have := (σ a).isLt; have := (σ a2).isLt
      have hne2 : a ≠ a2 := hne
      have hs : σ a ≠ σ a2 := fun h => hne2 (σ.injective h)
      rcases d with ⟨e1, f1⟩ | ⟨e1, f1⟩ <;> rcases d2 with ⟨e2, f2⟩ | ⟨e2, f2⟩ <;>
        first
        | omega
        | exact twoF hI hne2 hs (hL a) (incF ⟨p, l, m, rfl, rfl⟩ a (σ a2) (by omega) (by omega))
            (incF ⟨p2, l2, m2, rfl, rfl⟩ a2 (σ a) (by omega) (by omega)) (hL a2)
        | exact twoF hI hne2 hs (hL a) (incF ⟨p2, l2, m2, rfl, rfl⟩ a (σ a2) (by omega) (by omega))
            (incF ⟨p, l, m, rfl, rfl⟩ a2 (σ a) (by omega) (by omega)) (hL a2))
  simpa using c

lemma finish (n : ℕ) (E : Finset (Fin n × Fin n)) (σ : Equiv.Perm (Fin n))
    (G : SimpleGraph (Fin (n + n))) [DecidableRel G.Adj] (C : Circuit)
    (rect : ∀ (a b c d : Fin n), a ≠ b → c ≠ d →
      ¬((a, c) ∈ E ∧ (a, d) ∈ E ∧ (b, c) ∈ E ∧ (b, d) ∈ E))
    (perm : ∀ a : Fin n, (a, σ a) ∈ E)
    (hadj : ∀ (u v : Fin (n + n)), G.Adj u v ↔ ∃ (p : Fin n) (l : Fin n), (p, l) ∈ E ∧
      (u = Fin.castAdd n p ∧ v = Fin.natAdd n l ∨ v = Fin.castAdd n p ∧ u = Fin.natAdd n l))
    (hAO : PEqualNP.TopForm.IsAO2 (n + n) C)
    (hfun : circuitFun (n + n) C = graphFun G ∅)
    (htop : PEqualNP.TopForm.TopForm G C)
    (hjunk : PEqualNP.TopForm.junk G C = ∅) :
    E.card + n ≤ C.size + 1 := by
  classical
  let L : Fin n → Finset (Fin n) := fun l => Finset.univ.filter (fun p => (p, l) ∈ E)
  have memL : ∀ p l, p ∈ L l ↔ (p, l) ∈ E := by intro p l; simp [L]
  have hf : ∀ x : Fin (n + n) → Bool, circuitFun (n + n) C x = decide (∃ a b : Fin n, a ∈ L b ∧
      x (Fin.castAdd n a) = true ∧ x (Fin.natAdd n b) = true) := by
    intro x
    rw [hfun]
    unfold graphFun
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, decide_eq_true_eq, Finset.notMem_empty, false_and, exists_false,
      false_or]
    constructor
    · rintro ⟨u, v, huv, hu, hv⟩
      obtain ⟨p, l, hpl, h⟩ := (hadj u v).1 huv
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨p, l, (memL p l).2 hpl, hu, hv⟩
      · exact ⟨p, l, (memL p l).2 hpl, hv, hu⟩
    · rintro ⟨a, b, hab, ha, hb⟩
      exact ⟨Fin.castAdd n a, Fin.natAdd n b,
        (hadj _ _).2 ⟨a, b, (memL a b).1 hab, Or.inl ⟨rfl, rfl⟩⟩, ha, hb⟩
  have hI : ∀ b b', b ≠ b' → (L b ∩ L b').card ≤ 1 := by
    intro b b2 hbb
    rw [Finset.card_le_one]
    intro p hp q hq
    by_contra hpq
    rw [Finset.mem_inter, memL, memL] at hp hq
    exact rect p q b b2 hpq hbb ⟨hp.1, hp.2, hq.1, hq.2⟩
  have hL : ∀ a : Fin n, a ∈ L (σ a) := fun a => (memL a (σ a)).2 (perm a)
  obtain ⟨hW, hA⟩ := W_props G C hAO htop hjunk
  have hinc : PEqualNP.HeptadCover.incidences L = E := by
    ext ⟨p, l⟩
    simp [PEqualNP.HeptadCover.incidences, L]
  have e1 := card_E hI hAO hW hA hf
  have e2 := card_n2 σ hL hI hAO hW hA hf
  have e3 := card_AT (W := Wset (n + n) C) hAO
  have e4 := Finset.card_union_le (Aset C (n + n) (Wset (n + n) C))
    (Oset C (n + n) (Wset (n + n) C))
  have e5 := card_all hW
  rw [hinc] at e1
  show _ ≤ C.gates.length + 1
  omega

end PEqualNP.Outside.L_meta_2583.NoJunk


namespace PEqualNP.Outside.L_meta_2583.NoJunk

open PEqualNP.CircuitLowerBounds

def planeEdges {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] :
    Finset (Fin N × Fin N) := Finset.univ.filter fun e => I e.1 e.2

lemma planeEdges_card {N q : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hL : ∀ l, (Finset.univ.filter (fun p => I p l)).card = q + 1) :
    (planeEdges I).card = N * (q + 1) := by
  classical
  let F (l : Fin N) : Finset (Fin N × Fin N) :=
    (Finset.univ.filter (fun p => I p l)).map ⟨fun p => (p, l), fun _ _ h => congrArg Prod.fst h⟩
  have hF (l : Fin N) (e : Fin N × Fin N) : e ∈ F l ↔ I e.1 l ∧ e.2 = l := by
    constructor
    · intro he
      obtain ⟨p, hp, ht⟩ := Finset.mem_map.mp he
      change (p, l) = e at ht
      rw [← ht]
      exact ⟨(Finset.mem_filter.mp hp).2, rfl⟩
    · rintro ⟨hi, hh⟩
      refine Finset.mem_map.mpr ⟨e.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, ?_⟩
      exact Prod.ext rfl hh.symm
  have heq : planeEdges I = Finset.univ.biUnion F := by
    ext e
    simp only [planeEdges, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_biUnion, hF]
    exact ⟨fun h => ⟨e.2, h, rfl⟩, fun ⟨l, hi, he⟩ => he ▸ hi⟩
  rw [heq, Finset.card_biUnion]
  · simp [F, hL]
  · intro l _ l' _ hne
    refine Finset.disjoint_left.mpr ?_
    intro e he he'
    exact hne (((hF l e).mp he).2.symm.trans ((hF l' e).mp he').2)

lemma plane_noJunk_lower {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (σ : Equiv.Perm (Fin N)) (G : SimpleGraph (Fin (N + N))) [DecidableRel G.Adj]
    (C : Circuit)
    (hL : ∀ l, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hU : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (hMatch : ∀ p, I p (σ p))
    (hAdj : ∀ u v, G.Adj u v ↔ ∃ p l : Fin N, I p l ∧
      (u = Fin.castAdd N p ∧ v = Fin.natAdd N l ∨
       v = Fin.castAdd N p ∧ u = Fin.natAdd N l))
    (hAO : PEqualNP.TopForm.IsAO2 (N + N) C)
    (hfun : PEqualNP.MetaComplexity.circuitFun (N + N) C =
      PEqualNP.MetaComplexity.NestedCover.graphFun G ∅)
    (hTop : PEqualNP.TopForm.TopForm G C)
    (hJunk : PEqualNP.TopForm.junk G C = ∅) :
    N * (q + 2) - 1 ≤ C.size := by
  let E := planeEdges I
  have hmem (p l : Fin N) : (p,l) ∈ E ↔ I p l := by simp [E, planeEdges]
  have hRect : ∀ (p p' l l' : Fin N), p ≠ p' → l ≠ l' →
      ¬((p,l) ∈ E ∧ (p,l') ∈ E ∧ (p',l) ∈ E ∧ (p',l') ∈ E) := by
    intro p p' l l' hp hl ⟨hpl,hpl',hp'l,hp'l'⟩
    obtain ⟨w,_,hu⟩ := hU p p' hp
    exact hl ((hu l ⟨(hmem _ _).mp hpl,(hmem _ _).mp hp'l⟩).trans
      (hu l' ⟨(hmem _ _).mp hpl',(hmem _ _).mp hp'l'⟩).symm)
  have hCard : E.card = N * (q + 1) := planeEdges_card I hL
  have hBound := finish N E σ G C hRect (by simpa only [hmem] using hMatch)
    (by simpa only [hmem] using hAdj) hAO hfun hTop hJunk
  have hEq : N * (q + 2) = N * (q + 1) + N := by
    simp [Nat.mul_add, Nat.mul_two, Nat.add_assoc]
  rw [hCard] at hBound
  omega

end PEqualNP.Outside.L_meta_2583.NoJunk
