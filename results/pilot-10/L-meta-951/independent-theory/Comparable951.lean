import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_951

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

lemma wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

lemma getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

lemma on1_wires_output (gs : List Gate) (o o' : ℕ) (x : List Bool) :
    Circuit.wires ⟨gs, o⟩ x = Circuit.wires ⟨gs, o'⟩ x := rfl

/-- `Circuit.wires` is the fold `wiresFrom`. -/
lemma on1_wires_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.wires ⟨gs, o⟩ x = wiresFrom gs x := rfl

/-- The wire list has one wire per input bit and one per gate. -/
lemma on1_length_wires (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length :=
  length_wiresFrom C.gates x

/-- Reading at or beyond the length gives `false`. -/
lemma on1_getD_wires_of_ge (C : Circuit) (x : List Bool) (i : ℕ)
    (h : x.length + C.gates.length ≤ i) : (C.wires x).getD i false = false := by
  rw [List.getD_eq_default]; rw [on1_length_wires]; exact h

/-- The same for `wiresFrom`. -/
lemma on1_getD_wiresFrom_of_ge (gs : List Gate) (w : List Bool) (i : ℕ)
    (h : w.length + gs.length ≤ i) : (wiresFrom gs w).getD i false = false := by
  rw [List.getD_eq_default]; rw [length_wiresFrom]; exact h

/-- The wires of `l1 ++ l2`: run `l2` on the wires of `l1`. -/
lemma on1_wires_append (l1 l2 : List Gate) (o o' : ℕ) (x : List Bool) :
    Circuit.wires ⟨l1 ++ l2, o⟩ x = wiresFrom l2 (Circuit.wires ⟨l1, o'⟩ x) :=
  wiresFrom_append l1 l2 x

/-- One gate on a wire list: the old wires, then the gate's value. -/
lemma on1_wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w
      = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

lemma on1_wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

/-- Input wire `i < n` of `List.ofFn x` reads `x i`, whatever the gates. -/
lemma on1_getD_wires_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (C.wires (List.ofFn x)).getD i false = x ⟨i, hi⟩ := by
  show (wiresFrom C.gates (List.ofFn x)).getD i false = x ⟨i, hi⟩
  rw [getD_wiresFrom _ _ _ (by simpa using hi)]
  simp [List.getD_eq_getElem?_getD, hi]

/-- The wire a gate reads in a list `w`, read through a list that extends `w`. -/
lemma on1_getD_append_left (w t : List Bool) (i : ℕ) (h : i < w.length) :
    (w ++ t).getD i false = w.getD i false := List.getD_append _ _ _ _ h

lemma on1_getD_ofFn {n : ℕ} (x : Fin n → Bool) (i : ℕ) (h : i < n) :
    (List.ofFn x).getD i false = x ⟨i, h⟩ := by
  simp [List.getD_eq_getElem?_getD, h]

def on1_Above (v v' : List Bool) : Prop :=
  v.length = v'.length ∧ ∀ i, v.getD i false = true → v'.getD i false = true

lemma on1_above_snoc {v v' : List Bool} {a a' : Bool} (h : on1_Above v v')
    (ha : a = true → a' = true) : on1_Above (v ++ [a]) (v' ++ [a']) := by
  refine ⟨by simp [h.1], ?_⟩
  intro i hi
  by_cases hiv : i = v.length
  · subst hiv
    rw [getD_snoc_eq] at hi
    rw [h.1, getD_snoc_eq]; exact ha hi
  · rw [getD_snoc_ne _ _ _ _ hiv] at hi
    rw [getD_snoc_ne _ _ _ _ (by rw [← h.1]; exact hiv)]
    exact h.2 i hi

lemma on1_above_wiresFrom (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ v v' : List Bool, on1_Above v v' → on1_Above (wiresFrom gs v) (wiresFrom gs v') := by
  induction gs with
  | nil => intro v v' h; exact h
  | cons g gs ih =>
    intro v v' h
    rw [on1_wiresFrom_cons, on1_wiresFrom_cons]
    apply ih (fun g' hg' => hgs g' (by simp [hg']))
    apply on1_above_snoc h
    rcases hgs g (by simp) with hop | hop
    · rw [hop]
      simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
      intro hall b hb
      obtain ⟨j, hj, rfl⟩ := hb
      exact h.2 j (hall _ ⟨j, hj, rfl⟩)
    · rw [hop]
      simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
      rintro ⟨b, ⟨j, hj, rfl⟩, hb⟩
      exact ⟨_, ⟨j, hj, rfl⟩, h.2 j hb⟩

/-- S-PIECE-H: the value the NOT gate reads is monotone in the input. -/
lemma on1_piece_h : ∀ (n : ℕ) (pre : List PEqualNP.CircuitLowerBounds.Gate) (ins : List ℕ),
    (∀ g ∈ pre, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    ∀ x y : Fin n → Bool, (∀ i, x i = true → y i = true) →
      ((ins.map fun i => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨pre, 0⟩
          (List.ofFn x)).getD i false).headD false) = true →
      ((ins.map fun i => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨pre, 0⟩
          (List.ofFn y)).getD i false).headD false) = true := by
  intro n pre ins hpre x y hxy
  have hab : on1_Above (wiresFrom pre (List.ofFn x)) (wiresFrom pre (List.ofFn y)) := by
    apply on1_above_wiresFrom pre (fun g hg => (hpre g hg).1)
    refine ⟨by simp, ?_⟩
    intro i hi
    by_cases hin : i < n
    · rw [on1_getD_ofFn _ _ hin] at hi ⊢; exact hxy _ hi
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hi; exact absurd hi (by simp)
  cases ins with
  | nil => simp
  | cons j _ =>
    simp only [List.map_cons, List.headD_cons]
    exact hab.2 j

/-! ## Changing one slot -/

/-- Two gate lists that differ only at one slot have equal wires once the two slot gates give
the same value on the wires before the slot. -/
lemma on1_wires_slot (pre post : List Gate) (g g' : Gate) (o o' : ℕ) (x : List Bool)
    (h : g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨pre, 0⟩ x).getD i false)
      = g'.op.eval (g'.inputs.map fun i => (Circuit.wires ⟨pre, 0⟩ x).getD i false)) :
    Circuit.wires ⟨pre ++ g :: post, o⟩ x = Circuit.wires ⟨pre ++ g' :: post, o'⟩ x := by
  rw [on1_wires_append _ _ o 0, on1_wires_append _ _ o' 0, on1_wiresFrom_cons,
    on1_wiresFrom_cons, h]

/-- S-PIECE-D: where the NOT gate reads false, it can be replaced in place by AND of nothing. -/
lemma on1_piece_d : ∀ (n : ℕ) (pre post : List PEqualNP.CircuitLowerBounds.Gate)
    (ins : List ℕ) (o : ℕ) (x : Fin n → Bool),
    ((ins.map fun i => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨pre, 0⟩
        (List.ofFn x)).getD i false).headD false) = false →
    PEqualNP.CircuitLowerBounds.Circuit.eval
        ⟨pre ++ ({ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] } :
          PEqualNP.CircuitLowerBounds.Gate) :: post, o⟩ (List.ofFn x)
      = PEqualNP.CircuitLowerBounds.Circuit.eval
        ⟨pre ++ ({ op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := ins } :
          PEqualNP.CircuitLowerBounds.Gate) :: post, o⟩ (List.ofFn x) := by
  intro n pre post ins o x h
  unfold Circuit.eval
  rw [on1_wires_slot pre post _ _ o o (List.ofFn x)]
  simp only [GateOp.eval, List.map_nil, List.all_nil]
  rw [h]; rfl

/-- The cheap U piece: where the NOT gate reads true, it can be replaced in place by OR of
nothing (same length; no renumbering). -/
lemma on1_piece_u_cheap : ∀ (n : ℕ) (pre post : List PEqualNP.CircuitLowerBounds.Gate)
    (ins : List ℕ) (o : ℕ) (x : Fin n → Bool),
    ((ins.map fun i => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨pre, 0⟩
        (List.ofFn x)).getD i false).headD false) = true →
    PEqualNP.CircuitLowerBounds.Circuit.eval
        ⟨pre ++ ({ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] } :
          PEqualNP.CircuitLowerBounds.Gate) :: post, o⟩ (List.ofFn x)
      = PEqualNP.CircuitLowerBounds.Circuit.eval
        ⟨pre ++ ({ op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := ins } :
          PEqualNP.CircuitLowerBounds.Gate) :: post, o⟩ (List.ofFn x) := by
  intro n pre post ins o x h
  unfold Circuit.eval
  rw [on1_wires_slot pre post _ _ o o (List.ofFn x)]
  simp only [GateOp.eval, List.map_nil, List.any_nil]
  rw [h]; rfl

lemma on1_split : ∀ gates : List PEqualNP.CircuitLowerBounds.Gate,
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) →
    (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not →
        (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∨
    ∃ (pre post : List PEqualNP.CircuitLowerBounds.Gate) (ins : List ℕ),
      gates = pre ++ ({ op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := ins } :
        PEqualNP.CircuitLowerBounds.Gate) :: post ∧
      (∀ g ∈ pre, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      (∀ g ∈ post, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) := by
  intro gates hops huniq
  by_cases hex : ∃ g ∈ gates, g.op = GateOp.not
  · right
    obtain ⟨g, hg, hop⟩ := hex
    obtain ⟨s, t, rfl⟩ := List.append_of_mem hg
    -- the NOT gate sits at index `s.length`
    have hslot : ((s ++ g :: t).get ⟨s.length, by simp⟩).op = GateOp.not := by
      simp [hop]
    have nf : ∀ g' ∈ s ++ g :: t, g'.op ≠ GateOp.not → (g'.op = GateOp.and ∨
        g'.op = GateOp.or) ∧ g'.inputs.length ≤ 2 := by
      intro g' hg' hne
      obtain ⟨h1 | h1 | h1, h2⟩ := hops g' hg'
      · exact ⟨Or.inl h1, h2⟩
      · exact ⟨Or.inr h1, h2⟩
      · exact absurd h1 hne
    refine ⟨s, t, g.inputs, ?_, ?_, ?_⟩
    · cases g with
      | mk op ins => simp only at hop; subst hop; rfl
    · intro g' hg'
      apply nf g' (by simp [hg'])
      intro hn
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg'
      have := huniq ⟨i, by simp; omega⟩ ⟨s.length, by simp⟩
        (by simp [List.getElem_append_left hi, hn]) hslot
      simp only [Fin.mk.injEq] at this; omega
    · intro g' hg'
      apply nf g' (by simp [hg'])
      intro hn
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg'
      have := huniq ⟨s.length + 1 + i, by simp; omega⟩ ⟨s.length, by simp⟩
        (by
          simp only [List.get_eq_getElem]
          rw [List.getElem_append_right (by omega)]
          simp only [show s.length + 1 + i - s.length = i + 1 by omega,
            List.getElem_cons_succ]
          exact hn) hslot
      simp only [Fin.mk.injEq] at this; omega
  · left
    intro g hg
    obtain ⟨h1 | h1 | h1, h2⟩ := hops g hg
    · exact ⟨Or.inl h1, h2⟩
    · exact ⟨Or.inr h1, h2⟩
    · exact absurd ⟨g, hg, h1⟩ hex

lemma on1_unique_of_cover (gates : List Gate)
    (hcover : ∃ ι : Fin 1 → Fin gates.length, ∀ i : Fin gates.length,
      (gates.get i).op = GateOp.not → ∃ j : Fin 1, ι j = i) :
    ∀ i j : Fin gates.length, (gates.get i).op = GateOp.not →
      (gates.get j).op = GateOp.not → i = j := by
  obtain ⟨ι, hι⟩ := hcover
  intro i j hi hj
  obtain ⟨a, rfl⟩ := hι i hi
  obtain ⟨b, rfl⟩ := hι j hj
  exact congrArg ι (Subsingleton.elim a b)

lemma on1_split_of_cover (gates : List Gate)
    (hops : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨
      g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hcover : ∃ ι : Fin 1 → Fin gates.length, ∀ i : Fin gates.length,
      (gates.get i).op = GateOp.not → ∃ j : Fin 1, ι j = i) :
    (∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∨
    ∃ (pre post : List Gate) (ins : List ℕ),
      gates = pre ++ ({ op := GateOp.not, inputs := ins } : Gate) :: post ∧
      (∀ g ∈ pre, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      (∀ g ∈ post, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) := by
  exact on1_split gates hops (on1_unique_of_cover gates hcover)

lemma on1_eval_slot_mono (pre post : List Gate)
    (hpost : ∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or)
    (g g' : Gate) (o : ℕ) (x : List Bool)
    (h : g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨pre, 0⟩ x).getD i false) = true →
      g'.op.eval (g'.inputs.map fun i => (Circuit.wires ⟨pre, 0⟩ x).getD i false) = true) :
    Circuit.eval ⟨pre ++ g :: post, o⟩ x = true →
      Circuit.eval ⟨pre ++ g' :: post, o⟩ x = true := by
  unfold Circuit.eval
  rw [on1_wires_append _ _ o 0, on1_wires_append _ _ o 0,
    on1_wiresFrom_cons, on1_wiresFrom_cons]
  apply (on1_above_wiresFrom post hpost _ _
    (on1_above_snoc ⟨rfl, fun _ hi => hi⟩ h)).2 o

lemma on1_lower_true (pre post : List Gate)
    (hpost : ∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or)
    (ins : List ℕ) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨pre ++ ({ op := GateOp.or, inputs := [] } : Gate) :: post, o⟩ x = true →
      Circuit.eval ⟨pre ++ ({ op := GateOp.not, inputs := ins } : Gate) :: post, o⟩ x = true := by
  apply on1_eval_slot_mono pre post hpost
  simp [GateOp.eval]

lemma on1_upper_true (pre post : List Gate)
    (hpost : ∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or)
    (ins : List ℕ) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨pre ++ ({ op := GateOp.not, inputs := ins } : Gate) :: post, o⟩ x = true →
      Circuit.eval ⟨pre ++ ({ op := GateOp.and, inputs := [] } : Gate) :: post, o⟩ x = true := by
  apply on1_eval_slot_mono pre post hpost
  simp [GateOp.eval]

lemma on1_eval_monotone {n : ℕ} (gates : List Gate)
    (hops : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (o : ℕ) (x y : Fin n → Bool)
    (hxy : ∀ i, x i = true → y i = true) :
    Circuit.eval ⟨gates, o⟩ (List.ofFn x) = true →
      Circuit.eval ⟨gates, o⟩ (List.ofFn y) = true := by
  apply (on1_above_wiresFrom gates hops _ _ ?_).2 o
  refine ⟨by simp, ?_⟩
  intro i hi
  by_cases hin : i < n
  · rw [on1_getD_ofFn _ _ hin] at hi ⊢
    exact hxy _ hi
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
    exact absurd hi (by simp)

lemma on1_constants_mono (pre post : List Gate)
    (hpre : ∀ g ∈ pre, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hpost : ∀ g ∈ post, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) :
    ∀ g ∈ pre ++ ({ op := op, inputs := [] } : Gate) :: post,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [List.mem_append, List.mem_cons] at hg
  rcases hg with hg | rfl | hg
  · exact hpre g hg
  · exact ⟨hop, by simp⟩
  · exact hpost g hg

lemma on1_exact_sums_bracket {n m : ℕ} (S : Fin m → Finset (Fin n))
    (pre post : List Gate)
    (hpost : ∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or)
    (ins : List ℕ) (out : Fin m → ℕ)
    (hexact : ∀ (w : Fin m) (x : Fin n → Bool),
      Circuit.eval ⟨pre ++ ({ op := GateOp.not, inputs := ins } : Gate) :: post, out w⟩
        (List.ofFn x) = decide (∃ v ∈ S w, x v = true)) :
    ∀ (w : Fin m) (x : Fin n → Bool),
      (Circuit.eval ⟨pre ++ ({ op := GateOp.or, inputs := [] } : Gate) :: post, out w⟩
        (List.ofFn x) = true → ∃ v ∈ S w, x v = true) ∧
      ((∃ v ∈ S w, x v = true) →
        Circuit.eval ⟨pre ++ ({ op := GateOp.and, inputs := [] } : Gate) :: post, out w⟩
          (List.ofFn x) = true) := by
  intro w x
  constructor
  · intro hx
    have ht := on1_lower_true pre post hpost ins (out w) (List.ofFn x) hx
    rw [hexact] at ht
    exact of_decide_eq_true ht
  · intro hx
    apply on1_upper_true pre post hpost ins (out w) (List.ofFn x)
    rw [hexact]
    exact decide_eq_true hx

lemma on1_replacements_monotone {n : ℕ} (pre post : List Gate)
    (hpre : ∀ g ∈ pre, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hpost : ∀ g ∈ post, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (o : ℕ) (x y : Fin n → Bool)
    (hxy : ∀ i, x i = true → y i = true) :
    (Circuit.eval ⟨pre ++ ({ op := GateOp.or, inputs := [] } : Gate) :: post, o⟩
      (List.ofFn x) = true →
      Circuit.eval ⟨pre ++ ({ op := GateOp.or, inputs := [] } : Gate) :: post, o⟩
        (List.ofFn y) = true) ∧
    (Circuit.eval ⟨pre ++ ({ op := GateOp.and, inputs := [] } : Gate) :: post, o⟩
      (List.ofFn x) = true →
      Circuit.eval ⟨pre ++ ({ op := GateOp.and, inputs := [] } : Gate) :: post, o⟩
        (List.ofFn y) = true) := by
  constructor
  · apply on1_eval_monotone _ _ _ _ _ hxy
    intro g hg
    exact (on1_constants_mono pre post hpre hpost GateOp.or (Or.inr rfl) g hg).1
  · apply on1_eval_monotone _ _ _ _ _ hxy
    intro g hg
    exact (on1_constants_mono pre post hpre hpost GateOp.and (Or.inl rfl) g hg).1

end PEqualNP.Outside.L_meta_951


namespace PEqualNP.Outside.L_meta_951_mono

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl step (List.ofFn x)).getD i false

theorem fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_cons]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

theorem val_nil {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    val [] x i = if h : i < n then x ⟨i, h⟩ else false := by
  unfold val
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

theorem val_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (i : ℕ) :
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

theorem gate_cases {X : Type} (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : g.inputs.length ≤ 2) (f : X → ℕ → Bool) (z : X) :
    (∀ y, g.op.eval (g.inputs.map (f y)) = false) ∨
    ∃ a b, g.op.eval (g.inputs.map (f z)) = false →
      (f z a = false ∧ f z b = false ∧
        ∀ y, g.op.eval (g.inputs.map (f y)) = true → f y a = true ∨ f y b = true) := by
  obtain ⟨op, ins⟩ := g
  simp only at hop hlen ⊢
  match ins, hlen with
  | [], _ =>
    rcases hop with rfl | rfl
    · right
      exact ⟨0, 0, by simp [GateOp.eval]⟩
    · left
      simp [GateOp.eval]
  | [a], _ =>
    right
    refine ⟨a, a, ?_⟩
    rcases hop with rfl | rfl <;> simp [GateOp.eval]
  | [a, b], _ =>
    rcases hop with rfl | rfl
    · right
      by_cases h : f z a = false
      · refine ⟨a, a, ?_⟩
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          Bool.and_true, id_eq, Bool.and_eq_true]
        intro _
        exact ⟨h, h, fun y hy => Or.inl hy.1⟩
      · refine ⟨b, b, ?_⟩
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          Bool.and_true, id_eq, Bool.and_eq_true]
        intro hz
        have hb : f z b = false := by
          cases ha : f z a <;> cases hb : f z b <;> simp_all
        exact ⟨hb, hb, fun y hy => Or.inl hy.2⟩
    · right
      refine ⟨a, b, ?_⟩
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        Bool.or_false, id_eq, Bool.or_eq_true, Bool.or_eq_false_iff]
      intro hz
      exact ⟨hz.1, hz.2, fun y hy => hy⟩
  | _ :: _ :: _ :: _, h => simp at h

def Zof {n : ℕ} (S : Finset (Fin n)) : Fin n → Bool := fun c => decide (c ∉ S)

def eof {n : ℕ} (u : Fin n) : Fin n → Bool := fun c => decide (c = u)

def Inv {n : ℕ} (S : Finset (Fin n)) (gs : List Gate) (l : Fin n → Fin n) : Prop :=
  ∀ i u v, val gs (Zof S) i = false → val gs (eof u) i = true → val gs (eof v) i = true →
    u ∈ S ∧ l u = l v

def Cnt {n : ℕ} (S : Finset (Fin n)) (gs : List Gate) (i : ℕ) : Prop :=
  val gs (Zof S) i = false ∧
    ∃ u v : Fin n, u ≠ v ∧ val gs (eof u) i = true ∧ val gs (eof v) i = true

open Classical in
noncomputable def D {n : ℕ} (S : Finset (Fin n)) (gs : List Gate) : Finset ℕ :=
  (Finset.Ico n (n + gs.length)).filter fun i => Cnt S gs i

theorem D_mono {n : ℕ} (S : Finset (Fin n)) (gs : List Gate) (g : Gate) :
    D S gs ⊆ D S (gs ++ [g]) := by
  classical
  intro i hi
  simp only [D, Finset.mem_filter, Finset.mem_Ico, List.length_append, List.length_cons,
    List.length_nil] at hi ⊢
  refine ⟨⟨hi.1.1, by omega⟩, ?_⟩
  have hne : i ≠ n + gs.length := by omega
  obtain ⟨hz, u, v, huv, hu, hv⟩ := hi.2
  refine ⟨?_, u, v, huv, ?_, ?_⟩
  · rw [val_snoc, if_neg hne]; exact hz
  · rw [val_snoc, if_neg hne]; exact hu
  · rw [val_snoc, if_neg hne]; exact hv

theorem main_inv {n : ℕ} (S : Finset (Fin n)) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∃ l : Fin n → Fin n, Inv S gs l ∧ S.card ≤ (S.image l).card + (D S gs).card := by
  classical
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨id, ?_, by simp⟩
    intro i u v hz hu hv
    rw [val_nil] at hz hu hv
    by_cases h : i < n
    · simp only [h, dite_true, Zof, eof, decide_eq_false_iff_not, not_not,
        decide_eq_true_eq] at hz hu hv
      subst hu
      subst hv
      exact ⟨hz, rfl⟩
    · simp [h] at hu
  | append_singleton gs g ih =>
    obtain ⟨l, hinv, hcard⟩ := ih (fun g' hg' => hg g' (by simp [hg']))
    obtain ⟨hop, hlen⟩ := hg g (by simp)
    set N := n + gs.length with hN
    set P : (Fin n → Bool) → Bool := fun x => g.op.eval (g.inputs.map fun j => val gs x j)
      with hP
    have hnew : ∀ x : Fin n → Bool, val (gs ++ [g]) x N = P x := by
      intro x
      rw [val_snoc, if_pos hN]
    have hold : ∀ (x : Fin n → Bool) (i : ℕ), i ≠ N → val (gs ++ [g]) x i = val gs x i := by
      intro x i hi
      rw [val_snoc, if_neg hi]
    -- facts about the new wire from the old invariant
    have key : P (Zof S) = false → ∀ u, P (eof u) = true →
        u ∈ S ∧ ∃ A B : Fin n → Prop, (∀ w, P (eof w) = true → A w ∨ B w) ∧
          (∀ w w', A w → A w' → l w = l w') ∧ (∀ w w', B w → B w' → l w = l w') := by
      intro hz u hu
      rcases gate_cases g hop hlen (fun x j => val gs x j) (Zof S) with hall | ⟨a, b, hab⟩
      · have := hall (eof u)
        simp only [hP] at hu
        rw [this] at hu
        exact absurd hu (by simp)
      · obtain ⟨ha, hb, hy⟩ := hab hz
        refine ⟨?_, fun w => val gs (eof w) a = true, fun w => val gs (eof w) b = true,
          fun w hw => hy (eof w) hw, fun w w' hw hw' => (hinv a w w' ha hw hw').2,
          fun w w' hw hw' => (hinv b w w' hb hw hw').2⟩
        rcases hy (eof u) hu with h | h
        · exact (hinv a u u ha h h).1
        · exact (hinv b u u hb h h).1
    by_cases hm : P (Zof S) = false ∧ ∃ u v, P (eof u) = true ∧ P (eof v) = true ∧ l u ≠ l v
    · obtain ⟨hz, u0, v0, hu0, hv0, hne⟩ := hm
      refine ⟨fun w => if l w = l v0 then l u0 else l w, ?_, ?_⟩
      · intro i u v hiz hiu hiv
        by_cases hi : i = N
        · subst hi
          rw [hnew] at hiz hiu hiv
          obtain ⟨huS, A, B, hAB, hA, hB⟩ := key hiz u hiu
          refine ⟨huS, ?_⟩
          have two : ∀ w, P (eof w) = true → l w = l u0 ∨ l w = l v0 := by
            intro w hw
            rcases hAB w hw with h | h <;> rcases hAB u0 hu0 with h0 | h0 <;>
              rcases hAB v0 hv0 with h1 | h1
            · exact Or.inl (hA w u0 h h0)
            · exact Or.inl (hA w u0 h h0)
            · exact Or.inr (hA w v0 h h1)
            · exact absurd (hB u0 v0 h0 h1) hne
            · exact absurd (hA u0 v0 h0 h1) hne
            · exact Or.inr (hB w v0 h h1)
            · exact Or.inl (hB w u0 h h0)
            · exact Or.inl (hB w u0 h h0)
          have red : ∀ w, P (eof w) = true → (if l w = l v0 then l u0 else l w) = l u0 := by
            intro w hw
            rcases two w hw with h | h
            · rw [h]; split_ifs <;> rfl
            · rw [if_pos h]
          show (if l u = l v0 then l u0 else l u) = (if l v = l v0 then l u0 else l v)
          rw [red u hiu, red v hiv]
        · rw [hold _ _ hi] at hiz hiu hiv
          obtain ⟨huS, hl⟩ := hinv i u v hiz hiu hiv
          refine ⟨huS, ?_⟩
          show (if l u = l v0 then l u0 else l u) = (if l v = l v0 then l u0 else l v)
          rw [hl]
      · have himg : S.image l ⊆
            insert (l v0) (S.image fun w => if l w = l v0 then l u0 else l w) := by
          intro y hy
          obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
          by_cases h : l w = l v0
          · rw [h]; exact Finset.mem_insert_self _ _
          · refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨w, hw, ?_⟩)
            rw [if_neg h]
        have h1 : (S.image l).card ≤
            (S.image fun w => if l w = l v0 then l u0 else l w).card + 1 :=
          (Finset.card_le_card himg).trans (Finset.card_insert_le _ _)
        have hNin : N ∈ D S (gs ++ [g]) := by
          simp only [D, Finset.mem_filter, Finset.mem_Ico, List.length_append,
            List.length_cons, List.length_nil]
          refine ⟨⟨by omega, by omega⟩, ?_, u0, v0, ?_, ?_, ?_⟩
          · rw [hnew]; exact hz
          · intro h; exact hne (by rw [h])
          · rw [hnew]; exact hu0
          · rw [hnew]; exact hv0
        have hNnot : N ∉ D S gs := by
          simp only [D, Finset.mem_filter, Finset.mem_Ico]
          intro h
          omega
        have h2 : (D S gs).card + 1 ≤ (D S (gs ++ [g])).card := by
          rw [← Finset.card_insert_of_notMem hNnot]
          apply Finset.card_le_card
          intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hi
          · exact hNin
          · exact D_mono S gs g hi
        omega
    · refine ⟨l, ?_, ?_⟩
      · intro i u v hiz hiu hiv
        by_cases hi : i = N
        · subst hi
          rw [hnew] at hiz hiu hiv
          obtain ⟨huS, -⟩ := key hiz u hiu
          refine ⟨huS, ?_⟩
          by_contra hne
          exact hm ⟨hiz, u, v, hiu, hiv, hne⟩
        · rw [hold _ _ hi] at hiz hiu hiv
          exact hinv i u v hiz hiu hiv
      · have := Finset.card_le_card (D_mono S gs g)
        omega

end PEqualNP.Outside.L_meta_951_mono

open PEqualNP.Outside.L_meta_951_mono in
theorem PEqualNP.Outside.L_meta_951_monotone_bound : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin m) (x : Fin n → Bool), (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x)) = decide (∃ v ∈ S w, x v = true)) → ∑ w, ((S w).card - 1) ≤ gates.length := by
  classical
  intro n m S hS gates out hg hev
  have hval : ∀ (w : Fin m) (x : Fin n → Bool),
      val gates x (out w) = decide (∃ v ∈ S w, x v = true) := fun w x => hev w x
  have hZ : ∀ w, val gates (Zof (S w)) (out w) = false := by
    intro w
    rw [hval]
    simp [Zof]
  have hE : ∀ w, ∀ u ∈ S w, val gates (eof u) (out w) = true := by
    intro w u hu
    rw [hval]
    simp only [decide_eq_true_eq]
    exact ⟨u, hu, by simp [eof]⟩
  choose l hinv hcard using fun w => main_inv (S w) gates hg
  have hbound : ∀ w, (S w).card - 1 ≤ (D (S w) gates).card := by
    intro w
    have h1 : ((S w).image (l w)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
      exact (hinv w (out w) u v (hZ w) (hE w u hu) (hE w v hv)).2
    have := hcard w
    omega
  have hdisj : ∀ a ∈ (Finset.univ : Finset (Fin m)), ∀ b ∈ (Finset.univ : Finset (Fin m)),
      a ≠ b → Disjoint (D (S a) gates) (D (S b) gates) := by
    intro a _ b _ hab
    rw [Finset.disjoint_left]
    intro i hia hib
    simp only [D, Finset.mem_filter, Finset.mem_Ico] at hia hib
    obtain ⟨-, hza, u, v, huv, hu, hv⟩ := hia
    obtain ⟨-, hzb, -⟩ := hib
    have hua := (hinv a i u u hza hu hu).1
    have hva := (hinv a i v v hza hv hv).1
    have hub := (hinv b i u u hzb hu hu).1
    have hvb := (hinv b i v v hzb hv hv).1
    have hsub : ({u, v} : Finset (Fin n)) ⊆ S a ∩ S b := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨hua, hub⟩
      · exact Finset.mem_inter.mpr ⟨hva, hvb⟩
    have h2 : ({u, v} : Finset (Fin n)).card = 2 := Finset.card_pair huv
    have := Finset.card_le_card hsub
    have := hS a b hab
    omega
  calc ∑ w, ((S w).card - 1) ≤ ∑ w, (D (S w) gates).card :=
        Finset.sum_le_sum fun w _ => hbound w
    _ = (Finset.univ.biUnion fun w => D (S w) gates).card :=
        (Finset.card_biUnion hdisj).symm
    _ ≤ (Finset.Ico n (n + gates.length)).card := by
        apply Finset.card_le_card
        intro i hi
        obtain ⟨w, -, hw⟩ := Finset.mem_biUnion.mp hi
        simp only [D, Finset.mem_filter] at hw
        exact hw.1
    _ = gates.length := by simp


namespace PEqualNP.Outside.L_meta_951
open PEqualNP.CircuitLowerBounds

lemma upper_exact_when_not_input_false {n : ℕ} (S : Finset (Fin n))
    (pre post : List Gate)
    (hpre : ∀ g ∈ pre, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hpost : ∀ g ∈ post, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (ins : List ℕ) (o : ℕ)
    (hexact : ∀ x : Fin n → Bool,
      Circuit.eval ⟨pre ++ ({op := GateOp.not, inputs := ins} : Gate) :: post, o⟩
        (List.ofFn x) = decide (∃ v ∈ S, x v = true))
    (hz : ((ins.map fun i => (Circuit.wires ⟨pre, 0⟩
      (List.ofFn fun v : Fin n => decide (v ∉ S))).getD i false).headD false) = false) :
    ∀ x : Fin n → Bool,
      Circuit.eval ⟨pre ++ ({op := GateOp.and, inputs := []} : Gate) :: post, o⟩
        (List.ofFn x) = decide (∃ v ∈ S, x v = true) := by
  classical
  intro x
  by_cases hx : ∃ v ∈ S, x v = true
  · rw [decide_eq_true hx]
    apply on1_upper_true pre post (fun g hg => (hpost g hg).1) ins o (List.ofFn x)
    rw [hexact, decide_eq_true hx]
  · rw [decide_eq_false hx]
    apply Bool.eq_false_iff.mpr
    intro ht
    have hle : ∀ v, x v = true → decide (v ∉ S) = true := by
      intro v hv
      exact decide_eq_true (fun hs => hx ⟨v, hs, hv⟩)
    have hu := (on1_replacements_monotone pre post hpre hpost o x
      (fun v => decide (v ∉ S)) hle).2 ht
    rw [on1_piece_d n pre post ins o _ hz, hexact] at hu
    simp only [decide_eq_true_eq] at hu
    obtain ⟨v, hv, hn⟩ := hu
    exact hn hv

lemma safe_branch_lower {n m : ℕ} (S : Fin m → Finset (Fin n))
    (hlinear : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (pre post : List Gate)
    (hpre : ∀ g ∈ pre, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hpost : ∀ g ∈ post, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (ins : List ℕ) (out : Fin m → ℕ)
    (hexact : ∀ (w : Fin m) (x : Fin n → Bool),
      Circuit.eval ⟨pre ++ ({op := GateOp.not, inputs := ins} : Gate) :: post, out w⟩
        (List.ofFn x) = decide (∃ v ∈ S w, x v = true))
    (hz : ∀ w : Fin m, ((ins.map fun i => (Circuit.wires ⟨pre, 0⟩
      (List.ofFn fun v : Fin n => decide (v ∉ S w))).getD i false).headD false) = false) :
    (∑ w : Fin m, ((S w).card - 1)) ≤
      (pre ++ ({op := GateOp.not, inputs := ins} : Gate) :: post).length := by
  have h := PEqualNP.Outside.L_meta_951_monotone_bound n m S hlinear
    (pre ++ ({op := GateOp.and, inputs := []} : Gate) :: post) out
    (on1_constants_mono pre post hpre hpost GateOp.and (Or.inl rfl))
    (fun w => upper_exact_when_not_input_false (S w) pre post hpre hpost ins
      (out w) (hexact w) (hz w))
  simpa only [List.length_append, List.length_cons] using h

end PEqualNP.Outside.L_meta_951

namespace PEqualNP.Outside.L_meta_951
open PEqualNP.CircuitLowerBounds

lemma lower_exact_when_target_implies_not_input {n : ℕ} (S : Finset (Fin n))
    (pre post : List Gate)
    (hpost : ∀ g ∈ post, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (ins : List ℕ) (o : ℕ)
    (hexact : ∀ x : Fin n → Bool,
      Circuit.eval ⟨pre ++ ({op := GateOp.not, inputs := ins} : Gate) :: post, o⟩
        (List.ofFn x) = decide (∃ v ∈ S, x v = true))
    (hh : ∀ x : Fin n → Bool, (∃ v ∈ S, x v = true) →
      ((ins.map fun i => (Circuit.wires ⟨pre, 0⟩ (List.ofFn x)).getD i false).headD false)
        = true) :
    ∀ x : Fin n → Bool,
      Circuit.eval ⟨pre ++ ({op := GateOp.or, inputs := []} : Gate) :: post, o⟩
        (List.ofFn x) = decide (∃ v ∈ S, x v = true) := by
  classical
  intro x
  by_cases hx : ∃ v ∈ S, x v = true
  · rw [on1_piece_u_cheap n pre post ins o x (hh x hx), hexact]
  · rw [decide_eq_false hx]
    apply Bool.eq_false_iff.mpr
    intro ht
    have hn := on1_lower_true pre post (fun g hg => (hpost g hg).1) ins o
      (List.ofFn x) ht
    rw [hexact, decide_eq_false hx] at hn
    contradiction

lemma comparable_sums_uniform {n m : ℕ} (S : Fin m → Finset (Fin n))
    (hcard : ∀ i : Fin m, 2 ≤ (S i).card)
    (hlinear : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (h : (Fin n → Bool) → Bool)
    (hc : ∀ i : Fin m,
      (∀ x : Fin n → Bool, h x = true → ∃ v ∈ S i, x v = true) ∨
      (∀ x : Fin n → Bool, (∃ v ∈ S i, x v = true) → h x = true)) :
    (∀ (i : Fin m) (x : Fin n → Bool), h x = true → ∃ v ∈ S i, x v = true) ∨
    (∀ (i : Fin m) (x : Fin n → Bool), (∃ v ∈ S i, x v = true) → h x = true) := by
  classical
  by_cases he : ∃ i : Fin m, ∀ x : Fin n → Bool, h x = true → ∃ v ∈ S i, x v = true
  · obtain ⟨i, hi⟩ := he
    left
    intro j
    rcases hc j with hj | hj
    · exact hj
    · have hsub : S j ⊆ S i := by
        intro u hu
        obtain ⟨v, hv, hvu⟩ := hi (fun t => decide (t = u))
          (hj (fun t => decide (t = u)) ⟨u, hu, by simp⟩)
        have hvu' : v = u := of_decide_eq_true hvu
        simpa only [hvu'] using hv
      have hji : j = i := by
        by_contra hne
        have hmeet := hlinear j i hne
        rw [Finset.inter_eq_left.mpr hsub] at hmeet
        have := hcard j
        omega
      simpa only [hji] using hi
  · right
    intro i
    rcases hc i with hi | hi
    · exact False.elim (he ⟨i, hi⟩)
    · exact hi

lemma comparable_branch_lower {n m : ℕ} (S : Fin m → Finset (Fin n))
    (hcard : ∀ i : Fin m, 2 ≤ (S i).card)
    (hlinear : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (pre post : List Gate)
    (hpre : ∀ g ∈ pre, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hpost : ∀ g ∈ post, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (ins : List ℕ) (out : Fin m → ℕ)
    (hexact : ∀ (w : Fin m) (x : Fin n → Bool),
      Circuit.eval ⟨pre ++ ({op := GateOp.not, inputs := ins} : Gate) :: post, out w⟩
        (List.ofFn x) = decide (∃ v ∈ S w, x v = true))
    (hc : ∀ w : Fin m,
      (∀ x : Fin n → Bool,
        ((ins.map fun i => (Circuit.wires ⟨pre, 0⟩ (List.ofFn x)).getD i false).headD false)
          = true → ∃ v ∈ S w, x v = true) ∨
      (∀ x : Fin n → Bool, (∃ v ∈ S w, x v = true) →
        ((ins.map fun i => (Circuit.wires ⟨pre, 0⟩ (List.ofFn x)).getD i false).headD false)
          = true)) :
    (∑ w : Fin m, ((S w).card - 1)) ≤
      (pre ++ ({op := GateOp.not, inputs := ins} : Gate) :: post).length := by
  classical
  rcases comparable_sums_uniform S hcard hlinear
    (fun x => ((ins.map fun i => (Circuit.wires ⟨pre, 0⟩ (List.ofFn x)).getD i false).headD false))
    hc with hall | hall
  · apply safe_branch_lower S hlinear pre post hpre hpost ins out hexact
    intro w
    apply Bool.eq_false_iff.mpr
    intro ht
    obtain ⟨v, hv, hn⟩ := hall w (fun t => decide (t ∉ S w)) ht
    exact of_decide_eq_true hn hv
  · have hb := PEqualNP.Outside.L_meta_951_monotone_bound n m S hlinear
      (pre ++ ({op := GateOp.or, inputs := []} : Gate) :: post) out
      (on1_constants_mono pre post hpre hpost GateOp.or (Or.inr rfl))
      (fun w => lower_exact_when_target_implies_not_input (S w) pre post hpost ins
        (out w) (hexact w) (hall w))
    simpa only [List.length_append, List.length_cons] using hb

end PEqualNP.Outside.L_meta_951
