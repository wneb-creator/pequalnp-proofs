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

def aboveExcept (v : ℕ) (w w' : List Bool) : Prop :=
  w.length = w'.length ∧ ∀ j, j ≠ v → w.getD j false = true → w'.getD j false = true

lemma aboveExcept_snoc {v : ℕ} {w w' : List Bool} {a a' : Bool}
    (h : aboveExcept v w w') (ha : a = true → a' = true) :
    aboveExcept v (w ++ [a]) (w' ++ [a']) := by
  refine ⟨by simp [h.1], ?_⟩
  intro j hj ht
  by_cases hjw : j = w.length
  · subst j
    rw [getD_snoc_eq] at ht
    rw [h.1, getD_snoc_eq]
    exact ha ht
  · rw [getD_snoc_ne _ _ _ _ hjw] at ht
    rw [getD_snoc_ne _ _ _ _ (by rw [← h.1]; exact hjw)]
    exact h.2 j hj ht

lemma aboveExcept_wiresFrom (v : ℕ) (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hexcl : ∀ g ∈ gs, v ∉ g.inputs) :
    ∀ w w', aboveExcept v w w' → aboveExcept v (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro w w' h; exact h
  | cons g gs ih =>
    intro w w' h
    rw [on1_wiresFrom_cons, on1_wiresFrom_cons]
    apply ih (fun g' hg' => hgs g' (by simp [hg']))
      (fun g' hg' => hexcl g' (by simp [hg']))
    apply aboveExcept_snoc h
    have hv : ∀ j ∈ g.inputs, j ≠ v := by
      intro j hj he
      apply hexcl g (by simp)
      exact he ▸ hj
    rcases hgs g (by simp) with hop | hop
    · rw [hop]
      simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
      intro hall b hb
      obtain ⟨j, hj, rfl⟩ := hb
      exact h.2 j (hv j hj) (hall _ ⟨j, hj, rfl⟩)
    · rw [hop]
      simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
      rintro ⟨b, ⟨j, hj, rfl⟩, hb⟩
      exact ⟨_, ⟨j, hj, rfl⟩, h.2 j (hv j hj) hb⟩

lemma positive_direct_consumer {n : ℕ} (v : Fin n) (gs : List Gate) (o : ℕ)
    (hops : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (huniq : ∀ i j : Fin gs.length, (gs.get i).op = GateOp.not →
      (gs.get j).op = GateOp.not → i = j)
    (hne : o ≠ v.val)
    (hzero : Circuit.eval ⟨gs, o⟩ (List.ofFn (fun _ : Fin n => false)) = false)
    (hsingle : Circuit.eval ⟨gs, o⟩
      (List.ofFn (Function.update (fun _ : Fin n => false) v true)) = true) :
    ∃ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ v.val ∈ g.inputs := by
  classical
  by_contra hn
  have hexcl : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) → v.val ∉ g.inputs := by
    intro g hg hop hmem
    exact hn ⟨g, hg, hop, hmem⟩
  let x : Fin n → Bool := fun _ => false
  let y : Fin n → Bool := Function.update x v true
  have hinit : aboveExcept v.val (List.ofFn y) (List.ofFn x) := by
    refine ⟨by simp, ?_⟩
    intro j hj ht
    by_cases hjn : j < n
    · rw [on1_getD_ofFn _ _ hjn] at ht ⊢
      have hjv : (⟨j, hjn⟩ : Fin n) ≠ v := by
        intro he
        exact hj (congrArg Fin.val he)
      simp [y, Function.update_of_ne hjv] at ht
    · rw [List.getD_eq_default _ _ (by simp; omega)] at ht
      contradiction
  have ha : aboveExcept v.val (wiresFrom gs (List.ofFn y)) (wiresFrom gs (List.ofFn x)) := by
    rcases on1_split gs hops huniq with hmono | ⟨pre,post,ins,hgs,hpre,hpost⟩
    · exact aboveExcept_wiresFrom v.val gs (fun g hg => (hmono g hg).1)
        (fun g hg => hexcl g hg (hmono g hg).1) _ _ hinit
    · have hpreEx : ∀ g ∈ pre, v.val ∉ g.inputs := by
        intro g hg
        apply hexcl g (by rw [hgs]; simp [hg]) (hpre g hg).1
      have hpostEx : ∀ g ∈ post, v.val ∉ g.inputs := by
        intro g hg
        apply hexcl g (by rw [hgs]; simp [hg]) (hpost g hg).1
      have hp := aboveExcept_wiresFrom v.val pre (fun g hg => (hpre g hg).1)
        hpreEx _ _ hinit
      have hm := on1_piece_h n pre ins hpre x y (by intro i hi; simp [x] at hi)
      have hnot : GateOp.not.eval (ins.map fun j => (wiresFrom pre (List.ofFn y)).getD j false) = true →
          GateOp.not.eval (ins.map fun j => (wiresFrom pre (List.ofFn x)).getD j false) = true := by
        change (ins.map fun j => (wiresFrom pre (List.ofFn x)).getD j false).headD false = true →
          (ins.map fun j => (wiresFrom pre (List.ofFn y)).getD j false).headD false = true at hm
        intro hytrue
        have hheady : (ins.map fun j => (wiresFrom pre (List.ofFn y)).getD j false).headD false = false := by
          simpa [GateOp.eval] using hytrue
        have hheadx : (ins.map fun j => (wiresFrom pre (List.ofFn x)).getD j false).headD false = false := by
          cases hx : (ins.map fun j => (wiresFrom pre (List.ofFn x)).getD j false).headD false with
          | false => rfl
          | true =>
            have hh := hm hx
            rw [hheady] at hh
            contradiction
        change !((ins.map fun j => (wiresFrom pre (List.ofFn x)).getD j false).headD false) = true
        rw [hheadx]
        rfl
      rw [hgs, wiresFrom_append, wiresFrom_append,
        on1_wiresFrom_cons, on1_wiresFrom_cons]
      apply aboveExcept_wiresFrom v.val post (fun g hg => (hpost g hg).1) hpostEx
      exact aboveExcept_snoc hp hnot
  have hh := ha.2 o hne hsingle
  rw [show (wiresFrom gs (List.ofFn x)).getD o false = false from hzero] at hh
  contradiction

end PEqualNP.Outside.L_meta_951


namespace PEqualNP.Outside.L_meta_951.Deletion

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

def on1_relabel (r : ℕ → ℕ) (g : Gate) : Gate := { op := g.op, inputs := g.inputs.map r }

/-- The generic simulation, with the invariant on every index. -/
lemma on1_relabel_sim_all (r : ℕ → ℕ) (gs : List Gate) : ∀ (v w : List Bool),
    (∀ i, v.getD (r i) false = w.getD i false) →
    (∀ i < w.length, r i < v.length ∨ v.length + gs.length ≤ r i) →
    (∀ k < gs.length, r (w.length + k) = v.length + k) →
    (∀ i, w.length + gs.length ≤ i → v.length + gs.length ≤ r i) →
    ∀ i, (wiresFrom (gs.map (on1_relabel r)) v).getD (r i) false
      = (wiresFrom gs w).getD i false := by
  induction gs with
  | nil => intro v w h1 _ _ _ i; exact h1 i
  | cons g gs ih =>
    intro v w h1 h2 h3 h4
    simp only [List.length_cons] at h2 h3 h4
    have hval : (on1_relabel r g).op.eval
          ((on1_relabel r g).inputs.map fun i => v.getD i false)
        = g.op.eval (g.inputs.map fun i => w.getD i false) := by
      simp only [on1_relabel, List.map_map]
      congr 1
      apply List.map_congr_left
      intro j _
      exact h1 j
    have hr0 : r w.length = v.length := by simpa using h3 0 (by omega)
    have hne : ∀ i, i ≠ w.length → r i ≠ v.length := by
      intro i hi
      by_cases hlt : i < w.length
      · rcases h2 i hlt with h | h <;> omega
      · by_cases hk : i < w.length + (gs.length + 1)
        · have := h3 (i - w.length) (by omega)
          rw [show w.length + (i - w.length) = i by omega] at this
          omega
        · have := h4 i (by omega); omega
    rw [List.map_cons, on1_wiresFrom_cons, on1_wiresFrom_cons, hval]
    apply ih
    · intro i
      by_cases hi : i = w.length
      · subst hi
        rw [hr0, getD_snoc_eq, getD_snoc_eq]
      · rw [getD_snoc_ne _ _ _ _ (hne i hi), getD_snoc_ne _ _ _ _ hi]
        exact h1 i
    · intro i hi
      simp only [List.length_append, List.length_singleton] at hi ⊢
      by_cases hlt : i < w.length
      · rcases h2 i hlt with h | h
        · left; omega
        · right; omega
      · left; have : i = w.length := by omega
        subst this; omega
    · intro k hk
      simp only [List.length_append, List.length_singleton]
      have := h3 (k + 1) (by omega)
      rw [show w.length + 1 + k = w.length + (k + 1) by omega, this]; omega
    · intro i hi
      simp only [List.length_append, List.length_singleton] at hi ⊢
      have := h4 i (by omega); omega

/-- The generic simulation: it is enough that `r` is right on the start wires. -/
lemma on1_relabel_sim (r : ℕ → ℕ) (gs : List Gate) (v w : List Bool)
    (h1 : ∀ i < w.length, v.getD (r i) false = w.getD i false)
    (h2 : ∀ i < w.length, r i < v.length ∨ v.length + gs.length ≤ r i)
    (h3 : ∀ k < gs.length, r (w.length + k) = v.length + k)
    (h4 : ∀ i, w.length + gs.length ≤ i → v.length + gs.length ≤ r i) (i : ℕ) :
    (wiresFrom (gs.map (on1_relabel r)) v).getD (r i) false
      = (wiresFrom gs w).getD i false := by
  apply on1_relabel_sim_all r gs v w _ h2 h3 h4
  intro j
  by_cases hj : j < w.length
  · exact h1 j hj
  · have hge : v.length ≤ r j := by
      by_cases hk : j < w.length + gs.length
      · have := h3 (j - w.length) (by omega)
        rw [show w.length + (j - w.length) = j by omega] at this
        omega
      · have := h4 j (by omega); omega
    rw [List.getD_eq_default _ _ hge, List.getD_eq_default _ _ (by omega)]

def deleteMap (p a : ℕ) (i : ℕ) : ℕ :=
  if i < p then i else if i = p then a else i - 1

lemma delete_alias (n : ℕ) (pre post : List Gate) (g : Gate) (a : ℕ)
    (ha : a < n + pre.length ∨ n + pre.length + post.length ≤ a)
    (o : ℕ) (x : Fin n → Bool)
    (hval : g.op.eval (g.inputs.map fun i =>
        (Circuit.wires ⟨pre, 0⟩ (List.ofFn x)).getD i false) =
      (Circuit.wires ⟨pre, 0⟩ (List.ofFn x)).getD a false) :
    Circuit.eval
      ⟨pre ++ post.map (on1_relabel (deleteMap (n + pre.length) a)),
        deleteMap (n + pre.length) a o⟩ (List.ofFn x) =
      Circuit.eval ⟨pre ++ g :: post, o⟩ (List.ofFn x) := by
  set p := n + pre.length with hp
  set r := deleteMap p a with hr
  set v := wiresFrom pre (List.ofFn x) with hv
  have hvl : v.length = p := by rw [hv, length_wiresFrom]; simp [hp]
  set gv := g.op.eval (g.inputs.map fun i => v.getD i false) with hgv
  have hgv' : gv = v.getD a false := hval
  unfold Circuit.eval
  rw [on1_wires_append _ _ _ 0, on1_wires_append _ _ _ 0, on1_wiresFrom_cons]
  change (wiresFrom (post.map (on1_relabel r)) v).getD (r o) false =
    (wiresFrom post (v ++ [gv])).getD o false
  apply on1_relabel_sim
  · intro i hi
    simp only [List.length_append, List.length_singleton, hvl] at hi
    by_cases hlt : i < p
    · simp only [hr, deleteMap, hlt, ite_true]
      rw [on1_getD_append_left _ _ _ (by omega)]
    · have hi' : i = p := by omega
      subst i
      simp only [hr, deleteMap, lt_irrefl, ite_false, ite_true]
      rw [← hvl, getD_snoc_eq, hgv']
  · intro i hi
    simp only [List.length_append, List.length_singleton, hvl] at hi ⊢
    by_cases hlt : i < p
    · left
      simp [hr, deleteMap, hlt]
    · have hi' : i = p := by omega
      subst i
      simpa [hr, deleteMap, hp] using ha
  · intro k _
    simp only [List.length_append, List.length_singleton, hvl, hr, deleteMap]
    split_ifs <;> omega
  · intro i hi
    simp only [List.length_append, List.length_singleton, hvl] at hi ⊢
    simp only [hr, deleteMap]
    split_ifs <;> omega

lemma delete_false (n : ℕ) (pre post : List Gate) (g : Gate)
    (o : ℕ) (x : Fin n → Bool)
    (hval : g.op.eval (g.inputs.map fun i =>
        (Circuit.wires ⟨pre, 0⟩ (List.ofFn x)).getD i false) = false) :
    Circuit.eval
      ⟨pre ++ post.map (on1_relabel
          (deleteMap (n + pre.length) (n + pre.length + post.length))),
        deleteMap (n + pre.length) (n + pre.length + post.length) o⟩ (List.ofFn x) =
      Circuit.eval ⟨pre ++ g :: post, o⟩ (List.ofFn x) := by
  apply delete_alias n pre post g _ (Or.inr (le_refl _)) o x
  rw [hval]
  symm
  apply on1_getD_wires_of_ge
  simp

lemma delete_length (n : ℕ) (pre post : List Gate) (g : Gate) (a : ℕ) :
    (pre ++ post.map (on1_relabel (deleteMap (n + pre.length) a))).length + 1 =
      (pre ++ g :: post).length := by simp; omega

lemma delete_allowed (pre post : List Gate) (g : Gate) (r : ℕ → ℕ)
    (hops : ∀ h ∈ pre ++ g :: post,
      (h.op = GateOp.and ∨ h.op = GateOp.or ∨ h.op = GateOp.not) ∧
        h.inputs.length ≤ 2) :
    ∀ h ∈ pre ++ post.map (on1_relabel r),
      (h.op = GateOp.and ∨ h.op = GateOp.or ∨ h.op = GateOp.not) ∧
        h.inputs.length ≤ 2 := by
  intro h hh
  rcases List.mem_append.mp hh with hh | hh
  · exact hops h (List.mem_append_left _ hh)
  · obtain ⟨h', hh', rfl⟩ := List.mem_map.mp hh
    have hs := hops h' (List.mem_append_right _ (List.mem_cons_of_mem _ hh'))
    simpa [on1_relabel] using hs

lemma positive_zero_alias (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (ins : List ℕ) (hins : ins.length ≤ 2) (v : ℕ) (hv : v ∈ ins) :
    ∃ a : Option ℕ, ∀ f : ℕ → Bool, f v = false →
      op.eval (ins.map f) = match a with | none => false | some j => f j := by
  rcases hop with rfl | rfl
  · refine ⟨none, ?_⟩
    intro f hf
    change (ins.map f).all id = false
    cases he : (ins.map f).all id with
    | false => rfl
    | true =>
      have hh := List.all_eq_true.mp he (f v) (List.mem_map.mpr ⟨v,hv,rfl⟩)
      simp [hf] at hh
  · cases ins with
    | nil => simp at hv
    | cons a rest =>
      cases rest with
      | nil =>
        simp only [List.mem_singleton] at hv
        subst v
        refine ⟨none, ?_⟩
        intro f hf
        simp [GateOp.eval, hf]
      | cons b tail =>
        have htail : tail = [] := by
          apply List.length_eq_zero_iff.mp
          have hh : tail.length + 1 + 1 ≤ 2 := hins
          omega
        subst tail
        rcases List.mem_cons.mp hv with hva | hvb
        · subst v
          refine ⟨some b, ?_⟩
          intro f hf
          simp [GateOp.eval, hf]
        · simp only [List.mem_singleton] at hvb
          subst v
          refine ⟨some a, ?_⟩
          intro f hf
          simp [GateOp.eval, hf]

lemma direct_zero_alias {n : ℕ} (pre post : List Gate) (g : Gate) (v : Fin n)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : g.inputs.length ≤ 2) (hmem : v.val ∈ g.inputs) :
    ∃ a : ℕ, (a < n + pre.length ∨ n + pre.length + post.length ≤ a) ∧
      ∀ x : Fin n → Bool, x v = false →
        g.op.eval (g.inputs.map fun j =>
          (Circuit.wires ⟨pre, 0⟩ (List.ofFn x)).getD j false) =
        (Circuit.wires ⟨pre, 0⟩ (List.ofFn x)).getD a false := by
  obtain ⟨a,ha⟩ := positive_zero_alias g.op hop g.inputs hlen v.val hmem
  have hv (x : Fin n → Bool) (hx : x v = false) :
      (Circuit.wires ⟨pre, 0⟩ (List.ofFn x)).getD v.val false = false := by
    rw [on1_getD_wires_input _ _ _ v.isLt]
    exact hx
  cases a with
  | none =>
    refine ⟨n + pre.length + post.length, Or.inr (le_refl _), ?_⟩
    intro x hx
    rw [ha _ (hv x hx)]
    symm
    apply on1_getD_wires_of_ge
    simp
  | some a =>
    by_cases hlt : a < n + pre.length
    · exact ⟨a, Or.inl hlt, fun x hx => ha _ (hv x hx)⟩
    · refine ⟨n + pre.length + post.length, Or.inr (le_refl _), ?_⟩
      intro x hx
      rw [ha _ (hv x hx)]
      change (Circuit.wires ⟨pre, 0⟩ (List.ofFn x)).getD a false =
        (Circuit.wires ⟨pre, 0⟩ (List.ofFn x)).getD (n + pre.length + post.length) false
      rw [on1_getD_wires_of_ge _ _ a (by simpa using Nat.le_of_not_gt hlt),
        on1_getD_wires_of_ge _ _ (n + pre.length + post.length) (by simp)]

lemma delete_positive_zero {n : ℕ} (pre post : List Gate) (g : Gate) (v : Fin n)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : g.inputs.length ≤ 2) (hmem : v.val ∈ g.inputs) :
    ∃ r : ℕ → ℕ,
      (pre ++ post.map (on1_relabel r)).length + 1 = (pre ++ g :: post).length ∧
      ∀ (o : ℕ) (x : Fin n → Bool), x v = false →
        Circuit.eval ⟨pre ++ post.map (on1_relabel r), r o⟩ (List.ofFn x) =
          Circuit.eval ⟨pre ++ g :: post, o⟩ (List.ofFn x) := by
  obtain ⟨a, ha, hval⟩ := direct_zero_alias pre post g v hop hlen hmem
  refine ⟨deleteMap (n + pre.length) a, delete_length n pre post g a, ?_⟩
  intro o x hx
  exact delete_alias n pre post g a ha o x (hval x hx)

lemma delete_not_unique (pre post : List Gate) (g : Gate) (r : ℕ → ℕ)
    (huniq : ∀ i j : Fin (pre ++ g :: post).length,
      ((pre ++ g :: post).get i).op = GateOp.not →
      ((pre ++ g :: post).get j).op = GateOp.not → i = j) :
    ∀ i j : Fin (pre ++ post.map (on1_relabel r)).length,
      ((pre ++ post.map (on1_relabel r)).get i).op = GateOp.not →
      ((pre ++ post.map (on1_relabel r)).get j).op = GateOp.not → i = j := by
  let emb : Fin (pre ++ post.map (on1_relabel r)).length → Fin (pre ++ g :: post).length :=
    fun k => ⟨if k.val < pre.length then k.val else k.val + 1, by
      have hk := k.isLt
      simp only [List.length_append, List.length_map, List.length_cons] at hk ⊢
      split_ifs <;> omega⟩
  have hinj : Function.Injective emb := by
    intro i j hij
    have hh := congrArg Fin.val hij
    dsimp [emb] at hh
    apply Fin.ext
    split_ifs at hh <;> omega
  have hop (k : Fin (pre ++ post.map (on1_relabel r)).length) :
      ((pre ++ post.map (on1_relabel r)).get k).op =
        ((pre ++ g :: post).get (emb k)).op := by
    simp only [List.get_eq_getElem]
    by_cases hk : k.val < pre.length
    · simp [emb, hk, List.getElem_append_left]
    · have hk' : pre.length ≤ k.val := by omega
      simp only [emb, hk, ite_false]
      rw [List.getElem_append_right hk', List.getElem_append_right (by omega)]
      simp only [show k.val + 1 - pre.length = (k.val - pre.length) + 1 by omega,
        List.getElem_cons_succ, List.getElem_map, on1_relabel]
  intro i j hi hj
  apply hinj
  apply huniq
  · rw [← hop i]
    exact hi
  · rw [← hop j]
    exact hj

lemma not_unique_cover (gs : List Gate) (hpos : 0 < gs.length)
    (huniq : ∀ i j : Fin gs.length, (gs.get i).op = GateOp.not →
      (gs.get j).op = GateOp.not → i = j) :
    ∃ ι : Fin 1 → Fin gs.length, ∀ i : Fin gs.length,
      (gs.get i).op = GateOp.not → ∃ j : Fin 1, ι j = i := by
  classical
  by_cases hex : ∃ i : Fin gs.length, (gs.get i).op = GateOp.not
  · obtain ⟨i, hi⟩ := hex
    refine ⟨fun _ => i, ?_⟩
    intro j hj
    exact ⟨0, huniq i j hi hj⟩
  · refine ⟨fun _ => ⟨0, hpos⟩, ?_⟩
    intro j hj
    exact False.elim (hex ⟨j,hj⟩)

lemma on1_restrict_down : ∀ (n : ℕ) (a : Finset (Fin n))
    (gates : List PEqualNP.CircuitLowerBounds.Gate), ∃ r : ℕ → ℕ,
    ∀ (o : ℕ) (x : Fin n → Bool),
      PEqualNP.CircuitLowerBounds.Circuit.eval
          ⟨gates.map (fun g => ({ op := g.op, inputs := g.inputs.map r } :
            PEqualNP.CircuitLowerBounds.Gate)), r o⟩ (List.ofFn x)
        = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩
            (List.ofFn (fun i => x i && decide (i ∈ a))) := by
  intro n a gates
  refine ⟨fun i => if h : i < n then (if (⟨i, h⟩ : Fin n) ∈ a then i else n + gates.length)
    else i, ?_⟩
  intro o x
  set r : ℕ → ℕ := fun i => if h : i < n then (if (⟨i, h⟩ : Fin n) ∈ a then i else
    n + gates.length) else i with hr
  show (wiresFrom (gates.map (on1_relabel r)) (List.ofFn x)).getD (r o) false
    = (wiresFrom gates (List.ofFn (fun i => x i && decide (i ∈ a)))).getD o false
  apply on1_relabel_sim
  · intro i hi
    simp only [List.length_ofFn] at hi
    rw [on1_getD_ofFn _ _ hi]
    by_cases ha : (⟨i, hi⟩ : Fin n) ∈ a
    · simp [hr, hi, ha]
    · simp only [hr, hi, ha, dite_true, ite_false]
      rw [List.getD_eq_default _ _ (by simp)]; simp
  · intro i hi
    simp only [List.length_ofFn] at hi ⊢
    by_cases ha : (⟨i, hi⟩ : Fin n) ∈ a
    · left; simp [hr, hi, ha]
    · right; simp [hr, hi, ha]
  · intro k _
    simp [hr]
  · intro i hi
    simp only [List.length_ofFn] at hi ⊢
    simp [hr, show ¬ i < n by omega]; omega

end PEqualNP.Outside.L_meta_951.Deletion

namespace PEqualNP.Outside.L_meta_951

open PEqualNP.CircuitLowerBounds

lemma relabel_allowed (gs : List Gate) (r : ℕ → ℕ)
    (hops : ∀ h ∈ gs, (h.op = GateOp.and ∨ h.op = GateOp.or ∨ h.op = GateOp.not) ∧
      h.inputs.length ≤ 2) :
    ∀ h ∈ gs.map (Deletion.on1_relabel r),
      (h.op = GateOp.and ∨ h.op = GateOp.or ∨ h.op = GateOp.not) ∧
        h.inputs.length ≤ 2 := by
  intro h hh
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hh
  simpa [Deletion.on1_relabel] using hops g hg

lemma relabel_not_unique (gs : List Gate) (r : ℕ → ℕ)
    (hu : ∀ i j : Fin gs.length, (gs.get i).op = GateOp.not →
      (gs.get j).op = GateOp.not → i = j) :
    ∀ i j : Fin (gs.map (Deletion.on1_relabel r)).length,
      ((gs.map (Deletion.on1_relabel r)).get i).op = GateOp.not →
      ((gs.map (Deletion.on1_relabel r)).get j).op = GateOp.not → i = j := by
  intro i j hi hj
  let i' : Fin gs.length := ⟨i.val, by simpa using i.isLt⟩
  let j' : Fin gs.length := ⟨j.val, by simpa using j.isLt⟩
  have hi' : (gs.get i').op = GateOp.not := by
    simpa [Deletion.on1_relabel, i'] using hi
  have hj' : (gs.get j').op = GateOp.not := by
    simpa [Deletion.on1_relabel, j'] using hj
  have hh := hu i' j' hi' hj'
  apply Fin.ext
  exact congrArg (fun k : Fin gs.length => k.val) hh

lemma erase_variable {n m : ℕ} (S : Fin m → Finset (Fin n))
    (gs : List Gate) (out : Fin m → ℕ)
    (hops : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (huniq : ∀ i j : Fin gs.length, (gs.get i).op = GateOp.not →
      (gs.get j).op = GateOp.not → i = j)
    (hev : ∀ (i : Fin m) (x : Fin n → Bool), Circuit.eval ⟨gs, out i⟩ (List.ofFn x) =
      decide (∃ v ∈ S i, x v = true))
    (i : Fin m) (v : Fin n) (hv : v ∈ S i) (hne : out i ≠ v.val) :
    ∃ (gs' : List Gate) (out' : Fin m → ℕ),
      gs'.length + 1 = gs.length ∧
      (∀ g ∈ gs', (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
        g.inputs.length ≤ 2) ∧
      (∀ j k : Fin gs'.length, (gs'.get j).op = GateOp.not →
        (gs'.get k).op = GateOp.not → j = k) ∧
      ∀ (j : Fin m) (x : Fin n → Bool), Circuit.eval ⟨gs', out' j⟩ (List.ofFn x) =
        decide (∃ w ∈ (S j).erase v, x w = true) := by
  classical
  have hzero : Circuit.eval ⟨gs, out i⟩ (List.ofFn (fun _ : Fin n => false)) = false := by
    rw [hev]
    simp
  have hsingle : Circuit.eval ⟨gs, out i⟩
      (List.ofFn (Function.update (fun _ : Fin n => false) v true)) = true := by
    rw [hev]
    exact decide_eq_true ⟨v, hv, by simp⟩
  obtain ⟨g,hg,hop,hmem⟩ := positive_direct_consumer v gs (out i) hops huniq hne hzero hsingle
  obtain ⟨pre,post,rfl⟩ := List.append_of_mem hg
  obtain ⟨r,hlen,hsem⟩ := Deletion.delete_positive_zero pre post g v hop (hops g hg).2 hmem
  let mid := pre ++ post.map (Deletion.on1_relabel r)
  have hmidallowed := Deletion.delete_allowed pre post g r hops
  have hmidunique := Deletion.delete_not_unique pre post g r huniq
  obtain ⟨r0,hr0⟩ := Deletion.on1_restrict_down n (Finset.univ.erase v) mid
  refine ⟨mid.map (Deletion.on1_relabel r0), fun j => r0 (r (out j)), ?_, ?_, ?_, ?_⟩
  · simpa [mid] using hlen
  · exact relabel_allowed mid r0 hmidallowed
  · exact relabel_not_unique mid r0 hmidunique
  · intro j x
    change Circuit.eval ⟨mid.map (fun g => ⟨g.op, g.inputs.map r0⟩), r0 (r (out j))⟩
      (List.ofFn x) = _
    rw [hr0]
    rw [hsem (out j) (fun w => x w && decide (w ∈ Finset.univ.erase v)) (by simp)]
    rw [hev]
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Bool.and_eq_true,
      decide_eq_true_eq]
    congr 1
    apply propext
    simp only [and_assoc, and_comm]

end PEqualNP.Outside.L_meta_951


namespace PEqualNP.Outside.L_meta_951

lemma private_erasure_demand {n m : ℕ} (S : Fin m → Finset (Fin n))
    (i : Fin m) (v : Fin n) (hv : v ∈ S i) (hsize : 2 ≤ (S i).card)
    (hprivate : ∀ j, j ≠ i → v ∉ S j) :
    (∑ j : Fin m, (((S j).erase v).card - 1)) + 1 =
      ∑ j : Fin m, ((S j).card - 1) := by
  have hpoint (j : Fin m) :
      (((S j).erase v).card - 1) + (if j = i then 1 else 0) = (S j).card - 1 := by
    by_cases hji : j = i
    · subst j
      rw [Finset.card_erase_of_mem hv]
      simp only [ite_true]
      omega
    · rw [Finset.erase_eq_of_notMem (hprivate j hji)]
      simp [hji]
  have hh := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun j _ => hpoint j)
  simpa only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using hh

lemma erased_family_linear {n m : ℕ} (S : Fin m → Finset (Fin n))
    (hlin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1) (v : Fin n) :
    ∀ i j, i ≠ j → ((S i).erase v ∩ (S j).erase v).card ≤ 1 := by
  intro i j hij
  apply le_trans (Finset.card_le_card (Finset.inter_subset_inter
    (Finset.erase_subset v (S i)) (Finset.erase_subset v (S j))))
  exact hlin i j hij

end PEqualNP.Outside.L_meta_951
