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
