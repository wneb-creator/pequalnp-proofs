
import PEqualNP.Defs

/-!
# Wire lemmas for the conditional assembly of the plane of order 2 (seat-pcx-2, leg light)

Facts about `Circuit.wires` used at the joints of the assembly: input wires read the input, a
wire past the list reads false, a gate wire is its operation on the wires before it, replacing a
gate by one computing the same function of the wires keeps every wire, and counts of two-wire
AND/OR gates. A copy of PlaneAsmWires that imports the definitions only, not the whole library,
so that its closure checks in less memory. Conjecture until checked.
-/

namespace PEqualNP.MetaComplexity.PlaneAsmLight

open PEqualNP.CircuitLowerBounds Classical

/-- One step of `Circuit.wires`. -/
def stepF (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_def (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.wires ⟨gs, o⟩ x = gs.foldl stepF x := rfl

theorem eval_def (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (gs.foldl stepF x).getD o false := rfl

theorem foldl_length (gs : List Gate) : ∀ w : List Bool,
    (gs.foldl stepF w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    simp [ih, stepF]
    omega

theorem foldl_getD_lt (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (gs.foldl stepF w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; simp
  | cons g gs ih =>
    intro w i hi
    simp only [List.foldl_cons]
    rw [ih _ i (by simp [stepF]; omega)]
    simp only [stepF, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left hi]

theorem foldl_getD_gate (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
    (gs.foldl stepF w).getD (w.length + k) false =
      (gs[k]).op.eval ((gs[k]).inputs.map fun i => ((gs.take k).foldl stepF w).getD i false) := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    simp
  conv_lhs => rw [hsplit]
  rw [List.foldl_append, List.foldl_cons]
  have hW : ((gs.take k).foldl stepF w).length = w.length + k := by
    rw [foldl_length]; simp; omega
  rw [foldl_getD_lt _ _ _ (by simp [stepF]; omega)]
  simp only [stepF, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by omega)]
  simp [hW]

theorem eval_input {n : ℕ} (gs : List Gate) (w : ℕ) (hw : w < n) (x : Fin n → Bool) :
    Circuit.eval ⟨gs, w⟩ (List.ofFn x) = x ⟨w, hw⟩ := by
  rw [eval_def, foldl_getD_lt _ _ _ (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

theorem eval_past {n : ℕ} (gs : List Gate) (w : ℕ) (hw : n + gs.length ≤ w)
    (x : Fin n → Bool) : Circuit.eval ⟨gs, w⟩ (List.ofFn x) = false := by
  rw [eval_def]
  apply List.getD_eq_default
  rw [foldl_length]; simpa using hw

/-- A gate wire: its operation on the wires before it, where an input wire reads the input. -/
theorem eval_gate {n : ℕ} (gs : List Gate) (k : ℕ) (hk : k < gs.length) (x : Fin n → Bool) :
    Circuit.eval ⟨gs, n + k⟩ (List.ofFn x) =
      (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
        ((gs.take k).foldl stepF (List.ofFn x)).getD i false) := by
  rw [eval_def]
  have := foldl_getD_gate gs (List.ofFn x) k hk
  simpa using this

theorem prefix_input {n : ℕ} (gs : List Gate) (i : ℕ) (hi : i < n) (x : Fin n → Bool) :
    (gs.foldl stepF (List.ofFn x)).getD i false = x ⟨i, hi⟩ := by
  rw [foldl_getD_lt _ _ _ (by simpa using hi)]
  simp [List.getD_eq_getElem?_getD, hi]

/-- An AND gate listing input `p` is false where `p` is false. -/
theorem eval_and_input_false {n : ℕ} (gs : List Gate) (k : ℕ) (hk : k < gs.length)
    (hand : (gs[k]).op = GateOp.and) (p : ℕ) (hp : p < n) (hpk : p ∈ (gs[k]).inputs)
    (x : Fin n → Bool) (hx : x ⟨p, hp⟩ = false) :
    Circuit.eval ⟨gs, n + k⟩ (List.ofFn x) = false := by
  rw [eval_gate gs k hk x, hand]
  simp only [GateOp.eval, List.all_eq_false]
  refine ⟨false, ?_, by simp⟩
  rw [List.mem_map]
  exact ⟨p, hpk, by rw [prefix_input _ p hp x, hx]⟩

/-- Two gates computing the same function of the wire list. -/
def Same (g g' : Gate) : Prop :=
  ∀ w : List Bool, g.op.eval (g.inputs.map fun i => w.getD i false) =
    g'.op.eval (g'.inputs.map fun i => w.getD i false)

theorem foldl_set_same : ∀ (l : List Gate) (i : ℕ) (g' : Gate),
    (∀ hi : i < l.length, Same l[i] g') → ∀ w : List Bool,
    (l.set i g').foldl stepF w = l.foldl stepF w := by
  intro l
  induction l with
  | nil => intro i g' _ w; simp
  | cons a l ih =>
    intro i g' h w
    cases i with
    | zero =>
      have hs := h (by simp)
      simp only [List.set_cons_zero, List.foldl_cons]
      congr 1
      have hw := hs w
      simp only [List.getElem_cons_zero] at hw
      simp only [stepF]
      rw [hw]
    | succ i =>
      simp only [List.set_cons_succ, List.foldl_cons]
      exact ih i g' (fun hi => h (by simp; omega)) _

/-- A NOT reading only its first listed wire. -/
noncomputable def normNot (g : Gate) : Gate :=
  if g.op = GateOp.not then ⟨GateOp.not, g.inputs.take 1⟩ else g

theorem same_normNot (g : Gate) : Same g (normNot g) := by
  intro w
  unfold normNot
  split_ifs with h
  · rw [h]
    simp only [GateOp.eval]
    cases g.inputs with
    | nil => simp
    | cons a t => simp
  · rfl

theorem normNot_op (g : Gate) : (normNot g).op = g.op := by
  unfold normNot; split_ifs with h <;> simp [h]

/-- The two-wire AND/OR predicate. -/
def Two (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2


/-- The set of two-wire AND/OR gates of a list. -/
noncomputable def twoSet (l : List Gate) : Finset (Fin l.length) :=
  Finset.univ.filter fun q => Two (l.get q)

theorem twoSet_sub (l : List Gate) (I : Finset (Fin l.length))
    (hI : ∀ q2 : Fin l.length, ((l.get q2).op = GateOp.and ∨ (l.get q2).op = GateOp.or) ∧
      (l.get q2).inputs.length = 2 → q2 ∈ I) : (twoSet l).card ≤ I.card := by
  apply Finset.card_le_card
  intro q hq
  unfold twoSet at hq
  rw [Finset.mem_filter] at hq
  exact hI q hq.2

theorem twoSet_cov (l : List Gate) : ∀ q2 : Fin l.length,
    ((l.get q2).op = GateOp.and ∨ (l.get q2).op = GateOp.or) ∧
      (l.get q2).inputs.length = 2 → q2 ∈ twoSet l := by
  intro q2 h
  unfold twoSet
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, h⟩

theorem twoSet_card_eq (l1 l2 : List Gate) (hl : l1.length = l2.length)
    (hiff : ∀ (q : ℕ) (h1 : q < l1.length) (h2 : q < l2.length), Two l1[q] ↔ Two l2[q]) :
    (twoSet l1).card = (twoSet l2).card := by
  apply Finset.card_bij' (fun q _ => Fin.cast hl q) (fun q _ => Fin.cast hl.symm q)
  · intro q hq
    unfold twoSet at hq ⊢
    rw [Finset.mem_filter] at hq ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    have := (hiff q.val q.isLt (by omega)).1 hq.2
    simpa using this
  · intro q hq
    unfold twoSet at hq ⊢
    rw [Finset.mem_filter] at hq ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    have := (hiff q.val (by omega) q.isLt).2 hq.2
    simpa using this
  · intro q _; rfl
  · intro q _; rfl

theorem twoSet_card_lt (l : List Gate) (q : Fin l.length) (hq : (l.get q).op = GateOp.not) :
    (twoSet l).card + 1 ≤ l.length := by
  have hsub : twoSet l ⊆ Finset.univ.erase q := by
    intro r hr
    unfold twoSet at hr
    rw [Finset.mem_filter] at hr
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ _⟩
    rintro rfl
    rcases hr.2.1 with h | h <;> rw [hq] at h <;> exact GateOp.noConfusion h
  have := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at this
  have hpos : 0 < l.length := Nat.lt_of_le_of_lt (Nat.zero_le _) q.isLt
  omega

/-- Index-wise op and listed-wire count from the two `map` equalities. -/
theorem get_key {l1 l2 : List Gate}
    (hop : l1.map Gate.op = l2.map Gate.op)
    (hlen : l1.map (fun g => g.inputs.length) = l2.map (fun h => h.inputs.length))
    (q : ℕ) (h1 : q < l1.length) (h2 : q < l2.length) :
    (l1[q]).op = (l2[q]).op ∧ (l1[q]).inputs.length = (l2[q]).inputs.length := by
  constructor
  · have := congrArg (fun l => l[q]?) hop
    simp only [List.getElem?_map, List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2,
      Option.map_some, Option.some.injEq] at this
    exact this
  · have := congrArg (fun l => l[q]?) hlen
    simp only [List.getElem?_map, List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2,
      Option.map_some, Option.some.injEq] at this
    exact this

theorem len_of_map {l1 l2 : List Gate} (hop : l1.map Gate.op = l2.map Gate.op) :
    l1.length = l2.length := by
  have := congrArg List.length hop
  simpa using this

end PEqualNP.MetaComplexity.PlaneAsmLight
