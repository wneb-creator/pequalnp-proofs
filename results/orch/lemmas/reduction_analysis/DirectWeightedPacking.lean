import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_650_aux.DirectWeightedPacking

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- One evaluation step: the gate adds one wire.
def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stp x := rfl

theorem getD_ge (W : List Bool) (i : ℕ) (h : W.length ≤ i) : W.getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

theorem getD_ofFn {m : ℕ} (x : Fin m → Bool) (i : ℕ) (h : i < m) :
    (List.ofFn x).getD i false = x ⟨i, h⟩ := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getD_app (W : List Bool) (v : Bool) (i : ℕ) :
    (W ++ [v]).getD i false
      = if i < W.length then W.getD i false else if i = W.length then v else false := by
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · subst h2
    simp [List.getD_eq_getElem?_getD]
  · exact getD_ge _ _ (by simp; omega)

-- The join of two inputs.
def jn {n : ℕ} (z z' : Fin n → Bool) : Fin n → Bool := fun i => z i || z' i

-- An AND gate that really reads two wires.
def realAnd (g : Gate) : Bool :=
  match g.op with
  | GateOp.and => decide (g.inputs.length = 2)
  | _ => false

theorem realAnd_spec (g : Gate) (h : realAnd g = true) : ∃ a b, g = ⟨GateOp.and, [a, b]⟩ := by
  obtain ⟨op, l⟩ := g
  cases op <;> simp [realAnd] at h
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp h
  exact ⟨a, b, rfl⟩

theorem eval_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (f f' : ℕ → Bool)
    (h : ∀ i, f i = true → f' i = true) :
    g.op.eval (g.inputs.map f) = true → g.op.eval (g.inputs.map f') = true := by
  rcases hg with e | e
  · rw [e]
    simp only [GateOp.eval]
    intro H
    rw [List.all_eq_true] at H ⊢
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact h i (H _ (List.mem_map.mpr ⟨i, hi, rfl⟩))
  · rw [e]
    simp only [GateOp.eval]
    intro H
    rw [List.any_eq_true] at H ⊢
    obtain ⟨b, hb, hbt⟩ := H
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact ⟨f' i, List.mem_map.mpr ⟨i, hi, rfl⟩, h i hbt⟩

-- Raising wire values never lowers a later wire of a circuit of AND and OR gates.
theorem mono_fold : ∀ (gs : List Gate) (W W' : List Bool), W.length = W'.length →
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    (∀ i, W.getD i false = true → W'.getD i false = true) →
    ∀ i, (gs.foldl stp W).getD i false = true → (gs.foldl stp W').getD i false = true := by
  intro gs
  induction gs with
  | nil => intro W W' _ _ h i; exact h i
  | cons g gs ih =>
    intro W W' hl hops h
    simp only [List.foldl_cons]
    apply ih (stp W g) (stp W' g) (by simp [stp, hl]) (fun g' hg' => hops g' (by simp [hg']))
    intro i
    simp only [stp]
    rw [getD_app, getD_app, ← hl]
    split_ifs
    · exact h i
    · exact eval_mono g (hops g (by simp)) _ _ h
    · exact id

theorem any_or (l : List ℕ) (f1 f2 : ℕ → Bool) :
    (l.map (fun i => f1 i || f2 i)).any id = ((l.map f1).any id || (l.map f2).any id) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.any_cons, ih, id]
    generalize (l.map f1).any id = X
    generalize (l.map f2).any id = Y
    cases f1 a <;> cases f2 a <;> cases X <;> cases Y <;> rfl

-- A gate that is not a real AND gate commutes with the join.
theorem eval_join (g : Gate) (hm : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hr : realAnd g = false) (f f1 f2 : ℕ → Bool) (h : ∀ i, f i = (f1 i || f2 i)) :
    g.op.eval (g.inputs.map f)
      = (g.op.eval (g.inputs.map f1) || g.op.eval (g.inputs.map f2)) := by
  have e : g.inputs.map f = g.inputs.map (fun i => f1 i || f2 i) :=
    List.map_congr_left (fun i _ => h i)
  rw [e]
  obtain ⟨op, l⟩ := g
  obtain ⟨hop, hlen⟩ := hm
  simp only at hop hlen
  rcases hop with rfl | rfl
  · rcases l with _ | ⟨i, _ | ⟨j, _ | ⟨k, l⟩⟩⟩
    · simp [GateOp.eval]
    · simp [GateOp.eval]
    · simp [realAnd] at hr
    · simp at hlen
  · simp only [GateOp.eval]
    exact any_or l f1 f2

theorem join_fold : ∀ (gs : List Gate) (W W1 W2 : List Bool), W.length = W1.length →
    W.length = W2.length →
    (∀ g ∈ gs, ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      realAnd g = false) →
    (∀ i, W.getD i false = (W1.getD i false || W2.getD i false)) →
    ∀ i, (gs.foldl stp W).getD i false
      = ((gs.foldl stp W1).getD i false || (gs.foldl stp W2).getD i false) := by
  intro gs
  induction gs with
  | nil => intro W W1 W2 _ _ _ h i; exact h i
  | cons g gs ih =>
    intro W W1 W2 hl1 hl2 hg h
    simp only [List.foldl_cons]
    apply ih (stp W g) (stp W1 g) (stp W2 g) (by simp [stp, hl1]) (by simp [stp, hl2])
      (fun g' hg' => hg g' (by simp [hg']))
    intro i
    simp only [stp]
    rw [getD_app, getD_app, getD_app, ← hl1, ← hl2]
    split_ifs
    · exact h i
    · exact eval_join g (hg g (by simp)).1 (hg g (by simp)).2 _ _ _ h
    · rfl

theorem ofFn_jn {n : ℕ} (z z' : Fin n → Bool) (i : ℕ) :
    (List.ofFn (jn z z')).getD i false
      = ((List.ofFn z).getD i false || (List.ofFn z').getD i false) := by
  by_cases h : i < n
  · rw [getD_ofFn _ i h, getD_ofFn _ i h, getD_ofFn _ i h]
    rfl
  · rw [getD_ge _ _ (by simp; omega), getD_ge _ _ (by simp; omega),
      getD_ge _ _ (by simp; omega)]
    rfl

-- Without a real AND gate the circuit commutes with joins, so at most one member of a
-- family of zeros with pairwise true joins exists.
theorem bound0 {n : ℕ} {ι : Type} [DecidableEq ι] (Z : ι → Fin n → Bool) (o : ℕ)
    (gs : List Gate)
    (hm : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (h0 : gs.countP realAnd = 0) (S : Finset ι)
    (hz : ∀ s ∈ S, (gs.foldl stp (List.ofFn (Z s))).getD o false = false)
    (hj : ∀ s ∈ S, ∀ t ∈ S, s ≠ t →
      (gs.foldl stp (List.ofFn (jn (Z s) (Z t)))).getD o false = true) :
    S.card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro s hs t ht
  by_contra hne
  have h1 := hj s hs t ht hne
  have hreal : ∀ g ∈ gs, realAnd g = false := by
    intro g hg
    have := List.countP_eq_zero.mp h0 g hg
    simpa using this
  rw [join_fold gs _ (List.ofFn (Z s)) (List.ofFn (Z t)) (by simp) (by simp)
    (fun g hg => ⟨hm g hg, hreal g hg⟩) (ofFn_jn (Z s) (Z t)) o, hz s hs, hz t ht] at h1
  simp at h1

-- Replacing a real AND gate by one of its two operands.
theorem and_zero (W : List Bool) (a b o : ℕ) (post : List Gate)
    (h : (post.foldl stp (stp W ⟨GateOp.and, [a, b]⟩)).getD o false = false) :
    (post.foldl stp (stp W ⟨GateOp.and, [a]⟩)).getD o false = false ∨
      (post.foldl stp (stp W ⟨GateOp.and, [b]⟩)).getD o false = false := by
  have e1 : stp W ⟨GateOp.and, [a, b]⟩ = W ++ [W.getD a false && W.getD b false] := by
    simp [stp, GateOp.eval]
  have e2 : stp W ⟨GateOp.and, [a]⟩ = W ++ [W.getD a false] := by simp [stp, GateOp.eval]
  have e3 : stp W ⟨GateOp.and, [b]⟩ = W ++ [W.getD b false] := by simp [stp, GateOp.eval]
  rw [e1] at h
  rw [e2, e3]
  cases ha : W.getD a false
  · rw [ha] at h
    exact Or.inl h
  · rw [ha] at h
    exact Or.inr h

theorem and_up (W : List Bool) (a b o : ℕ) (post : List Gate)
    (hops : ∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or)
    (h : (post.foldl stp (stp W ⟨GateOp.and, [a, b]⟩)).getD o false = true) :
    (post.foldl stp (stp W ⟨GateOp.and, [a]⟩)).getD o false = true ∧
      (post.foldl stp (stp W ⟨GateOp.and, [b]⟩)).getD o false = true := by
  have e1 : stp W ⟨GateOp.and, [a, b]⟩ = W ++ [W.getD a false && W.getD b false] := by
    simp [stp, GateOp.eval]
  have e2 : stp W ⟨GateOp.and, [a]⟩ = W ++ [W.getD a false] := by simp [stp, GateOp.eval]
  have e3 : stp W ⟨GateOp.and, [b]⟩ = W ++ [W.getD b false] := by simp [stp, GateOp.eval]
  rw [e1] at h
  rw [e2, e3]
  constructor
  · apply mono_fold post _ _ (by simp) hops _ o h
    intro i
    rw [getD_app, getD_app]
    split_ifs
    · exact id
    · intro hv
      rw [Bool.and_eq_true] at hv
      exact hv.1
    · exact id
  · apply mono_fold post _ _ (by simp) hops _ o h
    intro i
    rw [getD_app, getD_app]
    split_ifs
    · exact id
    · intro hv
      rw [Bool.and_eq_true] at hv
      exact hv.2
    · exact id


def joinW (W V : List Bool) : List Bool := List.zipWith (fun a b => a || b) W V

theorem joinW_length (W V : List Bool) (hl : W.length = V.length) :
    (joinW W V).length = W.length := by simp [joinW, hl]

theorem joinW_getD (W V : List Bool) (hl : W.length = V.length) (i : ℕ) :
    (joinW W V).getD i false = (W.getD i false || V.getD i false) := by
  induction W generalizing V i with
  | nil => cases V <;> simp_all [joinW]
  | cons a W ih =>
    cases V with
    | nil => simp at hl
    | cons b V =>
      cases i with
      | zero => rfl
      | succ i => exact ih V (by simpa using hl) i

theorem joinW_append (W V : List Bool) (hl : W.length = V.length) (a b : Bool) :
    joinW (W ++ [a]) (V ++ [b]) = joinW W V ++ [a || b] := by
  induction W generalizing V with
  | nil => cases V <;> simp_all [joinW]
  | cons x W ih =>
    cases V with
    | nil => simp at hl
    | cons y V =>
      simpa only [List.cons_append, joinW, List.zipWith_cons_cons] using
        (congrArg (List.cons (x || y)) (ih V (by simpa using hl)))

theorem joinW_step (g : Gate)
    (hm : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hr : realAnd g = false) (W V : List Bool) (hl : W.length = V.length) :
    joinW (stp W g) (stp V g) = stp (joinW W V) g := by
  unfold stp
  rw [joinW_append W V hl]
  congr 2
  exact (eval_join g hm hr _ _ _ (joinW_getD W V hl)).symm

def equalAnd (g : Gate) (W : List Bool) : Bool :=
  realAnd g && decide (W.getD (g.inputs.getD 0 0) false = W.getD (g.inputs.getD 1 0) false)

def wildcards : List Gate → List Bool → ℕ
  | [], _ => 0
  | g :: gs, W => wildcards gs (stp W g) + if equalAnd g W then 1 else 0

theorem chosen_left (W : List Bool) (a b : ℕ)
    (h : W.getD a false = false ∨ W.getD b false = true) :
    stp W ⟨GateOp.and, [a,b]⟩ = stp W ⟨GateOp.and, [a]⟩ := by
  simp only [stp, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
    List.all_nil, id_eq, Bool.and_true]
  cases ha : W.getD a false <;> cases hb : W.getD b false <;> simp_all

theorem chosen_right (W : List Bool) (a b : ℕ)
    (h : W.getD b false = false ∨ W.getD a false = true) :
    stp W ⟨GateOp.and, [a,b]⟩ = stp W ⟨GateOp.and, [b]⟩ := by
  simp only [stp, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
    List.all_nil, id_eq, Bool.and_true]
  cases ha : W.getD a false <;> cases hb : W.getD b false <;> simp_all

set_option maxHeartbeats 4000000 in
theorem weighted_bound {ι : Type} [DecidableEq ι] (gs : List Gate) :
    ∀ (Z : ι → List Bool) (o : ℕ),
    (∀ s t, (Z s).length = (Z t).length) →
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
    ∀ S : Finset ι,
    (∀ s ∈ S, (gs.foldl stp (Z s)).getD o false = false) →
    (∀ s ∈ S, ∀ t ∈ S, s ≠ t →
      (gs.foldl stp (joinW (Z s) (Z t))).getD o false = true) →
    (∑ s ∈ S, 2 ^ wildcards gs (Z s)) ≤ 2 ^ gs.countP realAnd := by
  induction gs with
  | nil =>
    intro Z o hl hm S hz hj
    have hcard : S.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro s hs t ht
      by_contra hne
      have hp := hj s hs t ht hne
      simp only [List.foldl_nil, joinW_getD _ _ (hl s t)] at hp
      have hs0 := hz s hs
      have ht0 := hz t ht
      simp only [List.foldl_nil] at hs0 ht0
      rw [hs0, ht0] at hp
      cases hp
    simpa [wildcards] using hcard
  | cons g gs ih =>
    intro Z o hl hm S hz hj
    have hg := hm g (by simp)
    have hmt : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 :=
      fun g hg => hm g (by simp [hg])
    simp only [List.foldl_cons] at hz hj
    by_cases hr : realAnd g = true
    · obtain ⟨a,b,rfl⟩ := realAnd_spec g hr
      let A := S.filter fun s => (Z s).getD a false = false ∨ (Z s).getD b false = true
      let B := S.filter fun s => (Z s).getD b false = false ∨ (Z s).getD a false = true
      let weight := fun s => 2 ^ wildcards gs (stp (Z s) ⟨GateOp.and, [a,b]⟩)
      have heqa : ∀ s ∈ A, stp (Z s) ⟨GateOp.and, [a,b]⟩ =
          stp (Z s) ⟨GateOp.and, [a]⟩ :=
        fun s hs => chosen_left (Z s) a b (Finset.mem_filter.mp hs).2
      have heqb : ∀ s ∈ B, stp (Z s) ⟨GateOp.and, [a,b]⟩ =
          stp (Z s) ⟨GateOp.and, [b]⟩ :=
        fun s hs => chosen_right (Z s) a b (Finset.mem_filter.mp hs).2
      have ha : (∑ s ∈ A, weight s) ≤ 2 ^ gs.countP realAnd := by
        have h := ih (fun s => stp (Z s) ⟨GateOp.and, [a]⟩) o
          (by intro s t; simp [stp, hl s t]) hmt A
          (by
            intro s hs
            rw [← heqa s hs]
            exact hz s (Finset.mem_filter.mp hs).1)
          (by
            intro s hs t ht hne
            rw [joinW_step _ ⟨Or.inl rfl, by simp⟩ (by simp [realAnd]) _ _ (hl s t)]
            exact (and_up _ a b o gs (fun g hg => (hmt g hg).1)
              (hj s (Finset.mem_filter.mp hs).1 t (Finset.mem_filter.mp ht).1 hne)).1)
        calc
          _ = ∑ s ∈ A, 2 ^ wildcards gs (stp (Z s) ⟨GateOp.and, [a]⟩) := by
            apply Finset.sum_congr rfl
            intro s hs
            exact congrArg (fun W => 2 ^ wildcards gs W) (heqa s hs)
          _ ≤ _ := h
      have hb : (∑ s ∈ B, weight s) ≤ 2 ^ gs.countP realAnd := by
        have h := ih (fun s => stp (Z s) ⟨GateOp.and, [b]⟩) o
          (by intro s t; simp [stp, hl s t]) hmt B
          (by
            intro s hs
            rw [← heqb s hs]
            exact hz s (Finset.mem_filter.mp hs).1)
          (by
            intro s hs t ht hne
            rw [joinW_step _ ⟨Or.inl rfl, by simp⟩ (by simp [realAnd]) _ _ (hl s t)]
            exact (and_up _ a b o gs (fun g hg => (hmt g hg).1)
              (hj s (Finset.mem_filter.mp hs).1 t (Finset.mem_filter.mp ht).1 hne)).2)
        calc
          _ = ∑ s ∈ B, 2 ^ wildcards gs (stp (Z s) ⟨GateOp.and, [b]⟩) := by
            apply Finset.sum_congr rfl
            intro s hs
            exact congrArg (fun W => 2 ^ wildcards gs W) (heqb s hs)
          _ ≤ _ := h
      have hsum : (∑ s ∈ S, 2 ^ wildcards (⟨GateOp.and, [a,b]⟩ :: gs) (Z s)) =
          (∑ s ∈ A, weight s) + (∑ s ∈ B, weight s) := by
        simp only [A, B, Finset.sum_filter, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro s hs
        have heq : equalAnd ⟨GateOp.and, [a,b]⟩ (Z s) =
            decide ((Z s).getD a false = (Z s).getD b false) := rfl
        simp only [wildcards, heq, decide_eq_true_eq]
        cases ha : (Z s).getD a false <;> cases hb : (Z s).getD b false <;>
          simp [ha, hb, weight, pow_succ, Nat.mul_two]
      rw [hsum, List.countP_cons_of_pos hr, pow_succ, Nat.mul_two]
      omega
    · have hrf : realAnd g = false := by cases h : realAnd g <;> simp_all
      have h := ih (fun s => stp (Z s) g) o
        (by intro s t; simp [stp, hl s t]) hmt S hz
        (by
          intro s hs t ht hne
          rw [joinW_step g hg hrf _ _ (hl s t)]
          exact hj s hs t ht hne)
      simpa [wildcards, equalAnd, hrf, List.countP_cons_of_neg hr] using h

theorem weighted_rejected_family {ι : Type} [DecidableEq ι]
    (C : Circuit) (hm : Monotone2 C) (Z : ι → List Bool)
    (hl : ∀ s t, (Z s).length = (Z t).length) (S : Finset ι)
    (hz : ∀ s ∈ S, C.eval (Z s) = false)
    (hj : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → C.eval (joinW (Z s) (Z t)) = true) :
    (∑ s ∈ S, 2 ^ wildcards C.gates (Z s)) ≤ 2 ^ C.gates.countP realAnd :=
  weighted_bound C.gates Z C.output hl (by simpa [Monotone2] using hm) S hz hj

end PEqualNP.Outside.L_meta_650_aux.DirectWeightedPacking
