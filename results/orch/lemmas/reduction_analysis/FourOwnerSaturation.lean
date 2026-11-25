import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_650_aux.SaturatedFamily

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

-- A family of zeros whose pairwise joins are true has at most 2 ^ r members when the circuit
-- has at most r real AND gates.
theorem bound {n : ℕ} {ι : Type} [DecidableEq ι] (Z : ι → Fin n → Bool) (o : ℕ) :
    ∀ (r : ℕ) (gs : List Gate),
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
      gs.countP realAnd ≤ r → ∀ S : Finset ι,
      (∀ s ∈ S, (gs.foldl stp (List.ofFn (Z s))).getD o false = false) →
      (∀ s ∈ S, ∀ t ∈ S, s ≠ t →
        (gs.foldl stp (List.ofFn (jn (Z s) (Z t)))).getD o false = true) →
      S.card ≤ 2 ^ r := by
  intro r
  induction r with
  | zero =>
    intro gs hm hc S hz hj
    have := bound0 Z o gs hm (by omega) S hz hj
    simpa using this
  | succ r ih =>
    intro gs hm hc S hz hj
    by_cases h0 : gs.countP realAnd = 0
    · have h1 := bound0 Z o gs hm h0 S hz hj
      have h2 : 1 ≤ 2 ^ (r + 1) := Nat.one_le_two_pow
      omega
    · have hex : ∃ g ∈ gs, realAnd g = true := by
        by_contra hno
        apply h0
        apply List.countP_eq_zero.mpr
        intro g hg hp
        exact hno ⟨g, hg, hp⟩
      obtain ⟨g, hg, hreal⟩ := hex
      obtain ⟨a, b, rfl⟩ := realAnd_spec g hreal
      obtain ⟨pre, post, rfl⟩ := List.append_of_mem hg
      have hpost : ∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or :=
        fun g hg' => (hm g (by simp [hg'])).1
      have hcount : ∀ c : ℕ, (pre ++ (⟨GateOp.and, [c]⟩ : Gate) :: post).countP realAnd ≤ r := by
        intro c
        have e1 : (pre ++ (⟨GateOp.and, [a, b]⟩ : Gate) :: post).countP realAnd
            = pre.countP realAnd + (post.countP realAnd + 1) := by
          rw [List.countP_append, List.countP_cons_of_pos (by simp [realAnd])]
        have e2 : (pre ++ (⟨GateOp.and, [c]⟩ : Gate) :: post).countP realAnd
            = pre.countP realAnd + post.countP realAnd := by
          rw [List.countP_append, List.countP_cons_of_neg (by simp [realAnd])]
        omega
      have hmono : ∀ c : ℕ, ∀ g ∈ pre ++ (⟨GateOp.and, [c]⟩ : Gate) :: post,
          (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
        intro c g hg'
        rcases List.mem_append.mp hg' with h | h
        · exact hm g (by simp [h])
        · rcases List.mem_cons.mp h with rfl | h
          · exact ⟨Or.inl rfl, by simp⟩
          · exact hm g (by simp [h])
      simp only [List.foldl_append, List.foldl_cons] at hz hj
      have ha := ih (pre ++ (⟨GateOp.and, [a]⟩ : Gate) :: post) (hmono a) (hcount a)
        (S.filter (fun s => (post.foldl stp (stp (pre.foldl stp (List.ofFn (Z s)))
          ⟨GateOp.and, [a]⟩)).getD o false = false))
        (by
          intro s hs
          simp only [List.foldl_append, List.foldl_cons]
          exact (Finset.mem_filter.mp hs).2)
        (by
          intro s hs t ht hne
          simp only [List.foldl_append, List.foldl_cons]
          exact (and_up _ a b o post hpost
            (hj s (Finset.mem_filter.mp hs).1 t (Finset.mem_filter.mp ht).1 hne)).1)
      have hb := ih (pre ++ (⟨GateOp.and, [b]⟩ : Gate) :: post) (hmono b) (hcount b)
        (S.filter (fun s => (post.foldl stp (stp (pre.foldl stp (List.ofFn (Z s)))
          ⟨GateOp.and, [b]⟩)).getD o false = false))
        (by
          intro s hs
          simp only [List.foldl_append, List.foldl_cons]
          exact (Finset.mem_filter.mp hs).2)
        (by
          intro s hs t ht hne
          simp only [List.foldl_append, List.foldl_cons]
          exact (and_up _ a b o post hpost
            (hj s (Finset.mem_filter.mp hs).1 t (Finset.mem_filter.mp ht).1 hne)).2)
      have hsub : S ⊆ S.filter (fun s => (post.foldl stp (stp (pre.foldl stp (List.ofFn (Z s)))
            ⟨GateOp.and, [a]⟩)).getD o false = false) ∪
          S.filter (fun s => (post.foldl stp (stp (pre.foldl stp (List.ofFn (Z s)))
            ⟨GateOp.and, [b]⟩)).getD o false = false) := by
        intro s hs
        rcases and_zero _ a b o post (hz s hs) with h | h
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hs, h⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hs, h⟩)
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_union_le
        (S.filter (fun s => (post.foldl stp (stp (pre.foldl stp (List.ofFn (Z s)))
          ⟨GateOp.and, [a]⟩)).getD o false = false))
        (S.filter (fun s => (post.foldl stp (stp (pre.foldl stp (List.ofFn (Z s)))
          ⟨GateOp.and, [b]⟩)).getD o false = false))
      have h3 : 2 ^ (r + 1) = 2 ^ r + 2 ^ r := by ring
      omega


-- The preceding reusable counting argument is copied from accepted L-meta-267.
-- Saturation forces a binary AND to have unequal operands on every family member.
theorem saturated_operands {n : ℕ} {ι : Type} [DecidableEq ι]
    (Z : ι → Fin n → Bool) (o r : ℕ) (pre post : List Gate) (a b : ℕ)
    (hm : ∀ g ∈ pre ++ (⟨GateOp.and, [a, b]⟩ : Gate) :: post,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hc : (pre ++ (⟨GateOp.and, [a, b]⟩ : Gate) :: post).countP realAnd ≤ r + 1)
    (S : Finset ι) (hcard : 2 ^ (r + 1) ≤ S.card)
    (hz : ∀ s ∈ S, ((pre ++ (⟨GateOp.and, [a, b]⟩ : Gate) :: post).foldl
      stp (List.ofFn (Z s))).getD o false = false)
    (hj : ∀ s ∈ S, ∀ t ∈ S, s ≠ t →
      ((pre ++ (⟨GateOp.and, [a, b]⟩ : Gate) :: post).foldl
        stp (List.ofFn (jn (Z s) (Z t)))).getD o false = true) :
    ∀ s ∈ S, (pre.foldl stp (List.ofFn (Z s))).getD a false ≠
      (pre.foldl stp (List.ofFn (Z s))).getD b false := by
  have hpost : ∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or :=
    fun g hg => (hm g (by simp [hg])).1
  have hcount : ∀ c : ℕ, (pre ++ (⟨GateOp.and, [c]⟩ : Gate) :: post).countP realAnd ≤ r := by
    intro c
    have e1 : (pre ++ (⟨GateOp.and, [a, b]⟩ : Gate) :: post).countP realAnd
        = pre.countP realAnd + (post.countP realAnd + 1) := by
      rw [List.countP_append, List.countP_cons_of_pos (by simp [realAnd])]
    have e2 : (pre ++ (⟨GateOp.and, [c]⟩ : Gate) :: post).countP realAnd
        = pre.countP realAnd + post.countP realAnd := by
      rw [List.countP_append, List.countP_cons_of_neg (by simp [realAnd])]
    omega
  have hmono : ∀ c : ℕ, ∀ g ∈ pre ++ (⟨GateOp.and, [c]⟩ : Gate) :: post,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro c g hg
    rcases List.mem_append.mp hg with h | h
    · exact hm g (by simp [h])
    · rcases List.mem_cons.mp h with rfl | h
      · exact ⟨Or.inl rfl, by simp⟩
      · exact hm g (by simp [h])
  simp only [List.foldl_append, List.foldl_cons] at hz hj
  let A := S.filter (fun s => (post.foldl stp (stp (pre.foldl stp (List.ofFn (Z s)))
    ⟨GateOp.and, [a]⟩)).getD o false = false)
  let B := S.filter (fun s => (post.foldl stp (stp (pre.foldl stp (List.ofFn (Z s)))
    ⟨GateOp.and, [b]⟩)).getD o false = false)
  have ha : A.card ≤ 2 ^ r := by
    apply bound Z o r (pre ++ (⟨GateOp.and, [a]⟩ : Gate) :: post) (hmono a) (hcount a) A
    · intro s hs
      simp only [List.foldl_append, List.foldl_cons]
      exact (Finset.mem_filter.mp hs).2
    · intro s hs t ht hne
      simp only [List.foldl_append, List.foldl_cons]
      exact (and_up _ a b o post hpost
        (hj s (Finset.mem_filter.mp hs).1 t (Finset.mem_filter.mp ht).1 hne)).1
  have hb : B.card ≤ 2 ^ r := by
    apply bound Z o r (pre ++ (⟨GateOp.and, [b]⟩ : Gate) :: post) (hmono b) (hcount b) B
    · intro s hs
      simp only [List.foldl_append, List.foldl_cons]
      exact (Finset.mem_filter.mp hs).2
    · intro s hs t ht hne
      simp only [List.foldl_append, List.foldl_cons]
      exact (and_up _ a b o post hpost
        (hj s (Finset.mem_filter.mp hs).1 t (Finset.mem_filter.mp ht).1 hne)).2
  have hsub : S ⊆ A ∪ B := by
    intro s hs
    rcases and_zero _ a b o post (hz s hs) with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hs, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hs, h⟩)
  have hunion := Finset.card_le_card hsub
  have hsum := Finset.card_union_add_card_inter A B
  have hp : 2 ^ (r + 1) = 2 ^ r + 2 ^ r := by ring
  intro s hs heq
  have ea : stp (pre.foldl stp (List.ofFn (Z s))) ⟨GateOp.and, [a]⟩ =
      stp (pre.foldl stp (List.ofFn (Z s))) ⟨GateOp.and, [a, b]⟩ := by
    simp only [stp, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
      List.all_nil, id_eq, Bool.and_true, heq, Bool.and_self]
  have eb : stp (pre.foldl stp (List.ofFn (Z s))) ⟨GateOp.and, [b]⟩ =
      stp (pre.foldl stp (List.ofFn (Z s))) ⟨GateOp.and, [a, b]⟩ := by
    simp only [stp, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
      List.all_nil, id_eq, Bool.and_true, heq, Bool.and_self]
  have hmem : s ∈ A ∩ B := by
    apply Finset.mem_inter.mpr
    constructor
    · apply Finset.mem_filter.mpr
      exact ⟨hs, by rw [ea]; exact hz s hs⟩
    · apply Finset.mem_filter.mpr
      exact ⟨hs, by rw [eb]; exact hz s hs⟩
  have hi : 0 < (A ∩ B).card := Finset.card_pos.mpr ⟨s, hmem⟩
  omega


def orEncode {m n : ℕ} (supports : Fin n → Finset (Fin m))
    (x : Fin m → Bool) : Fin n → Bool :=
  fun j => decide (∃ i ∈ supports j, x i = true)

theorem orEncode_join {m n : ℕ} (supports : Fin n → Finset (Fin m))
    (x y : Fin m → Bool) :
    orEncode supports (jn x y) = jn (orEncode supports x) (orEncode supports y) := by
  funext j
  apply Bool.eq_iff_iff.mpr
  simp only [orEncode, jn, decide_eq_true_eq, Bool.or_eq_true]
  aesop

theorem orEncode_mono {m n : ℕ} (supports : Fin n → Finset (Fin m))
    (x y : Fin m → Bool) (h : ∀ i, x i = true → y i = true) :
    ∀ j, orEncode supports x j = true → orEncode supports y j = true := by
  intro j hj
  simp only [orEncode, decide_eq_true_eq] at hj ⊢
  obtain ⟨i, hi, hx⟩ := hj
  exact ⟨i, hi, h i hx⟩

theorem ofFn_mono {n : ℕ} (x y : Fin n → Bool)
    (h : ∀ i, x i = true → y i = true) :
    ∀ i, (List.ofFn x).getD i false = true → (List.ofFn y).getD i false = true := by
  intro i hi
  by_cases hil : i < n
  · rw [getD_ofFn _ _ hil] at hi ⊢
    exact h ⟨i, hil⟩ hi
  · rw [getD_ge _ _ (by simp; omega)] at hi
    cases hi

-- A complete family of negatives upgrades saturation to soundness on all negatives.
theorem saturated_encoded_and_false {m n : ℕ} {ι : Type} [DecidableEq ι]
    (supports : Fin n → Finset (Fin m)) (f : (Fin m → Bool) → Bool)
    (C : Circuit) (hm : Monotone2 C)
    (heval : ∀ x, C.eval (List.ofFn (orEncode supports x)) = f x)
    (Z : ι → Fin m → Bool) (S : Finset ι) (r : ℕ)
    (hc : C.gates.countP realAnd ≤ r + 1) (hcard : 2 ^ (r + 1) ≤ S.card)
    (hz : ∀ s ∈ S, f (Z s) = false)
    (hj : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → f (jn (Z s) (Z t)) = true)
    (hcover : ∀ x, f x = false → ∃ s ∈ S, ∀ i, x i = true → Z s i = true)
    (pre post : List Gate) (a b : ℕ)
    (hg : C.gates = pre ++ (⟨GateOp.and, [a, b]⟩ : Gate) :: post)
    (x : Fin m → Bool) (hx : f x = false) :
    ((pre.foldl stp (List.ofFn (orEncode supports x))).getD a false &&
      (pre.foldl stp (List.ofFn (orEncode supports x))).getD b false) = false := by
  obtain ⟨s, hs, hxs⟩ := hcover x hx
  have hne := saturated_operands (fun s => orEncode supports (Z s)) C.output r
    pre post a b (by simpa [Monotone2, ← hg] using hm) (by simpa [← hg] using hc) S hcard
    (by
      intro t ht
      change (Circuit.mk (pre ++ (⟨GateOp.and, [a, b]⟩ : Gate) :: post) C.output).eval
        (List.ofFn (orEncode supports (Z t))) = false
      rw [← hg]
      exact (heval (Z t)).trans (hz t ht))
    (by
      intro t ht u hu htu
      rw [← orEncode_join]
      change (Circuit.mk (pre ++ (⟨GateOp.and, [a, b]⟩ : Gate) :: post) C.output).eval
        (List.ofFn (orEncode supports (jn (Z t) (Z u)))) = true
      rw [← hg]
      exact (heval (jn (Z t) (Z u))).trans (hj t ht u hu htu)) s hs
  have hpre : ∀ g ∈ pre, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hgp
    exact (hm g (by rw [hg]; simp [hgp])).1
  have hmono := mono_fold pre (List.ofFn (orEncode supports x))
    (List.ofFn (orEncode supports (Z s))) (by simp) hpre
    (ofFn_mono _ _ (orEncode_mono supports x (Z s) hxs))
  cases ha : (pre.foldl stp (List.ofFn (orEncode supports x))).getD a false <;>
    cases hb : (pre.foldl stp (List.ofFn (orEncode supports x))).getD b false
  · rfl
  · rfl
  · rfl
  · exact False.elim (hne ((hmono a ha).trans (hmono b hb).symm))

def bipartiteValue {p q : ℕ} (adj : Fin p → Fin q → Bool)
    (x : Fin (p + q) → Bool) : Bool :=
  decide (∃ i j, adj i j = true ∧ x (Fin.castAdd q i) = true ∧ x (Fin.natAdd p j) = true)

def maximalInput {p q : ℕ} (adj : Fin p → Fin q → Bool)
    (s : Fin p → Bool) : Fin (p + q) → Bool :=
  Fin.append s (fun j => decide (∀ i, s i = true → adj i j = false))

theorem maximalInput_false {p q : ℕ} (adj : Fin p → Fin q → Bool)
    (s : Fin p → Bool) : bipartiteValue adj (maximalInput adj s) = false := by
  simp only [bipartiteValue, decide_eq_false_iff_not]
  rintro ⟨i, j, ha, hi, hj⟩
  simp only [maximalInput, Fin.append_left] at hi
  simp only [maximalInput, Fin.append_right, decide_eq_true_eq] at hj
  have := hj i hi
  simp [ha] at this

theorem maximalInput_covers {p q : ℕ} (adj : Fin p → Fin q → Bool)
    (x : Fin (p + q) → Bool) (hx : bipartiteValue adj x = false) :
    ∀ k, x k = true → maximalInput adj (fun i => x (Fin.castAdd q i)) k = true := by
  have hno : ¬ ∃ i j, adj i j = true ∧ x (Fin.castAdd q i) = true ∧
      x (Fin.natAdd p j) = true := by simpa only [bipartiteValue, decide_eq_false_iff_not] using hx
  intro k
  refine Fin.addCases (fun i hi => ?_) (fun j hj => ?_) k
  · simpa only [maximalInput, Fin.append_left] using hi
  · simp only [maximalInput, Fin.append_right, decide_eq_true_eq]
    intro i hi
    cases ha : adj i j
    · rfl
    · exact False.elim (hno ⟨i, j, ha, hi, hj⟩)

theorem maximalInput_private {p q : ℕ} (adj : Fin p → Fin q → Bool)
    (privateLine : Fin p → Fin q)
    (hp : ∀ i j, adj i (privateLine j) = true ↔ i = j)
    (s : Fin p → Bool) (j : Fin p) (hj : s j = false) :
    maximalInput adj s (Fin.natAdd p (privateLine j)) = true := by
  simp only [maximalInput, Fin.append_right, decide_eq_true_eq]
  intro i hi
  cases ha : adj i (privateLine j)
  · rfl
  · have hij := (hp i j).mp ha
    subst i
    simp [hj] at hi

theorem maximalInput_pair_positive {p q : ℕ} (adj : Fin p → Fin q → Bool)
    (privateLine : Fin p → Fin q)
    (hp : ∀ i j, adj i (privateLine j) = true ↔ i = j)
    (s t : Fin p → Bool) (hne : s ≠ t) :
    bipartiteValue adj (jn (maximalInput adj s) (maximalInput adj t)) = true := by
  have hex : ∃ i, s i ≠ t i := by
    by_contra hn
    push Not at hn
    exact hne (funext hn)
  obtain ⟨i, hi⟩ := hex
  apply decide_eq_true_eq.mpr
  refine ⟨i, privateLine i, (hp i i).mpr rfl, ?_, ?_⟩
  · simp only [jn, maximalInput, Fin.append_left]
    cases hs : s i <;> cases ht : t i <;> simp_all
  · simp only [jn, Bool.or_eq_true]
    cases hs : s i <;> cases ht : t i
    · simp [hs, ht] at hi
    · exact Or.inl (maximalInput_private adj privateLine hp s i hs)
    · exact Or.inr (maximalInput_private adj privateLine hp t i ht)
    · simp [hs, ht] at hi

-- Exact raw graph of the compatible four-owner packet; line indices omit the four points.
def fourAdj (i : Fin 4) (j : Fin 10) : Bool :=
  decide ((i.val, j.val) ∈ ([(0,1),(0,0),(0,6),(0,2),
    (1,0),(1,4),(1,5),(1,7),(2,1),(2,3),(2,8),(2,5),
    (3,9),(3,3),(3,4),(3,2)] : List (ℕ × ℕ)))

def fourPrivate (i : Fin 4) : Fin 10 := ⟨i.val + 6, by omega⟩

theorem four_private : ∀ i j, fourAdj i (fourPrivate j) = true ↔ i = j := by decide

-- Every paid binary AND is graph-sound for an exact four-AND implementation,
-- irrespective of how many pure-OR free features are supplied.
theorem four_owner_and_sound {n : ℕ} (supports : Fin n → Finset (Fin 14))
    (C : Circuit) (hm : Monotone2 C)
    (heval : ∀ x, C.eval (List.ofFn (orEncode supports x)) = bipartiteValue fourAdj x)
    (hc : C.gates.countP realAnd ≤ 4)
    (pre post : List Gate) (a b : ℕ)
    (hg : C.gates = pre ++ (⟨GateOp.and, [a,b]⟩ : Gate) :: post)
    (x : Fin 14 → Bool) (hx : bipartiteValue fourAdj x = false) :
    ((pre.foldl stp (List.ofFn (orEncode supports x))).getD a false &&
      (pre.foldl stp (List.ofFn (orEncode supports x))).getD b false) = false := by
  apply saturated_encoded_and_false supports (bipartiteValue fourAdj) C hm heval
    (maximalInput fourAdj) Finset.univ 3 hc (by decide)
    (fun s _ => maximalInput_false fourAdj s)
    (fun s _ t _ h => maximalInput_pair_positive fourAdj fourPrivate four_private s t h)
    (fun x hx => ⟨fun i => x (Fin.castAdd 10 i), Finset.mem_univ _, maximalInput_covers fourAdj x hx⟩)
    pre post a b hg x hx

end PEqualNP.Outside.L_meta_650_aux.SaturatedFamily
