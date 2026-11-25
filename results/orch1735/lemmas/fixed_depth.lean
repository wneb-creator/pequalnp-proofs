import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1735_aux.FixedDepth

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
open PEqualNP.TopForm PEqualNP.CleanedNonEdge

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

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

lemma pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
  simp [pairInput]

lemma graphFun_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, pairInput_true]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro h
    exact ⟨u, v, h, Or.inl rfl, Or.inr rfl⟩

lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
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
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
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
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
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

lemma no4 {n : ℕ} (G : SimpleGraph (Fin n))
    (hg : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length)
    (a b c d : Fin n) (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (hac : a ≠ c) (hbd : b ≠ d) : False := by
  have e1 := G.ne_of_adj hab
  have e2 := G.ne_of_adj hbc
  have e3 := G.ne_of_adj hcd
  have e4 := G.ne_of_adj hda
  have hcyc : (SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc
      (SimpleGraph.Walk.cons hcd (SimpleGraph.Walk.cons hda SimpleGraph.Walk.nil)))).IsCycle := by
    rw [SimpleGraph.Walk.cons_isCycle_iff]
    refine ⟨?_, ?_⟩
    · simp [SimpleGraph.Walk.cons_isPath_iff, e2, e3, e4, hbd, Ne.symm e1, Ne.symm hac]
    · simp [e1, e2, hac, hbd, Ne.symm e1, Ne.symm e4]
  have h5 := hg a _ hcyc
  simp at h5

-- A certificate and a context are compatible when no edge runs between them.
def Apart {V : Type*} (E : V → V → Prop) (A B : Finset V) : Prop :=
  ∀ a ∈ A, ∀ b ∈ B, ¬ E a b

lemma apart_symm {V : Type*} {E : V → V → Prop} (hs : ∀ a b, E a b → E b a)
    {A B : Finset V} (h : Apart E A B) : Apart E B A :=
  fun b hb a ha hba => h a ha b hb (hs _ _ hba)

lemma apart_union_right {V : Type*} [DecidableEq V] {E : V → V → Prop}
    {A B D : Finset V} : Apart E A (B ∪ D) ↔ Apart E A B ∧ Apart E A D := by
  constructor
  · intro h
    exact ⟨fun x hx y hy => h x hx y (Finset.mem_union_left _ hy),
      fun x hx y hy => h x hx y (Finset.mem_union_right _ hy)⟩
  · rintro ⟨h₁, h₂⟩ x hx y hy
    exact (Finset.mem_union.mp hy).elim (h₁ x hx y) (h₂ x hx y)

lemma apart_union_left {V : Type*} [DecidableEq V] {E : V → V → Prop}
    {A B D : Finset V} : Apart E (A ∪ B) D ↔ Apart E A D ∧ Apart E B D := by
  constructor
  · intro h
    exact ⟨fun x hx => h x (Finset.mem_union_left _ hx),
      fun x hx => h x (Finset.mem_union_right _ hx)⟩
  · rintro ⟨h₁, h₂⟩ x hx
    exact (Finset.mem_union.mp hx).elim (h₁ x) (h₂ x)

lemma union_bound {I V : Type*} [DecidableEq V] (A : Finset I) (F : I → Finset V)
    (b : ℕ) (h : ∀ i ∈ A, (F i).card ≤ b) : (A.biUnion F).card ≤ A.card * b := by
  calc
    _ ≤ ∑ i ∈ A, (F i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ A, b := Finset.sum_le_sum h
    _ = _ := by simp

def vertices {V : Type*} [DecidableEq V] (A : Finset (Finset V)) : Finset V :=
  A.biUnion id

lemma vertices_bound {V : Type*} [DecidableEq V] (A : Finset (Finset V)) (t : ℕ)
    (h : ∀ W ∈ A, W.card ≤ t) : (vertices A).card ≤ A.card * t :=
  union_bound A id t h

lemma subset_vertices {V : Type*} [DecidableEq V] {A : Finset (Finset V)} {W : Finset V}
    (h : W ∈ A) : W ⊆ vertices A :=
  fun _ hw => Finset.mem_biUnion.mpr ⟨W, h, hw⟩

def common {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (a b : Fin n) :=
  Finset.univ.filter fun z => G.Adj a z ∧ G.Adj b z

def Rep {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ)
    (A R : Finset (Finset (Fin n))) : Prop :=
  R ⊆ A ∧ ∀ S : Finset (Fin n), S.card ≤ k →
    ∀ W ∈ A, Apart G.Adj W S → ∃ Z ∈ R, Apart G.Adj Z S

def budget (t : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => 1 + t * (budget t k + (budget t k * t) * budget t k)

-- Each context vertex blocking the seed hits one of its at most t vertices.
-- The remaining k vertices can be handled recursively. A second contact pins
-- the blocker to the unique common neighbour of two different vertices.
lemma representatives {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (t k : ℕ) (A : Finset (Finset (Fin n)))
    (hA : ∀ W ∈ A, W.card ≤ t) :
    ∃ R, Rep G k A R ∧ R.card ≤ budget t k := by
  classical
  induction k generalizing A with
  | zero =>
    by_cases h : A.Nonempty
    · obtain ⟨W, hW⟩ := h
      refine ⟨{W}, ⟨Finset.singleton_subset_iff.mpr hW, ?_⟩, by simp [budget]⟩
      intro S hS _ _ _
      have hs : S = ∅ := Finset.card_eq_zero.mp (by omega)
      exact ⟨W, by simp, by subst S; simp [Apart]⟩
    · exact ⟨∅, ⟨Finset.empty_subset _, fun _ _ W hW => (h ⟨W, hW⟩).elim⟩, by simp⟩
  | succ k ih =>
    by_cases h : A.Nonempty
    · obtain ⟨W₀, h₀⟩ := h
      let F (a : Fin n) := A.filter (fun W => a ∉ W)
      let H (b : Fin n) := A.filter (fun W => ∀ w ∈ W, ¬ G.Adj w b)
      have exF (a : Fin n) := ih (F a) (fun W hW => hA W (Finset.mem_filter.mp hW).1)
      have exH (b : Fin n) := ih (H b) (fun W hW => hA W (Finset.mem_filter.mp hW).1)
      choose R hR rBound using exF
      choose T hT tBound using exH
      let B (a : Fin n) := (vertices (R a)).biUnion (common G a)
      have bBound (a : Fin n) : (B a).card ≤ budget t k * t := by
        have ha (w : Fin n) (hw : w ∈ vertices (R a)) : a ≠ w := by
          obtain ⟨W, hW, hw⟩ := Finset.mem_biUnion.mp hw
          exact fun heq => (Finset.mem_filter.mp ((hR a).1 hW)).2 (heq ▸ hw)
        calc
          _ ≤ (vertices (R a)).card * 1 := union_bound _ _ _ (fun w hw => h4 a w (ha w hw))
          _ ≤ (R a).card * t := by
            rw [Nat.mul_one]
            exact vertices_bound _ _ (fun W hW => hA W (Finset.mem_filter.mp ((hR a).1 hW)).1)
          _ ≤ _ := Nat.mul_le_mul_right _ (rBound a)
      let P (a : Fin n) := R a ∪ (B a).biUnion T
      let Q := insert W₀ (W₀.biUnion P)
      refine ⟨Q, ⟨?_, ?_⟩, ?_⟩
      · intro W hW
        rcases Finset.mem_insert.mp hW with rfl | hw
        · exact h₀
        obtain ⟨a, _, ha⟩ := Finset.mem_biUnion.mp hw
        rcases Finset.mem_union.mp ha with hr | ht
        · exact (Finset.mem_filter.mp ((hR a).1 hr)).1
        obtain ⟨b, _, hb⟩ := Finset.mem_biUnion.mp ht
        exact (Finset.mem_filter.mp ((hT b).1 hb)).1
      · intro S hS W hW hwS
        by_cases good : Apart G.Adj W₀ S
        · exact ⟨W₀, Finset.mem_insert_self .., good⟩
        simp only [Apart, not_forall, Classical.not_not] at good
        obtain ⟨a, ha, b, hb, hab⟩ := good
        have hs : (S.erase b).card ≤ k := by rw [Finset.card_erase_of_mem hb]; omega
        have hwS' : Apart G.Adj W (S.erase b) :=
          fun w hw z hz => hwS w hw z (Finset.mem_of_mem_erase hz)
        have combine (Z : Finset (Fin n)) (hZ : Z ∈ P a)
            (hz : Apart G.Adj Z (S.erase b)) (hzb : ∀ w ∈ Z, ¬ G.Adj w b) :
            ∃ X ∈ Q, Apart G.Adj X S := by
          refine ⟨Z, Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨a, ha, hZ⟩), ?_⟩
          intro w hw z hzS
          by_cases h : z = b
          · subst z; exact hzb w hw
          · exact hz w hw z (Finset.mem_erase.mpr ⟨h, hzS⟩)
        by_cases hB : b ∈ B a
        · have hwH : W ∈ H b := Finset.mem_filter.mpr ⟨hW, fun w hw => hwS w hw b hb⟩
          obtain ⟨Z, hZ, hz⟩ := (hT b).2 _ hs W hwH hwS'
          exact combine Z (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨b, hB, hZ⟩)) hz
            (Finset.mem_filter.mp ((hT b).1 hZ)).2
        · have hwF : W ∈ F a := Finset.mem_filter.mpr ⟨hW, fun haw => hwS a haw b hb hab⟩
          obtain ⟨Z, hZ, hz⟩ := (hR a).2 _ hs W hwF hwS'
          refine combine Z (Finset.mem_union_left _ hZ) hz ?_
          intro w hw hwb
          exact hB (Finset.mem_biUnion.mpr ⟨w, subset_vertices hZ hw,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab, hwb⟩⟩)
      · have pBound (a : Fin n) : (P a).card ≤ budget t k + (budget t k * t) * budget t k :=
          (Finset.card_union_le ..).trans (Nat.add_le_add (rBound a)
            ((union_bound _ T _ (fun b _ => tBound b)).trans (Nat.mul_le_mul_right _ (bBound a))))
        calc
          Q.card ≤ (W₀.biUnion P).card + 1 := Finset.card_insert_le ..
          _ ≤ W₀.card * _ + 1 := Nat.add_le_add_right (union_bound _ _ _ (fun a _ => pBound a)) _
          _ ≤ t * _ + 1 := Nat.add_le_add_right (Nat.mul_le_mul_right _ (hA W₀ h₀)) _
          _ = _ := Nat.add_comm ..
    · exact ⟨∅, ⟨Finset.empty_subset _, fun _ _ W hW => (h ⟨W, hW⟩).elim⟩, by simp⟩

-- Delete the tested edge. Its two endpoints now form an independent input.
def away {n : ℕ} (G : SimpleGraph (Fin n)) (e : Sym2 (Fin n)) (a b : Fin n) : Prop :=
  G.Adj a b ∧ s(a, b) ≠ e

lemma away_symm {n : ℕ} {G : SimpleGraph (Fin n)} {e : Sym2 (Fin n)}
    (a b : Fin n) (h : away G e a b) : away G e b a :=
  ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩

lemma pair_apart {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
    Apart (away G s(u, v)) {u, v} {u, v} := by
  intro a ha b hb h
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact G.irrefl h.1
  · exact h.2 rfl
  · exact h.2 (Sym2.eq_swap ..)
  · exact G.irrefl h.1

lemma apart_weaken {n : ℕ} {G : SimpleGraph (Fin n)} {A B : Finset (Fin n)}
    (h : Apart G.Adj A B) (e : Sym2 (Fin n)) : Apart (away G e) A B :=
  fun x hx y hy hxy => h x hx y hy hxy.1

def doubleNbr {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D : Finset (Fin n)) :=
  D.biUnion fun a => D.biUnion fun b => if a = b then ∅ else common G a b

def charge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D : Finset (Fin n)) :=
  (D ×ˢ (D ∪ doubleNbr G D)).image fun p => s(p.1, p.2)

lemma charge_mem {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {D : Finset (Fin n)}
    {a b : Fin n} (ha : a ∈ D) (hb : b ∈ D ∪ doubleNbr G D) : s(a, b) ∈ charge G D :=
  Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩

lemma charge_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (h4 : NoFourCycle G)
    (D : Finset (Fin n)) (d : ℕ) (hD : D.card ≤ d) : (charge G D).card ≤ d * (d + d * d) := by
  have hDouble : (doubleNbr G D).card ≤ d * d := by
    refine (union_bound D _ d ?_).trans (Nat.mul_le_mul_right _ hD)
    intro a _
    refine (union_bound D _ 1 ?_).trans (by simpa using hD)
    intro b _
    split_ifs with h
    · simp
    · exact h4 a b h
  calc
    _ ≤ (D ×ˢ (D ∪ doubleNbr G D)).card := Finset.card_image_le
    _ = D.card * (D ∪ doubleNbr G D).card := Finset.card_product ..
    _ ≤ _ := Nat.mul_le_mul hD ((Finset.card_union_le ..).trans (Nat.add_le_add hD hDouble))

lemma recover_independent {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {D W : Finset (Fin n)} {e : Sym2 (Fin n)} (he : e ∉ charge G D) (hw : W ⊆ D)
    (h : Apart (away G e) W W) : Apart G.Adj W W := by
  intro a ha b hb hab
  apply h a ha b hb
  exact ⟨hab, fun eq => he (eq ▸ charge_mem (hw ha) (Finset.mem_union_left _ (hw hb)))⟩

-- An outer context vertex with a unique contact in D can simply be
-- omitted when that contact is deleted. Two contacts put it in doubleNbr.
lemma transfer_rep {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {D : Finset (Fin n)} {e : Sym2 (Fin n)} (he : e ∉ charge G D)
    {A R : Finset (Finset (Fin n))} {k : ℕ} (hr : Rep G k A R)
    (hD : ∀ W ∈ A, W ⊆ D) {S : Finset (Fin n)} (hs : S.card ≤ k)
    {W : Finset (Fin n)} (hw : W ∈ A) (h : Apart (away G e) W S) :
    ∃ Z ∈ R, Apart (away G e) Z S := by
  classical
  let T := S.filter (fun b => ¬ ∃ a ∈ D, G.Adj a b ∧ s(a, b) = e)
  have hT : Apart G.Adj W T := by
    intro a ha b hb hab
    obtain ⟨hbs, hn⟩ := Finset.mem_filter.mp hb
    exact h a ha b hbs ⟨hab, fun eq => hn ⟨a, hD W hw ha, hab, eq⟩⟩
  obtain ⟨Z, hZ, hz⟩ := hr.2 T ((Finset.card_filter_le ..).trans hs) W hw hT
  refine ⟨Z, hZ, ?_⟩
  intro z hzin b hb hzb
  by_cases hbt : b ∈ T
  · exact hz z hzin b hbt hzb.1
  have hh : ∃ a ∈ D, G.Adj a b ∧ s(a, b) = e := by
    by_contra hn
    exact hbt (Finset.mem_filter.mpr ⟨hb, hn⟩)
  obtain ⟨a, ha, hab, eq⟩ := hh
  have hne : a ≠ z := fun az => hzb.2 (az ▸ eq)
  have hzD := hD Z (hr.1 hZ) hzin
  have hbD : b ∈ doubleNbr G D := by
    refine Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_biUnion.mpr ⟨z, hzD, ?_⟩⟩
    rw [ite_eq_right hne]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab, hzb.1⟩
  exact he (eq ▸ charge_mem ha (Finset.mem_union_right _ hbD))

-- A numerical certificate bounds the number of AND layers on every path.
def DepthCertificate (n : ℕ) (C : Circuit) (D : ℕ) (r : ℕ → ℕ) : Prop :=
  (∀ w < n + C.gates.length, r w ≤ D) ∧
  (∀ j < C.gates.length, ∀ w ∈ (gateAt C j).inputs, r w ≤ r (n + j)) ∧
  (∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
    ∀ w ∈ (gateAt C j).inputs, r w < r (n + j))

def fires {n : ℕ} (C : Circuit) (w : ℕ) (x : Fin n → Bool) : Prop :=
  val C (List.ofFn x) w = true

lemma fires_input {n : ℕ} (C : Circuit) (i : Fin n) (x : Fin n → Bool) :
    fires C i x ↔ x i = true := by
  unfold fires
  rw [val_input (n := n) (by simp) i.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma fires_gate {n : ℕ} (C : Circuit) {j p q : ℕ} (hj : j < C.gates.length)
    (hin : (gateAt C j).inputs = [p, q]) (hp : p < n + j) (hq : q < n + j)
    (x : Fin n → Bool) :
    ((gateAt C j).op = GateOp.and → (fires C (n + j) x ↔ fires C p x ∧ fires C q x)) ∧
    ((gateAt C j).op = GateOp.or → (fires C (n + j) x ↔ fires C p x ∨ fires C q x)) := by
  unfold fires
  rw [val_gate (n := n) (by simp) hj, hin]
  constructor <;> intro hop <;> simp [hop, hp, hq, GateOp.eval]

def witnessBound (D : ℕ) := 2 ^ D

def contextStep (D : ℕ) := 2 ^ (D + 1)

def contextBound (D : ℕ) := contextStep D * D

def repLimit (D : ℕ) := budget (witnessBound D) (contextBound D)

def gateBound (D : ℕ) :=
  let d := contextStep D * repLimit D
  d * (d + d * d)

lemma contextStep_eq (D : ℕ) : contextStep D = 2 * witnessBound D := by
  simp [contextStep, witnessBound, pow_succ, Nat.mul_comm]

lemma contextStep_two (D : ℕ) : 2 ≤ contextStep D := by
  have hp : 1 ≤ 2 ^ D := Nat.one_le_pow D 2 (by decide)
  rw [contextStep_eq]
  unfold witnessBound
  omega

lemma witness_le_step (D : ℕ) : witnessBound D ≤ contextStep D := by
  rw [contextStep_eq]
  omega

lemma context_slack {D a d s t : ℕ} (ha : a < d)
    (hs : s + contextStep D * d ≤ contextBound D)
    (ht : t ≤ contextStep D) :
    s + t + contextStep D * a ≤ contextBound D := by
  have hm : contextStep D * (a + 1) ≤ contextStep D * d :=
    Nat.mul_le_mul_left _ (by omega)
  rw [Nat.mul_add, Nat.mul_one] at hm
  omega

def Forces {n : ℕ} (C : Circuit) (w : ℕ) (W : Finset (Fin n)) : Prop :=
  ∀ x : Fin n → Bool, (∀ v ∈ W, x v = true) → fires C w x

def Facts {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) (w d : ℕ)
    (R : Finset (Finset (Fin n))) : Prop :=
  ∀ W ∈ R, W.card ≤ 2 ^ d ∧ Apart G.Adj W W ∧ Forces C w W

-- A wire of rank d leaves room for contextStep D extra context vertices at each
-- lower AND layer. The graph in this invariant has the tested edge removed.
def Catches (D : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) (w d : ℕ)
    (B : Finset (Sym2 (Fin n))) (R : Finset (Finset (Fin n))) : Prop :=
  ∀ u v : Fin n, s(u, v) ∉ B → fires C w (pairInput u v) →
    ∀ S : Finset (Fin n), S.card + contextStep D * d ≤ contextBound D → Apart (away G s(u, v)) {u, v} S →
      ∃ W ∈ R, Apart (away G s(u, v)) W S

def Summary (D : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) (w d : ℕ)
    (B : Finset (Sym2 (Fin n))) (R : Finset (Finset (Fin n))) : Prop :=
  R.card ≤ repLimit D ∧ Facts G C w d R ∧ Catches D G C w d B R

lemma small_power {D d : ℕ} (hd : d ≤ D) : 2 ^ d ≤ witnessBound D :=
  Nat.pow_le_pow_right (by decide) hd

lemma summary_mono {D n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit} {w d : ℕ}
    {B B' : Finset (Sym2 (Fin n))} {R : Finset (Finset (Fin n))}
    (h : Summary D G C w d B R) (hsub : B ⊆ B') : Summary D G C w d B' R :=
  ⟨h.1, h.2.1, fun u v he => h.2.2 u v (fun hin => he (hsub hin))⟩

lemma input_summary (D : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) (i : Fin n)
    (d : ℕ) (B : Finset (Sym2 (Fin n))) : Summary D G C i d B {{i}} := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.card_singleton]
    unfold repLimit
    cases contextBound D <;> simp [budget]
  · intro W hW
    obtain rfl := Finset.mem_singleton.mp hW
    refine ⟨by simpa using (Nat.one_le_pow d 2 (by decide)), ?_, ?_⟩
    · intro a ha b hb
      obtain rfl := Finset.mem_singleton.mp ha
      obtain rfl := Finset.mem_singleton.mp hb
      exact G.irrefl
    · intro x hx
      exact (fires_input ..).mpr (hx _ (Finset.mem_singleton_self _))
  · intro u v _ hx S _ hS
    obtain hu | hv := (pairInput_true ..).mp ((fires_input ..).mp hx)
    · exact ⟨{i}, by simp, fun a ha => hS a (by simp [Finset.mem_singleton.mp ha, hu])⟩
    · exact ⟨{i}, by simp, fun a ha => hS a (by simp [Finset.mem_singleton.mp ha, hv])⟩

lemma compress (L : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (h4 : NoFourCycle G)
    (C : Circuit) {w d : ℕ} (hd : d ≤ L) {D : Finset (Fin n)} {A : Finset (Finset (Fin n))}
    {B : Finset (Sym2 (Fin n))} (hD : ∀ W ∈ A, W ⊆ D) (hc : charge G D ⊆ B)
    (hf : Facts G C w d A) (ht : Catches L G C w d B A) :
    ∃ R, Summary L G C w d B R := by
  obtain ⟨R, hr, hb⟩ := representatives G h4 (witnessBound L) (contextBound L) A (fun W hW => (hf W hW).1.trans (small_power hd))
  refine ⟨R, hb, fun W hW => hf W (hr.1 hW), ?_⟩
  intro u v he hfire S hs hS
  obtain ⟨W, hW, hwS⟩ := ht u v he hfire S hs hS
  exact transfer_rep G (fun h => he (hc h)) hr hD (by omega) hW hwS

lemma or_summary (L : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (h4 : NoFourCycle G)
    (C : Circuit) {p q w dp dq d : ℕ} (hd : d ≤ L) (hp : dp ≤ d) (hq : dq ≤ d)
    (sem : ∀ x : Fin n → Bool, fires C w x ↔ fires C p x ∨ fires C q x)
    {B : Finset (Sym2 (Fin n))} {P Q : Finset (Finset (Fin n))}
    (hP : Summary L G C p dp B P) (hQ : Summary L G C q dq B Q) :
    ∃ R, Summary L G C w d (B ∪ charge G (vertices P ∪ vertices Q)) R := by
  let D := vertices P ∪ vertices Q
  apply compress L G h4 C hd (D := D) (A := P ∪ Q) _ (Finset.subset_union_right)
  · intro W hW
    rcases Finset.mem_union.mp hW with h | h
    · obtain ⟨hw, hi, hf⟩ := hP.2.1 W h
      exact ⟨hw.trans (Nat.pow_le_pow_right (by decide) hp), hi,
        fun x hx => (sem x).mpr (Or.inl (hf x hx))⟩
    · obtain ⟨hw, hi, hf⟩ := hQ.2.1 W h
      exact ⟨hw.trans (Nat.pow_le_pow_right (by decide) hq), hi,
        fun x hx => (sem x).mpr (Or.inr (hf x hx))⟩
  · intro u v he hx S hs hS
    have he' : s(u, v) ∉ B := fun h => he (Finset.mem_union_left _ h)
    rcases (sem _).mp hx with h | h
    · obtain ⟨W, hw, ha⟩ := hP.2.2 u v he' h S (by have hm := Nat.mul_le_mul_left (contextStep L) hp; omega) hS
      exact ⟨W, Finset.mem_union_left _ hw, ha⟩
    · obtain ⟨W, hw, ha⟩ := hQ.2.2 u v he' h S (by have hm := Nat.mul_le_mul_left (contextStep L) hq; omega) hS
      exact ⟨W, Finset.mem_union_right _ hw, ha⟩
  · intro W hW
    rcases Finset.mem_union.mp hW with h | h
    · exact (subset_vertices h).trans Finset.subset_union_left
    · exact (subset_vertices h).trans Finset.subset_union_right

lemma add_powers {a b d : ℕ} (ha : a < d) (hb : b < d) : 2 ^ a + 2 ^ b ≤ 2 ^ d := by
  cases d with
  | zero => omega
  | succ k =>
    rw [pow_succ, Nat.mul_two]
    exact Nat.add_le_add (Nat.pow_le_pow_right (by decide) (by omega))
      (Nat.pow_le_pow_right (by decide) (by omega))

lemma and_summary (L : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (h4 : NoFourCycle G)
    (C : Circuit) {p q w dp dq d : ℕ} (hd : d ≤ L) (hp : dp < d) (hq : dq < d)
    (sem : ∀ x : Fin n → Bool, fires C w x ↔ fires C p x ∧ fires C q x)
    {B : Finset (Sym2 (Fin n))} {P Q : Finset (Finset (Fin n))}
    (hP : Summary L G C p dp B P) (hQ : Summary L G C q dq B Q) :
    ∃ R, Summary L G C w d (B ∪ charge G (vertices P ∪ vertices Q)) R := by
  classical
  let D := vertices P ∪ vertices Q
  let raw := P.biUnion fun U => Q.image (fun V => U ∪ V)
  let A := raw.filter (fun W => Apart G.Adj W W)
  have memRaw (W : Finset (Fin n)) : W ∈ raw ↔ ∃ U ∈ P, ∃ V ∈ Q, U ∪ V = W := by
    simp only [raw, Finset.mem_biUnion, Finset.mem_image]
  have inD (U V : Finset (Fin n)) (hu : U ∈ P) (hv : V ∈ Q) : U ∪ V ⊆ D :=
    Finset.union_subset_union (subset_vertices hu) (subset_vertices hv)
  have subD (W : Finset (Fin n)) (hw : W ∈ A) : W ⊆ D := by
    obtain ⟨U, hu, V, hv, rfl⟩ := (memRaw W).mp (Finset.mem_filter.mp hw).1
    exact inD U V hu hv
  apply compress L G h4 C hd subD Finset.subset_union_right
  · intro W hW
    obtain ⟨hw, hi⟩ := Finset.mem_filter.mp hW
    obtain ⟨U, hu, V, hv, rfl⟩ := (memRaw W).mp hw
    obtain ⟨hsU, _, hfU⟩ := hP.2.1 U hu
    obtain ⟨hsV, _, hfV⟩ := hQ.2.1 V hv
    refine ⟨(Finset.card_union_le ..).trans ((Nat.add_le_add hsU hsV).trans (add_powers hp hq)),
      hi, ?_⟩
    intro x hx
    exact (sem x).mpr ⟨hfU x (fun z hz => hx z (Finset.mem_union_left _ hz)),
      hfV x (fun z hz => hx z (Finset.mem_union_right _ hz))⟩
  · intro u v he hx S hs hS
    let e := s(u, v)
    let E := away G e
    have heB : e ∉ B := fun h => he (Finset.mem_union_left _ h)
    have heD : e ∉ charge G D := fun h => he (Finset.mem_union_right _ h)
    obtain ⟨hpf, hqf⟩ := (sem _).mp hx
    have hpairs : ({u, v} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
    have hs₁ : (S ∪ {u, v}).card + contextStep L * dp ≤ contextBound L := by
      have hslack := context_slack hp hs (contextStep_two L)
      have hh := Finset.card_union_le S {u, v}
      omega
    obtain ⟨U, hu, huC⟩ := hP.2.2 u v heB hpf (S ∪ {u, v}) hs₁
      (apart_union_right.mpr ⟨hS, pair_apart G u v⟩)
    obtain ⟨huS, huPair⟩ := apart_union_right.mp huC
    have hpairU := apart_symm (away_symm (G := G) (e := e)) huPair
    obtain ⟨hsU, hiU, _⟩ := hP.2.1 U hu
    have hs₁' : U.card ≤ contextStep L :=
      (hsU.trans (small_power (by omega : dp ≤ L))).trans (witness_le_step L)
    have hs₂ : (S ∪ U).card + contextStep L * dq ≤ contextBound L := by
      have hslack := context_slack hq hs hs₁'
      have hh := Finset.card_union_le S U
      omega
    obtain ⟨V, hv, hvC⟩ := hQ.2.2 u v heB hqf (S ∪ U) hs₂
      (apart_union_right.mpr ⟨hS, hpairU⟩)
    obtain ⟨hvS, hvU⟩ := apart_union_right.mp hvC
    have huV := apart_symm (away_symm (G := G) (e := e)) hvU
    have hiV := (hQ.2.1 V hv).2.1
    have hi : Apart E (U ∪ V) (U ∪ V) :=
      apart_union_left.mpr ⟨apart_union_right.mpr ⟨apart_weaken hiU e, huV⟩,
        apart_union_right.mpr ⟨hvU, apart_weaken hiV e⟩⟩
    refine ⟨U ∪ V, Finset.mem_filter.mpr ⟨(memRaw _).mpr ⟨U, hu, V, hv, rfl⟩, ?_⟩,
      apart_union_left.mpr ⟨huS, hvS⟩⟩
    exact recover_independent G heD (inD U V hu hv) hi

lemma stage_cost (D : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (h4 : NoFourCycle G)
    (C : Circuit) {p q dp dq : ℕ} (hp : dp ≤ D) (hq : dq ≤ D)
    {B : Finset (Sym2 (Fin n))} {P Q : Finset (Finset (Fin n))}
    (hP : Summary D G C p dp B P) (hQ : Summary D G C q dq B Q) :
    (charge G (vertices P ∪ vertices Q)).card ≤ gateBound D := by
  apply charge_bound G h4 _ (contextStep D * repLimit D)
  have sizeP := (vertices_bound P (witnessBound D) (fun W hW => (hP.2.1 W hW).1.trans (small_power hp))).trans
    (Nat.mul_le_mul_right _ hP.1)
  have sizeQ := (vertices_bound Q (witnessBound D) (fun W hW => (hQ.2.1 W hW).1.trans (small_power hq))).trans
    (Nat.mul_le_mul_right _ hQ.1)
  have h := Finset.card_union_le (vertices P) (vertices Q)
  rw [contextStep_eq, Nat.mul_assoc, Nat.mul_comm (witnessBound D), Nat.two_mul]
  omega

-- One common charged-edge set is retained for the entire circuit DAG.
lemma prefix_summaries (D : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (C : Circuit) (hAO : IsAO2 n C)
    (r : ℕ → ℕ) (hr : DepthCertificate n C D r)
    (k : ℕ) (hk : k ≤ C.gates.length) :
    ∃ B : Finset (Sym2 (Fin n)), B.card ≤ k * gateBound D ∧
      ∀ w < n + k, ∃ R, Summary D G C w (r w) B R := by
  induction k with
  | zero =>
    refine ⟨∅, by simp, ?_⟩
    intro w hw
    let i : Fin n := ⟨w, by omega⟩
    exact ⟨_, input_summary D G C i _ _⟩
  | succ j ih =>
    have hj : j < C.gates.length := by omega
    obtain ⟨B, hB, prev⟩ := ih (by omega)
    have hmem := gateAt_mem hj
    obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (hAO.2.2 _ hmem)
    have hpin : p ∈ (gateAt C j).inputs := by simp [hin]
    have hqin : q ∈ (gateAt C j).inputs := by simp [hin]
    have hp := hAO.2.1 j hj p hpin
    have hq := hAO.2.1 j hj q hqin
    obtain ⟨P, hP⟩ := prev p hp
    obtain ⟨Q, hQ⟩ := prev q hq
    let B' := B ∪ charge G (vertices P ∪ vertices Q)
    have step : ∃ R, Summary D G C (n + j) (r (n + j)) B' R := by
      have sem := fires_gate C hj hin hp hq
      rcases hAO.1 _ hmem with ha | ho
      · exact and_summary D G h4 C (hr.1 _ (by omega)) (hr.2.2 j hj ha p hpin)
          (hr.2.2 j hj ha q hqin) (fun x => (sem x).1 ha) hP hQ
      · exact or_summary D G h4 C (hr.1 _ (by omega)) (hr.2.1 j hj p hpin)
          (hr.2.1 j hj q hqin) (fun x => (sem x).2 ho) hP hQ
    refine ⟨B', ?_, ?_⟩
    · rw [Nat.succ_mul]
      exact (Finset.card_union_le ..).trans
        (Nat.add_le_add hB (stage_cost D G h4 C (hr.1 p (by omega))
          (hr.1 q (by omega)) hP hQ))
    · intro w hw
      by_cases hold : w < n + j
      · obtain ⟨R, hR⟩ := prev w hold
        exact ⟨R, summary_mono hR Finset.subset_union_left⟩
      · have he : w = n + j := by omega
        exact he ▸ step

-- At the output an uncharged edge would produce an independent certificate
-- forcing the graph function. Turning on just those vertices contradicts it.
lemma edge_bound (D : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (h4 : NoFourCycle G)
    (C : Circuit) (hAO : IsAO2 n C) (hfun : PEqualNP.MetaComplexity.circuitFun n C = graphFun G ∅)
    (r : ℕ → ℕ) (hr : DepthCertificate n C D r) :
    G.edgeFinset.card ≤ C.size * gateBound D := by
  obtain ⟨B, hB, hAll⟩ := prefix_summaries D G h4 C hAO r hr C.gates.length le_rfl
  refine (Finset.card_le_card (show G.edgeFinset ⊆ B from ?_)).trans hB
  intro e
  induction e using Sym2.ind with
  | _ u v =>
    intro he
    by_contra hu
    have hadj : G.Adj u v := SimpleGraph.mem_edgeFinset.mp he
    have equiv (x : Fin n → Bool) : fires C C.output x ↔ graphFun G ∅ x = true := by
      change PEqualNP.MetaComplexity.circuitFun n C x = true ↔ _
      rw [hfun]
    have hfire := (equiv _).mpr ((graphFun_pair G u v).mpr hadj)
    have hlen : C.output < n + C.gates.length := by
      by_contra! h
      have hf := val_ge (C := C) (x := List.ofFn (pairInput u v)) (by simp) h
      exact Bool.noConfusion (hf.symm.trans hfire)
    obtain ⟨R, hR⟩ := hAll C.output hlen
    have hd := hr.1 C.output hlen
    obtain ⟨W, hW, _⟩ := hR.2.2 u v hu hfire ∅
      (by simpa [contextBound] using Nat.mul_le_mul_left (contextStep D) hd) (by simp [Apart])
    obtain ⟨_, hi, force⟩ := hR.2.1 W hW
    let x (i : Fin n) := decide (i ∈ W)
    have yes := (equiv x).mp (force x (by simp [x]))
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq, x] at yes
    obtain ⟨a, b, hab, ha, hb⟩ := yes
    exact hi a ha b hb hab

-- The constant is uniform in the graph and circuit, but depends on D.
-- This does not provide a bound uniform in the AND depth.
lemma fixed_depth_ustar_bound (D : ℕ) :
    ∃ k : ℕ, ∀ n (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      NoFourCycle G → ∀ C : Circuit, IsAO2 n C →
      PEqualNP.MetaComplexity.circuitFun n C = graphFun G ∅ →
      (∃ r : ℕ → ℕ, DepthCertificate n C D r) →
      (Ustar G C).card ≤ k * (C.size + 1) := by
  refine ⟨gateBound D, ?_⟩
  intro n G _ h4 C hAO hfun hr
  obtain ⟨r, hr⟩ := hr
  calc
    (Ustar G C).card ≤ G.edgeFinset.card := Finset.card_le_card Finset.sdiff_subset
    _ ≤ C.size * gateBound D := edge_bound D G h4 C hAO hfun r hr
    _ = gateBound D * C.size := Nat.mul_comm ..
    _ ≤ gateBound D * (C.size + 1) := Nat.mul_le_mul_left _ (by omega)

end PEqualNP.Outside.L_meta_1735_aux.FixedDepth
