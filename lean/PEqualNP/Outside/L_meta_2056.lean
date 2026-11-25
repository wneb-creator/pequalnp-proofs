import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_2056

def offSet {α β : Type} [Fintype β] [DecidableEq β]
    (R : α → β → Prop) [DecidableRel R] (s : Finset α) : Finset β :=
  Finset.univ.filter fun b => ∀ a ∈ s, ¬R a b

lemma exact_of_tests {α β : Type} [Fintype β] [DecidableEq α] [DecidableEq β]
    (R : α → β → Prop) [DecidableRel R] (f : Finset α → Finset β → Bool)
    (hm : ∀ s s' t t', s ⊆ s' → t ⊆ t' → f s t = true → f s' t' = true)
    (hp : ∀ a b, R a b → f {a} {b} = true)
    (hn : ∀ s, f s (offSet R s) = false) :
    ∀ s t, f s t = true ↔ ∃ a ∈ s, ∃ b ∈ t, R a b := by
  intro s t
  constructor
  · intro hf
    by_contra h
    have ht : t ⊆ offSet R s := by
      intro b hb
      simp only [offSet, Finset.mem_filter, Finset.mem_univ, true_and]
      intro a ha hab
      exact h ⟨a, ha, b, hb, hab⟩
    have hf' := hm s s t (offSet R s) (fun _ h => h) ht hf
    rw [hn] at hf'
    contradiction
  · rintro ⟨a, ha, b, hb, hab⟩
    exact hm {a} s {b} t (Finset.singleton_subset_iff.mpr ha)
      (Finset.singleton_subset_iff.mpr hb) (hp a b hab)

lemma core_exact_of_tests {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (R : α → β → Prop) [DecidableRel R]
    (rows : Finset α) (f : Finset α → Finset β → Bool)
    (hm : ∀ s s' t t', s ⊆ s' → t ⊆ t' → f s t = true → f s' t' = true)
    (hp : ∀ a ∈ rows, ∀ b, R a b → f {a} {b} = true)
    (hn : ∀ s ∈ rows.powerset, f (s ∪ rowsᶜ) (offSet R s) = false) :
    ∀ s t, f s t = true ↔ ∃ a ∈ s, a ∈ rows ∧ ∃ b ∈ t, R a b := by
  intro s t
  constructor
  · intro hf
    by_contra h
    have ht : t ⊆ offSet R (s ∩ rows) := by
      intro b hb
      simp only [offSet, Finset.mem_filter, Finset.mem_univ, true_and]
      intro a ha hab
      obtain ⟨has, har⟩ := Finset.mem_inter.mp ha
      exact h ⟨a, has, har, b, hb, hab⟩
    have hs : s ⊆ (s ∩ rows) ∪ rowsᶜ := by
      intro a ha
      by_cases har : a ∈ rows
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨ha, har⟩)
      · exact Finset.mem_union_right _ (Finset.mem_compl.mpr har)
    have hf' := hm s ((s ∩ rows) ∪ rowsᶜ) t (offSet R (s ∩ rows)) hs ht hf
    have hi : s ∩ rows ∈ rows.powerset :=
      Finset.mem_powerset.mpr (fun _ h => (Finset.mem_inter.mp h).2)
    rw [hn _ hi] at hf'
    contradiction
  · rintro ⟨a, ha, har, b, hb, hab⟩
    exact hm {a} s {b} t (Finset.singleton_subset_iff.mpr ha)
      (Finset.singleton_subset_iff.mpr hb) (hp a har b hab)

lemma fold_mono (gs : List Gate)
    (hm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (a b : List Bool) (hab : ∀ i, a.getD i false = true → b.getD i false = true)
    (hlen : a.length = b.length) :
    ∀ i, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) a).getD i false = true →
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) b).getD i false = true := by
  induction gs generalizing a b with
  | nil => exact hab
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hg : g.op.eval (g.inputs.map fun j => a.getD j false) = true →
        g.op.eval (g.inputs.map fun j => b.getD j false) = true := by
      rcases hm g (by simp) with h | h
      · simp only [h, GateOp.eval, List.all_map]
        rw [List.all_eq_true, List.all_eq_true]
        exact fun he j hj => hab j (he j hj)
      · simp only [h, GateOp.eval, List.any_map]
        rw [List.any_eq_true, List.any_eq_true]
        rintro ⟨j, hj, he⟩
        exact ⟨j, hj, hab j he⟩
    apply ih (fun g' hg' => hm g' (List.mem_cons_of_mem _ hg')) _ _ _ (by simp [hlen])
    intro i hi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append, ← hlen] at hi ⊢
    split at hi <;> rename_i hlt
    · simp only [ite_eq_left hlt]
      exact hab _ hi
    · simp only [ite_eq_right hlt]
      by_cases he : i = a.length
      · subst i
        simpa using hg (by simpa using hi)
      · cases hs : i - a.length with
        | zero =>
          exact (he (Nat.le_antisymm (Nat.sub_eq_zero_iff_le.mp hs) (Nat.le_of_not_gt hlt))).elim
        | succ k => simp [hs] at hi

lemma eval_mono (C : Circuit) (hm : Monotone2 C) {n : ℕ} {x y : Fin n → Bool}
    (hxy : ∀ i, x i = true → y i = true) :
    C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true := by
  apply fold_mono _ (fun g hg => by simpa using (hm g hg).1) _ _ _ (by simp)
  intro i hi
  by_cases h : i < n
  · simpa [List.getD_eq_getElem?_getD, List.getElem?_ofFn, h] using
      hxy ⟨i, h⟩ (by simpa [List.getD_eq_getElem?_getD, List.getElem?_ofFn, h] using hi)
  · simp [List.getD_eq_getElem?_getD, h] at hi

def join (P D : Circuit) : Circuit :=
  ⟨P.gates ++ D.gates, D.output⟩

lemma join_size (P D : Circuit) : (join P D).size = P.size + D.size := by
  simp [join, Circuit.size]

lemma join_monotone (P D : Circuit) (hP : Monotone2 P) (hD : Monotone2 D) :
    Monotone2 (join P D) := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact hP g hg
  · exact hD g hg

lemma join_eval (P D : Circuit) (x : List Bool) :
    (join P D).eval x = D.eval (P.wires x) := by
  simp [join, Circuit.eval, Circuit.wires, List.foldl_append]

def twoGate (op₀ op₁ : GateOp) (a b c d : ℕ) : Circuit :=
  ⟨[⟨op₀, [a, b]⟩, ⟨op₁, [c, d]⟩], 0⟩

lemma twoGate_size (op₀ op₁ : GateOp) (a b c d : ℕ) :
    (twoGate op₀ op₁ a b c d).size = 2 := rfl

lemma twoGate_monotone (op₀ op₁ : GateOp) (a b c d : ℕ)
    (h₀ : op₀ = GateOp.and ∨ op₀ = GateOp.or)
    (h₁ : op₁ = GateOp.and ∨ op₁ = GateOp.or) :
    Monotone2 (twoGate op₀ op₁ a b c d) := by
  intro g hg
  simp only [twoGate, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact ⟨by simpa using h₀, by simp⟩
  · exact ⟨by simpa using h₁, by simp⟩

lemma twoGate_wires (op₀ op₁ : GateOp) (a b c d : ℕ) (x : List Bool) :
    (twoGate op₀ op₁ a b c d).wires x =
      let y := x ++ [op₀.eval [x.getD a false, x.getD b false]]
      y ++ [op₁.eval [y.getD c false, y.getD d false]] := by
  simp [twoGate, Circuit.wires]

lemma twoGate_assembly (op₀ op₁ : GateOp) (a b c d : ℕ) (D : Circuit)
    (h₀ : op₀ = GateOp.and ∨ op₀ = GateOp.or)
    (h₁ : op₁ = GateOp.and ∨ op₁ = GateOp.or)
    (hD : Monotone2 D) (hsize : D.size ≤ 61) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 63 ∧
      ∀ x : List Bool, C.eval x =
        let y := x ++ [op₀.eval [x.getD a false, x.getD b false]]
        D.eval (y ++ [op₁.eval [y.getD c false, y.getD d false]]) := by
  refine ⟨join (twoGate op₀ op₁ a b c d) D,
    join_monotone _ _ (twoGate_monotone _ _ _ _ _ _ h₀ h₁) hD, ?_, ?_⟩
  · rw [join_size, twoGate_size]
    omega
  · intro x
    rw [join_eval, twoGate_wires]


lemma row_wires_length (D : Circuit) (x : List Bool) :
    (D.wires x).length = x.length + D.size := by
  unfold Circuit.wires Circuit.size
  induction D.gates generalizing x with
  | nil => simp
  | cons g gs ih =>
    simpa [List.foldl_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (ih (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]))

def addRow (n : ℕ) (D : Circuit) (p a b c d : ℕ) : Circuit :=
  let k := n + D.size
  ⟨D.gates ++ [⟨GateOp.or, [a,b]⟩, ⟨GateOp.or, [c,d]⟩,
    ⟨GateOp.or, [k,k+1]⟩, ⟨GateOp.and, [p,k+2]⟩,
    ⟨GateOp.or, [D.output,k+3]⟩], k+4⟩

lemma addRow_size (n : ℕ) (D : Circuit) (p a b c d : ℕ) :
    (addRow n D p a b c d).size = D.size + 5 := by
  simp [addRow, Circuit.size]

lemma addRow_monotone (n : ℕ) (D : Circuit) (p a b c d : ℕ)
    (hD : Monotone2 D) : Monotone2 (addRow n D p a b c d) := by
  intro g hg
  simp only [addRow, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | rfl | rfl | rfl | rfl | rfl
  · exact hD g h
  all_goals simp

lemma row_getD_append (x y : List Bool) (i : ℕ) (h : i < x.length) :
    (x ++ y).getD i false = x.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append, h]

lemma row_getD_last (x : List Bool) (v : Bool) :
    (x ++ [v]).getD x.length false = v := by
  simp [List.getD_eq_getElem?_getD]

lemma row_input (D : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (D.wires x).getD i false = x.getD i false := by
  unfold Circuit.wires
  induction D.gates generalizing x with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)])
      (by simp; omega), row_getD_append _ _ _ hi]

lemma row_getD_new (w l : List Bool) (j : ℕ) :
    (w ++ l).getD (w.length + j) false = l.getD j false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append, Nat.not_lt_of_ge (Nat.le_add_right _ _)]

lemma row_getD_at (w l : List Bool) :
    (w ++ l).getD w.length false = l.getD 0 false := by
  simpa using row_getD_new w l 0

set_option maxHeartbeats 800000 in
lemma row_run (w : List Bool) (p a b c d out : ℕ)
    (hp : p < w.length) (_ha : a < w.length) (_hb : b < w.length)
    (hc : c < w.length) (hd : d < w.length) (hout : out < w.length) :
    let k := w.length
    let gs : List Gate := [⟨GateOp.or, [a,b]⟩, ⟨GateOp.or, [c,d]⟩,
      ⟨GateOp.or, [k,k+1]⟩, ⟨GateOp.and, [p,k+2]⟩,
      ⟨GateOp.or, [out,k+3]⟩]
    (gs.foldl (fun v g => v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)])
      w).getD (k+4) false =
      (w.getD out false || (w.getD p false &&
        ((w.getD a false || w.getD b false) ||
          (w.getD c false || w.getD d false)))) := by
  simp only [List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil,
    GateOp.eval, List.any_cons, List.any_nil, List.all_cons, List.all_nil,
    id_eq, Bool.or_false, Bool.and_true]
  simp only [List.append_assoc, List.cons_append, List.nil_append,
    row_getD_append _ _ _ hc, row_getD_append _ _ _ hd,
    row_getD_append _ _ _ hp, row_getD_append _ _ _ hout,
    row_getD_new, row_getD_at]
  simp

lemma addRow_eval (n : ℕ) (D : Circuit) (p a b c d : ℕ)
    (x : List Bool) (hx : x.length = n)
    (hp : p < n) (ha : a < n) (hb : b < n) (hc : c < n) (hd : d < n)
    (hout : D.output < n + D.size) :
    (addRow n D p a b c d).eval x =
      (D.eval x || (x.getD p false &&
        ((x.getD a false || x.getD b false) ||
          (x.getD c false || x.getD d false)))) := by
  have hw : (D.wires x).length = n + D.size := by simp [row_wires_length, hx]
  have hi (i : ℕ) (h : i < n) : (D.wires x).getD i false = x.getD i false :=
    row_input D x i (by omega)
  have hh := row_run (D.wires x) p a b c d D.output
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  simp only [hw, hi p hp, hi a ha, hi b hb, hi c hc, hi d hd] at hh
  simpa only [addRow, Circuit.eval, Circuit.wires, List.foldl_append] using hh

lemma addRow_output (n : ℕ) (D : Circuit) (p a b c d : ℕ) :
    (addRow n D p a b c d).output < n + (addRow n D p a b c d).size := by
  rw [addRow_size]
  change n + D.size + 4 < n + (D.size + 5)
  omega

def pgLine (p : Fin 13) (t : ℕ) : ℕ := 13 + ((t + 13 - p.val) % 13)

def pgAddRow (D : Circuit) (p : Fin 13) : Circuit :=
  addRow 26 D p.val (pgLine p 0) (pgLine p 1) (pgLine p 3) (pgLine p 9)

def pgRowValue (x : List Bool) (p : Fin 13) : Bool :=
  x.getD p.val false && ((x.getD (pgLine p 0) false || x.getD (pgLine p 1) false) ||
    (x.getD (pgLine p 3) false || x.getD (pgLine p 9) false))

def pgAddRows : Circuit → List (Fin 13) → Circuit
  | D, [] => D
  | D, p :: ps => pgAddRows (pgAddRow D p) ps

lemma pgLine_bound (p : Fin 13) (t : ℕ) : pgLine p t < 26 := by
  unfold pgLine
  have := Nat.mod_lt (t + 13 - p.val) (by decide : 0 < 13)
  omega

lemma pgAddRow_eval (D : Circuit) (p : Fin 13) (x : List Bool)
    (hx : x.length = 26) (hout : D.output < 26 + D.size) :
    (pgAddRow D p).eval x = (D.eval x || pgRowValue x p) := by
  exact addRow_eval 26 D p.val _ _ _ _ x hx (by omega)
    (pgLine_bound p 0) (pgLine_bound p 1) (pgLine_bound p 3) (pgLine_bound p 9) hout

lemma pgAddRows_size (D : Circuit) (ps : List (Fin 13)) :
    (pgAddRows D ps).size = D.size + 5 * ps.length := by
  induction ps generalizing D with
  | nil => simp [pgAddRows]
  | cons p ps ih =>
    simp only [pgAddRows, ih, pgAddRow, addRow_size, List.length_cons]
    omega

lemma pgAddRows_monotone (D : Circuit) (ps : List (Fin 13)) (hD : Monotone2 D) :
    Monotone2 (pgAddRows D ps) := by
  induction ps generalizing D with
  | nil => exact hD
  | cons p ps ih => exact ih _ (addRow_monotone _ _ _ _ _ _ _ hD)

lemma pgAddRows_output (D : Circuit) (ps : List (Fin 13))
    (hout : D.output < 26 + D.size) :
    (pgAddRows D ps).output < 26 + (pgAddRows D ps).size := by
  induction ps generalizing D with
  | nil => exact hout
  | cons p ps ih => exact ih _ (addRow_output _ _ _ _ _ _ _)

lemma pgAddRows_eval (D : Circuit) (ps : List (Fin 13)) (x : List Bool)
    (hx : x.length = 26) (hout : D.output < 26 + D.size) :
    (pgAddRows D ps).eval x = (D.eval x || ps.any (pgRowValue x)) := by
  induction ps generalizing D with
  | nil => simp [pgAddRows]
  | cons p ps ih =>
    rw [pgAddRows, ih (pgAddRow D p) (addRow_output _ _ _ _ _ _ _),
      pgAddRow_eval D p x hx hout]
    simp [Bool.or_assoc]

def pgNear (p l : Fin 13) : Prop := (p.val + l.val) % 13 ∈ ([0,1,3,9] : List ℕ)

def pgBits (S T : Finset (Fin 13)) : List Bool :=
  List.ofFn fun i : Fin 26 => if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ S)
    else decide (Fin.ofNat 13 i.val ∈ T)

lemma pgBits_left (S T : Finset (Fin 13)) (p : Fin 13) :
    (pgBits S T).getD p.val false = decide (p ∈ S) := by
  have h26 : p.val < 26 := by omega
  have hp : Fin.ofNat 13 p.val = p := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt p.isLt
  simp only [pgBits, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left h26,
    Option.getD_some, p.isLt, ite_eq_left, hp]

lemma pgBits_line (S T : Finset (Fin 13)) (p : Fin 13) (t : ℕ) :
    (pgBits S T).getD (pgLine p t) false = decide (Fin.ofNat 13 (pgLine p t) ∈ T) := by
  have h26 := pgLine_bound p t
  have h13 : ¬ pgLine p t < 13 := by unfold pgLine; omega
  simp only [pgBits, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left h26,
    Option.getD_some, h13, ite_false]

lemma pgNear_iff (p l : Fin 13) :
    pgNear p l ↔ l = Fin.ofNat 13 (pgLine p 0) ∨ l = Fin.ofNat 13 (pgLine p 1) ∨
      l = Fin.ofNat 13 (pgLine p 3) ∨ l = Fin.ofNat 13 (pgLine p 9) := by
  revert p l
  unfold pgNear pgLine
  decide +kernel

lemma pgRowValue_bits (S T : Finset (Fin 13)) (p : Fin 13) :
    pgRowValue (pgBits S T) p = true ↔ p ∈ S ∧ ∃ l ∈ T, pgNear p l := by
  rw [pgRowValue, pgBits_left, pgBits_line, pgBits_line, pgBits_line, pgBits_line]
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  simp only [pgNear_iff]
  aesop

lemma pgRows_full (D : Circuit) (rows : List (Fin 13))
    (heval : ∀ S T : Finset (Fin 13), D.eval (pgBits S T) = rows.any (pgRowValue (pgBits S T)))
    (hall : ∀ p : Fin 13, p ∈ rows) :
    ∀ S T : Finset (Fin 13), D.eval (pgBits S T) = true ↔ ∃ p ∈ S, ∃ l ∈ T, pgNear p l := by
  intro S T
  rw [heval, List.any_eq_true]
  simp only [pgRowValue_bits]
  constructor
  · rintro ⟨p, _, hp, hl⟩
    exact ⟨p, hp, hl⟩
  · rintro ⟨p, hp, hl⟩
    exact ⟨p, hall p, hp, hl⟩

lemma rows_assembly (D : Circuit) (core more : List (Fin 13))
    (hD : Monotone2 D) (hsize : D.size + 5 * more.length ≤ 63)
    (hout : D.output < 26 + D.size)
    (hcore : ∀ S T : Finset (Fin 13), D.eval (pgBits S T) =
      core.any (pgRowValue (pgBits S T)))
    (hall : ∀ p : Fin 13, p ∈ core ++ more) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 63 ∧
      ∀ S T : Finset (Fin 13), C.eval (pgBits S T) = true ↔ ∃ p ∈ S, ∃ l ∈ T, pgNear p l := by
  let C := pgAddRows D more
  refine ⟨C, pgAddRows_monotone D more hD, ?_, ?_⟩
  · change (pgAddRows D more).size ≤ 63
    rw [pgAddRows_size]
    exact hsize
  · apply pgRows_full C (core ++ more)
    · intro S T
      change (pgAddRows D more).eval (pgBits S T) = _
      rw [pgAddRows_eval D more _ (by simp [pgBits]) hout, hcore, List.any_append]
    · exact hall

lemma sixRow_assembly (D : Circuit) (hD : Monotone2 D) (hsize : D.size ≤ 28)
    (hout : D.output < 26 + D.size)
    (hcore : ∀ S T : Finset (Fin 13), D.eval (pgBits S T) =
      ([1,2,3,8,9,12] : List (Fin 13)).any (pgRowValue (pgBits S T))) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 63 ∧
      ∀ S T : Finset (Fin 13), C.eval (pgBits S T) = true ↔ ∃ p ∈ S, ∃ l ∈ T, pgNear p l := by
  refine rows_assembly D [1,2,3,8,9,12] [0,4,5,6,7,10,11] hD ?_ hout hcore ?_
  · change D.size + 5 * 7 ≤ 63
    omega
  · decide +kernel

lemma fiveRow_assembly (D : Circuit) (hD : Monotone2 D) (hsize : D.size ≤ 23)
    (hout : D.output < 26 + D.size)
    (hcore : ∀ S T : Finset (Fin 13), D.eval (pgBits S T) =
      ([0,1,2,3,4] : List (Fin 13)).any (pgRowValue (pgBits S T))) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 63 ∧
      ∀ S T : Finset (Fin 13), C.eval (pgBits S T) = true ↔ ∃ p ∈ S, ∃ l ∈ T, pgNear p l := by
  refine rows_assembly D [0,1,2,3,4] [5,6,7,8,9,10,11,12] hD ?_ hout hcore ?_
  · change D.size + 5 * 8 ≤ 63
    omega
  · decide +kernel


lemma pgBits_mono (D : Circuit) (hm : Monotone2 D)
    (S S' T T' : Finset (Fin 13)) (hS : S ⊆ S') (hT : T ⊆ T') :
    D.eval (pgBits S T) = true → D.eval (pgBits S' T') = true := by
  unfold pgBits
  apply eval_mono D hm
  intro i hi
  by_cases h : i.val < 13
  · simp only [h, ite_true, decide_eq_true_eq] at hi ⊢
    exact hS hi
  · simp only [h, ite_false, decide_eq_true_eq] at hi ⊢
    exact hT hi

lemma coreTests_correct (D : Circuit) (rows : List (Fin 13))
    (hm : Monotone2 D)
    (hp : ∀ p ∈ rows, ∀ l : Fin 13, pgNear p l → D.eval (pgBits {p} {l}) = true)
    (hn : ∀ S ∈ rows.toFinset.powerset,
      D.eval (pgBits (S ∪ rows.toFinsetᶜ)
        (offSet (fun p l : Fin 13 => (p.val + l.val) % 13 ∈ ([0,1,3,9] : List ℕ)) S)) = false) :
    ∀ S T : Finset (Fin 13), D.eval (pgBits S T) = rows.any (pgRowValue (pgBits S T)) := by
  have hh := core_exact_of_tests
    (fun p l : Fin 13 => (p.val + l.val) % 13 ∈ ([0,1,3,9] : List ℕ))
    rows.toFinset (fun S T => D.eval (pgBits S T))
    (pgBits_mono D hm)
    (by intro p hp' l hl; exact hp p (List.mem_toFinset.mp hp') l hl) hn
  intro S T
  apply Bool.eq_iff_iff.mpr
  rw [hh, List.any_eq_true]
  simp only [pgRowValue_bits, List.mem_toFinset]
  constructor
  · rintro ⟨p, hpS, hpR, l, hlT, hnear⟩
    exact ⟨p, hpR, hpS, l, hlT, hnear⟩
  · rintro ⟨p, hpR, hpS, l, hlT, hnear⟩
    exact ⟨p, hpS, hpR, l, hlT, hnear⟩


lemma from_full (C : Circuit) (hm : Monotone2 C) (hs : C.size ≤ 63)
    (hfull : ∀ S T : Finset (Fin 13), C.eval (pgBits S T) = true ↔
      ∃ p ∈ S, ∃ l ∈ T, pgNear p l) :
∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 ∧     x1.size ≤ (63 : ℕ) ∧       let x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => (↑x2 + ↑x3) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];       have x3 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x3 x4 : Finset (Fin (13 : ℕ))) (x5 : Fin (26 : ℕ)) => if ↑x5 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x5 ∈ x3) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x5 ∈ x4);       have x4 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x4 : Finset (Fin (13 : ℕ))) => {x5 : Fin (13 : ℕ) | ∀ x6 ∈ x4, ¬x2 x6 x5};       have x5 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x5 x6 : Finset (Fin (13 : ℕ))) => x1.eval (List.ofFn (x3 x5 x6));       (∀ (x6 x7 : Fin (13 : ℕ)), x2 x6 x7 → x5 {x6} {x7} = Bool.true) ∧ ∀ (x6 : Finset (Fin (13 : ℕ))), x6.card ≤ (3 : ℕ) → x5 x6 (x4 x6) = Bool.false ∧ x5 (x4 x6) x6 = Bool.false := by
  refine ⟨C, hm, hs, ?_⟩
  let off := fun S : Finset (Fin 13) =>
    Finset.univ.filter fun l : Fin 13 => ∀ p ∈ S,
      ¬((p.val + l.val) % 13 ∈ ([0,1,3,9] : List ℕ))
  change (∀ p l : Fin 13, pgNear p l → C.eval (pgBits {p} {l}) = true) ∧
    ∀ S : Finset (Fin 13), S.card ≤ 3 →
      C.eval (pgBits S (off S)) = false ∧ C.eval (pgBits (off S) S) = false
  constructor
  · intro p l h
    exact (hfull _ _).mpr ⟨p, by simp, l, by simp, h⟩
  · intro S _
    constructor
    · apply Bool.eq_false_iff.mpr
      intro h
      obtain ⟨p, hp, l, hl, hn⟩ := (hfull _ _).mp h
      exact (Finset.mem_filter.mp hl).2 p hp hn
    · apply Bool.eq_false_iff.mpr
      intro h
      obtain ⟨p, hp, l, hl, hn⟩ := (hfull _ _).mp h
      apply (Finset.mem_filter.mp hp).2 l hl
      simpa [pgNear, Nat.add_comm] using hn

end PEqualNP.Outside.L_meta_2056
