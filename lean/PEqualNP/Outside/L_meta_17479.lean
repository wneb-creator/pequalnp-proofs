import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17479_aux

open PEqualNP.CircuitLowerBounds

def F (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl F x := rfl

lemma len_foldl (gs : List Gate) : ∀ w : List Bool, (gs.foldl F w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih => intro w; simp only [List.foldl_cons, ih, F]; simp; omega

lemma getD_F (w : List Bool) (g : Gate) (i : ℕ) : (F w g).getD i false =
    if i < w.length then w.getD i false
    else if i = w.length then g.op.eval (g.inputs.map fun i => w.getD i false) else false := by
  unfold F
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · subst h2; rw [List.getD_append_right _ _ _ _ (le_refl _)]; simp
  · rw [List.getD_eq_default _ _ (by simp; omega)]

lemma pref (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (gs.foldl F w).getD i false = w.getD i false := by
  induction gs with
  | nil => intros; rfl
  | cons g gs ih =>
    intro w i h
    rw [List.foldl_cons, ih _ i (by simp [F]; omega), getD_F, if_pos h]

lemma gateval (gs : List Gate) : ∀ (w : List Bool) (k : ℕ) (hk : k < gs.length),
    (gs.foldl F w).getD (w.length + k) false =
      (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
        if i < w.length + k then (gs.foldl F w).getD i false else false) := by
  induction gs with
  | nil => intro w k hk; simp at hk
  | cons g gs ih =>
    intro w k hk
    cases k with
    | zero =>
      simp only [List.foldl_cons, List.getElem_cons_zero, Nat.add_zero]
      rw [pref gs (F w g) w.length (by simp [F]), getD_F, if_neg (lt_irrefl _), if_pos rfl]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with h
      · rw [pref gs (F w g) i (by simp [F]; omega), getD_F, if_pos h]
      · rw [List.getD_eq_default _ _ (by omega)]
    | succ k =>
      simp only [List.foldl_cons, List.getElem_cons_succ]
      have h1 := ih (F w g) k (by simpa using hk)
      have hl : (F w g).length = w.length + 1 := by simp [F]
      rw [hl] at h1
      rw [show w.length + (k + 1) = w.length + 1 + k by omega, h1]

open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

abbrev bits := Fin 10 → Bool

def v (c : Circuit) (x : bits) (i : Nat) := (c.wires (List.ofFn x)).getD i false

theorem inp (c : Circuit) (x : bits) (i : Nat) (h : i < 10) :
    v c x i = x ⟨i,h⟩ := by
  unfold v
  rw [wires_eq, pref _ _ _ (by simpa using h), List.getD_eq_getElem _ _ (by simpa using h)]
  simp only [List.getElem_ofFn]

theorem outOf (c : Circuit) (x : bits) (i : Nat) (h : 10 + c.size ≤ i) :
    v c x i = false := by
  apply List.getD_eq_default
  simpa [wires_eq,len_foldl,Circuit.size] using h

def atG (c : Circuit) (j : Nat) := gateAt c j

def good (n : Nat) (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 ∧ ∀ i ∈ g.inputs, i < n

theorem at_eq (c : Circuit) {j : Nat} (h : j < c.size) : atG c j = c.gates[j]'h :=
  List.getD_eq_getElem _ _ h

theorem shape (c : Circuit) : IsAO2 10 c ↔ ∀ j < c.size, good (10+j) (atG c j) := by
  constructor
  · rintro ⟨ao,back,len⟩ j hj
    exact ⟨ao _ (at_eq c hj ▸ List.getElem_mem hj), len _ (at_eq c hj ▸ List.getElem_mem hj), back j hj⟩
  · intro h
    refine ⟨?_,fun j hj => (h j hj).2.2,?_⟩
    · intro g hg
      obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hg
      simpa only [at_eq c hj] using (h j hj).1
    · intro g hg
      obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hg
      simpa only [at_eq c hj] using (h j hj).2.1

theorem at_value (c : Circuit) (ao : IsAO2 10 c) (x : bits) {j : Nat} (hj : j<c.size) :
    v c x (10+j) = (atG c j).op.eval ((atG c j).inputs.map (v c x)) := by
  have h := gateval c.gates (List.ofFn x) j hj
  simp only [List.length_ofFn, ← wires_eq, ← at_eq c hj] at h
  rw [show v c x (10+j) = _ from h]
  congr 1
  apply List.map_congr_left
  intro i hi
  simp [v, ((shape c).mp ao j hj).2.2 i hi]

def move (k i : Nat) := if i = 0 then 10+k else if i < 10+k then i else i+1

def mapped (k : Nat) (g : Gate) : Gate := ⟨g.op,g.inputs.map (move k)⟩

def newGate (c : Circuit) (w k j : Nat) : Gate :=
  if j < k then atG c j else if j = k then ⟨GateOp.or,[0,w]⟩ else mapped k (atG c (j-1))

def insertOr (c : Circuit) (w k : Nat) : Circuit where
  gates := List.ofFn (fun j : Fin (c.size+1) => newGate c w k j)
  output := move k c.output

@[simp] theorem newSize (c : Circuit) (w k : Nat) : (insertOr c w k).size = c.size+1 := by
  simp [Circuit.size,insertOr]

theorem newAt (c : Circuit) {w k j : Nat} (h : j < c.size+1) :
    atG (insertOr c w k) j = newGate c w k j := by
  rw [at_eq _ (by simpa using h)]
  simp only [insertOr,List.getElem_ofFn]

theorem newAO (c : Circuit) (ao : IsAO2 10 c) (w k : Nat) (hk : k≤c.size) (hw : w<10+k) :
    IsAO2 10 (insertOr c w k) := by
  apply (shape _).mpr
  intro j hj
  rw [newSize] at hj
  rw [newAt c hj]
  unfold newGate
  split_ifs with h e
  · exact (shape c).mp ao j (by omega)
  · subst j
    exact ⟨Or.inr rfl,rfl,by simpa using And.intro (show 0<10+k by omega) hw⟩
  · obtain ⟨hop,hlen,hback⟩ := (shape c).mp ao (j-1) (by omega)
    refine ⟨hop,by simpa [mapped] using hlen,?_⟩
    intro i hi
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hi
    have := hback a ha
    unfold move
    split_ifs <;> omega

theorem before (a b : Circuit) (aa : IsAO2 10 a) (ab : IsAO2 10 b) (k : Nat)
    (ka : k ≤ a.size) (kb : k ≤ b.size)
    (same : ∀ j < k, atG a j = atG b j) (noread : ∀ j < k, 0 ∉ (atG b j).inputs)
    (x y : bits) (xy : ∀ i ≠ (0 : Fin 10), x i = y i) :
    ∀ i < 10+k, i ≠ 0 → v a x i = v b y i := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hi nz
    by_cases input : i < 10
    · rw [inp _ _ _ input,inp _ _ _ input]
      apply xy
      exact fun e => nz (congrArg Fin.val e)
    · let j := i-10
      have eq : i = 10+j := by dsimp [j]; omega
      have jk : j<k := by omega
      rw [eq,at_value a aa _ (by omega : j<a.size),at_value b ab _ (by omega : j<b.size),same j jk]
      congr 1
      apply List.map_congr_left
      intro m hm
      have hm' := ((shape b).mp ab j (by omega)).2.2 m hm
      exact ih m (by omega) (by omega) (fun e => noread j jk (e ▸ hm))

theorem simulate (c : Circuit) (ao : IsAO2 10 c) (w k : Nat) (hk : k ≤ c.size)
    (hw : w < 10+k) (hw0 : w ≠ 0) (hr : ∀ j < k, 0 ∉ (atG c j).inputs) (x : bits) :
    let z := Function.update x 0 false
    let y := Function.update x 0 (x 0 || v c z w)
    ∀ i, v (insertOr c w k) x (move k i) = v c y i := by
  let d := insertOr c w k
  let z := Function.update x 0 false
  let y := Function.update x 0 (x 0 || v c z w)
  change ∀ i, v d x (move k i) = v c y i
  have da : IsAO2 10 d := newAO c ao w k hk hw
  have sz : d.size = c.size+1 := newSize ..
  have eqg (j : Nat) (hj : j<k) : atG d j = atG c j := by
    rw [newAt c (by omega : j < c.size+1)]
    simp [newGate,hj]
  have pre (t : bits) (ht : ∀ i ≠ (0 : Fin 10), x i = t i) :=
    before d c da ao k (by omega) hk eqg hr x t ht
  have readw : v d x w = v c z w := pre z (by intro i hi; simp [z,Function.update_of_ne hi]) w hw hw0
  have read0 : v d x (10+k) = y 0 := by
    rw [at_value d da x (by omega : k<d.size),newAt c (by omega : k<c.size+1)]
    simp [newGate,GateOp.eval,inp d x 0 (by decide),readw,y]
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    by_cases iz : i = 0
    · subst i
      rw [show move k 0 = 10+k by rfl, inp c y 0 (by decide)]
      exact read0
    by_cases hi : i < 10+k
    · rw [show move k i = i by simp [move,iz,hi]]
      exact pre y (by intro l hl; simp [y,Function.update_of_ne hl]) i hi iz
    have ren : move k i = i+1 := by simp [move,iz,hi]
    rw [ren]
    by_cases bound : i < 10+c.size
    · let j := i-10
      have ji : 10+j = i := by dsimp [j]; omega
      have cut : k ≤ j := by omega
      have nj : j<c.size := by omega
      have dj : j+1<d.size := by omega
      rw [← ji,show 10+j+1=10+(j+1) by omega,at_value d da _ dj,at_value c ao _ nj,
        newAt c (by omega : j+1<c.size+1)]
      simp only [newGate,if_neg (show ¬j+1<k by omega),if_neg (show j+1≠k by omega),
        Nat.add_sub_cancel,mapped,List.map_map]
      congr 1
      apply List.map_congr_left
      intro m hm
      exact ih m (by have := ((shape c).mp ao j nj).2.2 m hm; omega)
    · rw [outOf d _ _ (by omega),outOf c _ _ (by omega)]

end PEqualNP.Outside.L_meta_17479_aux

open PEqualNP.Outside.L_meta_17479_aux in
theorem PEqualNP.Outside.L_meta_17479 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ), PEqualNP.TopForm.IsAO2 (10 : ℕ) x1 → x2 ≠ (0 : ℕ) → x2 < (10 : ℕ) + x1.size → (∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate), (10 : ℕ) + x6 ≤ x2 → x1.gates[x6]? = Option.some x7 → (0 : ℕ) ∉ x7.inputs) → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (10 : ℕ) x7 ∧ x7.size ≤ x1.size + (1 : ℕ) ∧ ∀ (x8 : Fin (10 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x7 x8 = PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x1 (Function.update x8 (0 : Fin (10 : ℕ)) (x8 (0 : Fin (10 : ℕ)) || (x1.wires (List.ofFn (Function.update x8 (0 : Fin (10 : ℕ)) Bool.false))).getD x2 Bool.false)) := by
  intro c w ao hw0 hw hr
  let k := w+1-10
  have hk : k ≤ c.size := by dsimp [k]; omega
  have cut : w<10+k := by dsimp [k]; omega
  refine ⟨insertOr c w k,newAO c ao w k hk cut,by simp,?_⟩
  intro x
  apply simulate c ao w k hk cut hw0 _ x c.output
  intro j hj
  apply hr j (atG c j) (by dsimp [k] at hj; omega)
  have h : j<c.size := by omega
  simp [at_eq c h,List.getElem?_eq_getElem h]
