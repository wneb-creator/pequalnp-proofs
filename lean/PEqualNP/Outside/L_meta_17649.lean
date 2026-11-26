import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17649_aux

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

variable {n : Nat}

abbrev bits (n : Nat) := Fin n → Bool

def v (c : Circuit) (x : bits n) (i : Nat) := (c.wires (List.ofFn x)).getD i false

theorem inp (c : Circuit) (x : bits n) (i : Nat) (h : i < n) :
    v c x i = x ⟨i,h⟩ := by
  unfold v
  rw [wires_eq, pref _ _ _ (by simpa using h), List.getD_eq_getElem _ _ (by simpa using h)]
  simp only [List.getElem_ofFn]

def atG (c : Circuit) (j : Nat) := gateAt c j

theorem at_eq (c : Circuit) {j : Nat} (h : j < c.size) : atG c j = c.gates[j]'h :=
  List.getD_eq_getElem _ _ h

theorem at_value (c : Circuit) (back : ReadsBack n c) (x : bits n) {j : Nat} (hj : j<c.size) :
    v c x (n+j) = (atG c j).op.eval ((atG c j).inputs.map (v c x)) := by
  have h := gateval c.gates (List.ofFn x) j hj
  simp only [List.length_ofFn, ← wires_eq, ← at_eq c hj] at h
  rw [show v c x (n+j) = _ from h]
  congr 1
  apply List.map_congr_left
  intro i hi
  simp [v, back j hj i hi]

def rnk (R : Finset ℕ) (j : ℕ) : ℕ := ((List.range j).filter (fun i => decide (i ∉ R))).length

lemma rnk_le (R : Finset ℕ) (j : ℕ) : rnk R j ≤ j := by
  unfold rnk; exact le_trans (List.length_filter_le _ _) (by simp)

lemma rnk_mono (R : Finset ℕ) {i j : ℕ} (h : i ≤ j) : rnk R i ≤ rnk R j := by
  unfold rnk
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [List.range_add, List.filter_append, List.length_append]
  omega

lemma rnk_succ_of_not_mem (R : Finset ℕ) {j : ℕ} (h : j ∉ R) : rnk R (j + 1) = rnk R j + 1 := by
  unfold rnk
  rw [List.range_succ, List.filter_append, List.length_append]
  simp [h]

lemma rnk_lt (R : Finset ℕ) {i j : ℕ} (hi : i ∉ R) (h : i < j) : rnk R i < rnk R j := by
  have := rnk_mono R (show i + 1 ≤ j by omega)
  rw [rnk_succ_of_not_mem R hi] at this
  omega

lemma filt_get (R : Finset ℕ) (L j : ℕ) (hj : j < L) (hjR : j ∉ R) :
    ∃ h : rnk R j < ((List.range L).filter (fun i => decide (i ∉ R))).length,
      ((List.range L).filter (fun i => decide (i ∉ R)))[rnk R j] = j := by
  obtain ⟨m, rfl⟩ : ∃ m, L = j + (m + 1) := ⟨L - j - 1, by omega⟩
  have hsplit : (List.range (j + (m + 1))).filter (fun i => decide (i ∉ R)) =
      (List.range j).filter (fun i => decide (i ∉ R)) ++
        (j :: ((List.range m).map (fun k => j + (k + 1))).filter (fun i => decide (i ∉ R))) := by
    rw [List.range_add, List.filter_append, List.range_succ_eq_map]
    simp [hjR, List.map_map, Function.comp_def]
  have hl : rnk R j < ((List.range (j + (m + 1))).filter (fun i => decide (i ∉ R))).length := by
    rw [hsplit]; simp [rnk]
  refine ⟨hl, ?_⟩
  simp only [hsplit]
  rw [List.getElem_append_right (by simp [rnk])]
  simp [rnk]

lemma filt_len (R : Finset ℕ) (L : ℕ) (hR : ∀ r ∈ R, r < L) :
    ((List.range L).filter (fun i => decide (i ∉ R))).length = L - R.card := by
  rw [← List.toFinset_card_of_nodup (List.nodup_range.filter _), List.toFinset_filter,
    List.toFinset_range]
  have hsub : R ⊆ Finset.range L := fun r hr => Finset.mem_range.mpr (hR r hr)
  have : (Finset.range L).filter (fun i => decide (i ∉ R) = true) = Finset.range L \ R := by
    ext i; simp
  rw [this, Finset.card_sdiff, Finset.inter_eq_left.mpr hsub]
  simp

def keep (R : Finset Nat) (L : Nat) := (List.range L).filter (fun j => decide (j∉R))

def send (p : Equiv.Perm (Fin n)) (R : Finset Nat) (w : Nat) :=
  if h : w<n then (p ⟨w,h⟩).val else n+rnk R (w-n)

def mk (c : Circuit) (p : Equiv.Perm (Fin n)) (R : Finset Nat) (j : Nat) : Gate :=
  ⟨(atG c j).op, (atG c j).inputs.map (send p R)⟩

def strip (c : Circuit) (p : Equiv.Perm (Fin n)) (R : Finset Nat) : Circuit :=
  ⟨(keep R c.size).map (mk c p R),0⟩

variable (c : Circuit) (p : Equiv.Perm (Fin n)) (R : Finset Nat)

theorem size_strip : (strip c p R).size = (keep R c.size).length := List.length_map _

theorem at_strip {j : Nat} (h : j<c.size) (keepj : j∉R) :
    atG (strip c p R) (rnk R j) = mk c p R j := by
  obtain ⟨h',e⟩ := filt_get R c.size j h keepj
  rw [at_eq _ (by rwa [size_strip])]
  have hh : rnk R j < ((keep R c.size).map (mk c p R)).length := by simpa [keep] using h'
  change ((keep R c.size).map (mk c p R))[rnk R j]'hh = _
  rw [List.getElem_map]
  congr 1

def safe (n : Nat) (c : Circuit) (R : Finset Nat) := ∀ j<c.size, ∀ w ∈ (atG c j).inputs, n≤w → w-n∉R

theorem bound (back : ReadsBack n c) (ok : safe n c R) {j w : Nat} (h : j<c.size)
    (hw : w ∈ (atG c j).inputs) : send p R w < n+rnk R j := by
  have lt := back j h w hw
  unfold send
  split_ifs with small
  · have := (p ⟨w,small⟩).isLt; omega
  · exact Nat.add_lt_add_left (rnk_lt R (ok j h w hw (by omega)) (by omega)) _

theorem model (mono : Monotone2 c) (back : ReadsBack n c) (ok : safe n c R) :
    Monotone2 (strip c p R) ∧ ReadsBack n (strip c p R) := by
  constructor
  · intro g hg
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hg
    have lt : j<c.size := List.mem_range.mp (List.mem_filter.mp hj).1
    have hm := mono _ (at_eq c lt ▸ List.getElem_mem lt)
    exact ⟨hm.1,by simpa [mk] using hm.2⟩
  · intro k hk w hw
    let ks := keep R c.size
    have hl : k < ks.length := by change k < (strip c p R).size at hk; rwa [size_strip] at hk
    let j := ks[k]
    have hm : j ∈ ks := List.getElem_mem hl
    have lt : j<c.size := List.mem_range.mp (List.mem_filter.mp hm).1
    have hj : j∉R := of_decide_eq_true (List.mem_filter.mp hm).2
    obtain ⟨h',e⟩ := filt_get R c.size j lt hj
    have nd : ks.Nodup := List.nodup_range.filter _
    have eq : rnk R j = k := nd.getElem_inj_iff.mp e
    change w ∈ (atG (strip c p R) k).inputs at hw
    rw [← eq,at_strip c p R lt hj] at hw
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hw
    rw [← eq]
    exact bound c p R back ok lt ha

theorem evaluate (mono : Monotone2 c) (back : ReadsBack n c) (ok : safe n c R)
    (x : bits n) (w : Nat) (hw : w<n+c.size) (keepw : n≤w → w-n∉R) :
    v (strip c p R) x (send p R w) = v c (x ∘ p) w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases small : w<n
    · rw [inp _ _ _ (by simpa [send,small] using (p ⟨w,small⟩).isLt),inp _ _ _ small]
      simp [send,small]
    let j := w-n
    have hj : j<c.size := by dsimp [j]; omega
    have keepj : j∉R := keepw (by omega)
    have eq : w=n+j := by dsimp [j]; omega
    have pos : rnk R j < (strip c p R).size := by rw [size_strip]; exact (filt_get R _ j hj keepj).1
    rw [show send p R w = n+rnk R j by simp [send,small,j],
      at_value _ (model c p R mono back ok).2 _ pos,at_strip c p R hj keepj,
      eq,at_value _ back _ hj]
    simp only [mk,List.map_map]
    congr 1
    apply List.map_congr_left
    intro i hi
    have hlt := back j hj i hi
    exact ih i (by omega) (by omega) (ok j hj i hi)

def finalValue (d : Circuit) (g : Gate) (x : bits n) := g.op.eval (g.inputs.map (v d x))

theorem terminal (mono : Monotone2 c) (back : ReadsBack n c) (ok : safe n c R)
    (j : Nat) (hj : j<c.size) :
    ((mk c p R j).op = .and ∨ (mk c p R j).op = .or) ∧ (mk c p R j).inputs.length≤2 ∧
      (∀ w ∈ (mk c p R j).inputs, w<n+(strip c p R).size) := by
  have hm := mono _ (at_eq c hj ▸ List.getElem_mem hj)
  refine ⟨by simpa [mk] using hm.1,by simpa [mk] using hm.2,?_⟩
  intro w hw
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hw
  have h := bound c p R back ok hj ha
  have le := rnk_mono R (Nat.le_of_lt hj)
  rw [size_strip]
  change _ < n+rnk R c.size
  omega

theorem finalEq (mono : Monotone2 c) (back : ReadsBack n c) (ok : safe n c R)
    (j : Nat) (hj : j<c.size) (x : bits n) :
    finalValue (strip c p R) (mk c p R j) x = v c (x ∘ p) (n+j) := by
  rw [at_value _ back _ hj]
  simp only [finalValue,mk,List.map_map]
  congr 1
  apply List.map_congr_left
  intro a ha
  apply evaluate c p R mono back ok
  · have := back j hj a ha; omega
  · exact ok j hj a ha

end PEqualNP.Outside.L_meta_17649_aux

open PEqualNP.Outside.L_meta_17649_aux in
theorem PEqualNP.Outside.L_meta_17649 : ∀ (x1 : ℕ),   have x2 : PEqualNP.CircuitLowerBounds.Circuit → PEqualNP.CircuitLowerBounds.Gate → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : PEqualNP.CircuitLowerBounds.Gate) => (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ x3.inputs.length ≤ (2 : ℕ) ∧ ∀ x4 ∈ x3.inputs, x4 < x1 + x2.size;   have x3 : PEqualNP.CircuitLowerBounds.Circuit → PEqualNP.CircuitLowerBounds.Gate → (Fin x1 → Bool) → Bool := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : PEqualNP.CircuitLowerBounds.Gate) (x5 : Fin x1 → Bool) => x4.op.eval (List.map (fun (x6 : ℕ) => (x3.wires (List.ofFn x5)).getD x6 Bool.false) x4.inputs);   have x4 : Bool → Bool × Bool → Bool × Bool := fun (x4 : Bool) (x5 : Bool × Bool) => if x4 = Bool.true then x5.swap else x5;   ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 x7 : ℕ),     PEqualNP.MetaComplexity.Monotone2 x5 →       PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x5 →         x1 ≤ x6 →           x1 ≤ x7 →             x6 < x1 + x5.size →               x7 < x1 + x5.size →                 x6 ≠ x7 →                   (∀ x15 ∈ x5.gates, x6 ∉ x15.inputs ∧ x7 ∉ x15.inputs) →                     ∀ (x16 : Equiv.Perm (Fin x1)) (x17 : Bool),                       ∃ (x18 : PEqualNP.CircuitLowerBounds.Circuit) (x19 : PEqualNP.CircuitLowerBounds.Gate) (x20 : PEqualNP.CircuitLowerBounds.Gate),                         x18.size + (2 : ℕ) ≤ x5.size ∧                           PEqualNP.MetaComplexity.Monotone2 x18 ∧                             PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x18 ∧                               x2 x18 x19 ∧                                 x2 x18 x20 ∧                                   ∀ (x21 : Fin x1 → Bool),                                     have x22 : List Bool := x5.wires (List.ofFn (x21 ∘ ⇑x16));                                     (x3 x18 x19 x21, x3 x18 x20 x21) = x4 x17 (x22.getD x6 Bool.false, x22.getD x7 Bool.false) := by
  intro n
  dsimp only
  intro c a b mono back ha hb ba bb ne dead p swap
  let A := a-n
  let B := b-n
  have ea : n+A=a := by dsimp [A]; omega
  have eb : n+B=b := by dsimp [B]; omega
  have ab : A≠B := by omega
  have al : A<c.size := by omega
  have bl : B<c.size := by omega
  let R : Finset Nat := {A,B}
  have ok : safe n c R := by
    intro j hj w hw hn
    have gmem : atG c j ∈ c.gates := at_eq c hj ▸ List.getElem_mem hj
    obtain ⟨na,nb⟩ := dead _ gmem
    intro h
    have opts : w-n=A ∨ w-n=B := by simpa [R] using h
    rcases opts with h | h
    · exact na ((show w=a by omega) ▸ hw)
    · exact nb ((show w=b by omega) ▸ hw)
  have sz : (strip c p R).size+2≤c.size := by
    have inside : ∀ i ∈ R, i<c.size := by
      intro i hi
      have opts : i=A ∨ i=B := by simpa [R] using hi
      rcases opts with rfl | rfl <;> assumption
    have cardR : R.card=2 := by simp [R,ab]
    have minSz : 2≤c.size := by omega
    rw [size_strip,keep,filt_len R c.size inside,cardR]; omega
  have m := model c p R mono back ok
  have eA (x : bits n) := finalEq c p R mono back ok A al x
  have eB (x : bits n) := finalEq c p R mono back ok B bl x
  simp only [ea] at eA
  simp only [eb] at eB
  cases swap with
  | false =>
    exact ⟨_,mk c p R A,mk c p R B,sz,m.1,m.2,terminal c p R mono back ok A al,
      terminal c p R mono back ok B bl,fun x => Prod.ext (eA x) (eB x)⟩
  | true =>
    exact ⟨_,mk c p R B,mk c p R A,sz,m.1,m.2,terminal c p R mono back ok B bl,
      terminal c p R mono back ok A al,fun x => Prod.ext (eB x) (eA x)⟩
