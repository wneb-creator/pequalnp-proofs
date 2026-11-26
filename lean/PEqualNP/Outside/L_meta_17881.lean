import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP PEqualNP.TopForm PEqualNP.EdgeOwnership

namespace PEqualNP.Outside.L_meta_17881

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

def shiftW (n k w : ℕ) : ℕ :=
  if w < n + k then w else w - 1

def unshiftW (n k w : ℕ) : ℕ :=
  if w < n + k then w else w + 1

def unshiftG (k j : ℕ) : ℕ :=
  if j < k then j else j + 1

def shiftGate (n k : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (shiftW n k)⟩

def delDead (n k : ℕ) (C : Circuit) : Circuit :=
  ⟨(C.gates.eraseIdx k).map (shiftGate n k), shiftW n k C.output⟩

lemma unshiftW_shiftW (n k w : ℕ) (hne : w ≠ n + k) :
    unshiftW n k (shiftW n k w) = w := by
  unfold unshiftW shiftW
  split_ifs <;> omega


lemma delDead_size (n k : ℕ) (C : Circuit) (hk : k < C.size) :
    (delDead n k C).size + 1 = C.size := by
  unfold Circuit.size at hk ⊢
  unfold delDead
  simp only [List.length_map, List.length_eraseIdx_of_lt hk]
  omega

lemma delDead_length (n k : ℕ) (C : Circuit) (hk : k < C.gates.length) :
    (delDead n k C).gates.length = C.gates.length - 1 := by
  simp [delDead, List.length_eraseIdx_of_lt hk]

lemma delDead_gateAt (n k : ℕ) (C : Circuit) (hk : k < C.gates.length)
    (j : ℕ) (hj : j < (delDead n k C).gates.length) :
    gateAt (delDead n k C) j = shiftGate n k (gateAt C (unshiftG k j)) := by
  have hj_lt : j < C.gates.length - 1 := by
    rw [← delDead_length n k C hk]; exact hj
  have hj_e : j < (C.gates.eraseIdx k).length := by
    rw [List.length_eraseIdx_of_lt hk]; exact hj_lt
  rw [gateAt_eq hj]
  simp only [delDead, List.getElem_map, unshiftG]
  split_ifs with hjk
  · rw [List.getElem_eraseIdx_of_lt hj_e hjk, gateAt_eq (C := C) (j := j) (by omega)]
  · rw [List.getElem_eraseIdx_of_ge hj_e (by omega), gateAt_eq (C := C) (j := j + 1) (by omega)]


lemma delDead_readsBack (n k : ℕ) (C : Circuit) (hRB : ReadsBack n C)
    (hk : k < C.gates.length) (hno : ∀ j < C.gates.length, n + k ∉ (gateAt C j).inputs) :
    ReadsBack n (delDead n k C) := by
  intro j hj w' hw'
  rw [delDead_gateAt n k C hk j hj] at hw'
  simp only [shiftGate, List.mem_map] at hw'
  obtain ⟨w, hw, rfl⟩ := hw'
  have hj_len : j < C.gates.length - 1 := by
    rw [← delDead_length n k C hk]; exact hj
  have hj0_lt : unshiftG k j < C.gates.length := by
    unfold unshiftG; split_ifs <;> omega
  have hw_lt : w < n + unshiftG k j := hRB (unshiftG k j) hj0_lt w hw
  have hw_ne : w ≠ n + k := fun heq => hno (unshiftG k j) hj0_lt (heq ▸ hw)
  unfold shiftW
  unfold unshiftG at hw_lt
  split_ifs at hw_lt ⊢ <;> omega


def evalStep {α : Type} (d0 : α) (evalG : GateOp → List α → α) (acc : List α) (g : Gate) :
    List α :=
  acc ++ [evalG g.op (g.inputs.map fun i => acc.getD i d0)]

lemma foldl_evalStep_length {α : Type} (d0 : α) (evalG : GateOp → List α → α)
    (gs : List Gate) (acc : List α) :
    (gs.foldl (evalStep d0 evalG) acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, evalStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_evalStep_prefix {α : Type} (d0 : α) (evalG : GateOp → List α → α)
    (gs : List Gate) (acc : List α) (w : ℕ) (hw : w < acc.length) :
    (gs.foldl (evalStep d0 evalG) acc).getD w d0 = acc.getD w d0 := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    have hw' : w < (evalStep d0 evalG acc g).length := by
      simp only [evalStep, List.length_append, List.length_singleton]
      omega
    rw [List.foldl_cons, ih (evalStep d0 evalG acc g) hw']
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    simp only [evalStep, List.getElem?_append_left hw]

lemma foldl_evalStep_gate {α : Type} (d0 : α) (evalG : GateOp → List α → α)
    (n : ℕ) (C : Circuit) (init : List α) (hinit : init.length = n)
    (hRB : ReadsBack n C) (j : ℕ) (hj : j < C.gates.length) :
    (C.gates.foldl (evalStep d0 evalG) init).getD (n + j) d0 =
      evalG (gateAt C j).op
        ((gateAt C j).inputs.map fun u => (C.gates.foldl (evalStep d0 evalG) init).getD u d0) := by
  have hsplit : C.gates = C.gates.take j ++ [C.gates[j]] ++ C.gates.drop (j + 1) := by
    have h1 := List.take_append_drop j C.gates
    have h2 : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    simp only [List.append_assoc, List.singleton_append, h1]
  set acc := (C.gates.take j).foldl (evalStep d0 evalG) init with hacc
  have hacc_len : acc.length = n + j := by
    rw [hacc, foldl_evalStep_length, hinit, List.length_take]
    omega
  have hpref : ∀ u < n + j,
      (C.gates.foldl (evalStep d0 evalG) init).getD u d0 = acc.getD u d0 := by
    intro u hu
    conv_lhs => rw [← List.take_append_drop j C.gates]
    rw [List.foldl_append, ← hacc]
    exact foldl_evalStep_prefix d0 evalG (C.gates.drop j) acc u (by omega)
  have hval : (C.gates.foldl (evalStep d0 evalG) init).getD (n + j) d0 =
      evalG C.gates[j].op (C.gates[j].inputs.map fun u => acc.getD u d0) := by
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_append, ← hacc, List.foldl_cons, List.foldl_nil]
    have hlen : n + j < (evalStep d0 evalG acc C.gates[j]).length := by
      simp only [evalStep, List.length_append, List.length_singleton]
      omega
    rw [foldl_evalStep_prefix d0 evalG (C.gates.drop (j + 1)) (evalStep d0 evalG acc C.gates[j])
      (n + j) hlen]
    rw [List.getD_eq_getElem?_getD]
    simp only [evalStep, List.getElem?_append_right (by omega : acc.length ≤ n + j),
      hacc_len, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  rw [hval, gateAt_eq hj]
  congr 1
  apply List.map_congr_left
  intro u hu
  rw [← gateAt_eq hj] at hu
  exact (hpref u (hRB j hj u hu)).symm

lemma delDead_evalStep_eq {α : Type} (d0 : α) (evalG : GateOp → List α → α)
    (n k : ℕ) (C : Circuit) (init : List α) (hinit : init.length = n)
    (hRB : ReadsBack n C) (hk : k < C.gates.length)
    (hno : ∀ j < C.gates.length, n + k ∉ (gateAt C j).inputs) :
    ∀ w : ℕ,
      ((delDead n k C).gates.foldl (evalStep d0 evalG) init).getD w d0 =
        (C.gates.foldl (evalStep d0 evalG) init).getD (unshiftW n k w) d0 := by
  have hRB' : ReadsBack n (delDead n k C) := delDead_readsBack n k C hRB hk hno
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw_oob : n + (delDead n k C).gates.length ≤ w
    · have hlen' : ((delDead n k C).gates.foldl (evalStep d0 evalG) init).length =
          n + (delDead n k C).gates.length := by
        rw [foldl_evalStep_length, hinit]
      have hlen : (C.gates.foldl (evalStep d0 evalG) init).length = n + C.gates.length := by
        rw [foldl_evalStep_length, hinit]
      have hdl := delDead_length n k C hk
      have huw : n + C.gates.length ≤ unshiftW n k w := by
        unfold unshiftW; split_ifs <;> omega
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
    · push Not at hw_oob
      by_cases hwn : w < n
      · have huw : unshiftW n k w = w := by unfold unshiftW; split_ifs <;> omega
        rw [huw]
        rw [foldl_evalStep_prefix d0 evalG (delDead n k C).gates init w (by omega)]
        rw [foldl_evalStep_prefix d0 evalG C.gates init w (by omega)]
      · set j := w - n with hj_def
        have hw_eq : w = n + j := by omega
        have hj_lt : j < (delDead n k C).gates.length := by omega
        have hdl := delDead_length n k C hk
        have hj0_lt : unshiftG k j < C.gates.length := by
          unfold unshiftG; split_ifs <;> omega
        have huw : unshiftW n k (n + j) = n + unshiftG k j := by
          unfold unshiftW unshiftG; split_ifs <;> omega
        rw [hw_eq, huw]
        rw [foldl_evalStep_gate d0 evalG n (delDead n k C) init hinit hRB' j hj_lt]
        rw [foldl_evalStep_gate d0 evalG n C init hinit hRB (unshiftG k j) hj0_lt]
        rw [delDead_gateAt n k C hk j hj_lt]
        simp only [shiftGate, List.map_map]
        congr 1
        apply List.map_congr_left
        intro u hu
        have hu_lt : shiftW n k u < n + j := by
          have hmem : shiftW n k u ∈ (gateAt (delDead n k C) j).inputs := by
            rw [delDead_gateAt n k C hk j hj_lt]
            simp only [shiftGate, List.mem_map]
            exact ⟨u, hu, rfl⟩
          exact hRB' j hj_lt (shiftW n k u) hmem
        have hu_ne : u ≠ n + k := fun heq => hno (unshiftG k j) hj0_lt (heq ▸ hu)
        simp only [Function.comp_apply]
        rw [ih (shiftW n k u) (by omega), unshiftW_shiftW n k u hu_ne]

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

lemma inCone_trans (n : ℕ) (C : Circuit) (a k : ℕ) (hak : InCone n C a k) :
    ∀ j, InCone n C k j → InCone n C a j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k2, hk2, hin, h3 | h3⟩ := h
    · subst h3
      rw [inCone_iff]
      exact ⟨h0, k, hk2, hin, Or.inr hak⟩
    · rw [inCone_iff]
      exact ⟨h0, k2, hk2, hin, Or.inr (ih k2 hk2 h3)⟩

theorem exists_unread (n : ℕ) (C : Circuit) (T : List (ℕ×ℕ)) (M : IsAO2 n C)
    (bad : ¬∀ j<C.size, ReadTwo.isAnd C j → ∃ e∈T, ∃ w∈[e.1,e.2],
      w=n+j ∨ n≤w ∧ InCone n C j (w-n)) :
    ∃ k<C.size, (∀ e∈T, n+k≠e.1 ∧ n+k≠e.2) ∧
      ∀ j<C.gates.length, n+k ∉ (gateAt C j).inputs := by
  classical
  let used (j : ℕ) := ∃ e∈T, ∃ w∈[e.1,e.2], w=n+j ∨ n≤w ∧ InCone n C j (w-n)
  let unused := (Finset.range C.size).filter fun j => ¬used j
  have ne : unused.Nonempty := by
    by_contra h
    apply bad
    intro j hj _
    change used j
    by_contra no
    exact h ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,no⟩⟩
  let k := unused.max' ne
  have km : k∈unused := unused.max'_mem ne
  obtain ⟨small,notUsed⟩ := Finset.mem_filter.mp km
  have hk := Finset.mem_range.mp small
  refine ⟨k,hk,?_,?_⟩
  · intro e he
    constructor
    · intro eq
      exact notUsed ⟨e,he,e.1,by simp,Or.inl eq.symm⟩
    · intro eq
      exact notUsed ⟨e,he,e.2,by simp,Or.inl eq.symm⟩
  · intro j hj reads
    have ord := M.2.1 j hj (n+k) reads
    have kj : k<j := by omega
    have cone := (inCone_iff n C k j).mpr ⟨hj,k,kj,reads,Or.inl rfl⟩
    have uj : used j := by
      by_contra no
      have jm : j∈unused := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,no⟩
      have bound := Finset.le_max' unused j jm
      change j≤k at bound
      omega
    obtain ⟨e,he,w,hw,loc⟩ := uj
    apply notUsed
    refine ⟨e,he,w,hw,Or.inr ?_⟩
    rcases loc with eq | ⟨lo,h⟩
    · exact ⟨by omega,by simpa [eq] using cone⟩
    · exact ⟨lo,inCone_trans n C k j cone (w-n) h⟩

def packOp (op : GateOp) (vals : List ℕ) : ℕ :=
  if op.eval [false,true]=true then vals.getD 0 0 ||| vals.getD 1 0 else vals.getD 0 0 &&& vals.getD 1 0

def packStep (s : List ℕ) (g : Gate) : List ℕ :=
  let a := s.getD (g.inputs.getD 0 0) 0
  let b := s.getD (g.inputs.getD 1 0) 0
  s++[if g.op.eval [false,true]=true then a ||| b else a &&& b]

theorem packed_eq (gs : List Gate) (arity : ∀ g∈gs,g.inputs.length=2) (base : List ℕ) :
    gs.foldl packStep base=gs.foldl (evalStep 0 packOp) base := by
  induction gs generalizing base with
  | nil => rfl
  | cons g gs ih =>
    have ag := arity g (List.mem_cons_self ..)
    have step : packStep base g=evalStep 0 packOp base g := by
      obtain ⟨op,vs⟩ := g
      cases vs with
      | nil => contradiction
      | cons a xs =>
        cases xs with
        | nil => change 1=2 at ag; omega
        | cons b ys =>
          have len : ys.length=0 := by change (_::_::ys).length=2 at ag; simpa using ag
          obtain rfl := List.length_eq_zero_iff.mp len
          rfl
    rw [List.foldl_cons,List.foldl_cons,step]
    exact ih (fun h hm => arity h (List.mem_cons_of_mem _ hm)) _

theorem andCount_delete (n k : ℕ) (C : Circuit) : ReadTwo.nAnd C≤ReadTwo.nAnd (delDead n k C)+1 := by
  let _ : DecidableEq GateOp := gateOpDecEq
  let p := fun g : Gate => decide (g.op=.and)
  have erased (ls : List Gate) (j : ℕ) : ls.countP p ≤ (ls.eraseIdx j).countP p+1 := by
    induction ls generalizing j with
    | nil => simp
    | cons a ls ih =>
      cases j with
      | zero => cases h : p a <;> simp [h]
      | succ j =>
        cases h : p a <;> simp [h,List.eraseIdx] <;> have h' := ih j <;> omega
  unfold ReadTwo.nAnd
  simp only [delDead,←List.countP_eq_length_filter,List.countP_map]
  exact erased C.gates k

end PEqualNP.Outside.L_meta_17881

open PEqualNP.Outside.L_meta_17881

theorem PEqualNP.Outside.L_meta_17881 : (∀ (x1 : List ℕ),   have x2 : List ℕ → PEqualNP.CircuitLowerBounds.Gate → List ℕ := fun (x2 : List ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate) =>     have x4 : ℕ := x2.getD (x3.inputs.getD (0 : ℕ) (0 : ℕ)) (0 : ℕ);     have x5 : ℕ := x2.getD (x3.inputs.getD (1 : ℕ) (0 : ℕ)) (0 : ℕ);     x2 ++ [if x3.op.eval [Bool.false, Bool.true] = Bool.true then x4 ||| x5 else x4 &&& x5];   have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → ℕ := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) => (List.foldl x2 x1 x3.gates).getD x4 (0 : ℕ);   have x4 : PEqualNP.CircuitLowerBounds.Circuit → ℕ × ℕ → ℕ := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ × ℕ) => x3 x4 x5.1 &&& x3 x4 x5.2;   have x5 : ℕ → PEqualNP.CircuitLowerBounds.Circuit → List (ℕ × ℕ) → Prop := fun (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : List (ℕ × ℕ)) => ∀ x8 ∈ x7, x8.1 < x5 + x6.size ∧ x8.2 < x5 + x6.size;   have x6 : ℕ → PEqualNP.CircuitLowerBounds.Circuit → List (ℕ × ℕ) → Prop := fun (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 : List (ℕ × ℕ)) => ∀ x9 < x7.size, PEqualNP.ReadTwo.isAnd x7 x9 → ∃ x12 ∈ x8, ∃ x13 ∈ [x12.1, x12.2], x13 = x6 + x9 ∨ x6 ≤ x13 ∧ PEqualNP.EdgeOwnership.InCone x6 x7 x9 (x13 - x6);   ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 : List (ℕ × ℕ)), PEqualNP.TopForm.IsAO2 x1.length x7 → x5 x1.length x7 x8 → ¬x6 x1.length x7 x8 → ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit) (x13 : List (ℕ × ℕ)), PEqualNP.TopForm.IsAO2 x1.length x12 ∧ x5 x1.length x12 x13 ∧ x12.size + (1 : ℕ) = x7.size ∧ PEqualNP.ReadTwo.nAnd x7 ≤ PEqualNP.ReadTwo.nAnd x12 + (1 : ℕ) ∧ x13.length = x8.length ∧ List.map (x4 x12) x13 = List.map (x4 x7) x8 ∧ ∀ x14 < x12.size, ∃ x16 < x7.size, x3 x12 (x1.length + x14) = x3 x7 (x1.length + x16)) := by
  intro base f v prod bounds live C T model bd no
  let n := base.length
  obtain ⟨k,hk,out,noread⟩ := exists_unread n C T model no
  let D := delDead n k C
  let shift (e : ℕ×ℕ) := (shiftW n k e.1,shiftW n k e.2)
  have mapped (g : Gate) (hg : g ∈ D.gates) : (g.op=.and ∨ g.op=.or) ∧ g.inputs.length=2 := by
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
    have was := List.mem_of_mem_eraseIdx ha
    exact ⟨model.1 a was,by simp [shiftGate,model.2.2 a was]⟩
  have modelD : IsAO2 n D := ⟨fun g hg => (mapped g hg).1,delDead_readsBack n k C model.2.1 hk noread,
    fun g hg => (mapped g hg).2⟩
  have smaller := delDead_size n k C hk
  have transported (w : ℕ) : v D w=v C (unshiftW n k w) := by
    change (D.gates.foldl packStep base).getD w 0=(C.gates.foldl packStep base).getD (unshiftW n k w) 0
    rw [packed_eq D.gates modelD.2.2,packed_eq C.gates model.2.2]
    exact delDead_evalStep_eq 0 packOp n k C base rfl model.2.1 hk noread w
  have atShift (w : ℕ) (hn : n+k≠w) : v D (shiftW n k w)=v C w := by
    rw [transported,unshiftW_shiftW n k w hn.symm]
  refine ⟨D,T.map shift,modelD,?_,smaller,andCount_delete n k C,by simp,?_,?_⟩
  · intro z hz
    obtain ⟨e,hm,rfl⟩ := List.mem_map.mp hz
    obtain ⟨x,y⟩ := bd e hm
    obtain ⟨u,w⟩ := out e hm
    change e.1<n+C.size at x
    change e.2<n+C.size at y
    change shiftW n k e.1<n+D.size ∧ shiftW n k e.2<n+D.size
    change D.size+1=C.size at smaller
    unfold shiftW
    constructor <;> split_ifs <;> omega
  · rw [List.map_map]
    apply List.map_congr_left
    intro e hm
    obtain ⟨u,w⟩ := out e hm
    change (v D (shiftW n k e.1) &&& v D (shiftW n k e.2))=(v C e.1 &&& v C e.2)
    rw [atShift _ u,atShift _ w]
  · intro j hj
    refine ⟨unshiftG k j,?_,?_⟩
    · change D.size+1=C.size at smaller
      unfold unshiftG
      split_ifs <;> omega
    · change v D (n+j)=v C (n+unshiftG k j)
      rw [transported]
      apply congrArg (v C)
      unfold unshiftW unshiftG
      split_ifs <;> omega
