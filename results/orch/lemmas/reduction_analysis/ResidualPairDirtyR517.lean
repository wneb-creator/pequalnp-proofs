import PEqualNP.Outside.L_meta_2656

namespace PEqualNP.Outside.L_meta_650

def incidenceEdges : List (ℕ × ℕ) :=
  [(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)]

def matchingColumn (p : Fin 13) : Fin 13 :=
  ![0, 2, 11, 6, 10, 8, 7, 9, 5, 4, 12, 3, 1] p

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma matchingColumn_injective : Function.Injective matchingColumn := by
  intro p q h
  fin_cases p <;> fin_cases q <;> first | rfl | norm_num [matchingColumn] at h

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma matchingColumn_edge : ∀ p : Fin 13,
    (p.val, 13 + (matchingColumn p).val) ∈ incidenceEdges := by
  intro p
  fin_cases p <;> decide

def leftVertex (p : Fin 13) : Fin 26 := ⟨p.val, by omega⟩

def rightVertex (l : Fin 13) : Fin 26 := ⟨13 + l.val, by omega⟩

lemma matching_cover_card (T : Finset (Fin 26))
    (hT : ∀ p : Fin 13, leftVertex p ∈ T ∨ rightVertex (matchingColumn p) ∈ T) :
    13 ≤ T.card := by
  let choose : Fin 13 → Fin 26 := fun p =>
    if leftVertex p ∈ T then leftVertex p else rightVertex (matchingColumn p)
  have hc : ∀ p, choose p ∈ T := by
    intro p
    dsimp [choose]
    split_ifs with hp
    · exact hp
    · exact (hT p).resolve_left hp
  have hi : Function.Injective choose := by
    intro p q h
    dsimp [choose] at h
    split_ifs at h with hp hq hq
    · apply Fin.ext
      exact congrArg (fun v : Fin 26 => v.val) h
    · have hv := congrArg Fin.val h
      dsimp [leftVertex, rightVertex] at hv
      have := p.isLt
      omega
    · have hv := congrArg Fin.val h
      dsimp [leftVertex, rightVertex] at hv
      have := q.isLt
      omega
    · apply matchingColumn_injective
      apply Fin.ext
      have hv := congrArg Fin.val h
      dsimp [rightVertex] at hv
      omega
  have hs : Finset.univ.image choose ⊆ T := by
    intro v hv
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hv
    exact hc p
  have hb := Finset.card_le_card hs
  simpa [Finset.card_image_of_injective, hi] using hb

lemma incidence_cover_card (T : Finset (Fin 26))
    (hT : ∀ u v : Fin 26, (u.val, v.val) ∈ incidenceEdges → u ∈ T ∨ v ∈ T) :
    13 ≤ T.card := by
  apply matching_cover_card T
  intro p
  apply hT
  exact matchingColumn_edge p


-- Research partial: the imported outside theorem is not a permitted final dependency.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def incidenceGraph : SimpleGraph (Fin 26) where
  Adj u v := (u.val, v.val) ∈ incidenceEdges ∨ (v.val, u.val) ∈ incidenceEdges
  symm := ⟨by intro u v h; exact h.symm⟩
  loopless := ⟨by
    intro u
    fin_cases u <;> decide⟩

instance incidenceGraph_decidable : DecidableRel incidenceGraph.Adj :=
  fun u v => inferInstanceAs (Decidable
    ((u.val, v.val) ∈ incidenceEdges ∨ (v.val, u.val) ∈ incidenceEdges))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma incidenceGraph_noFour : PEqualNP.TopForm.NoFourCycle incidenceGraph := by
  intro a b h
  fin_cases a <;> fin_cases b <;> first | exact (h rfl).elim | decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma incidenceGraph_edges : incidenceGraph.edgeFinset.card = 52 := by decide +kernel

lemma incidenceGraph_noRectangle (a b c d : Fin 26) (hac : a ≠ c) (hbd : b ≠ d) :
    ¬ (incidenceGraph.Adj a b ∧ incidenceGraph.Adj b c ∧
      incidenceGraph.Adj c d ∧ incidenceGraph.Adj d a) := by
  rintro ⟨hab, hbc, hcd, hda⟩
  have sub : ({b, d} : Finset (Fin 26)) ⊆
      Finset.univ.filter (fun w => incidenceGraph.Adj a w ∧ incidenceGraph.Adj c w) := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · simp [hab, hbc.symm]
    · simp [hda.symm, hcd]
  have card := Finset.card_le_card sub
  have upper := incidenceGraph_noFour a c hac
  have two : ({b, d} : Finset (Fin 26)).card = 2 := by simp [hbd]
  omega

lemma incidenceGraph_cover (T : Finset (Fin 26))
    (hT : ∀ u v, incidenceGraph.Adj u v → u ∈ T ∨ v ∈ T) : 13 ≤ T.card := by
  apply incidence_cover_card T
  intro u v huv
  exact hT u v (Or.inl huv)

def postedValue (x : Fin 26 → Bool) : Prop :=
  ∃ u v : Fin 26, (u.val, v.val) ∈ incidenceEdges ∧ x u = true ∧ x v = true

lemma incidenceGraph_value (x : Fin 26 → Bool) :
    (∃ u v : Fin 26, incidenceGraph.Adj u v ∧ x u = true ∧ x v = true) ↔
      postedValue x := by
  constructor
  · rintro ⟨u,v,h,hu,hv⟩
    rcases h with h | h
    · exact ⟨u,v,h,hu,hv⟩
    · exact ⟨v,u,h,hv,hu⟩
  · rintro ⟨u,v,h,hu,hv⟩
    exact ⟨u,v,Or.inl h,hu,hv⟩

def smallInput (x : Fin 26 → Bool) : Prop :=
  x = (fun _ => false) ∨
  (∃ u : Fin 26, x = fun z => decide (z = u)) ∨
  (∃ u v : Fin 26, x = fun z => decide (z = u ∨ z = v))

lemma pair_clean_lower (C : Circuit) (mono : Monotone2 C)
    (correct : ∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔ postedValue x)
    (clean : ∀ (i : Fin C.gates.length) (x : Fin 26 → Bool), smallInput x →
      (C.gates.get i).op = GateOp.and →
      (C.wires (List.ofFn x)).getD (26 + i.val) false = true → postedValue x) :
    64 ≤ C.size := by
  obtain ⟨T,cover,bound⟩ := PEqualNP.Outside.L_meta_2656.pairCleanBound
    26 incidenceGraph incidenceGraph_noRectangle C.gates C.output mono
    (fun x => Bool.eq_iff_iff.mpr (by
      simp only [decide_eq_true_eq]
      exact (correct x).trans (incidenceGraph_value x).symm))
    (fun i x hx hop hv => (incidenceGraph_value x).mpr (clean i x hx hop hv))
  have lower := incidenceGraph_cover T cover
  rw [incidenceGraph_edges] at bound
  change 64 ≤ C.gates.length
  omega

lemma small_circuit_has_dirty_pair (C : Circuit) (mono : Monotone2 C)
    (size : C.size ≤ 63)
    (correct : ∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔ postedValue x) :
    ∃ (i : Fin C.gates.length) (x : Fin 26 → Bool), smallInput x ∧
      (C.gates.get i).op = GateOp.and ∧
      (C.wires (List.ofFn x)).getD (26 + i.val) false = true ∧ ¬ postedValue x := by
  by_contra h
  have clean : ∀ (i : Fin C.gates.length) (x : Fin 26 → Bool), smallInput x →
      (C.gates.get i).op = GateOp.and →
      (C.wires (List.ofFn x)).getD (26 + i.val) false = true → postedValue x := by
    intro i x hx hop hv
    by_contra hf
    exact h ⟨i,x,hx,hop,hv,hf⟩
  have lower := pair_clean_lower C mono correct clean
  omega


def attachRun (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

def shiftedGate (g : Gate) : Gate := ⟨g.op, g.inputs.map Nat.succ⟩

lemma attachRun_length (gs : List Gate) (x : List Bool) :
    (attachRun gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    simp only [attachRun, List.foldl_cons] at *
    rw [ih]
    simp
    omega

lemma shiftedGate_run (gs : List Gate) (b : Bool) (x : List Bool) :
    attachRun (gs.map shiftedGate) (b :: x) = b :: attachRun gs x := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    simp only [attachRun, List.map_cons, List.foldl_cons, shiftedGate,
      List.map_map, Function.comp_def, List.getD_cons_succ]
    exact ih _

def attachedPoint (D : Circuit) (j : ℕ) : Circuit :=
  ⟨D.gates.map shiftedGate ++
    [⟨.and, [0, j + 1]⟩, ⟨.or, [D.output + 1, 26 + D.size]⟩],
    27 + D.size⟩

lemma attachedPoint_size (D : Circuit) (j : ℕ) :
    (attachedPoint D j).size = D.size + 2 := by
  simp [attachedPoint, Circuit.size]

lemma attachedPoint_monotone (D : Circuit) (j : ℕ) (hm : Monotone2 D) :
    Monotone2 (attachedPoint D j) := by
  intro g hg
  change g ∈ D.gates.map shiftedGate ++ _ at hg
  rcases List.mem_append.mp hg with hmap | hlast
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hmap
    obtain ⟨op, arity⟩ := hm a ha
    exact ⟨op, by simpa [shiftedGate] using arity⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hlast
    rcases hlast with rfl | rfl <;> simp

lemma attachedPoint_eval (D : Circuit) (j : ℕ)
    (hout : D.output < 25 + D.size) (b : Bool) (y : Fin 25 → Bool) :
    (attachedPoint D j).eval (b :: List.ofFn y) =
      (D.eval (List.ofFn y) || (b && (D.wires (List.ofFn y)).getD j false)) := by
  let w := D.wires (List.ofFn y)
  have len : w.length = 25 + D.size := by
    simpa only [w, Circuit.wires, Circuit.size, attachRun, List.length_ofFn]
      using attachRun_length D.gates (List.ofFn y)
  have shifted : attachRun (D.gates.map shiftedGate) (b :: List.ofFn y) = b :: w :=
    shiftedGate_run _ _ _
  change (attachRun (D.gates.map shiftedGate ++
    [⟨.and, [0, j + 1]⟩, ⟨.or, [D.output + 1, 26 + D.size]⟩])
    (b :: List.ofFn y)).getD (27 + D.size) false = _
  unfold attachRun at shifted ⊢
  rw [List.foldl_append, shifted]
  simp only [List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil,
    GateOp.eval, List.all_cons, List.all_nil, List.any_cons, List.any_nil,
    List.getD_cons_zero, List.getD_cons_succ, Bool.and_true, Bool.or_false, id_eq]
  have readOutput : ((b :: w) ++ [b && w.getD j false]).getD (D.output + 1) false =
      w.getD D.output false := by
    rw [List.getD_append]
    · rfl
    · simp only [List.length_cons, len]
      omega
  have readNew : ((b :: w) ++ [b && w.getD j false]).getD (26 + D.size) false =
      (b && w.getD j false) := by
    rw [List.getD_append_right]
    · simp only [List.length_cons, len]
      rw [show 26 + D.size - (25 + D.size + 1) = 0 by omega]
      rfl
    · simp only [List.length_cons, len]
      omega
  rw [readOutput, readNew, List.getD_append_right]
  · simp only [List.length_append, List.length_cons, List.length_nil, len]
    rw [show 27 + D.size - (25 + D.size + 1 + (0 + 1)) = 0 by omega]
    rfl
  · simp only [List.length_append, List.length_cons, List.length_nil, len]
    omega

lemma attach_point (D : Circuit) (j : ℕ) (hm : Monotone2 D)
    (hout : D.output < 25 + D.size) (_hj : j < 25 + D.size) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ D.size + 2 ∧
      ∀ (b : Bool) (y : Fin 25 → Bool),
        C.eval (b :: List.ofFn y) =
          (D.eval (List.ofFn y) || (b && (D.wires (List.ofFn y)).getD j false)) := by
  exact ⟨attachedPoint D j, attachedPoint_monotone D j hm,
    le_of_eq (attachedPoint_size D j), attachedPoint_eval D j hout⟩


def residualValue (y : Fin 25 → Bool) : Prop :=
  ∃ u v : Fin 25, (u.succ.val, v.succ.val) ∈ incidenceEdges ∧
    y u = true ∧ y v = true

def residualSmallInput (y : Fin 25 → Bool) : Prop :=
  y = (fun _ => false) ∨
  (∃ u : Fin 25, y = fun z => decide (z = u)) ∨
  (∃ u v : Fin 25, y = fun z => decide (z = u ∨ z = v))

lemma smallInput_tail (x : Fin 26 → Bool) (h : smallInput x) :
    residualSmallInput (fun i => x i.succ) := by
  rcases h with rfl | ⟨u,rfl⟩ | ⟨u,v,rfl⟩
  · exact Or.inl rfl
  · cases u using Fin.cases with
    | zero =>
      left
      funext i
      simp
    | succ u =>
      right; left
      refine ⟨u, ?_⟩
      funext i
      simp
  · cases u using Fin.cases with
    | zero =>
      cases v using Fin.cases with
      | zero =>
        left
        funext i
        simp
      | succ v =>
        right; left
        refine ⟨v, ?_⟩
        funext i
        simp
    | succ u =>
      cases v using Fin.cases with
      | zero =>
        right; left
        refine ⟨u, ?_⟩
        funext i
        simp
      | succ v =>
        right; right
        refine ⟨u,v,?_⟩
        funext i
        simp

lemma independent_tail (x : Fin 26 → Bool) (h : ¬ postedValue x) :
    ¬ residualValue (fun i => x i.succ) := by
  rintro ⟨u,v,huv,hu,hv⟩
  exact h ⟨u.succ,v.succ,huv,hu,hv⟩

lemma attachRun_preserve (gs : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length) : (attachRun gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [attachRun, List.foldl_cons] at *
    rw [ih _ (by simp; omega)]
    exact List.getD_append _ _ _ _ hi

lemma attachedPoint_old_wire (D : Circuit) (j i : ℕ) (hi : i < D.gates.length)
    (b : Bool) (y : Fin 25 → Bool) :
    ((attachedPoint D j).wires (b :: List.ofFn y)).getD (26 + i) false =
      (D.wires (List.ofFn y)).getD (25 + i) false := by
  let w := D.wires (List.ofFn y)
  have len : w.length = 25 + D.gates.length := by
    exact attachRun_length D.gates (List.ofFn y) |>.trans (by simp)
  change (attachRun (D.gates.map shiftedGate ++ _) (b :: List.ofFn y)).getD _ _ = _
  have happ (gs hs : List Gate) (z : List Bool) :
      attachRun (gs ++ hs) z = attachRun hs (attachRun gs z) := List.foldl_append
  rw [happ, shiftedGate_run, attachRun_preserve]
  · change (b :: w).getD (26+i) false = _
    rw [show 26+i=Nat.succ (25+i) by omega]
    rfl
  · change 26+i < (b :: w).length
    simp only [List.length_cons,len]
    omega

lemma attachedPoint_new_wire (D : Circuit) (j : ℕ) (b : Bool) (y : Fin 25 → Bool) :
    ((attachedPoint D j).wires (b :: List.ofFn y)).getD (26 + D.size) false =
      (b && (D.wires (List.ofFn y)).getD j false) := by
  let w := D.wires (List.ofFn y)
  have len : w.length = 25 + D.size := by
    exact attachRun_length D.gates (List.ofFn y) |>.trans (by simp [Circuit.size])
  change (attachRun (D.gates.map shiftedGate ++ _) (b :: List.ofFn y)).getD _ _ = _
  have happ (gs hs : List Gate) (z : List Bool) :
      attachRun (gs ++ hs) z = attachRun hs (attachRun gs z) := List.foldl_append
  rw [happ, shiftedGate_run]
  change (attachRun ([⟨.and,[0,j+1]⟩] ++ [⟨.or,[D.output+1,26+D.size]⟩])
    (b :: w)).getD (26+D.size) false = _
  rw [happ]
  have first : attachRun [⟨.and,[0,j+1]⟩] (b :: w) =
      (b :: w) ++ [b && w.getD j false] := by
    simp [attachRun,GateOp.eval]
  rw [first]
  rw [attachRun_preserve]
  · rw [List.getD_append_right]
    · simp only [List.length_cons,len]
      rw [show 26+D.size-(25+D.size+1)=0 by omega]
      rfl
    · simp only [List.length_cons,len]
      omega
  · simp only [List.length_append,List.length_cons,List.length_nil,len]
    omega

lemma attachedPoint_old_op (D : Circuit) (j : ℕ)
    (i : Fin (attachedPoint D j).gates.length) (hi : i.val < D.gates.length) :
    ((attachedPoint D j).gates.get i).op = (D.gates.get ⟨i.val,hi⟩).op := by
  change ((D.gates.map shiftedGate ++
    [⟨.and,[0,j+1]⟩,⟨.or,[D.output+1,26+D.size]⟩])[i.val]).op = (D.gates[i.val]).op
  rw [List.getElem_append_left (by simpa using hi)]
  simp [shiftedGate]

lemma residual_pair_dirty (D : Circuit) (j : ℕ) (mono : Monotone2 D)
    (size : D.size ≤ 61) (hout : D.output < 25 + D.size)
    (correct : ∀ x : Fin 26 → Bool,
      (attachedPoint D j).eval (List.ofFn x) = true ↔ postedValue x) :
    ∃ (i : Fin D.gates.length) (y : Fin 25 → Bool), residualSmallInput y ∧
      (D.gates.get i).op = GateOp.and ∧
      (D.wires (List.ofFn y)).getD (25+i.val) false = true ∧ ¬ residualValue y := by
  obtain ⟨i,x,hsmall,hop,hval,hfalse⟩ := small_circuit_has_dirty_pair
    (attachedPoint D j) (attachedPoint_monotone D j mono)
    (by rw [attachedPoint_size]; omega) correct
  let y : Fin 25 → Bool := fun k => x k.succ
  have xsplit : List.ofFn x = x 0 :: List.ofFn y := List.ofFn_succ
  have old : i.val < D.gates.length := by
    by_contra hge
    have length : (attachedPoint D j).gates.length = D.gates.length+2 := by
      simp [attachedPoint]
    have upper : i.val < D.gates.length+2 := by simpa only [length] using i.isLt
    have cases : i.val = D.gates.length ∨ i.val = D.gates.length+1 := by omega
    rcases cases with hi | hi
    · have hv : (x 0 && (D.wires (List.ofFn y)).getD j false) = true := by
        rw [xsplit] at hval
        rw [← attachedPoint_new_wire D j (x 0) y]
        simpa only [hi,Circuit.size] using hval
      apply hfalse
      apply (correct x).mp
      rw [xsplit,attachedPoint_eval D j hout]
      rw [Bool.or_eq_true]
      exact Or.inr hv
    · have hior : ((attachedPoint D j).gates.get i).op = GateOp.or := by
        change ((D.gates.map shiftedGate ++
          [⟨.and,[0,j+1]⟩,⟨.or,[D.output+1,26+D.size]⟩])[i.val]).op = GateOp.or
        rw [List.getElem_append_right (by simp; omega)]
        simp [hi]
      rw [hior] at hop
      cases hop
  refine ⟨⟨i.val,old⟩,y,smallInput_tail x hsmall,?_,?_,independent_tail x hfalse⟩
  · exact (attachedPoint_old_op D j i old) ▸ hop
  · rw [xsplit,attachedPoint_old_wire D j i.val old] at hval
    exact hval


def residualNeighbor (y : Fin 25 → Bool) : Bool := y 12 || y 13 || y 15 || y 21

def residualI (i k : Fin 25) : Prop :=
  i.val < 12 ∧ 12 ≤ k.val ∧ (i.val+k.val+2)%13 ∈ ([0,1,3,9] : List ℕ)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma residual_edges : ∀ i k : Fin 25,
    (i.succ.val,k.succ.val) ∈ incidenceEdges ↔ residualI i k := by
  unfold residualI
  decide +kernel

lemma residualValue_iff_I (y : Fin 25 → Bool) :
    residualValue y ↔ ∃ i k : Fin 25, residualI i k ∧ y i = true ∧ y k = true := by
  simp only [residualValue,residual_edges]

lemma postedValue_split (x : Fin 26 → Bool) :
    postedValue x ↔ residualValue (fun i => x i.succ) ∨
      (x 0 = true ∧ residualNeighbor (fun i => x i.succ) = true) := by
  have row0 : ∀ v : Fin 26, (0,v.val) ∈ incidenceEdges ↔
      v=13 ∨ v=14 ∨ v=16 ∨ v=22 := by decide
  have col0 : ∀ i : Fin 25, (i.succ.val,0) ∉ incidenceEdges := by decide
  constructor
  · rintro ⟨u,v,mem,hu,hv⟩
    cases u using Fin.cases with
    | zero =>
      right
      refine ⟨hu,?_⟩
      change (x 13 || x 14 || x 16 || x 22)=true
      rcases (row0 v).mp mem with rfl | rfl | rfl | rfl <;> simp [hv]
    | succ i =>
      cases v using Fin.cases with
      | zero => exact False.elim (col0 i mem)
      | succ k => exact Or.inl ⟨i,k,mem,hu,hv⟩
  · rintro (⟨i,k,hik,hi,hk⟩ | ⟨h0,hn⟩)
    · exact ⟨i.succ,k.succ,hik,hi,hk⟩
    · change (x 13 || x 14 || x 16 || x 22)=true at hn
      have make (v : Fin 26) (h : v=13 ∨ v=14 ∨ v=16 ∨ v=22) (hv : x v=true) :
          postedValue x := ⟨0,v,(row0 v).mpr h,h0,hv⟩
      simp only [Bool.or_eq_true_iff] at hn
      rcases hn with ((h|h)|h)|h
      · exact make 13 (by decide) h
      · exact make 14 (by decide) h
      · exact make 16 (by decide) h
      · exact make 22 (by decide) h

lemma attachedPoint_correct (D : Circuit) (j : ℕ) (hout : D.output < 25+D.size)
    (reads : ∀ y : Fin 25 → Bool,
      (D.eval (List.ofFn y)=true ↔ residualValue y) ∧
      (D.eval (List.ofFn y)=false →
        (D.wires (List.ofFn y)).getD j false = residualNeighbor y)) :
    ∀ x : Fin 26 → Bool, (attachedPoint D j).eval (List.ofFn x)=true ↔ postedValue x := by
  intro x
  rw [postedValue_split,List.ofFn_succ,attachedPoint_eval D j hout]
  let y : Fin 25 → Bool := fun i => x i.succ
  obtain ⟨detect,tap⟩ := reads y
  change (D.eval (List.ofFn y) || (x 0 && (D.wires (List.ofFn y)).getD j false))=true ↔
    residualValue y ∨ (x 0=true ∧ residualNeighbor y=true)
  cases h : D.eval (List.ofFn y) with
  | true => simp [detect.mp h]
  | false =>
    have hr : ¬ residualValue y := fun r => Bool.noConfusion (h.symm.trans (detect.mpr r))
    rw [tap h]
    simpa only [Bool.false_or,Bool.and_eq_true,hr,false_or]

lemma residual_joint_pair_dirty (D : Circuit) (j : ℕ) (mono : Monotone2 D)
    (size : D.size ≤ 61) (hout : D.output < 25+D.size) (_hj : j < 25+D.size)
    (reads : ∀ y : Fin 25 → Bool,
      (D.eval (List.ofFn y)=true ↔ ∃ i k : Fin 25,
        residualI i k ∧ y i=true ∧ y k=true) ∧
      (D.eval (List.ofFn y)=false →
        (D.wires (List.ofFn y)).getD j false = (y 12 || y 13 || y 15 || y 21))) :
    ∃ (i : Fin D.gates.length) (y : Fin 25 → Bool), residualSmallInput y ∧
      (D.gates.get i).op = GateOp.and ∧
      (D.wires (List.ofFn y)).getD (25+i.val) false = true ∧
      ¬ ∃ a b : Fin 25, residualI a b ∧ y a=true ∧ y b=true := by
  have correct := attachedPoint_correct D j hout (fun y =>
    ⟨(reads y).1.trans (residualValue_iff_I y).symm,(reads y).2⟩)
  obtain ⟨i,y,hy,hi,hv,hfalse⟩ := residual_pair_dirty D j mono size hout correct
  exact ⟨i,y,hy,hi,hv,fun h => hfalse ((residualValue_iff_I y).mpr h)⟩

end PEqualNP.Outside.L_meta_650
