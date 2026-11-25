import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10760

open PEqualNP.CircuitLowerBounds

def normalizeWire (m i : ℕ) : ℕ := if i < m then i + 2 else 0

def normalizeInputs (m unit : ℕ) : List ℕ → List ℕ
  | [] => [unit, unit]
  | [a] => [normalizeWire m a, normalizeWire m a]
  | a :: b :: _ => [normalizeWire m a, normalizeWire m b]

def normalizeGate (m : ℕ) (g : Gate) : Gate :=
  ⟨g.op, match g.op with
    | GateOp.and => normalizeInputs m 1 g.inputs
    | GateOp.or => normalizeInputs m 0 g.inputs
    | GateOp.not => [normalizeWire m (g.inputs.headD m)]
    | _ => g.inputs.map (normalizeWire m)⟩

def normalizeGates : ℕ → List Gate → List Gate
  | _, [] => []
  | m, g :: gs => normalizeGate m g :: normalizeGates (m + 1) gs

def runGates (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun v g => v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]) w

def basisGate (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

lemma normalizeWire_lt (m i : ℕ) : normalizeWire m i < m + 2 := by
  unfold normalizeWire
  split_ifs <;> omega

lemma normalizeGate_op (m : ℕ) (g : Gate) : (normalizeGate m g).op = g.op := rfl

lemma normalizeGates_length (m : ℕ) (gs : List Gate) :
    (normalizeGates m gs).length = gs.length := by
  induction gs generalizing m with
  | nil => rfl
  | cons g gs ih => simp only [normalizeGates, List.length_cons, ih]

lemma normalizeWire_value (w : List Bool) (i : ℕ) :
    ([false, true] ++ w).getD (normalizeWire w.length i) false = w.getD i false := by
  unfold normalizeWire
  split_ifs with hi
  · change (false :: true :: w).getD ((i + 1) + 1) false = w.getD i false
    rw [List.getD_cons_succ, List.getD_cons_succ]
  · rw [show w.getD i false = false from List.getD_eq_default _ _ (by omega)]
    rfl

lemma normalizeInputs_length (m unit : ℕ) (ins : List ℕ) :
    (normalizeInputs m unit ins).length = 2 := by
  cases ins with
  | nil => rfl
  | cons a ins => cases ins <;> rfl

lemma normalizeInputs_lt (m unit : ℕ) (hu : unit < m + 2) (ins : List ℕ) :
    ∀ i ∈ normalizeInputs m unit ins, i < m + 2 := by
  cases ins with
  | nil => simpa [normalizeInputs] using hu
  | cons a ins =>
    cases ins with
    | nil => simpa [normalizeInputs] using normalizeWire_lt m a
    | cons b ins =>
      intro i hi
      simp only [normalizeInputs, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact normalizeWire_lt m a
      · exact normalizeWire_lt m b

lemma normalizeGate_shape (m : ℕ) (g : Gate) (hg : basisGate g) :
    (((normalizeGate m g).op = GateOp.and ∨ (normalizeGate m g).op = GateOp.or) ∧
      (normalizeGate m g).inputs.length = 2 ∨
      (normalizeGate m g).op = GateOp.not ∧ (normalizeGate m g).inputs.length = 1) ∧
    ∀ i ∈ (normalizeGate m g).inputs, i < m + 2 := by
  rcases hg.1 with hop | hop | hop
  · constructor
    · left
      exact ⟨Or.inl hop, by simpa [normalizeGate, hop] using normalizeInputs_length m 1 g.inputs⟩
    · simpa [normalizeGate, hop] using normalizeInputs_lt m 1 (by omega) g.inputs
  · constructor
    · left
      exact ⟨Or.inr hop, by simpa [normalizeGate, hop] using normalizeInputs_length m 0 g.inputs⟩
    · simpa [normalizeGate, hop] using normalizeInputs_lt m 0 (by omega) g.inputs
  · constructor
    · right
      exact ⟨hop, by simp [normalizeGate, hop]⟩
    · simpa [normalizeGate, hop] using normalizeWire_lt m (g.inputs.headD m)

lemma normalizeGate_value (w : List Bool) (g : Gate) (hg : basisGate g) :
    (normalizeGate w.length g).op.eval
        ((normalizeGate w.length g).inputs.map fun i => ([false, true] ++ w).getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false) := by
  rcases g with ⟨op, ins⟩
  rcases hg with ⟨hop, hlen⟩
  rcases hop with rfl | rfl | rfl
  · cases ins with
    | nil => rfl
    | cons a ins =>
      cases ins with
      | nil =>
        simp only [normalizeGate, normalizeInputs, List.map_cons, List.map_nil, normalizeWire_value]
        simp [GateOp.eval]
      | cons b ins =>
        have he : ins = [] := by simpa using hlen
        subst ins
        simp only [normalizeGate, normalizeInputs, List.map_cons, List.map_nil, normalizeWire_value]
  · cases ins with
    | nil => rfl
    | cons a ins =>
      cases ins with
      | nil =>
        simp only [normalizeGate, normalizeInputs, List.map_cons, List.map_nil, normalizeWire_value]
        simp [GateOp.eval]
      | cons b ins =>
        have he : ins = [] := by simpa using hlen
        subst ins
        simp only [normalizeGate, normalizeInputs, List.map_cons, List.map_nil, normalizeWire_value]
  · cases ins with
    | nil => simp [normalizeGate, normalizeWire, GateOp.eval]
    | cons a ins =>
      simp only [normalizeGate, List.headD_cons, List.map_cons, List.map_nil, normalizeWire_value]
      simp [GateOp.eval]

lemma runGates_length (gs : List Gate) (w : List Bool) :
    (runGates gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [runGates]
  | cons g gs ih =>
    change (runGates gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).length = _
    rw [ih]
    simp [Nat.add_comm, Nat.add_left_comm]

lemma normalizeGates_value (gs : List Gate) (w : List Bool)
    (hgs : ∀ g ∈ gs, basisGate g) :
    runGates (normalizeGates w.length gs) ([false, true] ++ w) =
      [false, true] ++ runGates gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change runGates (normalizeGates (w.length + 1) gs)
      (([false, true] ++ w) ++ [(normalizeGate w.length g).op.eval
        ((normalizeGate w.length g).inputs.map fun i => ([false, true] ++ w).getD i false)]) =
      [false, true] ++ runGates gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    rw [normalizeGate_value w g (hgs g List.mem_cons_self), List.append_assoc]
    have he : (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).length = w.length + 1 :=
      by simp
    rw [← he]
    exact ih _ (fun g hg => hgs g (List.mem_cons_of_mem _ hg))

lemma normalizeGates_eval (gs : List Gate) (o : ℕ) (w : List Bool)
    (hgs : ∀ g ∈ gs, basisGate g) :
    Circuit.eval ⟨normalizeGates w.length gs, normalizeWire (w.length + gs.length) o⟩
      ([false, true] ++ w) = Circuit.eval ⟨gs, o⟩ w := by
  change (runGates (normalizeGates w.length gs) ([false, true] ++ w)).getD
    (normalizeWire (w.length + gs.length) o) false = (runGates gs w).getD o false
  rw [normalizeGates_value gs w hgs, ← runGates_length gs w]
  exact normalizeWire_value _ _

lemma normalizeGates_getElem (m : ℕ) (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    (normalizeGates m gs)[j]'(by rw [normalizeGates_length]; exact hj) =
      normalizeGate (m + j) gs[j] := by
  induction gs generalizing m j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero => simp [normalizeGates]
    | succ j =>
      simpa [normalizeGates, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (m + 1) j (by simpa using hj)

lemma normalizeGates_shape (m : ℕ) (gs : List Gate) (hgs : ∀ g ∈ gs, basisGate g)
    (j : Fin (normalizeGates m gs).length) :
    (((normalizeGates m gs).get j).op = GateOp.and ∨
        ((normalizeGates m gs).get j).op = GateOp.or) ∧
      ((normalizeGates m gs).get j).inputs.length = 2 ∨
    ((normalizeGates m gs).get j).op = GateOp.not ∧
      ((normalizeGates m gs).get j).inputs.length = 1 := by
  have hj : j.val < gs.length := by simpa [normalizeGates_length] using j.isLt
  simpa only [List.get_eq_getElem, normalizeGates_getElem m gs j.val hj] using
    (normalizeGate_shape (m + j.val) gs[j.val] (hgs _ (List.getElem_mem hj))).1

lemma normalizeGates_readsBack (m : ℕ) (gs : List Gate) (hgs : ∀ g ∈ gs, basisGate g)
    (j : Fin (normalizeGates m gs).length) :
    ∀ i ∈ ((normalizeGates m gs).get j).inputs, i < m + 2 + j.val := by
  have hj : j.val < gs.length := by simpa [normalizeGates_length] using j.isLt
  simpa only [List.get_eq_getElem, normalizeGates_getElem m gs j.val hj,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (normalizeGate_shape (m + j.val) gs[j.val] (hgs _ (List.getElem_mem hj))).2

lemma normalizeGates_oneNot (m : ℕ) (gs : List Gate)
    (huniq : ∀ i j : Fin gs.length, (gs.get i).op = GateOp.not →
      (gs.get j).op = GateOp.not → i = j) :
    ∀ i j : Fin (normalizeGates m gs).length,
      ((normalizeGates m gs).get i).op = GateOp.not →
      ((normalizeGates m gs).get j).op = GateOp.not → i = j := by
  intro i j hi hj
  have hi' : i.val < gs.length := by simpa [normalizeGates_length] using i.isLt
  have hj' : j.val < gs.length := by simpa [normalizeGates_length] using j.isLt
  simp only [List.get_eq_getElem, normalizeGates_getElem m gs i.val hi',
    normalizeGates_getElem m gs j.val hj', normalizeGate_op] at hi hj
  have he := huniq ⟨i.val, hi'⟩ ⟨j.val, hj'⟩ hi hj
  apply Fin.ext
  exact congrArg (fun k : Fin gs.length => k.val) he


def padRun (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun v g => v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]) w

def padNormal : ℕ → List Gate → Prop
  | _, [] => True
  | n, g :: gs =>
      ((((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
        (g.op = GateOp.not ∧ g.inputs.length = 1)) ∧
        (∀ i ∈ g.inputs, i < n)) ∧ padNormal (n + 1) gs

def padCopy (o : ℕ) : Gate := ⟨GateOp.or, [o, o]⟩

def padGates (n K : ℕ) (gs : List Gate) (o : ℕ) : List Gate :=
  gs.take (o + 1 - n) ++ List.replicate (K - (o + 1 - n)) (padCopy o)

lemma padRun_append (gs hs : List Gate) (w : List Bool) :
    padRun (gs ++ hs) w = padRun hs (padRun gs w) := by
  simp only [padRun, List.foldl_append]

lemma padRun_length (gs : List Gate) (w : List Bool) :
    (padRun gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [padRun]
  | cons g gs ih =>
    change (padRun gs (w ++ [_])).length = _
    rw [ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

lemma padRun_prefix (gs : List Gate) (w : List Bool) :
    ∃ tail, padRun gs w = w ++ tail := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp [padRun]⟩
  | cons g gs ih =>
    obtain ⟨tail, ht⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    exact ⟨_ :: tail, by simpa only [padRun, List.foldl_cons, List.append_assoc,
      List.singleton_append] using ht⟩

lemma padRun_getD (gs : List Gate) (w : List Bool) (o : ℕ) (ho : o < w.length) :
    (padRun gs w).getD o false = w.getD o false := by
  obtain ⟨tail, ht⟩ := padRun_prefix gs w
  rw [ht, List.getD_append _ _ _ _ ho]

lemma padRun_take_getD (gs : List Gate) (w : List Bool) (q o : ℕ)
    (ho : o < w.length + (gs.take q).length) :
    (padRun gs w).getD o false = (padRun (gs.take q) w).getD o false := by
  conv_lhs => rw [← List.take_append_drop q gs]
  rw [padRun_append]
  apply padRun_getD
  simpa only [padRun_length] using ho

lemma padCopy_eval (w : List Bool) (o : ℕ) :
    (padCopy o).op.eval ((padCopy o).inputs.map fun i => w.getD i false) =
      w.getD o false := by
  simp [padCopy, GateOp.eval]

lemma padRun_replicate (w : List Bool) (o k : ℕ) (ho : o < w.length) :
    padRun (List.replicate k (padCopy o)) w =
      w ++ List.replicate k (w.getD o false) := by
  induction k generalizing w with
  | zero => simp [padRun]
  | succ k ih =>
    rw [List.replicate_succ]
    change padRun (List.replicate k (padCopy o))
      (w ++ [(padCopy o).op.eval ((padCopy o).inputs.map fun i => w.getD i false)]) = _
    rw [padCopy_eval, ih _ (by simp only [List.length_append, List.length_singleton]; omega),
      List.getD_append _ _ _ _ ho]
    simp only [List.append_assoc, List.singleton_append, List.replicate_succ]

lemma padNormal_take {n q : ℕ} {gs : List Gate} (h : padNormal n gs) :
    padNormal n (gs.take q) := by
  induction q generalizing n gs with
  | zero => simp [padNormal]
  | succ q ih =>
    cases gs with
    | nil => trivial
    | cons g gs => exact ⟨h.1, ih h.2⟩

lemma padNormal_append {n : ℕ} {gs hs : List Gate}
    (hg : padNormal n gs) (hh : padNormal (n + gs.length) hs) :
    padNormal n (gs ++ hs) := by
  induction gs generalizing n with
  | nil => simpa only [List.nil_append, List.length_nil, Nat.add_zero] using hh
  | cons g gs ih =>
    refine ⟨hg.1, ih hg.2 ?_⟩
    simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1 gs.length] using hh

lemma padNormal_replicate (n o k : ℕ) (ho : o < n) :
    padNormal n (List.replicate k (padCopy o)) := by
  induction k generalizing n with
  | zero => trivial
  | succ k ih =>
    refine ⟨⟨Or.inl ⟨Or.inr rfl, rfl⟩, ?_⟩, ih (n + 1) (by omega)⟩
    intro i hi
    simp only [padCopy, List.mem_cons, List.not_mem_nil, or_false, or_self] at hi
    simpa only [hi] using ho

lemma padGates_length {n K o : ℕ} {gs : List Gate}
    (hL : gs.length ≤ K) (ho : o < n + gs.length) :
    (padGates n K gs o).length = K := by
  have hq : o + 1 - n ≤ gs.length := by omega
  have hqK : o + 1 - n ≤ K := by omega
  simp only [padGates, List.length_append, List.length_take, Nat.min_eq_left hq,
    List.length_replicate]
  omega

lemma padGates_normal {n K o : ℕ} {gs : List Gate}
    (hn : padNormal n gs) (ho : o < n + gs.length) :
    padNormal n (padGates n K gs o) := by
  apply padNormal_append (padNormal_take hn)
  apply padNormal_replicate
  have hq : o + 1 - n ≤ gs.length := by omega
  simp only [List.length_take, Nat.min_eq_left hq]
  omega

lemma padGates_eval {n K o : ℕ} {gs : List Gate} (w : List Bool)
    (hw : w.length = n) (hL : gs.length ≤ K) (hK : 0 < K)
    (ho : o < n + gs.length) :
    (padRun (padGates n K gs o) w).getD (n + K - 1) false =
      (padRun gs w).getD o false := by
  have hq : o + 1 - n ≤ gs.length := by omega
  have hqK : o + 1 - n ≤ K := by omega
  have hlen : (gs.take (o + 1 - n)).length = o + 1 - n := by
    simp only [List.length_take, Nat.min_eq_left hq]
  have hwpre : (padRun (gs.take (o + 1 - n)) w).length = n + (o + 1 - n) := by
    rw [padRun_length, hw, hlen]
  have hopre : o < (padRun (gs.take (o + 1 - n)) w).length := by
    rw [hwpre]
    omega
  rw [padGates, padRun_append, padRun_replicate _ _ _ hopre]
  rw [padRun_take_getD gs w (o + 1 - n) o (by rw [hw, hlen]; omega)]
  by_cases hk : K = o + 1 - n
  · rw [hk, Nat.sub_self, List.replicate_zero, List.append_nil]
    have hoeq : n + (o + 1 - n) - 1 = o := by omega
    rw [hoeq]
  · rw [List.getD_append_right _ _ _ _ (by rw [hwpre]; omega)]
    apply List.getD_replicate
    rw [hwpre]
    omega

lemma padGates_not_source {n K o i : ℕ} {gs : List Gate}
    (_hL : gs.length ≤ K) (ho : o < n + gs.length)
    (hi : i < (padGates n K gs o).length)
    (hop : ((padGates n K gs o)[i]).op = GateOp.not) :
    ∃ hi' : i < gs.length, (gs[i]).op = GateOp.not := by
  have hq : o + 1 - n ≤ gs.length := by omega
  have hlen : (gs.take (o + 1 - n)).length = o + 1 - n := by
    simp only [List.length_take, Nat.min_eq_left hq]
  by_cases hleft : i < (gs.take (o + 1 - n)).length
  · have his : i < gs.length := by omega
    refine ⟨his, ?_⟩
    simpa only [padGates, List.getElem_append_left hleft, List.getElem_take] using hop
  · have hright : (gs.take (o + 1 - n)).length ≤ i := by omega
    simp only [padGates, List.getElem_append_right hright, List.getElem_replicate,
      padCopy] at hop
    cases hop

lemma padGates_oneNot {n K o : ℕ} {gs : List Gate}
    (hL : gs.length ≤ K) (ho : o < n + gs.length)
    (hu : ∀ i j : Fin gs.length,
      (gs.get i).op = GateOp.not → (gs.get j).op = GateOp.not → i = j) :
    ∀ i j : Fin (padGates n K gs o).length,
      ((padGates n K gs o).get i).op = GateOp.not →
      ((padGates n K gs o).get j).op = GateOp.not → i = j := by
  intro i j hi hj
  obtain ⟨hi', hni⟩ := padGates_not_source hL ho i.isLt hi
  obtain ⟨hj', hnj⟩ := padGates_not_source hL ho j.isLt hj
  have he := hu ⟨i.val, hi'⟩ ⟨j.val, hj'⟩ hni hnj
  exact Fin.ext (congrArg (fun v : Fin gs.length => v.val) he)

lemma padNormal_indexed (n : ℕ) (gs : List Gate) :
    padNormal n gs ↔ ∀ j : Fin gs.length,
      ((((gs.get j).op = GateOp.and ∨ (gs.get j).op = GateOp.or) ∧
        (gs.get j).inputs.length = 2) ∨
        ((gs.get j).op = GateOp.not ∧ (gs.get j).inputs.length = 1)) ∧
      (∀ i ∈ (gs.get j).inputs, i < n + j.val) := by
  induction gs generalizing n with
  | nil => simp [padNormal]
  | cons g gs ih =>
    constructor
    · intro h j
      refine Fin.cases ?_ (fun k => ?_) j
      · simpa only [List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero,
          Nat.add_zero] using h.1
      · have hk := (ih (n + 1)).mp h.2 k
        simpa only [List.get_eq_getElem, Fin.val_succ, List.getElem_cons_succ,
          Nat.add_assoc, Nat.add_comm 1 k.val] using hk
    · intro h
      refine ⟨?_, (ih (n + 1)).mpr ?_⟩
      · simpa only [List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero,
          Nat.add_zero] using h 0
      · intro k
        have hk := h k.succ
        simpa only [List.get_eq_getElem, Fin.val_succ, List.getElem_cons_succ,
          Nat.add_assoc, Nat.add_comm 1 k.val] using hk

lemma pad_exact {n K o : ℕ} {gs : List Gate}
    (hL : gs.length ≤ K) (hK : 0 < K) (ho : o < n + gs.length)
    (hs : ∀ j : Fin gs.length,
      ((((gs.get j).op = GateOp.and ∨ (gs.get j).op = GateOp.or) ∧
        (gs.get j).inputs.length = 2) ∨
        ((gs.get j).op = GateOp.not ∧ (gs.get j).inputs.length = 1)))
    (hr : ∀ j : Fin gs.length, ∀ i ∈ (gs.get j).inputs, i < n + j.val)
    (hu : ∀ i j : Fin gs.length,
      (gs.get i).op = GateOp.not → (gs.get j).op = GateOp.not → i = j) :
    ∃ padded : List Gate,
      padded.length = K ∧
      (∀ j : Fin padded.length,
        ((((padded.get j).op = GateOp.and ∨ (padded.get j).op = GateOp.or) ∧
          (padded.get j).inputs.length = 2) ∨
          ((padded.get j).op = GateOp.not ∧ (padded.get j).inputs.length = 1))) ∧
      (∀ j : Fin padded.length, ∀ i ∈ (padded.get j).inputs, i < n + j.val) ∧
      (∀ i j : Fin padded.length,
        (padded.get i).op = GateOp.not → (padded.get j).op = GateOp.not → i = j) ∧
      ∀ w : List Bool, w.length = n →
        Circuit.eval ⟨padded, n + K - 1⟩ w = Circuit.eval ⟨gs, o⟩ w := by
  have hn : padNormal n gs := (padNormal_indexed n gs).mpr (fun j => ⟨hs j, hr j⟩)
  have hp := (padNormal_indexed n (padGates n K gs o)).mp (padGates_normal hn ho)
  refine ⟨padGates n K gs o, padGates_length hL ho, (fun j => (hp j).1),
    (fun j => (hp j).2), padGates_oneNot hL ho hu, ?_⟩
  intro w hw
  exact padGates_eval w hw hL hK ho

lemma normalize_pad (n K : ℕ) (gs : List Gate) (o : ℕ)
    (hL : gs.length ≤ K) (hK : 0 < K) (hgs : ∀ g ∈ gs, basisGate g)
    (hu : ∀ i j : Fin gs.length,
      (gs.get i).op = GateOp.not → (gs.get j).op = GateOp.not → i = j) :
    ∃ padded : List Gate,
      padded.length = K ∧ padNormal (n + 2) padded ∧
      (∀ i j : Fin padded.length,
        (padded.get i).op = GateOp.not → (padded.get j).op = GateOp.not → i = j) ∧
      ∀ x : Fin n → Bool,
        Circuit.eval ⟨padded, n + 2 + K - 1⟩ ([false, true] ++ List.ofFn x) =
          Circuit.eval ⟨gs, o⟩ (List.ofFn x) := by
  have ho : normalizeWire (n + gs.length) o < n + 2 + (normalizeGates n gs).length := by
    rw [normalizeGates_length]
    have hh := normalizeWire_lt (n + gs.length) o
    omega
  obtain ⟨padded, hpL, hpS, hpR, hpU, hpE⟩ := pad_exact
    (n := n + 2) (K := K) (gs := normalizeGates n gs)
    (o := normalizeWire (n + gs.length) o)
    (by simpa only [normalizeGates_length] using hL) hK ho
    (normalizeGates_shape n gs hgs) (normalizeGates_readsBack n gs hgs)
    (normalizeGates_oneNot n gs hu)
  refine ⟨padded, hpL, (padNormal_indexed _ _).mpr (fun j => ⟨hpS j, hpR j⟩), hpU, ?_⟩
  intro x
  rw [hpE _ (by simp only [List.length_append, List.length_cons, List.length_nil,
    List.length_ofFn]; omega)]
  simpa only [List.length_ofFn] using normalizeGates_eval gs o (List.ofFn x) hgs

def keepPad (K : ℕ) (gs : List Gate) : List Gate :=
  gs ++ List.replicate (K - gs.length) (padCopy 0)

lemma keepPad_length (K : ℕ) (gs : List Gate) (hL : gs.length ≤ K) :
    (keepPad K gs).length = K := by
  simp only [keepPad, List.length_append, List.length_replicate]
  omega

lemma keepPad_normal {n K : ℕ} {gs : List Gate} (hn : padNormal n gs) (hn0 : 0 < n) :
    padNormal n (keepPad K gs) := by
  apply padNormal_append hn
  exact padNormal_replicate _ _ _ (by omega)

lemma keepPad_eval {n K o : ℕ} {gs : List Gate} (w : List Bool)
    (hw : w.length = n) (ho : o < n + gs.length) :
    Circuit.eval ⟨keepPad K gs, o⟩ w = Circuit.eval ⟨gs, o⟩ w := by
  change (padRun (keepPad K gs) w).getD o false = (padRun gs w).getD o false
  rw [keepPad, padRun_append]
  exact padRun_getD _ _ o (by rw [padRun_length, hw]; exact ho)

lemma keepPad_not_source {K i : ℕ} {gs : List Gate}
    (hi : i < (keepPad K gs).length) (hop : ((keepPad K gs)[i]).op = GateOp.not) :
    ∃ hi' : i < gs.length, (gs[i]).op = GateOp.not := by
  by_cases hleft : i < gs.length
  · exact ⟨hleft, by simpa only [keepPad, List.getElem_append_left hleft] using hop⟩
  · have hright : gs.length ≤ i := by omega
    simp only [keepPad, List.getElem_append_right hright, List.getElem_replicate, padCopy] at hop
    cases hop

lemma keepPad_oneNot {K : ℕ} {gs : List Gate}
    (hu : ∀ i j : Fin gs.length,
      (gs.get i).op = GateOp.not → (gs.get j).op = GateOp.not → i = j) :
    ∀ i j : Fin (keepPad K gs).length,
      ((keepPad K gs).get i).op = GateOp.not →
      ((keepPad K gs).get j).op = GateOp.not → i = j := by
  intro i j hi hj
  obtain ⟨hi', hni⟩ := keepPad_not_source i.isLt hi
  obtain ⟨hj', hnj⟩ := keepPad_not_source j.isLt hj
  exact Fin.ext (congrArg (fun v : Fin gs.length => v.val)
    (hu ⟨i.val, hi'⟩ ⟨j.val, hj'⟩ hni hnj))

lemma normalizeGates_hasNot (n : ℕ) (gs : List Gate)
    (hn : ∃ i : Fin gs.length, (gs.get i).op = GateOp.not) :
    ∃ i : Fin (normalizeGates n gs).length,
      ((normalizeGates n gs).get i).op = GateOp.not := by
  obtain ⟨i, hi⟩ := hn
  refine ⟨⟨i.val, by simpa only [normalizeGates_length] using i.isLt⟩, ?_⟩
  simpa only [List.get_eq_getElem, normalizeGates_getElem n gs i.val i.isLt,
    normalizeGate_op] using hi

lemma keepPad_hasNot (K : ℕ) (gs : List Gate)
    (hn : ∃ i : Fin gs.length, (gs.get i).op = GateOp.not) :
    ∃ i : Fin (keepPad K gs).length, ((keepPad K gs).get i).op = GateOp.not := by
  obtain ⟨i, hi⟩ := hn
  refine ⟨⟨i.val, by have hh := i.isLt; simp only [keepPad, List.length_append]; omega⟩, ?_⟩
  simpa only [List.get_eq_getElem, keepPad, List.getElem_append_left i.isLt] using hi

lemma normalize_pad_exactNot (n K : ℕ) (gs : List Gate) (o : ℕ)
    (hL : gs.length ≤ K) (hgs : ∀ g ∈ gs, basisGate g)
    (hu : ∀ i j : Fin gs.length,
      (gs.get i).op = GateOp.not → (gs.get j).op = GateOp.not → i = j)
    (hn : ∃ i : Fin gs.length, (gs.get i).op = GateOp.not) :
    ∃ (padded : List Gate) (output : ℕ),
      padded.length = K ∧ padNormal (n + 2) padded ∧ output < n + 2 + K ∧
      (∀ i j : Fin padded.length,
        (padded.get i).op = GateOp.not → (padded.get j).op = GateOp.not → i = j) ∧
      (∃ i : Fin padded.length, (padded.get i).op = GateOp.not) ∧
      ∀ x : Fin n → Bool,
        Circuit.eval ⟨padded, output⟩ ([false, true] ++ List.ofFn x) =
          Circuit.eval ⟨gs, o⟩ (List.ofFn x) := by
  have hlen : (normalizeGates n gs).length ≤ K := by
    simpa only [normalizeGates_length] using hL
  have ho : normalizeWire (n + gs.length) o < n + 2 + (normalizeGates n gs).length := by
    rw [normalizeGates_length]
    have hh := normalizeWire_lt (n + gs.length) o
    omega
  have hs : padNormal (n + 2) (normalizeGates n gs) :=
    (padNormal_indexed _ _).mpr (fun j =>
      ⟨normalizeGates_shape n gs hgs j, normalizeGates_readsBack n gs hgs j⟩)
  refine ⟨keepPad K (normalizeGates n gs), normalizeWire (n + gs.length) o,
    keepPad_length _ _ hlen, keepPad_normal hs (by omega), by omega,
    keepPad_oneNot (normalizeGates_oneNot n gs hu),
    keepPad_hasNot K _ (normalizeGates_hasNot n gs hn), ?_⟩
  intro x
  rw [keepPad_eval (n := n + 2) _ (by simp only [List.length_append, List.length_cons,
    List.length_nil, List.length_ofFn]; omega) ho]
  simpa only [List.length_ofFn] using normalizeGates_eval gs o (List.ofFn x) hgs

def outputPrefix (n : ℕ) (gs : List Gate) (o : ℕ) : List Gate :=
  if o < n + gs.length then gs.take (o + 1 - n) else []

lemma outputPrefix_length (n : ℕ) (gs : List Gate) (o : ℕ) :
    (outputPrefix n gs o).length ≤ gs.length := by
  unfold outputPrefix
  split_ifs
  · simp only [List.length_take]
    exact Nat.min_le_right _ _
  · simp

lemma outputPrefix_mem {n o : ℕ} {gs : List Gate} {g : Gate}
    (hg : g ∈ outputPrefix n gs o) : g ∈ gs := by
  unfold outputPrefix at hg
  split_ifs at hg
  · exact List.mem_of_mem_take hg
  · simp at hg

lemma outputPrefix_eval (n : ℕ) (gs : List Gate) (o : ℕ) (w : List Bool)
    (hw : w.length = n) : Circuit.eval ⟨outputPrefix n gs o, o⟩ w = Circuit.eval ⟨gs, o⟩ w := by
  change (padRun (outputPrefix n gs o) w).getD o false = (padRun gs w).getD o false
  unfold outputPrefix
  split_ifs with ho
  · have hq : o + 1 - n ≤ gs.length := by omega
    exact (padRun_take_getD gs w (o + 1 - n) o (by
      simp only [hw, List.length_take, Nat.min_eq_left hq]
      omega)).symm
  · change w.getD o false = (padRun gs w).getD o false
    rw [show w.getD o false = false from List.getD_eq_default _ _ (by omega),
      show (padRun gs w).getD o false = false from List.getD_eq_default _ _ (by
        rw [padRun_length, hw]
        omega)]

lemma outputPrefix_oneNot (n : ℕ) (gs : List Gate) (o : ℕ)
    (hu : ∀ i j : Fin gs.length,
      (gs.get i).op = GateOp.not → (gs.get j).op = GateOp.not → i = j) :
    ∀ i j : Fin (outputPrefix n gs o).length,
      ((outputPrefix n gs o).get i).op = GateOp.not →
      ((outputPrefix n gs o).get j).op = GateOp.not → i = j := by
  by_cases ho : o < n + gs.length
  · rw [show outputPrefix n gs o = gs.take (o + 1 - n) by simp [outputPrefix, ho]]
    intro i j hi hj
    have hi' : i.val < gs.length := lt_of_lt_of_le i.isLt (by
      simp only [List.length_take]; exact Nat.min_le_right _ _)
    have hj' : j.val < gs.length := lt_of_lt_of_le j.isLt (by
      simp only [List.length_take]; exact Nat.min_le_right _ _)
    have hi0 : (gs.get ⟨i.val, hi'⟩).op = GateOp.not := by
      simpa only [List.get_eq_getElem, List.getElem_take] using hi
    have hj0 : (gs.get ⟨j.val, hj'⟩).op = GateOp.not := by
      simpa only [List.get_eq_getElem, List.getElem_take] using hj
    exact Fin.ext (congrArg (fun k : Fin gs.length => k.val)
      (hu ⟨i.val, hi'⟩ ⟨j.val, hj'⟩ hi0 hj0))
  · rw [show outputPrefix n gs o = [] by simp [outputPrefix, ho]]
    intro i
    exact Fin.elim0 i

lemma outputPrefix_last {n o : ℕ} {gs : List Gate}
    (hn : ∃ i : Fin (outputPrefix n gs o).length,
      ((outputPrefix n gs o).get i).op = GateOp.not) :
    n + (outputPrefix n gs o).length = o + 1 := by
  have hp : 0 < (outputPrefix n gs o).length := by
    obtain ⟨i, _⟩ := hn
    exact Nat.zero_lt_of_lt i.isLt
  by_cases ho : o < n + gs.length
  · have hq : o + 1 - n ≤ gs.length := by omega
    simp only [outputPrefix, ho, ite_true, List.length_take, Nat.min_eq_left hq] at hp ⊢
    omega
  · simp only [outputPrefix, ho, ite_false, List.length_nil, Nat.lt_irrefl] at hp

def rootMonotoneReplacement (n : ℕ) (gs : List Gate) (o : ℕ) : Prop :=
  ∃ (ms : List Gate) (mo : ℕ),
    (∀ g ∈ ms, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
    ms.length ≤ gs.length ∧ ∀ x : Fin n → Bool,
      Circuit.eval ⟨ms, mo⟩ (List.ofFn x) = Circuit.eval ⟨gs, o⟩ (List.ofFn x)

lemma outputPrefix_noNot (n : ℕ) (gs : List Gate) (o : ℕ)
    (hgs : ∀ g ∈ gs, basisGate g)
    (hn : ¬ ∃ i : Fin (outputPrefix n gs o).length,
      ((outputPrefix n gs o).get i).op = GateOp.not) : rootMonotoneReplacement n gs o := by
  refine ⟨outputPrefix n gs o, o, ?_, outputPrefix_length n gs o, ?_⟩
  · intro g hg
    obtain ⟨hop, hlen⟩ := hgs g (outputPrefix_mem hg)
    refine ⟨?_, hlen⟩
    rcases hop with hop | hop | hop
    · exact Or.inl hop
    · exact Or.inr hop
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
      exact (hn ⟨⟨i, hi⟩, hop⟩).elim
  · intro x
    exact outputPrefix_eval n gs o (List.ofFn x) (by simp)


lemma padGates_last {n K o : ℕ} {gs : List Gate} (hlast : n + gs.length = o + 1) :
    padGates n K gs o = gs ++ List.replicate (K - gs.length) (padCopy o) := by
  have hq : o + 1 - n = gs.length := by omega
  simp only [padGates, hq, List.take_length]

lemma padGates_hasNot {n K o : ℕ} {gs : List Gate} (hlast : n + gs.length = o + 1)
    (hnot : ∃ j : Fin gs.length, (gs.get j).op = GateOp.not) :
    ∃ j : Fin (padGates n K gs o).length,
      ((padGates n K gs o).get j).op = GateOp.not := by
  obtain ⟨j, hj⟩ := hnot
  rw [padGates_last hlast]
  refine ⟨⟨j.val, by simp only [List.length_append, List.length_replicate]; omega⟩, ?_⟩
  simpa only [List.get_eq_getElem, List.getElem_append_left j.isLt] using hj

lemma pad_exact_last_hasNot {n K o : ℕ} {gs : List Gate}
    (hL : gs.length ≤ K) (hK : 0 < K) (hlast : n + gs.length = o + 1)
    (hn : padNormal n gs)
    (hu : ∀ i j : Fin gs.length,
      (gs.get i).op = GateOp.not → (gs.get j).op = GateOp.not → i = j)
    (hnot : ∃ j : Fin gs.length, (gs.get j).op = GateOp.not) :
    ∃ padded : List Gate,
      padded.length = K ∧ padNormal n padded ∧
      (∀ i j : Fin padded.length,
        (padded.get i).op = GateOp.not → (padded.get j).op = GateOp.not → i = j) ∧
      (∃ j : Fin padded.length, (padded.get j).op = GateOp.not) ∧
      ∀ w : List Bool, w.length = n →
        Circuit.eval ⟨padded, n + K - 1⟩ w = Circuit.eval ⟨gs, o⟩ w := by
  have ho : o < n + gs.length := by omega
  refine ⟨padGates n K gs o, padGates_length hL ho, padGates_normal hn ho,
    padGates_oneNot hL ho hu, padGates_hasNot hlast hnot, ?_⟩
  intro w hw
  exact padGates_eval w hw hL hK ho

lemma normalize_pad_last_hasNot (n K : ℕ) (gs : List Gate) (o : ℕ)
    (hL : gs.length ≤ K) (hK : 0 < K) (hlast : n + gs.length = o + 1)
    (hgs : ∀ g ∈ gs, basisGate g)
    (hu : ∀ i j : Fin gs.length,
      (gs.get i).op = GateOp.not → (gs.get j).op = GateOp.not → i = j)
    (hnot : ∃ j : Fin gs.length, (gs.get j).op = GateOp.not) :
    ∃ padded : List Gate,
      padded.length = K ∧ padNormal (n + 2) padded ∧
      (∀ i j : Fin padded.length,
        (padded.get i).op = GateOp.not → (padded.get j).op = GateOp.not → i = j) ∧
      (∃ j : Fin padded.length, (padded.get j).op = GateOp.not) ∧
      ∀ x : Fin n → Bool,
        Circuit.eval ⟨padded, n + 2 + K - 1⟩ ([false, true] ++ List.ofFn x) =
          Circuit.eval ⟨gs, o⟩ (List.ofFn x) := by
  have ho : o < n + gs.length := by omega
  have hnlast : n + 2 + (normalizeGates n gs).length =
      normalizeWire (n + gs.length) o + 1 := by
    simp only [normalizeGates_length, normalizeWire, ho, ite_true]
    omega
  have hn : padNormal (n + 2) (normalizeGates n gs) :=
    (padNormal_indexed _ _).mpr (fun j =>
      ⟨normalizeGates_shape n gs hgs j, normalizeGates_readsBack n gs hgs j⟩)
  obtain ⟨padded, hpL, hpN, hpU, hpNot, hpE⟩ := pad_exact_last_hasNot
    (n := n + 2) (K := K) (gs := normalizeGates n gs)
    (o := normalizeWire (n + gs.length) o)
    (by simpa only [normalizeGates_length] using hL) hK hnlast hn
    (normalizeGates_oneNot n gs hu) (normalizeGates_hasNot n gs hnot)
  refine ⟨padded, hpL, hpN, hpU, hpNot, ?_⟩
  intro x
  rw [hpE _ (by simp only [List.length_append, List.length_cons, List.length_nil,
    List.length_ofFn]; omega)]
  simpa only [List.length_ofFn] using normalizeGates_eval gs o (List.ofFn x) hgs

lemma pad_exact_hasNot {n K o : ℕ} {gs : List Gate}
    (hL : gs.length ≤ K) (hK : 0 < K) (hlast : n + gs.length = o + 1)
    (hs : ∀ j : Fin gs.length,
      ((((gs.get j).op = GateOp.and ∨ (gs.get j).op = GateOp.or) ∧
        (gs.get j).inputs.length = 2) ∨
        ((gs.get j).op = GateOp.not ∧ (gs.get j).inputs.length = 1)))
    (hr : ∀ j : Fin gs.length, ∀ i ∈ (gs.get j).inputs, i < n + j.val)
    (hu : ∀ i j : Fin gs.length,
      (gs.get i).op = GateOp.not → (gs.get j).op = GateOp.not → i = j)
    (hnot : ∃ j : Fin gs.length, (gs.get j).op = GateOp.not) :
    ∃ padded : List Gate,
      padded.length = K ∧
      (∀ j : Fin padded.length,
        ((((padded.get j).op = GateOp.and ∨ (padded.get j).op = GateOp.or) ∧
          (padded.get j).inputs.length = 2) ∨
          ((padded.get j).op = GateOp.not ∧ (padded.get j).inputs.length = 1))) ∧
      (∀ j : Fin padded.length, ∀ i ∈ (padded.get j).inputs, i < n + j.val) ∧
      (∀ i j : Fin padded.length,
        (padded.get i).op = GateOp.not → (padded.get j).op = GateOp.not → i = j) ∧
      (∃ j : Fin padded.length, (padded.get j).op = GateOp.not) ∧
      ∀ w : List Bool, w.length = n →
        Circuit.eval ⟨padded, n + K - 1⟩ w = Circuit.eval ⟨gs, o⟩ w := by
  have hn : padNormal n gs := (padNormal_indexed n gs).mpr (fun j => ⟨hs j, hr j⟩)
  obtain ⟨padded, hpL, hpN, hpU, hpNot, hpE⟩ := pad_exact_last_hasNot hL hK hlast hn hu hnot
  have hp := (padNormal_indexed n padded).mp hpN
  exact ⟨padded, hpL, (fun j => (hp j).1), (fun j => (hp j).2), hpU, hpNot, hpE⟩

lemma normalize_or_replace (n K : ℕ) (gs : List Gate) (o : ℕ)
    (hL : gs.length ≤ K) (hK : 0 < K) (hgs : ∀ g ∈ gs, basisGate g)
    (hu : ∀ i j : Fin gs.length,
      (gs.get i).op = GateOp.not → (gs.get j).op = GateOp.not → i = j) :
    rootMonotoneReplacement n gs o ∨
    ∃ padded : List Gate,
      padded.length = K ∧ padNormal (n + 2) padded ∧
      (∀ i j : Fin padded.length,
        (padded.get i).op = GateOp.not → (padded.get j).op = GateOp.not → i = j) ∧
      (∃ j : Fin padded.length, (padded.get j).op = GateOp.not) ∧
      ∀ x : Fin n → Bool,
        Circuit.eval ⟨padded, n + 2 + K - 1⟩ ([false, true] ++ List.ofFn x) =
          Circuit.eval ⟨gs, o⟩ (List.ofFn x) := by
  classical
  by_cases hn : ∃ i : Fin (outputPrefix n gs o).length,
      ((outputPrefix n gs o).get i).op = GateOp.not
  · right
    have hpL : (outputPrefix n gs o).length ≤ K :=
      (outputPrefix_length n gs o).trans hL
    have hpS : ∀ g ∈ outputPrefix n gs o, basisGate g :=
      fun g hg => hgs g (outputPrefix_mem hg)
    obtain ⟨padded, hlen, hnormal, huniq, hnot, heval⟩ :=
      normalize_pad_last_hasNot n K (outputPrefix n gs o) o hpL hK
        (outputPrefix_last hn) hpS (outputPrefix_oneNot n gs o hu) hn
    refine ⟨padded, hlen, hnormal, huniq, hnot, ?_⟩
    intro x
    rw [heval]
    exact outputPrefix_eval n gs o (List.ofFn x) (by simp)
  · exact Or.inl (outputPrefix_noNot n gs o hgs hn)

def stripSource (q i : ℕ) : ℕ := if i = 0 then q else i - 2

def stripAnd (q : ℕ) : List ℕ → List ℕ
  | [] => []
  | i :: is => if i = 1 then stripAnd q is else stripSource q i :: stripAnd q is

def stripGate (q : ℕ) (g : Gate) : Gate :=
  match g.op with
  | GateOp.and => ⟨GateOp.and, stripAnd q g.inputs⟩
  | GateOp.or => if 1 ∈ g.inputs then ⟨GateOp.and, []⟩
      else ⟨GateOp.or, g.inputs.map (stripSource q)⟩
  | _ => g

lemma stripSource_value (w : List Bool) (q i : ℕ) (hq : w.length ≤ q) (hi : i ≠ 1) :
    w.getD (stripSource q i) false = ([false, true] ++ w).getD i false := by
  cases i with
  | zero =>
    simp only [stripSource, ite_true]
    rw [List.getD_eq_default _ _ hq]
    rfl
  | succ i =>
    cases i with
    | zero => exact (hi rfl).elim
    | succ i =>
      simp only [stripSource, Nat.succ_ne_zero, ite_false]
      change w.getD i false = (false :: true :: w).getD ((i + 1) + 1) false
      rw [List.getD_cons_succ, List.getD_cons_succ]

lemma stripAnd_length (q : ℕ) (ins : List ℕ) : (stripAnd q ins).length ≤ ins.length := by
  induction ins with
  | nil => rfl
  | cons i ins ih =>
    simp only [stripAnd]
    split_ifs <;> simp only [List.length_cons] <;> omega

lemma stripAnd_value (w : List Bool) (q : ℕ) (ins : List ℕ) (hq : w.length ≤ q) :
    GateOp.and.eval ((stripAnd q ins).map fun i => w.getD i false) =
      GateOp.and.eval (ins.map fun i => ([false, true] ++ w).getD i false) := by
  induction ins with
  | nil => rfl
  | cons i ins ih =>
    simp only [stripAnd]
    by_cases hi : i = 1
    · subst i
      simpa only [ite_true, List.map_cons, GateOp.eval, List.all_cons,
        show ([false, true] ++ w).getD 1 false = true from rfl, id_eq, Bool.true_and] using ih
    · simp only [hi, ite_false, List.map_cons, GateOp.eval, List.all_cons, id_eq,
        stripSource_value w q i hq hi]
      exact congrArg (fun b : Bool => ([false, true] ++ w).getD i false && b) ih

lemma stripGate_value (w : List Bool) (q : ℕ) (g : Gate) (hq : w.length ≤ q)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) :
    (stripGate q g).op.eval ((stripGate q g).inputs.map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => ([false, true] ++ w).getD i false) := by
  rcases hop with hop | hop
  · simpa only [stripGate, hop] using stripAnd_value w q g.inputs hq
  · by_cases h1 : 1 ∈ g.inputs
    · simp only [stripGate, hop, h1, ite_true, List.map_nil, GateOp.eval, List.all_nil]
      symm
      apply List.any_eq_true.mpr
      exact ⟨true, List.mem_map.mpr ⟨1, h1, rfl⟩, rfl⟩
    · have he : g.inputs.map (fun i => w.getD (stripSource q i) false) =
          g.inputs.map (fun i => ([false, true] ++ w).getD i false) := by
        apply List.map_congr_left
        intro i hi
        exact stripSource_value w q i hq (fun he => h1 (he ▸ hi))
      simpa only [stripGate, hop, h1, ite_false, List.map_map, Function.comp_def] using
        congrArg GateOp.or.eval he

lemma stripGate_basis (q : ℕ) (g : Gate)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ((stripGate q g).op = GateOp.and ∨ (stripGate q g).op = GateOp.or) ∧
      (stripGate q g).inputs.length ≤ 2 := by
  rcases hg with ⟨hop | hop, hlen⟩
  · exact ⟨Or.inl (by simp only [stripGate, hop]),
      by simpa only [stripGate, hop] using (stripAnd_length q g.inputs).trans hlen⟩
  · by_cases h1 : 1 ∈ g.inputs
    · simp [stripGate, hop, h1]
    · simpa only [stripGate, hop, h1, ite_false, List.length_map] using
        And.intro (Or.inr rfl : GateOp.or = GateOp.and ∨ GateOp.or = GateOp.or) hlen

lemma stripGates_value (gs : List Gate) (w : List Bool) (q : ℕ)
    (hq : w.length + gs.length ≤ q) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    runGates gs ([false, true] ++ w) =
      [false, true] ++ runGates (gs.map (stripGate q)) w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change runGates gs (([false, true] ++ w) ++
      [g.op.eval (g.inputs.map fun i => ([false, true] ++ w).getD i false)]) =
      [false, true] ++ runGates (gs.map (stripGate q))
        (w ++ [(stripGate q g).op.eval ((stripGate q g).inputs.map fun i => w.getD i false)])
    rw [← stripGate_value w q g (by simp only [List.length_cons] at hq; omega)
      (hgs g List.mem_cons_self), List.append_assoc]
    apply ih
    · simp only [List.length_append, List.length_singleton]
      simp only [List.length_cons] at hq
      omega
    · intro g hg
      exact hgs g (List.mem_cons_of_mem _ hg)

lemma strip_constants (n : ℕ) (gs : List Gate) (o : ℕ) (ho : o ≠ 1)
    (hgs : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∃ (ms : List Gate) (mo : ℕ),
      (∀ g ∈ ms, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      ms.length = gs.length ∧ ∀ x : Fin n → Bool,
        Circuit.eval ⟨ms, mo⟩ (List.ofFn x) =
          Circuit.eval ⟨gs, o⟩ ([false, true] ++ List.ofFn x) := by
  refine ⟨gs.map (stripGate (n + gs.length)), stripSource (n + gs.length) o,
    ?_, by simp, ?_⟩
  · intro g hg
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
    exact stripGate_basis _ _ (hgs a ha)
  · intro x
    change (runGates (gs.map (stripGate (n + gs.length))) (List.ofFn x)).getD
      (stripSource (n + gs.length) o) false =
      (runGates gs ([false, true] ++ List.ofFn x)).getD o false
    rw [stripGates_value gs (List.ofFn x) (n + gs.length) (by simp)
      (fun g hg => (hgs g hg).1)]
    exact stripSource_value _ _ _ (by rw [runGates_length]; simp) ho

lemma initialTrue_value (gs : List Gate) (w : List Bool) :
    Circuit.eval ⟨gs, 1⟩ ([false, true] ++ w) = true := by
  change (padRun gs ([false, true] ++ w)).getD 1 false = true
  rw [padRun_getD gs _ 1 (by simp)]
  rfl

lemma strip_constants_of_false (n : ℕ) (gs : List Gate) (o : ℕ)
    (hgs : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x0 : Fin n → Bool)
    (h0 : Circuit.eval ⟨gs, o⟩ ([false, true] ++ List.ofFn x0) = false) :
    ∃ (ms : List Gate) (mo : ℕ),
      (∀ g ∈ ms, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      ms.length = gs.length ∧ ∀ x : Fin n → Bool,
        Circuit.eval ⟨ms, mo⟩ (List.ofFn x) =
          Circuit.eval ⟨gs, o⟩ ([false, true] ++ List.ofFn x) := by
  apply strip_constants n gs o _ hgs
  intro ho
  subst o
  rw [initialTrue_value] at h0
  cases h0



variable {α : Type} [DecidableEq α]

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

lemma live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

lemma live_tight_step {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) (hcard : s.card = k + 2) :
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧
        a ∉ rest ∧ b ∉ rest ∧ rest.card = k ∧ live ops goal k (insert z rest) := by
  rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
  · have hh := live_card skip
    omega
  · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
    have htail := live_card tail
    rw [Finset.card_insert_of_notMem hzrest] at htail
    have h₁ := Finset.card_insert_le a (insert b rest)
    have h₂ := Finset.card_insert_le b rest
    have hrest : rest.card = k := by omega
    have han : a ∉ rest := by
      intro har
      have hai : a ∈ insert b rest := Finset.mem_insert_of_mem har
      rw [Finset.insert_eq_of_mem hai] at hcard
      omega
    have hbn : b ∉ rest := by
      intro hbr
      rw [Finset.insert_eq_of_mem hbr] at hcard
      have hh := Finset.card_insert_le a rest
      omega
    exact ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, han, hbn, hrest, tail⟩

def ops {width : ℕ} (x y : BitVec width) : List (BitVec width) :=
  [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]

abbrev basicOps {width : ℕ} (a b : BitVec width) : Finset (BitVec width) :=
  (ops a b).toFinset

def signedValue (positive value : Bool) : Bool := if positive then value else !value

def boolOp (t : Fin 4) (a b : Bool) : Bool :=
  if t.val = 0 then a && b else if t.val = 1 then a || b
  else if t.val = 2 then a && !b else b && !a

lemma binary_orientation : ∀ t : Fin 4, ∀ d : Bool, ∃ da db : Bool,
    ∀ a0 a1 b0 b1 : Bool,
      (signedValue da a0 = true → signedValue da a1 = true) →
      (signedValue db b0 = true → signedValue db b1 = true) →
      signedValue d (boolOp t a0 b0) = true → signedValue d (boolOp t a1 b1) = true := by
  decide

lemma basicOps_bits {width : ℕ} {a b z : BitVec width} (hz : z ∈ basicOps a b) :
    ∃ t : Fin 4, ∀ p : Fin width,
      z.getLsbD p.val = boolOp t (a.getLsbD p.val) (b.getLsbD p.val) := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact ⟨0, by intro p; simp [boolOp]⟩
  · exact ⟨1, by intro p; simp [boolOp]⟩
  · exact ⟨2, by intro p; simp [boolOp]⟩
  · exact ⟨3, by intro p; simp [boolOp]⟩

def unateSeparator {width : ℕ} (goal : BitVec width) (s : Finset (BitVec width)) : Prop :=
  ∃ direction : BitVec width → Bool, ∀ p q : Fin width,
    (∀ w ∈ s, signedValue (direction w) (w.getLsbD p.val) = true →
      signedValue (direction w) (w.getLsbD q.val) = true) →
    goal.getLsbD p.val = true → goal.getLsbD q.val = true

lemma live_tight_unate {width : ℕ} {goal : BitVec width} {k : ℕ}
    {s : Finset (BitVec width)} (h : live basicOps goal k s) (hcard : s.card = k + 1) :
    unateSeparator goal s := by
  induction k generalizing s with
  | zero =>
    change s = {goal} at h
    subst s
    refine ⟨fun _ => true, ?_⟩
    intro p q hpq
    simpa only [signedValue, ite_true] using hpq goal (Finset.mem_singleton_self _)
  | succ k ih =>
    obtain ⟨a, ha, b, hb, hab, z, hz, hzout, rest, hs, han, hbn, hrest, htail⟩ :=
      live_tight_step h (by omega)
    have hzrest : z ∉ rest := fun hzmem => hzout (by rw [hs]; simp [hzmem])
    obtain ⟨direction, hdir⟩ := ih htail (by rw [Finset.card_insert_of_notMem hzrest, hrest])
    obtain ⟨t, ht⟩ := basicOps_bits hz
    obtain ⟨da, db, hd⟩ := binary_orientation t (direction z)
    let newDirection : BitVec width → Bool :=
      fun w => if w = a then da else if w = b then db else direction w
    refine ⟨newDirection, ?_⟩
    intro p q hpq hp
    apply hdir p q _ hp
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · have hapq := hpq a ha
      have hbpq := hpq b hb
      rw [show newDirection a = da by simp [newDirection]] at hapq
      rw [show newDirection b = db by simp [newDirection, Ne.symm hab]] at hbpq
      rw [ht p, ht q]
      exact hd _ _ _ _ hapq hbpq
    · have hwa : w ≠ a := by intro he; subst w; exact han hw
      have hwb : w ≠ b := by intro he; subst w; exact hbn hw
      have hwpq := hpq w (by rw [hs]; simp [hw])
      simpa only [newDirection, hwa, hwb, ite_false] using hwpq

lemma unate_no_opposite_edges {width : ℕ} {goal w : BitVec width}
    {s : Finset (BitVec width)} (hs : unateSeparator goal s) (_hw : w ∈ s)
    (p q r t : Fin width)
    (hp : goal.getLsbD p.val = true) (hq : goal.getLsbD q.val = false)
    (hr : goal.getLsbD r.val = true) (ht : goal.getLsbD t.val = false)
    (hwp : w.getLsbD p.val = true) (_hwq : w.getLsbD q.val = false)
    (_hwr : w.getLsbD r.val = false) (hwt : w.getLsbD t.val = true)
    (hpq : ∀ u ∈ s, u ≠ w → u.getLsbD p.val = u.getLsbD q.val)
    (hrt : ∀ u ∈ s, u ≠ w → u.getLsbD r.val = u.getLsbD t.val) : False := by
  obtain ⟨direction, hdir⟩ := hs
  cases hd : direction w with
  | false =>
    have hc := hdir p q (by
      intro u hu
      by_cases he : u = w
      · subst u
        simp [signedValue, hd, hwp]
      · rw [hpq u hu he]
        exact id) hp
    rw [hq] at hc
    cases hc
  | true =>
    have hc := hdir r t (by
      intro u hu
      by_cases he : u = w
      · subst u
        simp [signedValue, hd, hwt]
      · rw [hrt u hu he]
        exact id) hr
    rw [ht] at hc
    cases hc

lemma live_tight_no_opposite_edges {width : ℕ} {goal w : BitVec width} {k : ℕ}
    {s : Finset (BitVec width)} (h : live basicOps goal k s) (hcard : s.card = k + 1)
    (hw : w ∈ s) (p q r t : Fin width)
    (hp : goal.getLsbD p.val = true) (hq : goal.getLsbD q.val = false)
    (hr : goal.getLsbD r.val = true) (ht : goal.getLsbD t.val = false)
    (hwp : w.getLsbD p.val = true) (hwq : w.getLsbD q.val = false)
    (hwr : w.getLsbD r.val = false) (hwt : w.getLsbD t.val = true)
    (hpq : ∀ u ∈ s, u ≠ w → u.getLsbD p.val = u.getLsbD q.val)
    (hrt : ∀ u ∈ s, u ≠ w → u.getLsbD r.val = u.getLsbD t.val) : False :=
  unate_no_opposite_edges (live_tight_unate h hcard) hw p q r t hp hq hr ht
    hwp hwq hwr hwt hpq hrt


def bitVecOfFn {n : ℕ} (f : Fin n → Bool) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (by simp)

lemma bitVecOfFn_bit {n : ℕ} (f : Fin n → Bool) (i : Fin n) :
    (bitVecOfFn f).getLsbD i.val = f i := by
  simp only [bitVecOfFn, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  rw [List.getD_eq_getElem?_getD]
  simp only [List.getElem?_ofFn, i.isLt, dite_eq_left, Option.getD_some]

def orientationColumn (m i : ℕ) : BitVec (2 ^ m) :=
  bitVecOfFn (fun j : Fin (2 ^ m) => j.val.testBit i)

def orientationInputs {width : ℕ} (frontier : List (BitVec width)) :
    List (BitVec width × BitVec (2 ^ frontier.length)) :=
  List.ofFn fun i : Fin frontier.length => (frontier.get i, orientationColumn frontier.length i.val)

lemma orientationInputs_words {width : ℕ} (frontier : List (BitVec width)) :
    (orientationInputs frontier).map Prod.fst = frontier := by
  simp only [orientationInputs, List.map_ofFn]
  change List.ofFn (fun i : Fin frontier.length => frontier.get i) = frontier
  exact List.ofFn_get frontier

lemma orientationInputs_complete {width : ℕ} (frontier : List (BitVec width))
    (direction : BitVec width → Bool) :
    ∃ j : Fin (2 ^ frontier.length), ∀ wc ∈ orientationInputs frontier,
      wc.2.getLsbD j.val = direction wc.1 := by
  let dirs := bitVecOfFn (fun i : Fin frontier.length => direction (frontier.get i))
  refine ⟨⟨dirs.toNat, dirs.isLt⟩, ?_⟩
  intro wc hwc
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hwc
  rw [show (orientationColumn frontier.length i.val).getLsbD dirs.toNat =
      dirs.toNat.testBit i.val from bitVecOfFn_bit _ ⟨dirs.toNat, dirs.isLt⟩]
  exact bitVecOfFn_bit _ i

def orientationConstraint {width phases : ℕ}
    (wc : BitVec width × BitVec phases) (p q : ℕ) : BitVec phases :=
  if wc.1.getLsbD p = wc.1.getLsbD q then BitVec.allOnes phases
  else if wc.1.getLsbD q then wc.2 else ~~~wc.2

def dominationMask {width phases : ℕ} (inputs : List (BitVec width × BitVec phases))
    (p q : ℕ) : BitVec phases :=
  inputs.foldr (fun wc mask => orientationConstraint wc p q &&& mask) (BitVec.allOnes phases)

def clearOrientationPair {width phases : ℕ} (goal : BitVec width)
    (inputs : List (BitVec width × BitVec phases)) (p q : ℕ)
    (valid : BitVec phases) : BitVec phases :=
  if valid = 0 then 0
  else if goal.getLsbD p && !(goal.getLsbD q) then valid &&& ~~~dominationMask inputs p q
    else valid

def orientationMaskInputs {width phases : ℕ} (goal : BitVec width)
    (inputs : List (BitVec width × BitVec phases)) : BitVec phases :=
  let rows := List.range width
  let positiveRows := rows.filter (fun p => goal.getLsbD p)
  let negativeRows := rows.filter (fun q => !(goal.getLsbD q))
  positiveRows.foldl (fun valid p => negativeRows.foldl (fun valid q =>
    clearOrientationPair goal inputs p q valid) valid) (BitVec.allOnes phases)

def orientationMask {width : ℕ} (goal : BitVec width)
    (frontier : List (BitVec width)) : BitVec (2 ^ frontier.length) :=
  orientationMaskInputs goal (orientationInputs frontier)

def orientationCheck {width : ℕ} (goal : BitVec width)
    (frontier : List (BitVec width)) : Bool :=
  decide (orientationMask goal frontier.eraseDups ≠ 0)

lemma orientationConstraint_sound {width phases : ℕ} (wc : BitVec width × BitVec phases)
    (p q : ℕ) (j : Fin phases) (d : Bool) (hc : wc.2.getLsbD j.val = d)
    (h : (orientationConstraint wc p q).getLsbD j.val = true) :
    signedValue d (wc.1.getLsbD p) = true → signedValue d (wc.1.getLsbD q) = true := by
  cases hp : wc.1.getLsbD p <;> cases hq : wc.1.getLsbD q <;> cases d <;>
    simp_all [orientationConstraint, signedValue, j.isLt]

lemma dominationMask_sound {width phases : ℕ} (inputs : List (BitVec width × BitVec phases))
    (p q : ℕ) (j : Fin phases) (direction : BitVec width → Bool)
    (hc : ∀ wc ∈ inputs, wc.2.getLsbD j.val = direction wc.1)
    (h : (dominationMask inputs p q).getLsbD j.val = true) :
    ∀ w ∈ inputs.map Prod.fst,
      signedValue (direction w) (w.getLsbD p) = true →
      signedValue (direction w) (w.getLsbD q) = true := by
  induction inputs with
  | nil => simp
  | cons wc ws ih =>
    have hh : (orientationConstraint wc p q).getLsbD j.val = true ∧
        (dominationMask ws p q).getLsbD j.val = true := by
      simpa only [dominationMask, List.foldr_cons, BitVec.getLsbD_and, Bool.and_eq_true] using h
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact orientationConstraint_sound wc p q j _ (hc wc List.mem_cons_self) hh.1
    · exact ih (fun x hx => hc x (List.mem_cons_of_mem _ hx)) hh.2 w hw

lemma clearOrientationPair_preserves {width phases : ℕ} (goal : BitVec width)
    (inputs : List (BitVec width × BitVec phases)) (direction : BitVec width → Bool)
    (j : Fin phases) (hc : ∀ wc ∈ inputs, wc.2.getLsbD j.val = direction wc.1)
    (hmono : ∀ p q : Fin width,
      (∀ w ∈ inputs.map Prod.fst, signedValue (direction w) (w.getLsbD p.val) = true →
        signedValue (direction w) (w.getLsbD q.val) = true) →
      goal.getLsbD p.val = true → goal.getLsbD q.val = true)
    (p q : ℕ) (hp : p < width) (hq : q < width)
    (valid : BitVec phases) (hv : valid.getLsbD j.val = true) :
    (clearOrientationPair goal inputs p q valid).getLsbD j.val = true := by
  have hz : valid ≠ 0 := by
    intro hz
    rw [hz] at hv
    simp at hv
  unfold clearOrientationPair
  rw [ite_eq_right hz]
  split
  next hg =>
    have hgood : goal.getLsbD p = true ∧ goal.getLsbD q = false := by
      simpa using hg
    have hnot : (dominationMask inputs p q).getLsbD j.val = false := by
      cases hd : (dominationMask inputs p q).getLsbD j.val with
      | false => rfl
      | true =>
        have hh := hmono ⟨p, hp⟩ ⟨q, hq⟩ (dominationMask_sound inputs p q j direction hc hd) hgood.1
        rw [hgood.2] at hh
        cases hh
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, j.isLt, decide_true,
      Bool.true_and, hv, hnot, Bool.not_false]
  next hg => exact hv

lemma foldl_preserves_phase {phases : ℕ} {β : Type} (xs : List β)
    (f : BitVec phases → β → BitVec phases) (j : Fin phases)
    (hf : ∀ a ∈ xs, ∀ v : BitVec phases, v.getLsbD j.val = true →
      (f v a).getLsbD j.val = true) (v : BitVec phases) (hv : v.getLsbD j.val = true) :
    (xs.foldl f v).getLsbD j.val = true := by
  induction xs generalizing v with
  | nil => exact hv
  | cons a as ih =>
    apply ih (fun a ha => hf a (List.mem_cons_of_mem _ ha))
    exact hf a List.mem_cons_self v hv

lemma orientationMaskInputs_preserves {width phases : ℕ} (goal : BitVec width)
    (inputs : List (BitVec width × BitVec phases)) (direction : BitVec width → Bool)
    (j : Fin phases) (hc : ∀ wc ∈ inputs, wc.2.getLsbD j.val = direction wc.1)
    (hmono : ∀ p q : Fin width,
      (∀ w ∈ inputs.map Prod.fst, signedValue (direction w) (w.getLsbD p.val) = true →
        signedValue (direction w) (w.getLsbD q.val) = true) →
      goal.getLsbD p.val = true → goal.getLsbD q.val = true) :
    (orientationMaskInputs goal inputs).getLsbD j.val = true := by
  apply foldl_preserves_phase
  · intro p hp valid hv
    apply foldl_preserves_phase
    · intro q hq valid hv
      exact clearOrientationPair_preserves goal inputs direction j hc hmono p q
        (List.mem_range.mp (List.mem_filter.mp hp).1)
        (List.mem_range.mp (List.mem_filter.mp hq).1) valid hv
    · exact hv
  · simp [j.isLt]

lemma orientationMask_of_unate {width : ℕ} (goal : BitVec width)
    (frontier : List (BitVec width)) (h : unateSeparator goal frontier.toFinset) :
    orientationMask goal frontier ≠ 0 := by
  obtain ⟨direction, hdir⟩ := h
  obtain ⟨j, hj⟩ := orientationInputs_complete frontier direction
  have hmono : ∀ p q : Fin width,
      (∀ w ∈ (orientationInputs frontier).map Prod.fst,
        signedValue (direction w) (w.getLsbD p.val) = true →
        signedValue (direction w) (w.getLsbD q.val) = true) →
      goal.getLsbD p.val = true → goal.getLsbD q.val = true := by
    intro p q hpq
    apply hdir p q
    intro w hw
    apply hpq w
    rw [orientationInputs_words]
    exact List.mem_toFinset.mp hw
  have hh := orientationMaskInputs_preserves goal (orientationInputs frontier) direction j hj hmono
  intro hz
  change (orientationMask goal frontier).getLsbD j.val = true at hh
  rw [hz] at hh
  simp at hh

lemma orientationCheck_of_unate {width : ℕ} (goal : BitVec width)
    (frontier : List (BitVec width)) (h : unateSeparator goal frontier.toFinset) :
    orientationCheck goal frontier = true := by
  apply decide_eq_true
  apply orientationMask_of_unate
  have he : frontier.eraseDups.toFinset = frontier.toFinset := by
    apply Finset.ext
    intro w
    simp only [List.mem_toFinset, List.mem_eraseDups]
  rw [he]
  exact h

lemma not_live_of_orientationCheck {width k : ℕ} (goal : BitVec width)
    (frontier : List (BitVec width)) (hcard : frontier.toFinset.card = k + 1)
    (hcheck : orientationCheck goal frontier = false) :
    ¬ live basicOps goal k frontier.toFinset := by
  intro h
  have hh := orientationCheck_of_unate goal frontier (live_tight_unate h hcard)
  rw [hcheck] at hh
  cases hh


def graphEdge (graph : List ℕ) (i j : ℕ) : Bool :=
  (graph.getD i 0).testBit j || (graph.getD j 0).testBit i

def colorPrefix (f : ℕ → ℕ) (n : ℕ) : List ℕ := (List.range n).map f

lemma colorPrefix_length (f : ℕ → ℕ) (n : ℕ) : (colorPrefix f n).length = n := by
  simp [colorPrefix]

lemma colorPrefix_get (f : ℕ → ℕ) (n i : ℕ) (hi : i < n) :
    (colorPrefix f n).getD i 0 = f i := by
  simp [colorPrefix, List.getD_eq_getElem?_getD, hi]

lemma colorPrefix_succ (f : ℕ → ℕ) (n : ℕ) :
    colorPrefix f (n + 1) = colorPrefix f n ++ [f n] := by
  simp [colorPrefix, List.range_succ]

def fitsColor (graph assigned : List ℕ) (c : ℕ) : Bool :=
  !(graphEdge graph assigned.length assigned.length) &&
    (List.range assigned.length).all (fun i =>
      !(graphEdge graph assigned.length i) || assigned.getD i 0 != c)

def colorSearch (graph : List ℕ) (colors : ℕ) : ℕ → List ℕ → Bool
  | 0, _ => true
  | k + 1, assigned => (List.range colors).any (fun c =>
      fitsColor graph assigned c && colorSearch graph colors k (assigned ++ [c]))

def graphColorable (graph : List ℕ) (colors : ℕ) : Prop :=
  ∃ f : ℕ → ℕ, (∀ i < graph.length, f i < colors) ∧
    ∀ i < graph.length, ∀ j < graph.length,
      (graph.getD i 0).testBit j = true → f i ≠ f j

def graphColorCheck (graph : List ℕ) (colors : ℕ) : Bool :=
  colorSearch graph colors graph.length []

lemma graphEdge_colors {graph : List ℕ} {f : ℕ → ℕ}
    (hproper : ∀ i < graph.length, ∀ j < graph.length,
      (graph.getD i 0).testBit j = true → f i ≠ f j)
    {i j : ℕ} (hi : i < graph.length) (hj : j < graph.length)
    (h : graphEdge graph i j = true) : f i ≠ f j := by
  simp only [graphEdge, Bool.or_eq_true] at h
  rcases h with h | h
  · exact hproper i hi j hj h
  · exact Ne.symm (hproper j hj i hi h)

lemma fitsColor_prefix {graph : List ℕ} {f : ℕ → ℕ}
    (hproper : ∀ i < graph.length, ∀ j < graph.length,
      (graph.getD i 0).testBit j = true → f i ≠ f j)
    {n : ℕ} (hn : n < graph.length) :
    fitsColor graph (colorPrefix f n) (f n) = true := by
  have hself : graphEdge graph n n = false := by
    cases he : graphEdge graph n n with
    | false => rfl
    | true => exact False.elim ((graphEdge_colors hproper hn hn he) rfl)
  simp only [fitsColor, colorPrefix_length, hself, Bool.not_false, Bool.true_and]
  apply List.all_eq_true.mpr
  intro i hi
  have hin : i < n := List.mem_range.mp hi
  rw [colorPrefix_get f n i hin]
  cases he : graphEdge graph n i with
  | false => simp
  | true =>
    have hh : f i ≠ f n := Ne.symm (graphEdge_colors hproper hn (by omega) he)
    simp [hh]

lemma colorSearch_complete {graph : List ℕ} {colors : ℕ} {f : ℕ → ℕ}
    (hbound : ∀ i < graph.length, f i < colors)
    (hproper : ∀ i < graph.length, ∀ j < graph.length,
      (graph.getD i 0).testBit j = true → f i ≠ f j)
    (k n : ℕ) (hsize : n + k ≤ graph.length) :
    colorSearch graph colors k (colorPrefix f n) = true := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    have hn : n < graph.length := by omega
    apply List.any_eq_true.mpr
    refine ⟨f n, List.mem_range.mpr (hbound n hn), ?_⟩
    simp only [Bool.and_eq_true]
    constructor
    · exact fitsColor_prefix hproper hn
    · simpa only [colorPrefix_succ] using ih (n + 1) (by omega)

lemma graphColorCheck_complete {graph : List ℕ} {colors : ℕ}
    (h : graphColorable graph colors) : graphColorCheck graph colors = true := by
  obtain ⟨f, hbound, hproper⟩ := h
  simpa [graphColorCheck, colorPrefix] using
    colorSearch_complete hbound hproper graph.length 0 (by omega)

lemma not_graphColorable_of_check {graph : List ℕ} {colors : ℕ}
    (h : graphColorCheck graph colors = false) : ¬ graphColorable graph colors := by
  intro hc
  have hh := graphColorCheck_complete hc
  rw [h] at hh
  cases hh

def graphEmptyCheck (graph : List ℕ) : Bool :=
  graph.all (fun row => decide (BitVec.ofNat graph.length row = 0))

lemma graphEmptyCheck_complete {graph : List ℕ} (h : graphColorable graph 1) :
    graphEmptyCheck graph = true := by
  obtain ⟨f, hbound, hproper⟩ := h
  apply List.all_eq_true.mpr
  intro row hrow
  obtain ⟨i, hin, hroweq⟩ := List.mem_iff_getElem.mp hrow
  have hr : graph.getD i 0 = row := by
    simp [List.getD_eq_getElem?_getD, hin, hroweq]
  apply decide_eq_true
  rw [← hr]
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro j hj
  have hfalse : (graph.getD i 0).testBit j = false := by
    cases he : (graph.getD i 0).testBit j with
    | false => rfl
    | true =>
      have hh := hproper i hin j hj he
      have hb1 := hbound i hin
      have hb2 := hbound j hj
      omega
  simp only [BitVec.getLsbD_ofNat, hj, decide_true, Bool.true_and, hfalse]
  change false = (BitVec.ofNat graph.length 0).getLsbD j
  simp [BitVec.getLsbD_ofNat]

def graphColorFast (graph : List ℕ) (colors : ℕ) : Bool :=
  if colors = 1 then graphEmptyCheck graph else graphColorCheck graph colors

lemma graphColorFast_complete {graph : List ℕ} {colors : ℕ}
    (h : graphColorable graph colors) : graphColorFast graph colors = true := by
  unfold graphColorFast
  split
  next hc => subst colors; exact graphEmptyCheck_complete h
  next hc => exact graphColorCheck_complete h

lemma not_graphColorable_of_fast {graph : List ℕ} {colors : ℕ}
    (h : graphColorFast graph colors = false) : ¬ graphColorable graph colors := by
  intro hc
  have hh := graphColorFast_complete hc
  rw [h] at hh
  cases hh

lemma graphColorable_of_fin {graph : List ℕ} {colors : ℕ}
    (f : Fin graph.length → Fin colors)
    (hproper : ∀ i j, (graph.getD i.val 0).testBit j.val = true → f i ≠ f j) :
    graphColorable graph colors := by
  let g : ℕ → ℕ := fun i => if hi : i < graph.length then (f ⟨i, hi⟩).val else 0
  refine ⟨g, ?_, ?_⟩
  · intro i hi
    simp [g, hi]
  · intro i hi j hj he
    have hh := hproper ⟨i, hi⟩ ⟨j, hj⟩ he
    simp only [g, hi, hj, dite_true]
    intro eq
    apply hh
    exact Fin.ext eq

lemma not_fin_coloring_of_fast {graph : List ℕ} {colors : ℕ}
    (h : graphColorFast graph colors = false)
    (f : Fin graph.length → Fin colors)
    (hproper : ∀ i j, (graph.getD i.val 0).testBit j.val = true → f i ≠ f j) : False :=
  not_graphColorable_of_fast h (graphColorable_of_fin f hproper)



def inducedGraph (graph chosen : List ℕ) : List ℕ :=
  chosen.map fun v => (BitVec.ofBoolListLE (chosen.map fun u => graphEdge graph v u)).toNat

lemma inducedGraph_length (graph chosen : List ℕ) :
    (inducedGraph graph chosen).length = chosen.length := by
  simp only [inducedGraph, List.length_map]

lemma inducedGraph_bit (graph chosen : List ℕ) (i j : ℕ)
    (hi : i < chosen.length) (hj : j < chosen.length) :
    ((inducedGraph graph chosen).getD i 0).testBit j =
      graphEdge graph (chosen.getD i 0) (chosen.getD j 0) := by
  rw [List.getD_eq_getElem _ _ (by simpa only [inducedGraph_length] using hi)]
  simp only [inducedGraph, List.getElem_map, BitVec.testBit_toNat,
    BitVec.getLsbD_ofBoolListLE]
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hj),
    List.getElem_map, List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj]

lemma graphColorable_induced {graph chosen : List ℕ} {colors : ℕ}
    (hc : graphColorable graph colors)
    (hchosen : ∀ v ∈ chosen, v < graph.length) :
    graphColorable (inducedGraph graph chosen) colors := by
  obtain ⟨f, hbound, hproper⟩ := hc
  have hv (i : ℕ) (hi : i < chosen.length) : chosen.getD i 0 < graph.length := by
    rw [List.getD_eq_getElem _ _ hi]
    exact hchosen _ (List.getElem_mem hi)
  refine ⟨fun i => f (chosen.getD i 0), ?_, ?_⟩
  · intro i hi
    rw [inducedGraph_length] at hi
    exact hbound _ (hv i hi)
  · intro i hi j hj he
    rw [inducedGraph_length] at hi hj
    rw [inducedGraph_bit graph chosen i j hi hj] at he
    exact graphEdge_colors hproper (hv i hi) (hv j hj) he

def graphDegree (graph : List ℕ) (v : ℕ) : ℕ :=
  ((List.range graph.length).filter fun u => graphEdge graph v u).length

def degreeInsert (a : ℕ × ℕ) : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => [a]
  | b :: rest => if b.1 ≤ a.1 then a :: b :: rest else b :: degreeInsert a rest

def degreeSort : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => []
  | a :: rest => degreeInsert a (degreeSort rest)

def graphOrder (graph : List ℕ) : List ℕ :=
  (degreeSort (((List.range graph.length).map fun v => (graphDegree graph v, v)).filter
    fun entry => 0 < entry.1)).map Prod.snd

lemma mem_degreeInsert (a entry : ℕ × ℕ) (entries : List (ℕ × ℕ)) :
    entry ∈ degreeInsert a entries ↔ entry = a ∨ entry ∈ entries := by
  induction entries with
  | nil => simp [degreeInsert]
  | cons b rest ih =>
    simp only [degreeInsert]
    split
    · simp only [List.mem_cons]
    · simp only [List.mem_cons, ih]
      tauto

lemma mem_degreeSort (entry : ℕ × ℕ) (entries : List (ℕ × ℕ)) :
    entry ∈ degreeSort entries ↔ entry ∈ entries := by
  induction entries with
  | nil => rfl
  | cons a rest ih =>
    simp only [degreeSort, mem_degreeInsert, ih, List.mem_cons]

lemma graphOrder_valid (graph : List ℕ) :
    ∀ v ∈ graphOrder graph, v < graph.length := by
  intro v hv
  simp only [graphOrder, List.mem_map] at hv
  obtain ⟨entry, he, hvalue⟩ := hv
  rw [mem_degreeSort] at he
  have hentry := (List.mem_filter.mp he).1
  obtain ⟨u, hu, hue⟩ := List.mem_map.mp hentry
  have hlt : u < graph.length := List.mem_range.mp hu
  subst entry
  change u = v at hvalue
  simpa only [hvalue] using hlt

def graphOrderedCheck (graph : List ℕ) (colors : ℕ) : Bool :=
  graphColorCheck (inducedGraph graph (graphOrder graph)) colors

lemma graphOrderedCheck_complete {graph : List ℕ} {colors : ℕ}
    (hc : graphColorable graph colors) : graphOrderedCheck graph colors = true := by
  exact graphColorCheck_complete (graphColorable_induced hc (graphOrder_valid graph))

lemma not_graphColorable_of_ordered {graph : List ℕ} {colors : ℕ}
    (h : graphOrderedCheck graph colors = false) : ¬ graphColorable graph colors := by
  intro hc
  have hh := graphOrderedCheck_complete hc
  rw [h] at hh
  cases hh

def graphColorDegreeFast (graph : List ℕ) (colors : ℕ) : Bool :=
  if colors = 1 then graphEmptyCheck graph
  else if 1 < colors then graphOrderedCheck graph colors
  else graphColorCheck graph colors

lemma graphColorDegreeFast_complete {graph : List ℕ} {colors : ℕ}
    (hc : graphColorable graph colors) : graphColorDegreeFast graph colors = true := by
  unfold graphColorDegreeFast
  split
  · next h => subst colors; exact graphEmptyCheck_complete hc
  · split
    · exact graphOrderedCheck_complete hc
    · exact graphColorCheck_complete hc

lemma not_graphColorable_of_degreeFast {graph : List ℕ} {colors : ℕ}
    (h : graphColorDegreeFast graph colors = false) : ¬ graphColorable graph colors := by
  intro hc
  have hh := graphColorDegreeFast_complete hc
  rw [h] at hh
  cases hh


def colorSearchSym (graph : List ℕ) (colors : ℕ) : ℕ → ℕ → List ℕ → Bool
  | 0, _, _ => true
  | k + 1, used, assigned => (List.range (min colors (used + 1))).any (fun c =>
      fitsColor graph assigned c &&
        colorSearchSym graph colors k (max used (c + 1)) (assigned ++ [c]))

lemma colorPrefix_congr (f g : ℕ → ℕ) (n : ℕ) (h : ∀ i < n, f i = g i) :
    colorPrefix f n = colorPrefix g n := by
  apply List.map_congr_left
  intro i hi
  exact h i (List.mem_range.mp hi)

lemma colorRenaming_next (f : ℕ → ℕ) (n used colors : ℕ)
    (hnext : f n < colors) (hprior : ∀ i < n, f i < used) :
    ∃ e : ℕ ≃ ℕ,
      (∀ c < colors, e c < colors) ∧
      (∀ i < n, e (f i) = f i) ∧
      e (f n) < min colors (used + 1) := by
  by_cases hold : f n < used
  · refine ⟨Equiv.refl _, (fun c hc => hc), (fun i hi => rfl), ?_⟩
    change f n < min colors (used + 1)
    exact lt_min hnext (by omega)
  · have hu : used < colors := by omega
    refine ⟨Equiv.swap (f n) used, ?_, ?_, ?_⟩
    · intro c hc
      by_cases hcn : c = f n
      · subst c
        simpa only [Equiv.swap_apply_left] using hu
      · by_cases hcu : c = used
        · subst c
          simpa only [Equiv.swap_apply_right] using hnext
        · rwa [Equiv.swap_apply_of_ne_of_ne hcn hcu]
    · intro i hi
      have hfi := hprior i hi
      exact Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)
    · rw [Equiv.swap_apply_left]
      exact lt_min hu (Nat.lt_succ_self _)

lemma colorSearchSym_complete {graph : List ℕ} {colors : ℕ} {f : ℕ → ℕ}
    (hbound : ∀ i < graph.length, f i < colors)
    (hproper : ∀ i < graph.length, ∀ j < graph.length,
      (graph.getD i 0).testBit j = true → f i ≠ f j)
    (k n used : ℕ) (hsize : n + k ≤ graph.length) (hused : used ≤ colors)
    (hprior : ∀ i < n, f i < used) :
    colorSearchSym graph colors k used (colorPrefix f n) = true := by
  induction k generalizing f n used with
  | zero => rfl
  | succ k ih =>
    have hn : n < graph.length := by omega
    obtain ⟨e, heBound, heFix, heNext⟩ :=
      colorRenaming_next f n used colors (hbound n hn) hprior
    let g : ℕ → ℕ := fun i => e (f i)
    have hgBound : ∀ i < graph.length, g i < colors :=
      fun i hi => heBound (f i) (hbound i hi)
    have hgProper : ∀ i < graph.length, ∀ j < graph.length,
        (graph.getD i 0).testBit j = true → g i ≠ g j := by
      intro i hi j hj hedge heq
      exact hproper i hi j hj hedge (e.injective heq)
    have hprefix : colorPrefix g n = colorPrefix f n :=
      colorPrefix_congr g f n heFix
    apply List.any_eq_true.mpr
    refine ⟨g n, List.mem_range.mpr heNext, ?_⟩
    simp only [Bool.and_eq_true]
    constructor
    · rw [← hprefix]
      exact fitsColor_prefix hgProper hn
    · rw [← hprefix, ← colorPrefix_succ]
      apply ih hgBound hgProper (n + 1) (max used (g n + 1))
      · omega
      · exact max_le hused (Nat.succ_le_of_lt (hgBound n hn))
      · intro i hi
        by_cases hin : i < n
        · have heq : g i = f i := heFix i hin
          rw [heq]
          exact lt_of_lt_of_le (hprior i hin) (Nat.le_max_left _ _)
        · have heq : i = n := by omega
          subst i
          exact lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _)

def graphColorSym (graph : List ℕ) (colors : ℕ) : Bool :=
  colorSearchSym graph colors graph.length 0 []

lemma graphColorSym_complete {graph : List ℕ} {colors : ℕ}
    (h : graphColorable graph colors) : graphColorSym graph colors = true := by
  obtain ⟨f, hbound, hproper⟩ := h
  simpa only [graphColorSym, colorPrefix, List.range_zero, List.map_nil] using
    colorSearchSym_complete hbound hproper graph.length 0 0 (by omega) (by omega)
      (by intro i hi; omega)

lemma not_graphColorable_of_sym {graph : List ℕ} {colors : ℕ}
    (h : graphColorSym graph colors = false) : ¬ graphColorable graph colors := by
  intro hc
  have hh := graphColorSym_complete hc
  rw [h] at hh
  cases hh

def graphColorSymOrdered (graph : List ℕ) (colors : ℕ) : Bool :=
  graphColorSym (inducedGraph graph (graphOrder graph)) colors

lemma graphColorSymOrdered_complete {graph : List ℕ} {colors : ℕ}
    (hc : graphColorable graph colors) : graphColorSymOrdered graph colors = true := by
  exact graphColorSym_complete (graphColorable_induced hc (graphOrder_valid graph))

def graphColorSymFast (graph : List ℕ) (colors : ℕ) : Bool :=
  if colors = 1 then graphEmptyCheck graph
  else if 1 < colors then graphColorSymOrdered graph colors
  else graphColorSym graph colors

lemma graphColorSymFast_complete {graph : List ℕ} {colors : ℕ}
    (hc : graphColorable graph colors) : graphColorSymFast graph colors = true := by
  unfold graphColorSymFast
  split
  · next h => subst colors; exact graphEmptyCheck_complete hc
  · split
    · exact graphColorSymOrdered_complete hc
    · exact graphColorSym_complete hc

lemma not_graphColorable_of_symFast {graph : List ℕ} {colors : ℕ}
    (h : graphColorSymFast graph colors = false) : ¬ graphColorable graph colors := by
  intro hc
  have hh := graphColorSymFast_complete hc
  rw [h] at hh
  cases hh

lemma not_fin_coloring_of_symFast {graph : List ℕ} {colors : ℕ}
    (h : graphColorSymFast graph colors = false)
    (f : Fin graph.length → Fin colors)
    (hproper : ∀ i j, (graph.getD i.val 0).testBit j.val = true → f i ≠ f j) : False :=
  not_graphColorable_of_symFast h (graphColorable_of_fin f hproper)

end PEqualNP.Outside.L_meta_10760
