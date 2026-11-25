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

end PEqualNP.Outside.L_meta_10760
