import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_2592_aux.ReplaceLast

def Above (w v : List Bool) : Prop :=
  w.length = v.length ∧ ∀ i, w.getD i false = true → v.getD i false = true

lemma getD_snoc_ne (w : List Bool) (b : Bool) (i : ℕ) (h : i ≠ w.length) :
    (w ++ [b]).getD i false = w.getD i false := by
  by_cases hi : i < w.length
  · exact List.getD_append _ _ _ _ hi
  · have hlarge : (w ++ [b]).length ≤ i := by
      simp only [List.length_append, List.length_singleton]
      omega
    rw [List.getD_eq_default _ _ hlarge, List.getD_eq_default _ _ (by omega)]

lemma above_snoc {w v : List Bool} {b c : Bool} (h : Above w v)
    (hb : b = true → c = true) : Above (w ++ [b]) (v ++ [c]) := by
  refine ⟨by simp [h.1], ?_⟩
  intro i hi
  by_cases he : i = w.length
  · subst i
    simp only [List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self,
      List.getD_cons_zero] at hi
    rw [h.1]
    simpa only [List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self,
      List.getD_cons_zero]
      using hb hi
  · rw [getD_snoc_ne _ _ _ he] at hi
    rw [getD_snoc_ne _ _ _ (by rw [← h.1]; exact he)]
    exact h.2 i hi

lemma wires_above (gs : List Gate)
    (mono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ w v : List Bool, Above w v →
      Above (Circuit.wires ⟨gs, 0⟩ w) (Circuit.wires ⟨gs, 0⟩ v) := by
  induction gs with
  | nil => intro w v h; exact h
  | cons g gs ih =>
    intro w v h
    apply ih (fun a ha => mono a (List.mem_cons_of_mem _ ha))
    apply above_snoc h
    rcases mono g List.mem_cons_self with op | op
    · rw [op]
      simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
      intro hall b hb
      obtain ⟨i, hi, rfl⟩ := hb
      exact h.2 i (hall _ ⟨i, hi, rfl⟩)
    · rw [op]
      simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
      rintro ⟨b, ⟨i, hi, rfl⟩, hb⟩
      exact ⟨_, ⟨i, hi, rfl⟩, h.2 i hb⟩

def readValue (pre : List Gate) (ins : List ℕ) (x : List Bool) : Bool :=
  (ins.map (fun i => (Circuit.wires ⟨pre, 0⟩ x).getD i false)).headD false

def slotValue (pre post : List Gate) (o : ℕ) (b : Bool) (x : List Bool) : Bool :=
  Circuit.eval ⟨post, o⟩ (Circuit.wires ⟨pre, 0⟩ x ++ [b])

lemma slot_monotone (pre post : List Gate) (o : ℕ) (mono : Monotone2 ⟨post, o⟩)
    (x : List Bool) :
    slotValue pre post o false x = true → slotValue pre post o true x = true := by
  have h := wires_above post (fun g hg => (mono g hg).1)
    (Circuit.wires ⟨pre, 0⟩ x ++ [false]) (Circuit.wires ⟨pre, 0⟩ x ++ [true])
    (above_snoc ⟨rfl, fun _ h => h⟩ (by simp))
  exact h.2 o

lemma not_eval (pre post : List Gate) (ins : List ℕ) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨pre ++ ⟨GateOp.not, ins⟩ :: post, o⟩ x =
      slotValue pre post o (!(readValue pre ins x)) x := by
  simp only [Circuit.eval, Circuit.wires, List.foldl_append, List.foldl_cons,
    GateOp.eval, slotValue, readValue]

lemma true_eval (pre post : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨pre ++ ⟨GateOp.and, []⟩ :: post, o⟩ x =
      slotValue pre post o true x := by
  simp only [Circuit.eval, Circuit.wires, List.foldl_append, List.foldl_cons,
    GateOp.eval, List.map_nil, List.all_nil, slotValue]

lemma false_eval (pre post : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨pre ++ ⟨GateOp.or, []⟩ :: post, o⟩ x =
      slotValue pre post o false x := by
  simp only [Circuit.eval, Circuit.wires, List.foldl_append, List.foldl_cons,
    GateOp.eval, List.map_nil, List.any_nil, slotValue]

lemma replace_true (pre post : List Gate) (ins : List ℕ) (o : ℕ)
    (mono : Monotone2 ⟨post, o⟩) (x : List Bool)
    (h : readValue pre ins x = true →
      Circuit.eval ⟨pre ++ ⟨GateOp.not, ins⟩ :: post, o⟩ x = true) :
    Circuit.eval ⟨pre ++ ⟨GateOp.and, []⟩ :: post, o⟩ x =
      Circuit.eval ⟨pre ++ ⟨GateOp.not, ins⟩ :: post, o⟩ x := by
  rw [true_eval, not_eval]
  cases hr : readValue pre ins x with
  | false => rfl
  | true =>
    have old := h hr
    rw [not_eval, hr] at old
    exact (slot_monotone pre post o mono x old).trans old.symm

lemma replace_false (pre post : List Gate) (ins : List ℕ) (o : ℕ)
    (mono : Monotone2 ⟨post, o⟩) (x : List Bool)
    (h :
      Circuit.eval ⟨pre ++ ⟨GateOp.not, ins⟩ :: post, o⟩ x = true →
        readValue pre ins x = true) :
    Circuit.eval ⟨pre ++ ⟨GateOp.or, []⟩ :: post, o⟩ x =
      Circuit.eval ⟨pre ++ ⟨GateOp.not, ins⟩ :: post, o⟩ x := by
  rw [false_eval, not_eval]
  cases hr : readValue pre ins x with
  | true => rfl
  | false =>
    have old : slotValue pre post o true x = false := by
      apply Bool.eq_false_iff.mpr
      intro ht
      have bad := h (by rw [not_eval, hr]; exact ht)
      exact Bool.noConfusion (hr.symm.trans bad)
    have new : slotValue pre post o false x = false := by
      apply Bool.eq_false_iff.mpr
      intro ht
      have bad := slot_monotone pre post o mono x ht
      exact Bool.noConfusion (old.symm.trans bad)
    exact new.trans old.symm

end PEqualNP.Outside.L_meta_2592_aux.ReplaceLast
