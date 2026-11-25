import SoleReaderFreeCore
import SafeNotRaise

namespace PEqualNP.Outside.L_meta_1884.DirectFilter

open PEqualNP.CircuitLowerBounds
open SoleReader

def seed (x : Fin 10 → Bool) : List Bool := List.ofFn x ++ [!x 0]

def operand (pre : List Gate) (ins : List Nat) (x : Fin 10 → Bool) : Bool :=
  (ins.map fun i => (run pre (seed x)).getD i false).headD false

lemma run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (step w g)).length = _
    rw [ih]
    simp [step, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

lemma operand_independent (pre : List Gate) (ins : List Nat) (t : Fin 10)
    (ht0 : t ≠ 0) (away : ∀ g ∈ pre, t.val ∉ g.inputs) (hi : t.val ∉ ins)
    (x y : Fin 10 → Bool) (off : ∀ i, i ≠ t → x i = y i) :
    operand pre ins x = operand pre ins y := by
  apply congrArg (fun bs : List Bool => bs.headD false)
  apply List.map_congr_left
  intro i his
  exact partner_independent pre _ _ (free_input_agree t ht0 x y off) away
    (fun he => hi (he ▸ his))

lemma operand_fiber_mono (pre : List Gate) (ins : List Nat)
    (allowed : ∀ g ∈ pre, g.op = .and ∨ g.op = .or)
    (x y : Fin 10 → Bool) (hzero : x 0 = y 0)
    (hxy : ∀ i, x i = true → y i = true) :
    operand pre ins x = true → operand pre ins y = true := by
  have hi : SafeNot.above (List.ofFn x) (List.ofFn y) := by
    refine ⟨by simp, ?_⟩
    intro i
    by_cases hlt : i < 10
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt, dite_true,
        Option.getD_some]
      exact Bool.le_iff_imp.mpr (hxy ⟨i, hlt⟩)
    · rw [List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by simp; omega)]
  have hs : SafeNot.above (seed x) (seed y) :=
    SafeNot.append_above hi (by rw [hzero])
  have hr := SafeNot.run_above pre _ _ hs allowed
  cases ins with
  | nil => simp [operand]
  | cons i is => exact Bool.le_iff_imp.mp (hr.2 i)

lemma not_value (pre mid : List Gate) (ins : List Nat) (x : Fin 10 → Bool) :
    (run (pre ++ Gate.mk .not ins :: mid) (seed x)).getD (11 + pre.length) false =
      !operand pre ins x := by
  have hl : (run pre (seed x)).length = 11 + pre.length := by
    rw [run_length]; simp [seed]
  simp only [run, List.foldl_append, List.foldl_cons]
  change (run mid (run pre (seed x) ++ [!operand pre ins x])).getD
    (11 + pre.length) false = !operand pre ins x
  rw [run_input mid _ _ (by simp [hl])]
  rw [← hl]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append, lt_self_iff_false,
    if_false, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]

lemma filter_boolean (a b h : Bool) (hh : (a || h) = (b || h)) :
    (a && !h) = (b && !h) := by
  cases h <;> simpa using hh

lemma factor (pre mid post : List Gate) (ins : List Nat) (t : Fin 10) (ht0 : t ≠ 0)
    (out : Nat) (f : (Fin 10 → Bool) → Bool)
    (hp : ∀ g ∈ pre, t.val ∉ g.inputs) (hi : t.val ∉ ins)
    (hm : ∀ g ∈ mid, t.val ∉ g.inputs) (hs : ∀ g ∈ post, t.val ∉ g.inputs)
    (ho : out ≠ t.val)
    (computes : ∀ x, (Circuit.mk
      ((pre ++ Gate.mk .not ins :: mid) ++ Gate.mk .and [t.val, 11 + pre.length] :: post)
      out).eval (seed x) = f x)
    (x y : Fin 10 → Bool) (off : ∀ i, i ≠ t → x i = y i)
    (hgate : (x t || operand pre ins x) = (y t || operand pre ins y)) : f x = f y := by
  have hH := operand_independent pre ins t ht0 hp hi x y off
  have he := free_factor_and (pre ++ Gate.mk .not ins :: mid) post t ht0
    (11 + pre.length) out x y off (by
      intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact hp g hg
      · rcases List.mem_cons.mp hg with rfl | hg
        · exact hi
        · exact hm g hg) hs ho
  have hh : (x t && (run (pre ++ Gate.mk .not ins :: mid) (seed x)).getD
      (11 + pre.length) false) =
      (y t && (run (pre ++ Gate.mk .not ins :: mid) (seed y)).getD
        (11 + pre.length) false) := by
    rw [not_value, not_value, ← hH]
    rw [← hH] at hgate
    exact filter_boolean _ _ _ hgate
  exact (computes x).symm.trans ((he hh).trans (computes y))

end PEqualNP.Outside.L_meta_1884.DirectFilter
