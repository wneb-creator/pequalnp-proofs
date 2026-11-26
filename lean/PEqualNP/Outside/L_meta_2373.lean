import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2373_aux

namespace LastNot

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def Above (a b : List Bool) : Prop :=
  a.length = b.length ∧ ∀ i, a.getD i false = true → b.getD i false = true

lemma above_snoc {a b : List Bool} {p q : Bool} (hab : Above a b)
    (hpq : p = true → q = true) : Above (a ++ [p]) (b ++ [q]) := by
  refine ⟨by simp [hab.1], ?_⟩
  intro i hi
  by_cases hlt : i < a.length
  · rw [List.getD_append _ _ _ _ hlt] at hi
    rw [List.getD_append _ _ _ _ (by rw [← hab.1]; exact hlt)]
    exact hab.2 i hi
  · by_cases heq : i = a.length
    · subst i
      simpa [List.getD, List.getElem?_append, hab.1] using hpq (by
        simpa [List.getD, List.getElem?_append] using hi)
    · rw [List.getD_eq_default] at hi
      · contradiction
      · simp; omega

lemma above_wires (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ a b : List Bool, Above a b →
      Above ((⟨gs, 0⟩ : Circuit).wires a) ((⟨gs, 0⟩ : Circuit).wires b) := by
  induction gs with
  | nil => intro a b hab; exact hab
  | cons g gs ih =>
    intro a b hab
    change Above ((⟨gs, 0⟩ : Circuit).wires
      (a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)]))
      ((⟨gs, 0⟩ : Circuit).wires
      (b ++ [g.op.eval (g.inputs.map fun i => b.getD i false)]))
    apply ih (fun g hg => hgs g (by simp [hg]))
    apply above_snoc hab
    rcases hgs g (by simp) with hop | hop
    · rw [hop]
      simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
      intro hall v hv
      obtain ⟨j, hj, rfl⟩ := hv
      exact hab.2 j (hall _ ⟨j, hj, rfl⟩)
    · rw [hop]
      simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
      rintro ⟨v, ⟨j, hj, rfl⟩, hv⟩
      exact ⟨_, ⟨j, hj, rfl⟩, hab.2 j hv⟩

lemma context_monotone (post : List Gate)
    (hpost : ∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or)
    (base : List Bool) (out : ℕ) (p q : Bool) (hpq : p = true → q = true) :
    ((⟨post, out⟩ : Circuit).eval (base ++ [p])) = true →
      ((⟨post, out⟩ : Circuit).eval (base ++ [q])) = true :=
  (above_wires post hpost _ _ (above_snoc ⟨rfl, fun _ h => h⟩ hpq)).2 out

lemma negated_context_replace_true {α : Type*} (F h : α → Bool)
    (P : α → Bool → Bool)
    (hP : ∀ x p q, (p = true → q = true) → P x p = true → P x q = true)
    (correct : ∀ x, P x (!(h x)) = F x)
    (sound : ∀ x, h x = true → F x = true) : ∀ x, P x true = F x := by
  intro x
  cases hf : F x with
  | false =>
    have hh : h x = false := by
      cases he : h x <;> simp_all
    simpa [hh, hf] using correct x
  | true =>
    exact hP x (!(h x)) true (by simp) (by rw [correct, hf])

lemma negated_context_replace_false {α : Type*} (F h : α → Bool)
    (P : α → Bool → Bool)
    (hP : ∀ x p q, (p = true → q = true) → P x p = true → P x q = true)
    (correct : ∀ x, P x (!(h x)) = F x)
    (covers : ∀ x, F x = true → h x = true) : ∀ x, P x false = F x := by
  intro x
  cases hf : F x with
  | false =>
    cases hp : P x false with
    | false => rfl
    | true =>
      have contra := hP x false (!(h x)) (by simp) hp
      rw [correct, hf] at contra
      contradiction
  | true => simpa [covers x hf, hf] using correct x

def lastInput (pre : List Gate) (ins : List ℕ) (x : List Bool) : Bool :=
  (ins.map fun i => ((⟨pre, 0⟩ : Circuit).wires x).getD i false).headD false

def constant (b : Bool) : Gate := if b then ⟨GateOp.and, []⟩ else ⟨GateOp.or, []⟩

lemma constant_eval (b : Bool) (w : List Bool) :
    (constant b).op.eval ((constant b).inputs.map fun i => w.getD i false) = b := by
  cases b <;> rfl

lemma append_wires (pre post : List Gate) (out : ℕ) (x : List Bool) :
    (⟨pre ++ post, out⟩ : Circuit).wires x =
      (⟨post, out⟩ : Circuit).wires ((⟨pre, 0⟩ : Circuit).wires x) := by
  simp only [Circuit.wires, List.foldl_append]

lemma negated_split (pre post : List Gate) (ins : List ℕ) (out : ℕ) (x : List Bool) :
    (⟨pre ++ ⟨GateOp.not, ins⟩ :: post, out⟩ : Circuit).eval x =
      (⟨post, out⟩ : Circuit).eval
        (((⟨pre, 0⟩ : Circuit).wires x) ++ [!(lastInput pre ins x)]) := by
  unfold Circuit.eval
  rw [append_wires]
  rfl

lemma constant_split (pre post : List Gate) (b : Bool) (out : ℕ) (x : List Bool) :
    (⟨pre ++ constant b :: post, out⟩ : Circuit).eval x =
      (⟨post, out⟩ : Circuit).eval (((⟨pre, 0⟩ : Circuit).wires x) ++ [b]) := by
  unfold Circuit.eval
  rw [append_wires]
  change ((⟨post, out⟩ : Circuit).wires
    (((⟨pre, 0⟩ : Circuit).wires x) ++
      [(constant b).op.eval ((constant b).inputs.map fun i =>
        ((⟨pre, 0⟩ : Circuit).wires x).getD i false)])).getD out false = _
  rw [constant_eval]

lemma replace_true {α : Type*} (input : α → List Bool)
    (pre post : List Gate) (ins : List ℕ) (out : ℕ)
    (hpost : ∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or)
    (F : α → Bool)
    (correct : ∀ x, (⟨pre ++ ⟨GateOp.not, ins⟩ :: post, out⟩ : Circuit).eval (input x) = F x)
    (sound : ∀ x, lastInput pre ins (input x) = true → F x = true) :
    ∀ x, (⟨pre ++ constant true :: post, out⟩ : Circuit).eval (input x) = F x := by
  intro x
  rw [constant_split]
  exact negated_context_replace_true F (fun x => lastInput pre ins (input x))
    (fun x b => (⟨post, out⟩ : Circuit).eval (((⟨pre, 0⟩ : Circuit).wires (input x)) ++ [b]))
    (fun x p q hpq => context_monotone post hpost _ out p q hpq)
    (fun x => (negated_split pre post ins out (input x)).symm.trans (correct x)) sound x

lemma replace_false {α : Type*} (input : α → List Bool)
    (pre post : List Gate) (ins : List ℕ) (out : ℕ)
    (hpost : ∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or)
    (F : α → Bool)
    (correct : ∀ x, (⟨pre ++ ⟨GateOp.not, ins⟩ :: post, out⟩ : Circuit).eval (input x) = F x)
    (covers : ∀ x, F x = true → lastInput pre ins (input x) = true) :
    ∀ x, (⟨pre ++ constant false :: post, out⟩ : Circuit).eval (input x) = F x := by
  intro x
  rw [constant_split]
  exact negated_context_replace_false F (fun x => lastInput pre ins (input x))
    (fun x b => (⟨post, out⟩ : Circuit).eval (((⟨pre, 0⟩ : Circuit).wires (input x)) ++ [b]))
    (fun x p q hpq => context_monotone post hpost _ out p q hpq)
    (fun x => (negated_split pre post ins out (input x)).symm.trans (correct x)) covers x

lemma replace_fanInTwo (pre post : List Gate) (ins : List ℕ) (out : ℕ) (b : Bool)
    (hfan : FanInTwo (⟨pre ++ ⟨GateOp.not, ins⟩ :: post, out⟩ : Circuit)) :
    FanInTwo (⟨pre ++ constant b :: post, out⟩ : Circuit) := by
  intro g hg
  simp only [List.mem_append, List.mem_cons] at hg
  rcases hg with hg | rfl | hg
  · exact hfan g (by simp [hg])
  · cases b <;> simp [constant]
  · exact hfan g (by simp [hg])

lemma replace_size (pre post : List Gate) (ins : List ℕ) (out : ℕ) (b : Bool) :
    (⟨pre ++ constant b :: post, out⟩ : Circuit).size =
      (⟨pre ++ ⟨GateOp.not, ins⟩ :: post, out⟩ : Circuit).size := by
  simp [Circuit.size]

lemma replace_notCount (pre post : List Gate) (ins : List ℕ) (out : ℕ) (b : Bool) :
    PEqualNP.NotBracket.notCount (⟨pre ++ constant b :: post, out⟩ : Circuit) + 1 =
      PEqualNP.NotBracket.notCount (⟨pre ++ ⟨GateOp.not, ins⟩ :: post, out⟩ : Circuit) := by
  cases b <;> simp [PEqualNP.NotBracket.notCount, constant, List.filter_append] <;> omega

lemma negated_context_true_change {α : Type*} (F h : α → Bool)
    (P : α → Bool → Bool)
    (hP : ∀ x p q, (p = true → q = true) → P x p = true → P x q = true)
    (correct : ∀ x, P x (!(h x)) = F x)
    (x : α) (different : P x true ≠ F x) : F x = false ∧ h x = true := by
  have hh : h x = true := by
    cases he : h x with
    | false => exact False.elim (different (by simpa [he] using correct x))
    | true => rfl
  refine ⟨?_, hh⟩
  cases hf : F x with
  | false => rfl
  | true => exact False.elim (different (by
      rw [hf]
      exact hP x (!(h x)) true (by simp) (by rw [correct, hf])))

lemma negated_context_false_change {α : Type*} (F h : α → Bool)
    (P : α → Bool → Bool)
    (hP : ∀ x p q, (p = true → q = true) → P x p = true → P x q = true)
    (correct : ∀ x, P x (!(h x)) = F x)
    (x : α) (different : P x false ≠ F x) : F x = true ∧ h x = false := by
  have hh : h x = false := by
    cases he : h x with
    | false => rfl
    | true => exact False.elim (different (by simpa [he] using correct x))
  refine ⟨?_, hh⟩
  cases hf : F x with
  | true => rfl
  | false =>
    have hp : P x false = true := by
      cases he : P x false <;> simp_all
    have contra := hP x false (!(h x)) (by simp) hp
    rw [correct, hf] at contra
    contradiction


lemma inputs_above {n : ℕ} (x y : Fin n → Bool)
    (hxy : ∀ i, x i = true → y i = true) : Above (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp, ?_⟩
  intro i hi
  by_cases hin : i < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hin), List.getElem_ofFn] at hi ⊢
    exact hxy _ hi
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
    contradiction

lemma lastInput_monotone {n : ℕ} (pre : List Gate) (ins : List ℕ)
    (hpre : ∀ g ∈ pre, g.op = GateOp.and ∨ g.op = GateOp.or) :
    Monotone (fun x : Fin n → Bool => lastInput pre ins (List.ofFn x)) := by
  intro x y hxy
  have hab := above_wires pre hpre (List.ofFn x) (List.ofFn y) (inputs_above x y (by
    intro i hi
    cases hy : y i with
    | false =>
      have h := hxy i
      rw [hi, hy] at h
      exact False.elim ((by decide : ¬ (true : Bool) ≤ false) h)
    | true => rfl))
  cases ins with
  | nil => simp [lastInput]
  | cons i rest =>
    simp only [lastInput, List.map_cons, List.headD_cons]
    have h := hab.2 i
    cases hx : ((⟨pre, 0⟩ : Circuit).wires (List.ofFn x)).getD i false <;>
      cases hy : ((⟨pre, 0⟩ : Circuit).wires (List.ofFn y)).getD i false <;> simp_all

lemma exists_minimum_notCount {α : Type*} (input : α → List Bool) (F : α → Bool)
    (bound : ℕ) (C : Circuit) (hfan : FanInTwo C) (hsize : C.size ≤ bound)
    (correct : ∀ x, C.eval (input x) = F x) :
    ∃ D : Circuit, FanInTwo D ∧ D.size ≤ bound ∧ (∀ x, D.eval (input x) = F x) ∧
      ∀ E : Circuit, FanInTwo E → E.size ≤ bound → (∀ x, E.eval (input x) = F x) →
        PEqualNP.NotBracket.notCount D ≤ PEqualNP.NotBracket.notCount E := by
  classical
  let good (k : ℕ) : Prop := ∃ E : Circuit, FanInTwo E ∧ E.size ≤ bound ∧
    (∀ x, E.eval (input x) = F x) ∧ PEqualNP.NotBracket.notCount E = k
  have existsGood : ∃ k, good k := ⟨PEqualNP.NotBracket.notCount C, C, hfan, hsize, correct, rfl⟩
  obtain ⟨D, fan, size, computes, count⟩ := Nat.find_spec existsGood
  refine ⟨D, fan, size, computes, ?_⟩
  intro E eFan eSize eCorrect
  rw [count]
  exact Nat.find_min' existsGood ⟨E, eFan, eSize, eCorrect, rfl⟩

lemma minimum_not_replacement_changes {α : Type*} (input : α → List Bool) (F : α → Bool)
    (bound : ℕ) (pre post : List Gate) (ins : List ℕ) (out : ℕ)
    (fan : FanInTwo (⟨pre ++ ⟨GateOp.not, ins⟩ :: post, out⟩ : Circuit))
    (size : (⟨pre ++ ⟨GateOp.not, ins⟩ :: post, out⟩ : Circuit).size ≤ bound)
    (minimal : ∀ E : Circuit, FanInTwo E → E.size ≤ bound → (∀ x, E.eval (input x) = F x) →
      PEqualNP.NotBracket.notCount (⟨pre ++ ⟨GateOp.not, ins⟩ :: post, out⟩ : Circuit) ≤
        PEqualNP.NotBracket.notCount E) (b : Bool) :
    ∃ x, (⟨pre ++ constant b :: post, out⟩ : Circuit).eval (input x) ≠ F x := by
  classical
  by_contra h
  push Not at h
  have hc := minimal (⟨pre ++ constant b :: post, out⟩ : Circuit)
    (replace_fanInTwo pre post ins out b fan) (by rw [replace_size]; exact size) h
  have hd := replace_notCount pre post ins out b
  omega

lemma minimum_not_lastInput_incomparable {α : Type*}
    (input : α → List Bool) (F : α → Bool)
    (bound : ℕ) (pre post : List Gate) (ins : List ℕ) (out : ℕ)
    (fan : FanInTwo (⟨pre ++ ⟨GateOp.not, ins⟩ :: post, out⟩ : Circuit))
    (size : (⟨pre ++ ⟨GateOp.not, ins⟩ :: post, out⟩ : Circuit).size ≤ bound)
    (hpost : ∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or)
    (correct : ∀ x, (⟨pre ++ ⟨GateOp.not, ins⟩ :: post, out⟩ : Circuit).eval (input x) = F x)
    (minimal : ∀ E : Circuit, FanInTwo E → E.size ≤ bound → (∀ x, E.eval (input x) = F x) →
      PEqualNP.NotBracket.notCount (⟨pre ++ ⟨GateOp.not, ins⟩ :: post, out⟩ : Circuit) ≤
        PEqualNP.NotBracket.notCount E) :
    (∃ x, F x = false ∧ lastInput pre ins (input x) = true) ∧
      ∃ x, F x = true ∧ lastInput pre ins (input x) = false := by
  let P (x : α) (b : Bool) :=
    (⟨post, out⟩ : Circuit).eval (((⟨pre, 0⟩ : Circuit).wires (input x)) ++ [b])
  have mono : ∀ x p q, (p = true → q = true) → P x p = true → P x q = true :=
    fun x p q hpq => context_monotone post hpost _ out p q hpq
  have computes : ∀ x, P x (!(lastInput pre ins (input x))) = F x :=
    fun x => (negated_split pre post ins out (input x)).symm.trans (correct x)
  obtain ⟨x, hx⟩ := minimum_not_replacement_changes input F bound pre post ins out fan size minimal true
  obtain ⟨y, hy⟩ := minimum_not_replacement_changes input F bound pre post ins out fan size minimal false
  rw [constant_split] at hx hy
  exact ⟨⟨x, negated_context_true_change F _ P mono computes x hx⟩,
    y, negated_context_false_change F _ P mono computes y hy⟩

lemma split_last_not (gs : List Gate)
    (basis : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) :
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) ∨
      ∃ (pre post : List Gate) (ins : List ℕ), gs = pre ++ ⟨GateOp.not, ins⟩ :: post ∧
        ∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or := by
  induction gs with
  | nil => left; simp
  | cons g gs ih =>
    rcases ih (fun g hg => basis g (by simp [hg])) with mono | ⟨pre, post, ins, eq, mono⟩
    · rcases basis g (by simp) with hop | hop | hop
      · left; intro h hh; rcases List.mem_cons.mp hh with rfl | hh
        · exact Or.inl hop
        · exact mono h hh
      · left; intro h hh; rcases List.mem_cons.mp hh with rfl | hh
        · exact Or.inr hop
        · exact mono h hh
      · right
        refine ⟨[], gs, g.inputs, ?_, mono⟩
        cases g with
        | mk op inputs => simp only at hop; subst op; rfl
    · right
      exact ⟨g :: pre, post, ins, by simp [eq], mono⟩

lemma zero_not_mono (gs : List Gate)
    (basis : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (count : PEqualNP.NotBracket.notCount (⟨gs, 0⟩ : Circuit) = 0) :
    ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or := by
  classical
  intro g hg
  rcases basis g hg with hop | hop | hop
  · exact Or.inl hop
  · exact Or.inr hop
  · have nil : gs.filter (fun h => decide (h.op = GateOp.not)) = [] :=
      List.length_eq_zero_iff.mp (by simpa [PEqualNP.NotBracket.notCount] using count)
    have mem : g ∈ gs.filter (fun h => decide (h.op = GateOp.not)) := by simp [hg, hop]
    rw [nil] at mem
    contradiction

lemma one_not_split (gs : List Gate)
    (basis : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (count : PEqualNP.NotBracket.notCount (⟨gs, 0⟩ : Circuit) ≤ 1) :
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) ∨
      ∃ (pre post : List Gate) (ins : List ℕ), gs = pre ++ ⟨GateOp.not, ins⟩ :: post ∧
        (∀ g ∈ pre, g.op = GateOp.and ∨ g.op = GateOp.or) ∧
        (∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or) := by
  rcases split_last_not gs basis with mono | ⟨pre, post, ins, eq, mono⟩
  · exact Or.inl mono
  · right
    refine ⟨pre, post, ins, eq, ?_, mono⟩
    apply zero_not_mono pre
    · intro g hg
      exact basis g (by rw [eq]; simp [hg])
    · rw [eq] at count
      simp only [PEqualNP.NotBracket.notCount, List.filter_append, List.filter_cons,
        List.length_append, decide_true, ↓reduceIte, List.length_cons] at count
      unfold PEqualNP.NotBracket.notCount
      dsimp only
      omega

end LastNot

namespace Boundary

def pos : List ℕ := [3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320, 528, 576, 640]
def neg : List ℕ := [50, 69, 104, 116, 138, 201, 208, 276, 385, 402, 521, 548, 554, 770, 773]
def bits (r : ℕ) (i : Fin 10) := r.testBit i.val
def edge (x : Fin 10 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
def below (a b : Fin 10 → Bool) : Bool := (List.finRange 10).all fun i => !(a i) || b i
lemma below_elim {a b} (h : below a b = true) {i : Fin 10} (hi : a i = true) : b i = true := by
  have hh := List.all_eq_true.mp h i (by simp)
  simpa [hi] using hh
set_option maxRecDepth 20000 in
lemma endpoints : ∀ r : Fin 1024,
    (if edge (bits r) then pos.any (fun q => below (bits q) (bits r))
     else neg.any (fun q => below (bits r) (bits q))) = true := by decide +kernel

lemma encode (x : Fin 10 → Bool) : ∃ r : Fin 1024, bits r = x := by
  let w := BitVec.ofBoolListLE (List.ofFn x)
  have hw : w.toNat < 1024 := by simpa [w] using w.isLt
  refine ⟨⟨w.toNat, hw⟩, ?_⟩
  funext i
  change w.getLsbD i.val = x i
  rw [BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

lemma pos_value : ∀ q ∈ pos, edge (bits q) = true := by decide +kernel
lemma neg_value : ∀ q ∈ neg, edge (bits q) = false := by decide +kernel

lemma positive_endpoint (x : Fin 10 → Bool) (hx : edge x = true) :
    ∃ q ∈ pos, ∀ i, bits q i = true → x i = true := by
  obtain ⟨r, rfl⟩ := encode x
  have h := endpoints r
  rw [hx] at h
  obtain ⟨q, hq, hle⟩ := List.any_eq_true.mp h
  exact ⟨q, hq, fun _ hi => below_elim hle hi⟩

lemma negative_endpoint (x : Fin 10 → Bool) (hx : edge x = false) :
    ∃ q ∈ neg, ∀ i, x i = true → bits q i = true := by
  obtain ⟨r, rfl⟩ := encode x
  have h := endpoints r
  rw [hx] at h
  obtain ⟨q, hq, hle⟩ := List.any_eq_true.mp h
  exact ⟨q, hq, fun _ hi => below_elim hle hi⟩

def Increasing (h : (Fin 10 → Bool) → Bool) : Prop :=
  ∀ x y, (∀ i, x i = true → y i = true) → h x = true → h y = true

lemma above_edge_iff (h : (Fin 10 → Bool) → Bool) (hm : Increasing h) :
    (∀ x, edge x = true → h x = true) ↔ ∀ q ∈ pos, h (bits q) = true := by
  constructor
  · intro hh q hq
    exact hh _ (pos_value q hq)
  · intro hh x hx
    obtain ⟨q, hq, hle⟩ := positive_endpoint x hx
    exact hm _ _ hle (hh q hq)

lemma below_edge_iff (h : (Fin 10 → Bool) → Bool) (hm : Increasing h) :
    (∀ x, h x = true → edge x = true) ↔ ∀ q ∈ neg, h (bits q) = false := by
  constructor
  · intro hh q hq
    cases hv : h (bits q) with
    | false => rfl
    | true => have := hh _ hv; simp [neg_value q hq] at this
  · intro hh x hx
    cases he : edge x with
    | true => rfl
    | false =>
      obtain ⟨q, hq, hle⟩ := negative_endpoint x he
      have := hm _ _ hle hx
      simp [hh q hq] at this

lemma upper_failure (h : (Fin 10 → Bool) → Bool) (hm : Increasing h)
    (hf : ¬ ∀ x, edge x = true → h x = true) :
    ∃ q ∈ pos, h (bits q) = false := by
  have hn : ¬ ∀ q ∈ pos, h (bits q) = true :=
    fun hh => hf ((above_edge_iff h hm).mpr hh)
  push Not at hn
  obtain ⟨q, hq, hv⟩ := hn
  exact ⟨q, hq, Bool.eq_false_iff.mpr hv⟩

lemma lower_failure (h : (Fin 10 → Bool) → Bool) (hm : Increasing h)
    (hf : ¬ ∀ x, h x = true → edge x = true) :
    ∃ q ∈ neg, h (bits q) = true := by
  have hn : ¬ ∀ q ∈ neg, h (bits q) = false :=
    fun hh => hf ((below_edge_iff h hm).mpr hh)
  push Not at hn
  obtain ⟨q, hq, hv⟩ := hn
  exact ⟨q, hq, Bool.eq_true_of_ne_false hv⟩

lemma constant_true_of_below (P : (Fin 10 → Bool) → Bool → Bool)
    (h : (Fin 10 → Bool) → Bool)
    (hp : ∀ x, P x false = true → P x true = true)
    (he : ∀ x, P x (!(h x)) = edge x)
    (hh : ∀ x, h x = true → edge x = true) :
    ∀ x, P x true = edge x := by
  intro x
  cases hx : h x with
  | false => simpa [hx] using he x
  | true =>
    have hf := hh x hx
    have hv : P x false = true := by simpa [hx, hf] using he x
    exact (hp x hv).trans hf.symm

lemma constant_false_of_above (P : (Fin 10 → Bool) → Bool → Bool)
    (h : (Fin 10 → Bool) → Bool)
    (hp : ∀ x, P x false = true → P x true = true)
    (he : ∀ x, P x (!(h x)) = edge x)
    (hh : ∀ x, edge x = true → h x = true) :
    ∀ x, P x false = edge x := by
  intro x
  cases hx : h x with
  | true => simpa [hx] using he x
  | false =>
    have hf : edge x = false := by
      cases hf : edge x with
      | false => rfl
      | true => have := hh x hf; simp [hx] at this
    have hv : P x true = false := by simpa [hx, hf] using he x
    cases hv0 : P x false with
    | false => exact hf.symm
    | true => have := hp x hv0; simp [hv] at this

lemma essential_not_boundary (P : (Fin 10 → Bool) → Bool → Bool)
    (h : (Fin 10 → Bool) → Bool) (hm : Increasing h)
    (hp : ∀ x, P x false = true → P x true = true)
    (he : ∀ x, P x (!(h x)) = edge x)
    (hf : ¬ ∀ x, P x false = edge x)
    (ht : ¬ ∀ x, P x true = edge x) :
    (∃ q ∈ pos, h (bits q) = false) ∧ (∃ q ∈ neg, h (bits q) = true) := by
  constructor
  · apply upper_failure h hm
    intro hh
    exact hf (constant_false_of_above P h hp he hh)
  · apply lower_failure h hm
    intro hh
    exact ht (constant_true_of_below P h hp he hh)

lemma edge_increasing : Increasing edge := by
  intro x y hxy hx
  simp only [edge, Bool.or_eq_true, Bool.and_eq_true] at hx ⊢
  aesop

def rawAnd (S : Finset (Fin 10)) (x : Fin 10 → Bool) : Bool :=
  decide (∀ i ∈ S, x i = true)

def rawOr (S : Finset (Fin 10)) (x : Fin 10 → Bool) : Bool :=
  decide (∃ i ∈ S, x i = true)

def mark (S : Finset (Fin 10)) (i : Fin 10) : Bool := decide (i ∈ S)

def support (q : ℕ) : Finset (Fin 10) := Finset.univ.filter (fun i => bits q i = true)

lemma rawAnd_increasing (S : Finset (Fin 10)) : Increasing (rawAnd S) := by
  intro x y hxy hx
  simp only [rawAnd, decide_eq_true_eq] at hx ⊢
  exact fun i hi => hxy i (hx i hi)

lemma rawOr_increasing (S : Finset (Fin 10)) : Increasing (rawOr S) := by
  intro x y hxy hx
  simp only [rawOr, decide_eq_true_eq] at hx ⊢
  obtain ⟨i, hi, hx⟩ := hx
  exact ⟨i, hi, hxy i hx⟩

lemma rawAnd_below_iff (S : Finset (Fin 10)) :
    (∀ x, rawAnd S x = true → edge x = true) ↔ edge (mark S) = true := by
  constructor
  · intro h
    exact h _ (by simp [rawAnd, mark])
  · intro h x hx
    apply edge_increasing (mark S) x _ h
    intro i hi
    simp only [mark, decide_eq_true_eq] at hi
    exact (of_decide_eq_true hx) i hi

lemma negative_support_card : ∀ q ∈ neg, (support q).card ≤ 4 := by decide +kernel

lemma rawAnd_negative_boundary (S : Finset (Fin 10))
    (h : ∃ q ∈ neg, rawAnd S (bits q) = true) :
    edge (mark S) = false ∧ S.card ≤ 4 := by
  obtain ⟨q, hq, hv⟩ := h
  have hs : S ⊆ support q := by
    intro i hi
    simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (of_decide_eq_true hv) i hi
  refine ⟨?_, (Finset.card_le_card hs).trans (negative_support_card q hq)⟩
  cases he : edge (mark S) with
  | false => rfl
  | true =>
    have := (rawAnd_below_iff S).mpr he (bits q) hv
    simp [neg_value q hq] at this

lemma rawOr_positive_boundary (S : Finset (Fin 10))
    (h : ∃ q ∈ pos, rawOr S (bits q) = false) :
    ∃ q ∈ pos, ∀ i ∈ S, bits q i = false := by
  obtain ⟨q, hq, hv⟩ := h
  refine ⟨q, hq, ?_⟩
  intro i hi
  cases he : bits q i with
  | false => rfl
  | true =>
    have ht : rawOr S (bits q) = true := by
      simp only [rawOr, decide_eq_true_eq]
      exact ⟨i, hi, he⟩
    rw [hv] at ht
    contradiction

end Boundary


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma increasing_lastInput (pre : List Gate) (ins : List ℕ)
    (hpre : ∀ g ∈ pre, g.op = GateOp.and ∨ g.op = GateOp.or) :
    Boundary.Increasing (fun x => LastNot.lastInput pre ins (List.ofFn x)) := by
  intro x y hxy hx
  have hab := LastNot.above_wires pre hpre _ _ (LastNot.inputs_above x y hxy)
  cases ins with
  | nil => simp [LastNot.lastInput] at hx
  | cons i rest =>
    simp only [LastNot.lastInput, List.map_cons, List.headD_cons] at hx ⊢
    exact hab.2 i hx

lemma minimum_one_not_boundary (bound : ℕ) (pre post : List Gate)
    (ins : List ℕ) (out : ℕ)
    (fan : FanInTwo (⟨pre ++ ⟨GateOp.not, ins⟩ :: post, out⟩ : Circuit))
    (size : (⟨pre ++ ⟨GateOp.not, ins⟩ :: post, out⟩ : Circuit).size ≤ bound)
    (hpre : ∀ g ∈ pre, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hpost : ∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or)
    (correct : ∀ x : Fin 10 → Bool,
      (⟨pre ++ ⟨GateOp.not, ins⟩ :: post, out⟩ : Circuit).eval (List.ofFn x) = Boundary.edge x)
    (minimal : ∀ E : Circuit, FanInTwo E → E.size ≤ bound →
      (∀ x : Fin 10 → Bool, E.eval (List.ofFn x) = Boundary.edge x) →
      PEqualNP.NotBracket.notCount (⟨pre ++ ⟨GateOp.not, ins⟩ :: post, out⟩ : Circuit) ≤
        PEqualNP.NotBracket.notCount E) :
    (∃ q ∈ Boundary.pos, LastNot.lastInput pre ins (List.ofFn (Boundary.bits q)) = false) ∧
      ∃ q ∈ Boundary.neg, LastNot.lastInput pre ins (List.ofFn (Boundary.bits q)) = true := by
  obtain ⟨⟨x, hfx, hx⟩, ⟨y, hfy, hy⟩⟩ :=
    LastNot.minimum_not_lastInput_incomparable List.ofFn Boundary.edge bound pre post ins out
      fan size hpost correct minimal
  have hm := increasing_lastInput pre ins hpre
  constructor
  · apply Boundary.upper_failure _ hm
    intro hh
    have := hh y hfy
    rw [hy] at this
    contradiction
  · apply Boundary.lower_failure _ hm
    intro hh
    have := hh x hx
    rw [hfx] at this
    contradiction


end PEqualNP.Outside.L_meta_2373_aux
