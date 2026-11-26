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

def maskPair (a b c : Fin 10) (t u : Bool) (i : Fin 10) : Bool :=
  if i = a then u else if i = b then t else decide (i = c)

set_option maxRecDepth 10000 in
lemma conditional_essential_samples : ∀ a b : Fin 10, a ≠ b → ∀ t : Bool,
    ∃ c : Fin 10, c ≠ a ∧ c ≠ b ∧
      edge (maskPair a b c t false) = false ∧ edge (maskPair a b c t true) = true := by
  decide +kernel

lemma essential_with_other_fixed (a b : Fin 10) (hab : a ≠ b) (t : Bool) :
    ∃ x : Fin 10 → Bool, x a = false ∧ x b = t ∧ edge x = false ∧
      edge (Function.update x a true) = true := by
  obtain ⟨c, hca, hcb, hfalse, htrue⟩ := conditional_essential_samples a b hab t
  refine ⟨maskPair a b c t false, ?_, ?_, hfalse, ?_⟩
  · simp [maskPair]
  · simp [maskPair, hab.symm]
  · have he : Function.update (maskPair a b c t false) a true = maskPair a b c t true := by
      funext i
      by_cases hi : i = a <;> simp [Function.update, maskPair, hi]
    rw [he]
    exact htrue

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


namespace NandRestriction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

lemma getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2





lemma getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp





def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

abbrev Stat := Bool ⊕ Nat

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

lemma simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg; subst hg; simp [Ok]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg; subst hg; simp [Ok]
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg; subst hg; simp [Ok]
  · simp at hg
  · simp at hg

lemma simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

lemma simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · rcases a with ⟨_ | _⟩ | _ <;> rcases b with ⟨_ | _⟩ | _ <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · rcases a with ⟨_ | _⟩ | _ <;> rcases b with ⟨_ | _⟩ | _ <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

lemma getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

lemma toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

lemma elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

lemma elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

lemma Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

lemma Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false

lemma inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2


def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

lemma normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

lemma normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

lemma wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]


def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Stat)) ++ [Sum.inl b]

lemma inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Stat))).length = n := by simp
  have l2 : (List.ofFn y).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [initStats]
    rw [getD_snoc_len _ _ _ _ l1, getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [initStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, Stat.Valid, Stat.val, wiresFrom]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩

lemma ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp


def readerCount (k : ℕ) : List Gate → ℕ
  | [] => 0
  | g :: gs => (if k ∈ g.inputs then 1 else 0) + readerCount k gs

lemma elim_len_readers (n k : ℕ) (gs : List Gate) :
    ∀ acc : List Stat × List Gate,
      (∀ g ∈ gs, NOk g) → k < acc.1.length →
      (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
      (elim n gs acc).2.length + readerCount k gs ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _; simp [elim, readerCount]
  | cons g gs ih =>
    intro acc hok hk hc
    have ht := ih (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (by simp [elimStep]; omega)
      (by
        obtain ⟨c, hc⟩ := hc
        refine ⟨c, ?_⟩
        simp only [elimStep]
        rw [getD_snoc_ne _ _ _ _ (by omega)]
        exact hc)
    have he : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [he, List.length_cons]
    by_cases hr : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hr, hc⟩⟩
      have hs : (elimStep n acc g).2.length = acc.2.length := by
        simp only [elimStep, hnone]
        simp
      simp only [readerCount, ite_eq_left hr]
      omega
    · have hs : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      simp only [readerCount, ite_eq_right hr]
      omega

lemma fix_last_counted (n : ℕ) (b : Bool) (C : Circuit)
    (hC : FanInTwo C)
    (hnc : ∃ y y' : Fin n → Bool,
      C.eval (List.ofFn (Fin.snoc y b)) ≠ C.eval (List.ofFn (Fin.snoc y' b))) :
    ∃ E : Circuit, FanInTwo E ∧
      E.size + readerCount n (C.gates.map normGate) ≤ C.size ∧
      ∀ y : Fin n → Bool, E.eval (List.ofFn y) = C.eval (List.ofFn (Fin.snoc y b)) := by
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (hC g0 hg0)
  set acc := elim n gs (initStats n b, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y)
        (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool))) acc := by
    intro y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn y)) =
        C.eval (List.ofFn (Fin.snoc y b)) := by
    intro y
    rw [((hinv y).2 C.output).2, hgs, wiresFrom_norm]
    rfl
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]
    rfl
  | inr j =>
    have hlen := elim_len_readers n n gs (initStats n b, []) hnok
      (by simp [initStats]) ⟨b, getD_snoc_len _ _ _ _ (by simp)⟩
    rw [← hacc] at hlen
    have hok : ∀ g ∈ acc.2, Ok g := by
      rw [hacc]
      exact elim_ok n gs _ (by simp)
    refine ⟨⟨acc.2, j⟩, hok, ?_, ?_⟩
    · simpa [hgs, Circuit.size] using hlen
    · intro y
      have hv := hval y
      rw [hst] at hv
      exact hv

lemma readers_le_of_cofactor_lower (n q s : ℕ) (b : Bool) (C : Circuit)
    (hC : FanInTwo C) (hsize : C.size ≤ s)
    (hnc : ∃ y y' : Fin n → Bool,
      C.eval (List.ofFn (Fin.snoc y b)) ≠ C.eval (List.ofFn (Fin.snoc y' b)))
    (hlower : ∀ E : Circuit, FanInTwo E →
      (∀ y : Fin n → Bool, E.eval (List.ofFn y) = C.eval (List.ofFn (Fin.snoc y b))) →
      q ≤ E.size) :
    q + readerCount n (C.gates.map normGate) ≤ s := by
  obtain ⟨E, hE, hbound, hev⟩ := fix_last_counted n b C hC hnc
  have := hlower E hE hev
  omega

def setReaderCount (K : Finset ℕ) : List Gate → ℕ
  | [] => 0
  | g :: gs => (if ∃ k ∈ g.inputs, k ∈ K then 1 else 0) + setReaderCount K gs

lemma elim_len_setReaders (n : ℕ) (K : Finset ℕ) (gs : List Gate) :
    ∀ acc : List Stat × List Gate,
      (∀ g ∈ gs, NOk g) →
      (∀ k ∈ K, k < acc.1.length ∧ ∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
      (elim n gs acc).2.length + setReaderCount K gs ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _; simp [elim, setReaderCount]
  | cons g gs ih =>
    intro acc hok hK
    have ht := ih (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (by
        intro k hk
        obtain ⟨hlt, c, hc⟩ := hK k hk
        refine ⟨by simp [elimStep]; omega, c, ?_⟩
        simp only [elimStep]
        rw [getD_snoc_ne _ _ _ _ (by omega)]
        exact hc)
    have he : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [he, List.length_cons]
    by_cases hr : ∃ k ∈ g.inputs, k ∈ K
    · obtain ⟨k, hkg, hk⟩ := hr
      obtain ⟨_, c, hc⟩ := hK k hk
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have hs : (elimStep n acc g).2.length = acc.2.length := by
        simp only [elimStep, hnone]
        simp
      have hr : ∃ k ∈ g.inputs, k ∈ K := ⟨k, hkg, hk⟩
      simp only [setReaderCount, ite_eq_left hr]
      omega
    · have hs : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      simp only [setReaderCount, ite_eq_right hr]
      omega

lemma elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have he : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [he, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

lemma elim_status_length (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) :
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elim]
  | cons g gs ih =>
    change (elim n gs (elimStep n acc g)).1.length = _
    rw [ih]
    simp [elimStep, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

lemma simplify_and_false (m : ℕ) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hz : Sum.inl false ∈ ins) :
    simplify GateOp.and m ins = (none, Sum.inl false) := by
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;>
    (try cases a) <;> (try cases b) <;> simp_all [simplify, simpAnd]
  rcases hz with h | h <;> simp_all

lemma elim_and_reader_bound (n k : ℕ) (pre post : List Gate) (g : Gate)
    (acc : List Stat × List Gate)
    (hok : ∀ h ∈ pre ++ g :: post, NOk h)
    (hk : k < acc.1.length) (hz : acc.1.getD k (Sum.inl false) = Sum.inl false)
    (hg : g.op = GateOp.and) (hread : k ∈ g.inputs) :
    (elim n (pre ++ g :: post) acc).2.length + readerCount k pre + 1 +
        setReaderCount {k, acc.1.length + pre.length} post ≤
      acc.2.length + (pre ++ g :: post).length := by
  let mid := elim n pre acc
  have hm : mid.1.length = acc.1.length + pre.length := elim_status_length n pre acc
  have hmk : k < mid.1.length := by omega
  have hmz : mid.1.getD k (Sum.inl false) = Sum.inl false := by
    rw [elim_getD n k _ pre acc hk, hz]
  have hpre := elim_len_readers n k pre acc
    (fun h hh => hok h (List.mem_append_left _ hh)) hk ⟨false, hz⟩
  have hgood := hok g (List.mem_append_right _ List.mem_cons_self)
  have hs : simplify g.op (n + mid.2.length)
      (g.inputs.map fun i => mid.1.getD i (Sum.inl false)) = (none, Sum.inl false) := by
    rw [hg]
    apply simplify_and_false
    · simpa using hgood.1.2
    · exact List.mem_map.2 ⟨k, hread, hmz⟩
  have hstep : elimStep n mid g = (mid.1 ++ [Sum.inl false], mid.2) := by
    simp only [elimStep]
    rw [hs]
    simp
  have htail := elim_len_setReaders n {k, acc.1.length + pre.length} post
    (elimStep n mid g)
    (fun h hh => hok h (List.mem_append_right _ (List.mem_cons_of_mem _ hh)))
    (by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl
      · refine ⟨by rw [hstep]; simp; omega, false, ?_⟩
        rw [hstep, getD_snoc_ne _ _ _ _ (by omega)]
        exact hmz
      · refine ⟨by rw [hstep]; simp; omega, false, ?_⟩
        rw [hstep, ← hm, getD_snoc_eq])
  have he : elim n (pre ++ g :: post) acc = elim n post (elimStep n mid g) := by
    simp [elim, List.foldl_append, mid]
  rw [he, hstep]
  rw [hstep] at htail
  simp only [List.length_append, List.length_cons]
  change mid.2.length + readerCount k pre ≤ acc.2.length + pre.length at hpre
  dsimp only at htail
  omega

lemma readerCount_append (k : ℕ) (xs ys : List Gate) :
    readerCount k (xs ++ ys) = readerCount k xs + readerCount k ys := by
  induction xs with
  | nil => simp [readerCount]
  | cons g gs ih => simp [readerCount, ih, Nat.add_assoc]

lemma setReaderCount_pair_cons (k l : ℕ) (g : Gate) (gs : List Gate) :
    setReaderCount {k, l} (g :: gs) =
      (if k ∈ g.inputs ∨ l ∈ g.inputs then 1 else 0) + setReaderCount {k, l} gs := by
  have he : (∃ i ∈ g.inputs, i ∈ ({k, l} : Finset ℕ)) ↔ k ∈ g.inputs ∨ l ∈ g.inputs := by
    constructor
    · rintro ⟨i, hi, his⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at his
      rcases his with rfl | rfl
      · exact Or.inl hi
      · exact Or.inr hi
    · rintro (hk | hl)
      · exact ⟨k, hk, by simp⟩
      · exact ⟨l, hl, by simp⟩
  simp only [setReaderCount, he]

lemma setReaderCount_pair_ge (k l : ℕ) (gs : List Gate) :
    readerCount k gs ≤ setReaderCount {k, l} gs := by
  induction gs with
  | nil => simp [readerCount, setReaderCount]
  | cons g gs ih =>
    rw [setReaderCount_pair_cons]
    by_cases hk : k ∈ g.inputs <;> by_cases hl : l ∈ g.inputs <;>
      simp_all [readerCount] <;> omega

lemma setReaderCount_pair_extra (k l : ℕ) (gs : List Gate)
    (hx : ∃ g ∈ gs, l ∈ g.inputs ∧ k ∉ g.inputs) :
    readerCount k gs + 1 ≤ setReaderCount {k, l} gs := by
  induction gs with
  | nil => simpa using hx
  | cons g gs ih =>
    rw [setReaderCount_pair_cons]
    obtain ⟨h, hh, hl, hk⟩ := hx
    rcases List.mem_cons.mp hh with rfl | hh
    · have ht := setReaderCount_pair_ge k l gs
      simp only [readerCount, ite_eq_right hk, zero_add, hl, or_true, ite_true]
      omega
    · have ht := ih ⟨h, hh, hl, hk⟩
      by_cases hkg : k ∈ g.inputs <;> by_cases hlg : l ∈ g.inputs <;>
        simp_all [readerCount] <;> omega

lemma elim_and_extra_saving (n k : ℕ) (pre post : List Gate) (g : Gate)
    (acc : List Stat × List Gate)
    (hok : ∀ h ∈ pre ++ g :: post, NOk h)
    (hk : k < acc.1.length) (hz : acc.1.getD k (Sum.inl false) = Sum.inl false)
    (hg : g.op = GateOp.and) (hread : k ∈ g.inputs)
    (hconsumer : ∃ h ∈ post, acc.1.length + pre.length ∈ h.inputs ∧ k ∉ h.inputs) :
    (elim n (pre ++ g :: post) acc).2.length +
        readerCount k (pre ++ g :: post) + 1 ≤
      acc.2.length + (pre ++ g :: post).length := by
  have hb := elim_and_reader_bound n k pre post g acc hok hk hz hg hread
  have he := setReaderCount_pair_extra k (acc.1.length + pre.length) post hconsumer
  rw [readerCount_append]
  simp only [readerCount, ite_eq_left hread]
  omega

lemma fix_last_with_savings (n q : ℕ) (b : Bool) (C : Circuit)
    (hC : FanInTwo C)
    (hnc : ∃ y y' : Fin n → Bool,
      C.eval (List.ofFn (Fin.snoc y b)) ≠ C.eval (List.ofFn (Fin.snoc y' b)))
    (hbudget : (elim n (C.gates.map normGate) (initStats n b, [])).2.length + q ≤ C.size) :
    ∃ E : Circuit, FanInTwo E ∧ E.size + q ≤ C.size ∧
      ∀ y : Fin n → Bool, E.eval (List.ofFn y) = C.eval (List.ofFn (Fin.snoc y b)) := by
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (hC g0 hg0)
  set acc := elim n gs (initStats n b, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y)
        (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool))) acc := by
    intro y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn y)) =
        C.eval (List.ofFn (Fin.snoc y b)) := by
    intro y
    rw [((hinv y).2 C.output).2, hgs, wiresFrom_norm]
    rfl
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]
    rfl
  | inr j =>
    have hok : ∀ g ∈ acc.2, Ok g := by
      rw [hacc]
      exact elim_ok n gs _ (by simp)
    refine ⟨⟨acc.2, j⟩, hok, hbudget, ?_⟩
    intro y
    have hv := hval y
    rw [hst] at hv
    exact hv

lemma fix_false_and_extra (n : ℕ) (C : Circuit) (pre post : List Gate) (g : Gate)
    (hC : FanInTwo C)
    (hnc : ∃ y y' : Fin n → Bool,
      C.eval (List.ofFn (Fin.snoc y false)) ≠ C.eval (List.ofFn (Fin.snoc y' false)))
    (hgs : C.gates.map normGate = pre ++ g :: post)
    (hg : g.op = GateOp.and) (hread : n ∈ g.inputs)
    (hconsumer : ∃ h ∈ post, n + 1 + pre.length ∈ h.inputs ∧ n ∉ h.inputs) :
    ∃ E : Circuit, FanInTwo E ∧
      E.size + readerCount n (C.gates.map normGate) + 1 ≤ C.size ∧
      ∀ y : Fin n → Bool, E.eval (List.ofFn y) = C.eval (List.ofFn (Fin.snoc y false)) := by
  have hok : ∀ h ∈ pre ++ g :: post, NOk h := by
    intro h hh
    rw [← hgs] at hh
    obtain ⟨h0, hh0, rfl⟩ := List.mem_map.1 hh
    exact normGate_nok h0 (hC h0 hh0)
  have hb := elim_and_extra_saving n n pre post g (initStats n false, []) hok
    (by simp [initStats]) (getD_snoc_len _ _ _ _ (by simp)) hg hread
    (by simpa [initStats] using hconsumer)
  have hlen : (pre ++ g :: post).length = C.size := by
    rw [← hgs]
    simp [Circuit.size]
  have hbudget : (elim n (C.gates.map normGate) (initStats n false, [])).2.length +
      (readerCount n (C.gates.map normGate) + 1) ≤ C.size := by
    simpa only [hgs, hlen, List.length_nil, Nat.zero_add, Nat.add_assoc] using hb
  obtain ⟨E, hE, hsize, hev⟩ := fix_last_with_savings n
    (readerCount n (C.gates.map normGate) + 1) false C hC hnc hbudget
  exact ⟨E, hE, by omega, hev⟩

lemma and_readers_le_of_cofactor_lower (n q s : ℕ) (C : Circuit)
    (pre post : List Gate) (g : Gate)
    (hC : FanInTwo C) (hsize : C.size ≤ s)
    (hnc : ∃ y y' : Fin n → Bool,
      C.eval (List.ofFn (Fin.snoc y false)) ≠ C.eval (List.ofFn (Fin.snoc y' false)))
    (hlower : ∀ E : Circuit, FanInTwo E →
      (∀ y : Fin n → Bool, E.eval (List.ofFn y) = C.eval (List.ofFn (Fin.snoc y false))) →
      q ≤ E.size)
    (hgs : C.gates.map normGate = pre ++ g :: post)
    (hg : g.op = GateOp.and) (hread : n ∈ g.inputs)
    (hconsumer : ∃ h ∈ post, n + 1 + pre.length ∈ h.inputs ∧ n ∉ h.inputs) :
    q + readerCount n (C.gates.map normGate) + 1 ≤ s := by
  obtain ⟨E, hE, hbound, hev⟩ := fix_false_and_extra n C pre post g hC hnc
    hgs hg hread hconsumer
  have := hlower E hE hev
  omega

namespace Consumer

open PEqualNP.CircuitLowerBounds

lemma two_inputs_of_distinct (l : List ℕ) (v w : ℕ) (hvw : v ≠ w)
    (hl : l.length ≤ 2) (hv : v ∈ l) (hw : w ∈ l) :
    l = [v, w] ∨ l = [w, v] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · simp at hv
  · simp only [List.mem_singleton] at hv hw
    exact False.elim (hvw (hv.trans hw.symm))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv hw
    rcases hv with rfl | rfl <;> rcases hw with rfl | rfl
    · exact False.elim (hvw rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact False.elim (hvw rfl)
  · simp at hl

lemma and_value_implies_input {A : Type} (F : A → ℕ → Bool) (g : Gate) (v w : ℕ)
    (hop : g.op = GateOp.and) (hv : v ∈ g.inputs)
    (heval : ∀ a, F a w = g.op.eval (g.inputs.map (F a))) :
    ∀ a, F a w = true → F a v = true := by
  intro a ha
  rw [heval a, hop] at ha
  have hall : ∀ b ∈ g.inputs.map (F a), b = true := by
    simpa [GateOp.eval, List.all_eq_true] using ha
  exact hall _ (List.mem_map.2 ⟨v, hv, rfl⟩)

lemma consumer_absorbs {A : Type} (F : A → ℕ → Bool) (g : Gate) (v w out : ℕ)
    (hvw : v ≠ w) (hv : v ∈ g.inputs) (hw : w ∈ g.inputs)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hlen : g.inputs.length ≤ 2) (hnot : g.op = GateOp.not → g.inputs.length ≤ 1)
    (heval : ∀ a, F a out = g.op.eval (g.inputs.map (F a)))
    (himp : ∀ a, F a w = true → F a v = true) :
    (∀ a, F a out = F a w) ∨ (∀ a, F a out = F a v) := by
  have hins := two_inputs_of_distinct g.inputs v w hvw hlen hv hw
  rcases hop with hop | hop | hop
  · left
    intro a
    rw [heval a, hop]
    rcases hins with hins | hins <;> rw [hins] <;>
      cases hvv : F a v <;> cases hww : F a w <;>
      simp_all [GateOp.eval]
  · right
    intro a
    rw [heval a, hop]
    rcases hins with hins | hins <;> rw [hins] <;>
      cases hvv : F a v <;> cases hww : F a w <;>
      simp_all [GateOp.eval]
  · have := hnot hop
    rcases hins with hins | hins <;> simp_all

lemma consumer_avoids_raw_input {A : Type} (F : A → ℕ → Bool)
    (source consumer : Gate) (n v p q : ℕ) (hv : v < n) (hpq : p < q)
    (hsource : source.op = GateOp.and) (hsourcev : v ∈ source.inputs)
    (hread : n + p ∈ consumer.inputs)
    (hop : consumer.op = GateOp.and ∨ consumer.op = GateOp.or ∨ consumer.op = GateOp.not)
    (hlen : consumer.inputs.length ≤ 2)
    (hnot : consumer.op = GateOp.not → consumer.inputs.length ≤ 1)
    (hsourceval : ∀ a, F a (n + p) = source.op.eval (source.inputs.map (F a)))
    (hconsumerval : ∀ a, F a (n + q) = consumer.op.eval (consumer.inputs.map (F a)))
    (hnoalias : ∀ j, j < n + q → ¬ ∀ a, F a (n + q) = F a j) :
    v ∉ consumer.inputs := by
  intro hraw
  have himp := and_value_implies_input F source v (n + p) hsource hsourcev hsourceval
  rcases consumer_absorbs F consumer v (n + p) (n + q) (by omega) hraw hread
      hop hlen hnot hconsumerval himp with ha | ha
  · exact hnoalias (n + p) (by omega) ha
  · exact hnoalias v (by omega) ha

lemma live_consumer_avoids_raw_input {A : Type} (F : A → ℕ → Bool)
    (gs : List Gate) (n v p : ℕ) (source : Gate) (hv : v < n)
    (hsource : gs[p]? = some source) (hsourceop : source.op = GateOp.and)
    (hsourcev : v ∈ source.inputs)
    (hnormal : ∀ (q : ℕ) (g : Gate), gs[q]? = some g →
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2 ∧ (g.op = GateOp.not → g.inputs.length ≤ 1))
    (hvalues : ∀ (q : ℕ) (g : Gate), gs[q]? = some g →
      ∀ a, F a (n + q) = g.op.eval (g.inputs.map (F a)))
    (hnoalias : ∀ q, q < gs.length → ∀ j, j < n + q →
      ¬ ∀ a, F a (n + q) = F a j)
    (hlive : ∃ q, p < q ∧ ∃ g, gs[q]? = some g ∧ n + p ∈ g.inputs) :
    ∃ q g, p < q ∧ gs[q]? = some g ∧ n + p ∈ g.inputs ∧ v ∉ g.inputs := by
  obtain ⟨q, hpq, g, hq, hread⟩ := hlive
  have hqlt : q < gs.length := by
    by_contra h
    have hnone : gs[q]? = none := List.getElem?_eq_none_iff.2 (by omega)
    rw [hnone] at hq
    cases hq
  obtain ⟨hop, hlen, hnot⟩ := hnormal q g hq
  refine ⟨q, g, hpq, hq, hread, ?_⟩
  exact consumer_avoids_raw_input F source g n v p q hv hpq hsourceop hsourcev
    hread hop hlen hnot (hvalues p source hsource) (hvalues q g hq) (hnoalias q hqlt)

end Consumer

lemma elim_len_final_constants (n : ℕ) (K : Finset ℕ) (gs : List Gate) :
    ∀ acc : List Stat × List Gate,
      (∀ g ∈ gs, NOk g) →
      (∀ j g, gs[j]? = some g → ∀ k ∈ g.inputs, k < acc.1.length + j) →
      (∀ k ∈ K, ∃ b, (elim n gs acc).1.getD k (Sum.inl false) = Sum.inl b) →
      (elim n gs acc).2.length + setReaderCount K gs ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc hok back constants; simp [elim, setReaderCount]
  | cons g gs ih =>
    intro acc hok back constants
    have he : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    have ht := ih (elimStep n acc g)
      (fun h hh => hok h (List.mem_cons_of_mem _ hh))
      (by
        intro j h hj k hk
        have hb := back (j + 1) h (by simpa using hj) k hk
        dsimp only [elimStep]
        simp only [List.length_append, List.length_singleton]
        omega)
      (by simpa only [← he] using constants)
    by_cases hr : ∃ k ∈ g.inputs, k ∈ K
    · obtain ⟨k, hkg, hkK⟩ := hr
      have hk : k < acc.1.length := by simpa using back 0 g (by simp) k hkg
      obtain ⟨b, hb⟩ := constants k hkK
      have hb' : acc.1.getD k (Sum.inl false) = Sum.inl b := by
        rw [elim_getD n k _ (g :: gs) acc hk] at hb
        exact hb
      have hnok := hok g List.mem_cons_self
      have hn : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨b, List.mem_map.2 ⟨k, hkg, hb'⟩⟩
      have hs : (elimStep n acc g).2.length = acc.2.length := by
        simp only [elimStep]
        rw [hn]
        simp
      have hr : ∃ k ∈ g.inputs, k ∈ K := ⟨k, hkg, hkK⟩
      rw [he]
      simp only [setReaderCount, ite_eq_left hr, List.length_cons]
      omega
    · have hs : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      rw [he]
      simp only [setReaderCount, ite_eq_right hr, zero_add, List.length_cons]
      omega

lemma elim_output_status (n : ℕ) (pre post : List Gate) (g : Gate)
    (acc : List Stat × List Gate) :
    (elim n (pre ++ g :: post) acc).1.getD (acc.1.length + pre.length) (Sum.inl false) =
      (simplify g.op (n + (elim n pre acc).2.length)
        (g.inputs.map fun i => (elim n pre acc).1.getD i (Sum.inl false))).2 := by
  have hm := elim_status_length n pre acc
  have he : elim n (pre ++ g :: post) acc = elim n post (elimStep n (elim n pre acc) g) := by
    simp [elim, List.foldl_append]
  rw [he, elim_getD]
  · simp only [elimStep]
    rw [← hm, getD_snoc_eq]
  · simp [elimStep, hm]

lemma elim_before_status (n k : ℕ) (pre post : List Gate)
    (acc : List Stat × List Gate) (hk : k < acc.1.length + pre.length) :
    (elim n (pre ++ post) acc).1.getD k (Sum.inl false) =
      (elim n pre acc).1.getD k (Sum.inl false) := by
  have he : elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
    simp [elim, List.foldl_append]
  rw [he, elim_getD]
  rw [elim_status_length]
  exact hk

lemma elim_and_output_false (n k : ℕ) (pre post : List Gate) (g : Gate)
    (acc : List Stat × List Gate) (hop : g.op = GateOp.and)
    (hinputs : g.inputs.length ≤ 2) (hread : k ∈ g.inputs)
    (hback : k < acc.1.length + pre.length)
    (hconstant : (elim n (pre ++ g :: post) acc).1.getD k (Sum.inl false) = Sum.inl false) :
    (elim n (pre ++ g :: post) acc).1.getD (acc.1.length + pre.length) (Sum.inl false) = Sum.inl false := by
  have hm : (elim n pre acc).1.getD k (Sum.inl false) = Sum.inl false := by
    rw [elim_before_status n k pre (g :: post) acc hback] at hconstant
    exact hconstant
  rw [elim_output_status, hop]
  have he := simplify_and_false (n + (elim n pre acc).2.length)
    (g.inputs.map fun i => (elim n pre acc).1.getD i (Sum.inl false))
    (by simpa using hinputs) (List.mem_map.2 ⟨k, hread, hm⟩)
  rw [he]

lemma elim_not_output (n k : ℕ) (pre post : List Gate) (acc : List Stat × List Gate)
    (b : Bool) (hback : k < acc.1.length + pre.length)
    (hconstant : (elim n (pre ++ ⟨GateOp.not, [k]⟩ :: post) acc).1.getD k
      (Sum.inl false) = Sum.inl b) :
    (elim n (pre ++ ⟨GateOp.not, [k]⟩ :: post) acc).1.getD (acc.1.length + pre.length)
      (Sum.inl false) = Sum.inl (!b) := by
  have hm : (elim n pre acc).1.getD k (Sum.inl false) = Sum.inl b := by
    rw [elim_before_status n k pre (⟨GateOp.not, [k]⟩ :: post) acc hback] at hconstant
    exact hconstant
  rw [elim_output_status]
  simp only [List.map_cons, List.map_nil, hm]
  rfl

lemma setReaderCount_eq_countP (K : Finset ℕ) (gs : List Gate) :
    setReaderCount K gs = gs.countP (fun g => decide (∃ k ∈ g.inputs, k ∈ K)) := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp [setReaderCount, List.countP_cons, ih, Nat.add_comm]

lemma setReaderCount_eq_card (K : Finset ℕ) (gs : List Gate) :
    setReaderCount K gs =
      (Finset.univ.filter fun i : Fin gs.length => ∃ k ∈ (gs.get i).inputs, k ∈ K).card := by
  rw [setReaderCount_eq_countP]
  have h := List.countP_ofFn gs.get (fun g => decide (∃ k ∈ g.inputs, k ∈ K))
  simpa only [List.ofFn_get, decide_eq_true_eq] using h

lemma marked_readers_le (K : Finset ℕ) (gs : List Gate) (M : Finset (Fin gs.length))
    (hits : ∀ i ∈ M, ∃ k ∈ (gs.get i).inputs, k ∈ K) :
    M.card ≤ setReaderCount K gs := by
  rw [setReaderCount_eq_card]
  apply Finset.card_le_card
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hits i hi⟩

lemma four_readers_le (K : Finset ℕ) (gs : List Gate) (p q r s : Fin gs.length)
    (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s)
    (hits : ∀ i ∈ ({p, q, r, s} : Finset (Fin gs.length)),
      ∃ k ∈ (gs.get i).inputs, k ∈ K) : 4 ≤ setReaderCount K gs := by
  have h := marked_readers_le K gs {p, q, r, s} hits
  simpa [hpq, hpr, hps, hqr, hqs, hrs] using h

lemma gate_decomposition (gs : List Gate) (p : Fin gs.length) :
    gs = gs.take p.val ++ gs.get p :: gs.drop (p.val + 1) := by
  rw [List.get_eq_getElem, List.getElem_cons_drop p.isLt, List.take_append_drop]

lemma final_and_false (n k : ℕ) (gs : List Gate) (acc : List Stat × List Gate)
    (p : Fin gs.length) (hop : (gs.get p).op = GateOp.and)
    (hlen : (gs.get p).inputs.length ≤ 2) (hread : k ∈ (gs.get p).inputs)
    (hback : k < acc.1.length + p.val)
    (hz : (elim n gs acc).1.getD k (Sum.inl false) = Sum.inl false) :
    (elim n gs acc).1.getD (acc.1.length + p.val) (Sum.inl false) = Sum.inl false := by
  have h := elim_and_output_false n k (gs.take p.val) (gs.drop (p.val + 1)) (gs.get p)
    acc hop hlen hread (by simpa using hback) (by simpa [← gate_decomposition gs p] using hz)
  simpa only [← gate_decomposition gs p, List.length_take_of_le (Nat.le_of_lt p.isLt)] using h

lemma final_not (n k : ℕ) (gs : List Gate) (acc : List Stat × List Gate)
    (p : Fin gs.length) (hg : gs.get p = ⟨GateOp.not, [k]⟩)
    (b : Bool) (hback : k < acc.1.length + p.val)
    (hc : (elim n gs acc).1.getD k (Sum.inl false) = Sum.inl b) :
    (elim n gs acc).1.getD (acc.1.length + p.val) (Sum.inl false) = Sum.inl (!b) := by
  have eq : gs = gs.take p.val ++ ⟨GateOp.not, [k]⟩ :: gs.drop (p.val + 1) := by
    rw [← hg]
    exact gate_decomposition gs p
  have h := elim_not_output n k (gs.take p.val) (gs.drop (p.val + 1)) acc b
    (by simpa using hback) (by simpa [← eq] using hc)
  simpa only [← eq, List.length_take_of_le (Nat.le_of_lt p.isLt)] using h

lemma final_two_constants (n k l : ℕ) (gs : List Gate) (acc : List Stat × List Gate)
    (p : Fin gs.length) (hop : (gs.get p).op = GateOp.and ∨ (gs.get p).op = GateOp.or)
    (hlen : (gs.get p).inputs.length ≤ 2) (hkl : k ≠ l)
    (hk : k ∈ (gs.get p).inputs) (hl : l ∈ (gs.get p).inputs)
    (hbackk : k < acc.1.length + p.val) (hbackl : l < acc.1.length + p.val)
    (b c : Bool) (hb : (elim n gs acc).1.getD k (Sum.inl false) = Sum.inl b)
    (hc : (elim n gs acc).1.getD l (Sum.inl false) = Sum.inl c) :
    ∃ d, (elim n gs acc).1.getD (acc.1.length + p.val) (Sum.inl false) = Sum.inl d := by
  have hins := Consumer.two_inputs_of_distinct (gs.get p).inputs k l hkl hlen hk hl
  have hbk : (elim n (gs.take p.val) acc).1.getD k (Sum.inl false) = Sum.inl b := by
    have he := elim_before_status n k (gs.take p.val)
      (gs.get p :: gs.drop (p.val + 1)) acc (by simpa using hbackk)
    rw [← gate_decomposition gs p, hb] at he
    exact he.symm
  have hcl : (elim n (gs.take p.val) acc).1.getD l (Sum.inl false) = Sum.inl c := by
    have he := elim_before_status n l (gs.take p.val)
      (gs.get p :: gs.drop (p.val + 1)) acc (by simpa using hbackl)
    rw [← gate_decomposition gs p, hc] at he
    exact he.symm
  have he := elim_output_status n (gs.take p.val) (gs.drop (p.val + 1)) (gs.get p) acc
  rw [← gate_decomposition gs p, List.length_take_of_le (Nat.le_of_lt p.isLt)] at he
  rw [he]
  rcases hop with hop | hop <;> rcases hins with hins | hins <;>
    rw [hop, hins] <;> simp only [List.map_cons, List.map_nil, hbk, hcl] <;>
    simp [simplify, simpAnd, simpOr]

lemma nand_saving_distinct (n k : ℕ) (gs : List Gate) (acc : List Stat × List Gate)
    (p q r s : Fin gs.length)
    (normal : ∀ g ∈ gs, NOk g)
    (back : ∀ j g, gs[j]? = some g → ∀ a ∈ g.inputs, a < acc.1.length + j)
    (hk : k < acc.1.length) (hkfalse : acc.1.getD k (Sum.inl false) = Sum.inl false)
    (pand : (gs.get p).op = GateOp.and) (pread : k ∈ (gs.get p).inputs)
    (qnot : gs.get q = ⟨GateOp.not, [acc.1.length + p.val]⟩)
    (rread : k ∈ (gs.get r).inputs) (sread : acc.1.length + q.val ∈ (gs.get s).inputs)
    (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s) :
    (elim n gs acc).2.length + 4 ≤ acc.2.length + gs.length := by
  let K : Finset ℕ := {k, acc.1.length + p.val, acc.1.length + q.val}
  have hkfinal : (elim n gs acc).1.getD k (Sum.inl false) = Sum.inl false := by
    rw [elim_getD n k _ gs acc hk, hkfalse]
  have hpgood := normal (gs.get p) (List.get_mem gs p)
  have hpfalse := final_and_false n k gs acc p pand hpgood.1.2 pread (by omega) hkfinal
  have hqback : acc.1.length + p.val < acc.1.length + q.val := by
    apply back q.val (gs.get q) (by simp) (acc.1.length + p.val)
    simp only [qnot, List.mem_singleton]
  have hqtrue := final_not n (acc.1.length + p.val) gs acc q qnot false hqback hpfalse
  have hc : ∀ a ∈ K, ∃ b, (elim n gs acc).1.getD a (Sum.inl false) = Sum.inl b := by
    intro a ha
    simp only [K, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · exact ⟨false, hkfinal⟩
    · exact ⟨false, hpfalse⟩
    · exact ⟨true, hqtrue⟩
  have count := four_readers_le K gs p q r s hpq hpr hps hqr hqs hrs (by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact ⟨k, pread, by simp [K]⟩
    · exact ⟨acc.1.length + p.val, by simp only [qnot, List.mem_singleton], by simp [K]⟩
    · exact ⟨k, rread, by simp [K]⟩
    · exact ⟨acc.1.length + q.val, sread, by simp [K]⟩)
  have budget := elim_len_final_constants n K gs acc normal back hc
  omega

lemma nand_saving_collision (n k : ℕ) (gs : List Gate) (acc : List Stat × List Gate)
    (p q r t : Fin gs.length)
    (normal : ∀ g ∈ gs, NOk g)
    (back : ∀ j g, gs[j]? = some g → ∀ a ∈ g.inputs, a < acc.1.length + j)
    (hk : k < acc.1.length) (hkfalse : acc.1.getD k (Sum.inl false) = Sum.inl false)
    (pand : (gs.get p).op = GateOp.and) (pread : k ∈ (gs.get p).inputs)
    (qnot : gs.get q = ⟨GateOp.not, [acc.1.length + p.val]⟩)
    (rraw : k ∈ (gs.get r).inputs) (rnot : acc.1.length + q.val ∈ (gs.get r).inputs)
    (tread : acc.1.length + r.val ∈ (gs.get t).inputs) :
    (elim n gs acc).2.length + 4 ≤ acc.2.length + gs.length := by
  let K : Finset ℕ := {k, acc.1.length + p.val, acc.1.length + q.val, acc.1.length + r.val}
  have hkfinal : (elim n gs acc).1.getD k (Sum.inl false) = Sum.inl false := by
    rw [elim_getD n k _ gs acc hk, hkfalse]
  have hpgood := normal (gs.get p) (List.get_mem gs p)
  have hrgood := normal (gs.get r) (List.get_mem gs r)
  have hpfalse := final_and_false n k gs acc p pand hpgood.1.2 pread (by omega) hkfinal
  have hpq : p.val < q.val := by
    have hb := back q.val (gs.get q) (by simp) (acc.1.length + p.val) (by simp only [qnot, List.mem_singleton])
    omega
  have hqr : q.val < r.val := by
    have hb := back r.val (gs.get r) (by simp) (acc.1.length + q.val) rnot
    omega
  have hrt : r.val < t.val := by
    have hb := back t.val (gs.get t) (by simp) (acc.1.length + r.val) tread
    omega
  have hqtrue := final_not n (acc.1.length + p.val) gs acc q qnot false (by omega) hpfalse
  have hins := Consumer.two_inputs_of_distinct (gs.get r).inputs k (acc.1.length + q.val)
    (by omega) hrgood.1.2 rraw rnot
  have hrop : (gs.get r).op = GateOp.and ∨ (gs.get r).op = GateOp.or := by
    rcases hrgood.1.1 with hop | hop | hop
    · exact Or.inl hop
    · exact Or.inr hop
    · have hlen := hrgood.2 hop
      rcases hins with hins | hins <;> rw [hins] at hlen <;> simp at hlen
  obtain ⟨b, hrconstant⟩ := final_two_constants n k (acc.1.length + q.val) gs acc r hrop
    hrgood.1.2 (by omega) rraw rnot (by omega) (by omega) false true hkfinal hqtrue
  have hc : ∀ a ∈ K, ∃ b, (elim n gs acc).1.getD a (Sum.inl false) = Sum.inl b := by
    intro a ha
    simp only [K, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact ⟨false, hkfinal⟩
    · exact ⟨false, hpfalse⟩
    · exact ⟨true, hqtrue⟩
    · exact ⟨b, hrconstant⟩
  have count := four_readers_le K gs p q r t
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · exact ⟨k, pread, by simp [K]⟩
      · exact ⟨acc.1.length + p.val, by simp only [qnot, List.mem_singleton], by simp [K]⟩
      · exact ⟨k, rraw, by simp [K]⟩
      · exact ⟨acc.1.length + r.val, tread, by simp [K]⟩)
  have budget := elim_len_final_constants n K gs acc normal back hc
  omega

lemma nand_four_saving (n k : ℕ) (gs : List Gate) (acc : List Stat × List Gate)
    (p q r : Fin gs.length)
    (normal : ∀ g ∈ gs, NOk g)
    (back : ∀ j g, gs[j]? = some g → ∀ a ∈ g.inputs, a < acc.1.length + j)
    (hk : k < acc.1.length) (hkfalse : acc.1.getD k (Sum.inl false) = Sum.inl false)
    (pand : (gs.get p).op = GateOp.and) (pread : k ∈ (gs.get p).inputs)
    (qnot : gs.get q = ⟨GateOp.not, [acc.1.length + p.val]⟩)
    (rread : k ∈ (gs.get r).inputs) (hpr : p ≠ r)
    (live : ∀ i : Fin gs.length,
      (∃ b, (elim n gs acc).1.getD (acc.1.length + i.val) (Sum.inl false) = Sum.inl b) →
      ∃ j : Fin gs.length, acc.1.length + i.val ∈ (gs.get j).inputs) :
    (elim n gs acc).2.length + 4 ≤ acc.2.length + gs.length := by
  have hkfinal : (elim n gs acc).1.getD k (Sum.inl false) = Sum.inl false := by
    rw [elim_getD n k _ gs acc hk, hkfalse]
  have hpgood := normal (gs.get p) (List.get_mem gs p)
  have hpfalse := final_and_false n k gs acc p pand hpgood.1.2 pread (by omega) hkfinal
  have hpq : p.val < q.val := by
    have hb := back q.val (gs.get q) (by simp) (acc.1.length + p.val)
      (by simp only [qnot, List.mem_singleton])
    omega
  have hqtrue := final_not n (acc.1.length + p.val) gs acc q qnot false (by omega) hpfalse
  obtain ⟨s, sread⟩ := live q ⟨true, hqtrue⟩
  have hqs : q.val < s.val := by
    have hb := back s.val (gs.get s) (by simp) (acc.1.length + q.val) sread
    omega
  have hqr : q ≠ r := by
    intro heq
    subst r
    rw [qnot] at rread
    simp only [List.mem_singleton] at rread
    omega
  by_cases hsr : s = r
  · subst s
    have hrgood := normal (gs.get r) (List.get_mem gs r)
    have hins := Consumer.two_inputs_of_distinct (gs.get r).inputs k (acc.1.length + q.val)
      (by omega) hrgood.1.2 rread sread
    have hrop : (gs.get r).op = GateOp.and ∨ (gs.get r).op = GateOp.or := by
      rcases hrgood.1.1 with hop | hop | hop
      · exact Or.inl hop
      · exact Or.inr hop
      · have hlen := hrgood.2 hop
        rcases hins with hins | hins <;> rw [hins] at hlen <;> simp at hlen
    obtain ⟨b, hrconstant⟩ := final_two_constants n k (acc.1.length + q.val) gs acc r hrop
      hrgood.1.2 (by omega) rread sread (by omega) (by omega) false true hkfinal hqtrue
    obtain ⟨t, tread⟩ := live r ⟨b, hrconstant⟩
    exact nand_saving_collision n k gs acc p q r t normal back hk hkfalse pand pread qnot
      rread sread tread
  · exact nand_saving_distinct n k gs acc p q r s normal back hk hkfalse pand pread qnot
      rread sread (by omega) hpr (by omega) hqr (by omega) (Ne.symm hsr)

lemma restricted_output_not_constant (n : ℕ) (b : Bool) (C : Circuit)
    (hC : FanInTwo C)
    (hnc : ∃ y y' : Fin n → Bool,
      C.eval (List.ofFn (Fin.snoc y b)) ≠ C.eval (List.ofFn (Fin.snoc y' b))) :
    ∀ c, (elim n (C.gates.map normGate) (initStats n b, [])).1.getD C.output
      (Sum.inl false) ≠ Sum.inl c := by
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (hC g0 hg0)
  set acc := elim n gs (initStats n b, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y)
        (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool))) acc := by
    intro y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn y)) =
        C.eval (List.ofFn (Fin.snoc y b)) := by
    intro y
    rw [((hinv y).2 C.output).2, hgs, wiresFrom_norm]
    rfl
  intro c hc
  obtain ⟨y, y', hne⟩ := hnc
  apply hne
  rw [← hval y, ← hval y', hc]
  rfl

lemma fix_last_nand_four (n : ℕ) (C : Circuit) (gs : List Gate)
    (p q r : Fin gs.length) (hC : FanInTwo C)
    (hnc : ∃ y y' : Fin n → Bool,
      C.eval (List.ofFn (Fin.snoc y false)) ≠ C.eval (List.ofFn (Fin.snoc y' false)))
    (hgs : C.gates.map normGate = gs)
    (back : ∀ j g, gs[j]? = some g → ∀ a ∈ g.inputs, a < n + 1 + j)
    (live : ∀ i : Fin gs.length, n + 1 + i.val ≠ C.output →
      ∃ j : Fin gs.length, n + 1 + i.val ∈ (gs.get j).inputs)
    (pand : (gs.get p).op = GateOp.and) (pread : n ∈ (gs.get p).inputs)
    (qnot : gs.get q = ⟨GateOp.not, [n + 1 + p.val]⟩)
    (rread : n ∈ (gs.get r).inputs) (hpr : p ≠ r) :
    ∃ E : Circuit, FanInTwo E ∧ E.size + 4 ≤ C.size ∧
      ∀ y : Fin n → Bool, E.eval (List.ofFn y) = C.eval (List.ofFn (Fin.snoc y false)) := by
  have normal : ∀ g ∈ gs, NOk g := by
    intro g hg
    rw [← hgs] at hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    exact normGate_nok g0 (hC g0 hg0)
  have outNonconstant := restricted_output_not_constant n false C hC hnc
  rw [hgs] at outNonconstant
  have hbudget := nand_four_saving n n gs (initStats n false, []) p q r normal
    (by simpa [initStats] using back) (by simp [initStats])
    (getD_snoc_len _ _ _ _ (by simp)) pand pread (by simpa [initStats] using qnot)
    rread hpr (by
      intro i hi
      obtain ⟨b, hb⟩ := hi
      have hne : n + 1 + i.val ≠ C.output := by
        intro heq
        apply outNonconstant b
        simpa [initStats, heq] using hb
      simpa [initStats] using live i hne)
  apply fix_last_with_savings n 4 false C hC hnc
  rw [hgs]
  have hlength : gs.length = C.size := by rw [← hgs]; simp [Circuit.size]
  simpa [hlength] using hbudget

lemma nand_lower_bound (n lower : ℕ) (C : Circuit) (gs : List Gate)
    (p q r : Fin gs.length) (hC : FanInTwo C)
    (hnc : ∃ y y' : Fin n → Bool,
      C.eval (List.ofFn (Fin.snoc y false)) ≠ C.eval (List.ofFn (Fin.snoc y' false)))
    (hgs : C.gates.map normGate = gs)
    (back : ∀ j g, gs[j]? = some g → ∀ a ∈ g.inputs, a < n + 1 + j)
    (live : ∀ i : Fin gs.length, n + 1 + i.val ≠ C.output →
      ∃ j : Fin gs.length, n + 1 + i.val ∈ (gs.get j).inputs)
    (pand : (gs.get p).op = GateOp.and) (pread : n ∈ (gs.get p).inputs)
    (qnot : gs.get q = ⟨GateOp.not, [n + 1 + p.val]⟩)
    (rread : n ∈ (gs.get r).inputs) (hpr : p ≠ r)
    (hlower : ∀ E : Circuit, FanInTwo E →
      (∀ y : Fin n → Bool, E.eval (List.ofFn y) = C.eval (List.ofFn (Fin.snoc y false))) →
      lower ≤ E.size) : lower + 4 ≤ C.size := by
  obtain ⟨E, hE, size, computes⟩ := fix_last_nand_four n C gs p q r hC hnc hgs back live
    pand pread qnot rread hpr
  have bound := hlower E hE computes
  omega


def identityStats (n : ℕ) : List Stat :=
  List.ofFn (fun i : Fin n => Sum.inr (i : ℕ))

lemma inv_identity (n : ℕ) (x : Fin n → Bool) :
    Inv n (List.ofFn x) (List.ofFn x) (identityStats n, []) := by
  refine ⟨by simp [identityStats], ?_⟩
  intro i
  by_cases hi : i < n
  · simp [identityStats, hi, Stat.Valid, Stat.val, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [identityStats]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

def Back : ℕ → List Gate → Prop
  | _, [] => True
  | n, g :: gs => (∀ i ∈ g.inputs, i < n) ∧ Back (n + 1) gs

lemma back_append (n : ℕ) (gs hs : List Gate) (hg : Back n gs)
    (hh : Back (n + gs.length) hs) : Back n (gs ++ hs) := by
  induction gs generalizing n with
  | nil => simpa using hh
  | cons g gs ih =>
    refine ⟨hg.1, ?_⟩
    apply ih (n + 1) hg.2
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

lemma simplify_back (op : GateOp) (m : ℕ) (ins : List Stat)
    (hv : ∀ s ∈ ins, s.Valid m) : Back m (simplify op m ins).1.toList := by
  cases op <;> simp only [simplify]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simpAnd, Back, Stat.Valid]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simpOr, Back, Stat.Valid]
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp_all [simpNot, Back, Stat.Valid]
  · trivial
  · trivial

lemma simplify_nok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, NOk g := by
  intro g hg
  refine ⟨simplify_ok op m ins g hg, ?_⟩
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    simp
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    simp
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    simp
  · simp at hg
  · simp at hg

lemma elim_nok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, NOk g) → ∀ g ∈ (elim n gs acc).2, NOk g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_nok _ _ _ g' (by simpa using h1)

lemma elim_back (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ w acc, (∀ g ∈ gs, Ok g) → Inv n y w acc → Back n acc.2 →
      Back n (elim n gs acc).2 := by
  induction gs with
  | nil => intro w acc hok hinv hb; exact hb
  | cons g gs ih =>
    intro w acc hok hinv hb
    apply ih (wiresFrom [g] w) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    · exact inv_elim n y hy [g] w acc (by simpa using hok g List.mem_cons_self) hinv
    · apply back_append n acc.2 _ hb
      apply simplify_back
      intro s hs
      obtain ⟨i, _, rfl⟩ := List.mem_map.1 hs
      exact (hinv.2 i).1

lemma back_lookup (n : ℕ) (gs : List Gate) (h : Back n gs) :
    ∀ j g, gs[j]? = some g → ∀ i ∈ g.inputs, i < n + j := by
  induction gs generalizing n with
  | nil => intro j g hj; simp at hj
  | cons g gs ih =>
    intro j g' hj i hi
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst g'
      simpa using h.1 i hi
    | succ j =>
      have hj' : gs[j]? = some g' := by simpa using hj
      have hh := ih (n + 1) h.2 j g' hj' i hi
      omega

lemma exists_strict_equivalent (n : ℕ) (C : Circuit) (hfan : FanInTwo C)
    (hnc : ∃ x y : Fin n → Bool, C.eval (List.ofFn x) ≠ C.eval (List.ofFn y)) :
    ∃ E : Circuit, FanInTwo E ∧ E.size ≤ C.size ∧
      (∀ x : Fin n → Bool, E.eval (List.ofFn x) = C.eval (List.ofFn x)) ∧
      (∀ g ∈ E.gates, g.op = GateOp.not → g.inputs.length ≤ 1) ∧
      (∀ j g, E.gates[j]? = some g → ∀ i ∈ g.inputs, i < n + j) := by
  let acc := elim n C.gates (identityStats n, [])
  have hinv (x : Fin n → Bool) :
      Inv n (List.ofFn x) (wiresFrom C.gates (List.ofFn x)) acc :=
    inv_elim n _ (by simp) C.gates _ _ hfan (inv_identity n x)
  have hval (x : Fin n → Bool) :
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn x)) =
        C.eval (List.ofFn x) := (hinv x).2 C.output |>.2
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨x, y, hxy⟩ := hnc
    apply hxy
    rw [← hval x, ← hval y, hst]
    rfl
  | inr j =>
    have hnok : ∀ g ∈ acc.2, NOk g := elim_nok n C.gates _ (by simp)
    have hback : Back n acc.2 := elim_back n (List.ofFn (fun _ : Fin n => false))
      (by simp) C.gates _ _ hfan (inv_identity n _) trivial
    refine ⟨⟨acc.2, j⟩, fun g hg => (hnok g hg).1, ?_, ?_,
      fun g hg => (hnok g hg).2, back_lookup n acc.2 hback⟩
    · have := elim_len n C.gates (identityStats n, [])
      simpa [Circuit.size] using this
    · intro x
      have hv := hval x
      rw [hst] at hv
      exact hv

lemma minimal_strict_equivalent (n : ℕ) (C : Circuit) (hfan : FanInTwo C)
    (hnc : ∃ x y : Fin n → Bool, C.eval (List.ofFn x) ≠ C.eval (List.ofFn y))
    (hmin : ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) → C.size ≤ D.size) :
    ∃ E : Circuit, FanInTwo E ∧ E.size = C.size ∧
      (∀ x : Fin n → Bool, E.eval (List.ofFn x) = C.eval (List.ofFn x)) ∧
      (∀ g ∈ E.gates, g.op = GateOp.not → g.inputs.length ≤ 1) ∧
      (∀ j g, E.gates[j]? = some g → ∀ i ∈ g.inputs, i < n + j) ∧
      ∀ D : Circuit, FanInTwo D →
        (∀ x : Fin n → Bool, D.eval (List.ofFn x) = E.eval (List.ofFn x)) → E.size ≤ D.size := by
  obtain ⟨E, fan, size, computes, normal, back⟩ := exists_strict_equivalent n C hfan hnc
  have heq : E.size = C.size := Nat.le_antisymm size (hmin E fan computes)
  refine ⟨E, fan, heq, computes, normal, back, ?_⟩
  intro D dFan dComputes
  rw [heq]
  apply hmin D dFan
  intro x
  exact (dComputes x).trans (computes x)



lemma and_and_not_four_saving (n k : ℕ) (gs : List Gate) (acc : List Stat × List Gate)
    (p q r : Fin gs.length)
    (normal : ∀ g ∈ gs, NOk g)
    (back : ∀ j g, gs[j]? = some g → ∀ a ∈ g.inputs, a < acc.1.length + j)
    (hk : k < acc.1.length) (hkfalse : acc.1.getD k (Sum.inl false) = Sum.inl false)
    (pand : (gs.get p).op = GateOp.and) (pread : k ∈ (gs.get p).inputs)
    (qand : (gs.get q).op = GateOp.and) (qread : acc.1.length + p.val ∈ (gs.get q).inputs)
    (rnot : gs.get r = ⟨GateOp.not, [acc.1.length + q.val]⟩)
    (live : ∀ i : Fin gs.length,
      (∃ b, (elim n gs acc).1.getD (acc.1.length + i.val) (Sum.inl false) = Sum.inl b) →
      ∃ j : Fin gs.length, acc.1.length + i.val ∈ (gs.get j).inputs) :
    (elim n gs acc).2.length + 4 ≤ acc.2.length + gs.length := by
  let K : Finset ℕ := {k, acc.1.length + p.val, acc.1.length + q.val, acc.1.length + r.val}
  have hkfinal : (elim n gs acc).1.getD k (Sum.inl false) = Sum.inl false := by
    rw [elim_getD n k _ gs acc hk, hkfalse]
  have hpgood := normal (gs.get p) (List.get_mem gs p)
  have hqgood := normal (gs.get q) (List.get_mem gs q)
  have hpq : p.val < q.val := by
    have hb := back q.val (gs.get q) (by simp) (acc.1.length + p.val) qread
    omega
  have hqr : q.val < r.val := by
    have hb := back r.val (gs.get r) (by simp) (acc.1.length + q.val)
      (by simp only [rnot, List.mem_singleton])
    omega
  have hpfalse := final_and_false n k gs acc p pand hpgood.1.2 pread (by omega) hkfinal
  have hqfalse := final_and_false n (acc.1.length + p.val) gs acc q qand hqgood.1.2 qread
    (by omega) hpfalse
  have hrtrue := final_not n (acc.1.length + q.val) gs acc r rnot false (by omega) hqfalse
  obtain ⟨s, sread⟩ := live r ⟨true, hrtrue⟩
  have hrs : r.val < s.val := by
    have hb := back s.val (gs.get s) (by simp) (acc.1.length + r.val) sread
    omega
  have hc : ∀ a ∈ K, ∃ b, (elim n gs acc).1.getD a (Sum.inl false) = Sum.inl b := by
    intro a ha
    simp only [K, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact ⟨false, hkfinal⟩
    · exact ⟨false, hpfalse⟩
    · exact ⟨false, hqfalse⟩
    · exact ⟨true, hrtrue⟩
  have count := four_readers_le K gs p q r s
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · exact ⟨k, pread, by simp [K]⟩
      · exact ⟨acc.1.length + p.val, qread, by simp [K]⟩
      · exact ⟨acc.1.length + q.val, by simp only [rnot, List.mem_singleton], by simp [K]⟩
      · exact ⟨acc.1.length + r.val, sread, by simp [K]⟩)
  have budget := elim_len_final_constants n K gs acc normal back hc
  omega

lemma fix_last_and_and_not_four (n : ℕ) (C : Circuit) (gs : List Gate)
    (p q r : Fin gs.length) (hC : FanInTwo C)
    (hnc : ∃ y y' : Fin n → Bool,
      C.eval (List.ofFn (Fin.snoc y false)) ≠ C.eval (List.ofFn (Fin.snoc y' false)))
    (hgs : C.gates.map normGate = gs)
    (back : ∀ j g, gs[j]? = some g → ∀ a ∈ g.inputs, a < n + 1 + j)
    (live : ∀ i : Fin gs.length, n + 1 + i.val ≠ C.output →
      ∃ j : Fin gs.length, n + 1 + i.val ∈ (gs.get j).inputs)
    (pand : (gs.get p).op = GateOp.and) (pread : n ∈ (gs.get p).inputs)
    (qand : (gs.get q).op = GateOp.and) (qread : n + 1 + p.val ∈ (gs.get q).inputs)
    (rnot : gs.get r = ⟨GateOp.not, [n + 1 + q.val]⟩) :
    ∃ E : Circuit, FanInTwo E ∧ E.size + 4 ≤ C.size ∧
      ∀ y : Fin n → Bool, E.eval (List.ofFn y) = C.eval (List.ofFn (Fin.snoc y false)) := by
  have normal : ∀ g ∈ gs, NOk g := by
    intro g hg
    rw [← hgs] at hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    exact normGate_nok g0 (hC g0 hg0)
  have outNonconstant := restricted_output_not_constant n false C hC hnc
  rw [hgs] at outNonconstant
  have hbudget := and_and_not_four_saving n n gs (initStats n false, []) p q r normal
    (by simpa [initStats] using back) (by simp [initStats])
    (getD_snoc_len _ _ _ _ (by simp)) pand pread qand (by simpa [initStats] using qread)
    (by simpa [initStats] using rnot) (by
      intro i hi
      obtain ⟨b, hb⟩ := hi
      have hne : n + 1 + i.val ≠ C.output := by
        intro heq
        apply outNonconstant b
        simpa [initStats, heq] using hb
      simpa [initStats] using live i hne)
  apply fix_last_with_savings n 4 false C hC hnc
  rw [hgs]
  have hlength : gs.length = C.size := by rw [← hgs]; simp [Circuit.size]
  simpa [hlength] using hbudget

lemma and_and_not_lower_bound (n lower : ℕ) (C : Circuit) (gs : List Gate)
    (p q r : Fin gs.length) (hC : FanInTwo C)
    (hnc : ∃ y y' : Fin n → Bool,
      C.eval (List.ofFn (Fin.snoc y false)) ≠ C.eval (List.ofFn (Fin.snoc y' false)))
    (hgs : C.gates.map normGate = gs)
    (back : ∀ j g, gs[j]? = some g → ∀ a ∈ g.inputs, a < n + 1 + j)
    (live : ∀ i : Fin gs.length, n + 1 + i.val ≠ C.output →
      ∃ j : Fin gs.length, n + 1 + i.val ∈ (gs.get j).inputs)
    (pand : (gs.get p).op = GateOp.and) (pread : n ∈ (gs.get p).inputs)
    (qand : (gs.get q).op = GateOp.and) (qread : n + 1 + p.val ∈ (gs.get q).inputs)
    (rnot : gs.get r = ⟨GateOp.not, [n + 1 + q.val]⟩)
    (hlower : ∀ E : Circuit, FanInTwo E →
      (∀ y : Fin n → Bool, E.eval (List.ofFn y) = C.eval (List.ofFn (Fin.snoc y false))) →
      lower ≤ E.size) : lower + 4 ≤ C.size := by
  obtain ⟨E, hE, size, computes⟩ := fix_last_and_and_not_four n C gs p q r hC hnc hgs back live
    pand pread qand qread rnot
  have bound := hlower E hE computes
  omega


lemma and_constant_consumer_four_saving (n k : ℕ) (gs : List Gate)
    (acc : List Stat × List Gate) (p q r : Fin gs.length)
    (normal : ∀ g ∈ gs, NOk g)
    (back : ∀ j g, gs[j]? = some g → ∀ a ∈ g.inputs, a < acc.1.length + j)
    (hk : k < acc.1.length) (hkfalse : acc.1.getD k (Sum.inl false) = Sum.inl false)
    (pand : (gs.get p).op = GateOp.and) (pread : k ∈ (gs.get p).inputs)
    (qread : acc.1.length + p.val ∈ (gs.get q).inputs) (qavoids : k ∉ (gs.get q).inputs)
    (qconstant : ∃ b, (elim n gs acc).1.getD (acc.1.length + q.val) (Sum.inl false) = Sum.inl b)
    (rread : k ∈ (gs.get r).inputs) (hpr : p ≠ r)
    (live : ∀ i : Fin gs.length,
      (∃ b, (elim n gs acc).1.getD (acc.1.length + i.val) (Sum.inl false) = Sum.inl b) →
      ∃ j : Fin gs.length, acc.1.length + i.val ∈ (gs.get j).inputs) :
    (elim n gs acc).2.length + 4 ≤ acc.2.length + gs.length := by
  have hkfinal : (elim n gs acc).1.getD k (Sum.inl false) = Sum.inl false := by
    rw [elim_getD n k _ gs acc hk, hkfalse]
  have hpgood := normal (gs.get p) (List.get_mem gs p)
  have hpfalse := final_and_false n k gs acc p pand hpgood.1.2 pread (by omega) hkfinal
  have hpq : p.val < q.val := by
    have hb := back q.val (gs.get q) (by simp) (acc.1.length + p.val) qread
    omega
  obtain ⟨b, hqb⟩ := qconstant
  obtain ⟨s, sread⟩ := live q ⟨b, hqb⟩
  have hqs : q.val < s.val := by
    have hb := back s.val (gs.get s) (by simp) (acc.1.length + q.val) sread
    omega
  have hqr : q ≠ r := by intro heq; subst r; exact qavoids rread
  by_cases hsr : s = r
  · subst s
    have hrgood := normal (gs.get r) (List.get_mem gs r)
    have hins := Consumer.two_inputs_of_distinct (gs.get r).inputs k (acc.1.length + q.val)
      (by omega) hrgood.1.2 rread sread
    have hrop : (gs.get r).op = GateOp.and ∨ (gs.get r).op = GateOp.or := by
      rcases hrgood.1.1 with hop | hop | hop
      · exact Or.inl hop
      · exact Or.inr hop
      · have hlen := hrgood.2 hop
        rcases hins with hins | hins <;> rw [hins] at hlen <;> simp at hlen
    obtain ⟨c, hrc⟩ := final_two_constants n k (acc.1.length + q.val) gs acc r hrop
      hrgood.1.2 (by omega) rread sread (by omega) (by omega) false b hkfinal hqb
    obtain ⟨t, tread⟩ := live r ⟨c, hrc⟩
    have hrt : r.val < t.val := by
      have hb := back t.val (gs.get t) (by simp) (acc.1.length + r.val) tread
      omega
    let K : Finset ℕ := {k, acc.1.length + p.val, acc.1.length + q.val, acc.1.length + r.val}
    have hc : ∀ a ∈ K, ∃ c, (elim n gs acc).1.getD a (Sum.inl false) = Sum.inl c := by
      intro a ha
      simp only [K, Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl | rfl
      · exact ⟨false, hkfinal⟩
      · exact ⟨false, hpfalse⟩
      · exact ⟨b, hqb⟩
      · exact ⟨c, hrc⟩
    have count := four_readers_le K gs p q r t
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by
        intro i hi
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with rfl | rfl | rfl | rfl
        · exact ⟨k, pread, by simp [K]⟩
        · exact ⟨acc.1.length + p.val, qread, by simp [K]⟩
        · exact ⟨k, rread, by simp [K]⟩
        · exact ⟨acc.1.length + r.val, tread, by simp [K]⟩)
    have budget := elim_len_final_constants n K gs acc normal back hc
    omega
  · let K : Finset ℕ := {k, acc.1.length + p.val, acc.1.length + q.val}
    have hc : ∀ a ∈ K, ∃ c, (elim n gs acc).1.getD a (Sum.inl false) = Sum.inl c := by
      intro a ha
      simp only [K, Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl
      · exact ⟨false, hkfinal⟩
      · exact ⟨false, hpfalse⟩
      · exact ⟨b, hqb⟩
    have count := four_readers_le K gs p q r s
      (by omega) hpr (by omega) hqr (by omega) (Ne.symm hsr) (by
        intro i hi
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with rfl | rfl | rfl | rfl
        · exact ⟨k, pread, by simp [K]⟩
        · exact ⟨acc.1.length + p.val, qread, by simp [K]⟩
        · exact ⟨k, rread, by simp [K]⟩
        · exact ⟨acc.1.length + q.val, sread, by simp [K]⟩)
    have budget := elim_len_final_constants n K gs acc normal back hc
    omega

lemma and_and_four_saving (n k : ℕ) (gs : List Gate) (acc : List Stat × List Gate)
    (p q r : Fin gs.length)
    (normal : ∀ g ∈ gs, NOk g)
    (back : ∀ j g, gs[j]? = some g → ∀ a ∈ g.inputs, a < acc.1.length + j)
    (hk : k < acc.1.length) (hkfalse : acc.1.getD k (Sum.inl false) = Sum.inl false)
    (pand : (gs.get p).op = GateOp.and) (pread : k ∈ (gs.get p).inputs)
    (qand : (gs.get q).op = GateOp.and) (qread : acc.1.length + p.val ∈ (gs.get q).inputs)
    (qavoids : k ∉ (gs.get q).inputs) (rread : k ∈ (gs.get r).inputs) (hpr : p ≠ r)
    (live : ∀ i : Fin gs.length,
      (∃ b, (elim n gs acc).1.getD (acc.1.length + i.val) (Sum.inl false) = Sum.inl b) →
      ∃ j : Fin gs.length, acc.1.length + i.val ∈ (gs.get j).inputs) :
    (elim n gs acc).2.length + 4 ≤ acc.2.length + gs.length := by
  have hkfinal : (elim n gs acc).1.getD k (Sum.inl false) = Sum.inl false := by
    rw [elim_getD n k _ gs acc hk, hkfalse]
  have hpgood := normal (gs.get p) (List.get_mem gs p)
  have hqgood := normal (gs.get q) (List.get_mem gs q)
  have hpq := back q.val (gs.get q) (by simp) (acc.1.length + p.val) qread
  have hpfalse := final_and_false n k gs acc p pand hpgood.1.2 pread (by omega) hkfinal
  have hqfalse := final_and_false n (acc.1.length + p.val) gs acc q qand hqgood.1.2 qread hpq hpfalse
  exact and_constant_consumer_four_saving n k gs acc p q r normal back hk hkfalse pand pread
    qread qavoids ⟨false, hqfalse⟩ rread hpr live

lemma two_and_consumers_four_saving (n k : ℕ) (gs : List Gate) (acc : List Stat × List Gate)
    (p q r s : Fin gs.length)
    (normal : ∀ g ∈ gs, NOk g)
    (back : ∀ j g, gs[j]? = some g → ∀ a ∈ g.inputs, a < acc.1.length + j)
    (hk : k < acc.1.length) (hkfalse : acc.1.getD k (Sum.inl false) = Sum.inl false)
    (pand : (gs.get p).op = GateOp.and) (pread : k ∈ (gs.get p).inputs)
    (qread : acc.1.length + p.val ∈ (gs.get q).inputs) (qavoids : k ∉ (gs.get q).inputs)
    (sread : acc.1.length + p.val ∈ (gs.get s).inputs) (savoids : k ∉ (gs.get s).inputs)
    (rread : k ∈ (gs.get r).inputs) (hpr : p ≠ r) (hqs : q ≠ s) :
    (elim n gs acc).2.length + 4 ≤ acc.2.length + gs.length := by
  let K : Finset ℕ := {k, acc.1.length + p.val}
  have hkfinal : (elim n gs acc).1.getD k (Sum.inl false) = Sum.inl false := by
    rw [elim_getD n k _ gs acc hk, hkfalse]
  have hpgood := normal (gs.get p) (List.get_mem gs p)
  have hpfalse := final_and_false n k gs acc p pand hpgood.1.2 pread (by omega) hkfinal
  have hpq := back q.val (gs.get q) (by simp) (acc.1.length + p.val) qread
  have hps := back s.val (gs.get s) (by simp) (acc.1.length + p.val) sread
  have hqr : q ≠ r := by intro heq; subst r; exact qavoids rread
  have hrs : r ≠ s := by intro heq; subst r; exact savoids rread
  have hc : ∀ a ∈ K, ∃ b, (elim n gs acc).1.getD a (Sum.inl false) = Sum.inl b := by
    intro a ha
    simp only [K, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact ⟨false, hkfinal⟩
    · exact ⟨false, hpfalse⟩
  have count := four_readers_le K gs p q r s (by omega) hpr (by omega) hqr hqs hrs (by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact ⟨k, pread, by simp [K]⟩
    · exact ⟨acc.1.length + p.val, qread, by simp [K]⟩
    · exact ⟨k, rread, by simp [K]⟩
    · exact ⟨acc.1.length + p.val, sread, by simp [K]⟩)
  have budget := elim_len_final_constants n K gs acc normal back hc
  omega

def normalizationIsNot : GateOp → Bool
  | GateOp.not => true
  | _ => false

def normalizationNotCount (gs : List Gate) : ℕ :=
  gs.countP (fun g => normalizationIsNot g.op)

lemma normalizationNotCount_eq (C : Circuit) :
    normalizationNotCount C.gates = PEqualNP.NotBracket.notCount C := by
  unfold normalizationNotCount PEqualNP.NotBracket.notCount
  rw [List.countP_eq_length_filter]
  congr 2
  funext g
  cases g.op <;> rfl

lemma normalizationNotCount_append (gs hs : List Gate) :
    normalizationNotCount (gs ++ hs) = normalizationNotCount gs + normalizationNotCount hs := by
  simp [normalizationNotCount]

lemma simplify_notCount_le (op : GateOp) (m : ℕ) (ins : List Stat) :
    normalizationNotCount (simplify op m ins).1.toList ≤ if normalizationIsNot op then 1 else 0 := by
  cases op <;> simp only [simplify]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd, normalizationNotCount, normalizationIsNot]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr, normalizationNotCount, normalizationIsNot]
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot, normalizationNotCount, normalizationIsNot]
  · simp [normalizationNotCount, normalizationIsNot]
  · simp [normalizationNotCount, normalizationIsNot]

lemma elim_notCount_le (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    normalizationNotCount (elim n gs acc).2 ≤ normalizationNotCount acc.2 + normalizationNotCount gs := by
  induction gs with
  | nil => intro acc; simp [elim, normalizationNotCount]
  | cons g gs ih =>
    intro acc
    have hi := ih (elimStep n acc g)
    have hs : normalizationNotCount (elimStep n acc g).2 ≤
        normalizationNotCount acc.2 + if normalizationIsNot g.op then 1 else 0 := by
      change normalizationNotCount (acc.2 ++ _ ) ≤ _
      rw [normalizationNotCount_append]
      exact Nat.add_le_add_left (simplify_notCount_le g.op _ _) _
    have hc : normalizationNotCount (g :: gs) =
        (if normalizationIsNot g.op then 1 else 0) + normalizationNotCount gs := by
      simp [normalizationNotCount, List.countP_cons, Nat.add_comm]
    change normalizationNotCount (elim n gs (elimStep n acc g)).2 ≤ _
    rw [hc]
    omega

lemma exists_strict_equivalent_count (n : ℕ) (C : Circuit) (hfan : FanInTwo C)
    (hnc : ∃ x y : Fin n → Bool, C.eval (List.ofFn x) ≠ C.eval (List.ofFn y)) :
    ∃ E : Circuit, FanInTwo E ∧ E.size ≤ C.size ∧
      (∀ x : Fin n → Bool, E.eval (List.ofFn x) = C.eval (List.ofFn x)) ∧
      (∀ g ∈ E.gates, g.op = GateOp.not → g.inputs.length ≤ 1) ∧
      (∀ j g, E.gates[j]? = some g → ∀ i ∈ g.inputs, i < n + j) ∧
      PEqualNP.NotBracket.notCount E ≤ PEqualNP.NotBracket.notCount C := by
  let acc := elim n C.gates (identityStats n, [])
  have hinv (x : Fin n → Bool) :
      Inv n (List.ofFn x) (wiresFrom C.gates (List.ofFn x)) acc :=
    inv_elim n _ (by simp) C.gates _ _ hfan (inv_identity n x)
  have hval (x : Fin n → Bool) :
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn x)) =
        C.eval (List.ofFn x) := (hinv x).2 C.output |>.2
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨x, y, hxy⟩ := hnc
    apply hxy
    rw [← hval x, ← hval y, hst]
    rfl
  | inr j =>
    have hnok : ∀ g ∈ acc.2, NOk g := elim_nok n C.gates _ (by simp)
    have hback : Back n acc.2 := elim_back n (List.ofFn (fun _ : Fin n => false))
      (by simp) C.gates _ _ hfan (inv_identity n _) trivial
    refine ⟨⟨acc.2, j⟩, fun g hg => (hnok g hg).1, ?_, ?_,
      fun g hg => (hnok g hg).2, back_lookup n acc.2 hback, ?_⟩
    · have := elim_len n C.gates (identityStats n, [])
      simpa [Circuit.size] using this
    · intro x
      have hv := hval x
      rw [hst] at hv
      exact hv
    · have hc := elim_notCount_le n C.gates (identityStats n, [])
      rw [← normalizationNotCount_eq, ← normalizationNotCount_eq]
      change normalizationNotCount acc.2 ≤ normalizationNotCount C.gates
      simpa [normalizationNotCount] using hc

lemma minimum_not_strict_equivalent (n bound : ℕ) (C : Circuit) (hfan : FanInTwo C)
    (hsize : C.size ≤ bound)
    (hnc : ∃ x y : Fin n → Bool, C.eval (List.ofFn x) ≠ C.eval (List.ofFn y))
    (hmin : ∀ D : Circuit, FanInTwo D → D.size ≤ bound →
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) →
      PEqualNP.NotBracket.notCount C ≤ PEqualNP.NotBracket.notCount D) :
    ∃ E : Circuit, FanInTwo E ∧ E.size ≤ C.size ∧
      (∀ x : Fin n → Bool, E.eval (List.ofFn x) = C.eval (List.ofFn x)) ∧
      (∀ g ∈ E.gates, g.op = GateOp.not → g.inputs.length ≤ 1) ∧
      (∀ j g, E.gates[j]? = some g → ∀ i ∈ g.inputs, i < n + j) ∧
      PEqualNP.NotBracket.notCount E = PEqualNP.NotBracket.notCount C ∧
      ∀ D : Circuit, FanInTwo D → D.size ≤ bound →
        (∀ x : Fin n → Bool, D.eval (List.ofFn x) = E.eval (List.ofFn x)) →
        PEqualNP.NotBracket.notCount E ≤ PEqualNP.NotBracket.notCount D := by
  obtain ⟨E, fan, size, computes, normal, back, count⟩ := exists_strict_equivalent_count n C hfan hnc
  have heq : PEqualNP.NotBracket.notCount E = PEqualNP.NotBracket.notCount C :=
    Nat.le_antisymm count (hmin E fan (size.trans hsize) computes)
  refine ⟨E, fan, size, computes, normal, back, heq, ?_⟩
  intro D dFan dSize dComputes
  rw [heq]
  apply hmin D dFan dSize
  intro x
  exact (dComputes x).trans (computes x)

lemma simultaneous_minimal_strict_equivalent (n bound : ℕ) (C : Circuit) (hfan : FanInTwo C)
    (hsize : C.size ≤ bound)
    (hnc : ∃ x y : Fin n → Bool, C.eval (List.ofFn x) ≠ C.eval (List.ofFn y))
    (hminSize : ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) → C.size ≤ D.size)
    (hminNot : ∀ D : Circuit, FanInTwo D → D.size ≤ bound →
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) →
      PEqualNP.NotBracket.notCount C ≤ PEqualNP.NotBracket.notCount D) :
    ∃ E : Circuit, FanInTwo E ∧ E.size = C.size ∧
      (∀ x : Fin n → Bool, E.eval (List.ofFn x) = C.eval (List.ofFn x)) ∧
      (∀ g ∈ E.gates, g.op = GateOp.not → g.inputs.length ≤ 1) ∧
      (∀ j g, E.gates[j]? = some g → ∀ i ∈ g.inputs, i < n + j) ∧
      PEqualNP.NotBracket.notCount E = PEqualNP.NotBracket.notCount C ∧
      (∀ D : Circuit, FanInTwo D →
        (∀ x : Fin n → Bool, D.eval (List.ofFn x) = E.eval (List.ofFn x)) → E.size ≤ D.size) ∧
      ∀ D : Circuit, FanInTwo D → D.size ≤ bound →
        (∀ x : Fin n → Bool, D.eval (List.ofFn x) = E.eval (List.ofFn x)) →
        PEqualNP.NotBracket.notCount E ≤ PEqualNP.NotBracket.notCount D := by
  obtain ⟨E, fan, size, computes, normal, back, count, leastNot⟩ :=
    minimum_not_strict_equivalent n bound C hfan hsize hnc hminNot
  have heq : E.size = C.size := Nat.le_antisymm size (hminSize E fan computes)
  refine ⟨E, fan, heq, computes, normal, back, count, ?_, leastNot⟩
  intro D dFan dComputes
  rw [heq]
  apply hminSize D dFan
  intro x
  exact (dComputes x).trans (computes x)

lemma exists_minimum_size_then_not (n : ℕ) (C : Circuit) (hfan : FanInTwo C) :
    ∃ D : Circuit, FanInTwo D ∧ D.size ≤ C.size ∧
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) ∧
      (∀ E : Circuit, FanInTwo E →
        (∀ x : Fin n → Bool, E.eval (List.ofFn x) = D.eval (List.ofFn x)) → D.size ≤ E.size) ∧
      ∀ E : Circuit, FanInTwo E → E.size ≤ D.size →
        (∀ x : Fin n → Bool, E.eval (List.ofFn x) = D.eval (List.ofFn x)) →
        PEqualNP.NotBracket.notCount D ≤ PEqualNP.NotBracket.notCount E := by
  classical
  let sizeGood (s : ℕ) : Prop := ∃ E : Circuit, FanInTwo E ∧ E.size = s ∧
    ∀ x : Fin n → Bool, E.eval (List.ofFn x) = C.eval (List.ofFn x)
  have hasSize : ∃ s, sizeGood s := ⟨C.size, C, hfan, rfl, fun _ => rfl⟩
  obtain ⟨A, aFan, aSize, aCorrect⟩ := Nat.find_spec hasSize
  have leastSize (E : Circuit) (eFan : FanInTwo E)
      (eCorrect : ∀ x : Fin n → Bool, E.eval (List.ofFn x) = C.eval (List.ofFn x)) :
      A.size ≤ E.size := by
    rw [aSize]
    exact Nat.find_min' hasSize ⟨E, eFan, rfl, eCorrect⟩
  let notGood (k : ℕ) : Prop := ∃ E : Circuit, FanInTwo E ∧ E.size ≤ A.size ∧
    (∀ x : Fin n → Bool, E.eval (List.ofFn x) = C.eval (List.ofFn x)) ∧
    PEqualNP.NotBracket.notCount E = k
  have hasNot : ∃ k, notGood k :=
    ⟨PEqualNP.NotBracket.notCount A, A, aFan, le_rfl, aCorrect, rfl⟩
  obtain ⟨D, dFan, dBound, dCorrect, dCount⟩ := Nat.find_spec hasNot
  have dSize : D.size = A.size := Nat.le_antisymm dBound (leastSize D dFan dCorrect)
  refine ⟨D, dFan, dBound.trans (leastSize C hfan (fun _ => rfl)), dCorrect, ?_, ?_⟩
  · intro E eFan eCorrect
    rw [dSize]
    exact leastSize E eFan (fun x => (eCorrect x).trans (dCorrect x))
  · intro E eFan eSize eCorrect
    rw [dCount]
    exact Nat.find_min' hasNot ⟨E, eFan, eSize.trans dBound,
      (fun x => (eCorrect x).trans (dCorrect x)), rfl⟩

lemma exists_strict_lex_minimum (n : ℕ) (C : Circuit) (hfan : FanInTwo C)
    (hnc : ∃ x y : Fin n → Bool, C.eval (List.ofFn x) ≠ C.eval (List.ofFn y)) :
    ∃ E : Circuit, FanInTwo E ∧ E.size ≤ C.size ∧
      (∀ x : Fin n → Bool, E.eval (List.ofFn x) = C.eval (List.ofFn x)) ∧
      (∀ g ∈ E.gates, g.op = GateOp.not → g.inputs.length ≤ 1) ∧
      (∀ j g, E.gates[j]? = some g → ∀ i ∈ g.inputs, i < n + j) ∧
      (∀ D : Circuit, FanInTwo D →
        (∀ x : Fin n → Bool, D.eval (List.ofFn x) = E.eval (List.ofFn x)) → E.size ≤ D.size) ∧
      ∀ D : Circuit, FanInTwo D → D.size ≤ E.size →
        (∀ x : Fin n → Bool, D.eval (List.ofFn x) = E.eval (List.ofFn x)) →
        PEqualNP.NotBracket.notCount E ≤ PEqualNP.NotBracket.notCount D := by
  obtain ⟨D, dFan, dBound, dCorrect, dLeastSize, dLeastNot⟩ := exists_minimum_size_then_not n C hfan
  have dNonconstant : ∃ x y : Fin n → Bool, D.eval (List.ofFn x) ≠ D.eval (List.ofFn y) := by
    obtain ⟨x, y, hxy⟩ := hnc
    refine ⟨x, y, ?_⟩
    simpa only [dCorrect] using hxy
  obtain ⟨E, eFan, eSize, eCorrect, eNormal, eBack, _, eLeastSize, eLeastNot⟩ :=
    simultaneous_minimal_strict_equivalent n D.size D dFan le_rfl dNonconstant dLeastSize dLeastNot
  refine ⟨E, eFan, eSize.le.trans dBound, (fun x => (eCorrect x).trans (dCorrect x)),
    eNormal, eBack, eLeastSize, ?_⟩
  intro A aFan aSize aCorrect
  exact eLeastNot A aFan (aSize.trans eSize.le) aCorrect

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma global_gate_value (n : ℕ) (gs : List Gate) (p : Fin gs.length)
    (x : List Bool) (hlen : x.length = n)
    (back : ∀ i ∈ (gs.get p).inputs, i < n + p.val) :
    (wiresFrom gs x).getD (n + p.val) false =
      (gs.get p).op.eval ((gs.get p).inputs.map fun i => (wiresFrom gs x).getD i false) := by
  let w := wiresFrom (gs.take p.val) x
  let b := (gs.get p).op.eval ((gs.get p).inputs.map fun i => w.getD i false)
  have hw : w.length = n + p.val := by
    simp [w, length_wiresFrom, hlen, Nat.le_of_lt p.isLt]
  have hs : wiresFrom gs x = wiresFrom (gs.drop (p.val + 1)) (w ++ [b]) := by
    conv_lhs => rw [gate_decomposition gs p]
    rw [wiresFrom_append]
    rfl
  have hi (i : ℕ) (hlt : i < n + p.val) :
      (wiresFrom gs x).getD i false = w.getD i false := by
    rw [hs, getD_wiresFrom _ _ _ (by simp [hw]; omega)]
    exact List.getD_append _ _ _ _ (by omega)
  have ho : (wiresFrom gs x).getD (n + p.val) false = b := by
    rw [hs, getD_wiresFrom _ _ _ (by simp [hw])]
    exact getD_snoc_len w b false (n + p.val) hw
  rw [ho]
  apply congrArg (gs.get p).op.eval
  apply List.map_congr_left
  intro i hmem
  exact (hi i (back i hmem)).symm

lemma actual_consumer_avoids_raw_input (n : ℕ) (C : Circuit)
    (p q : Fin C.gates.length) (v : ℕ) (hv : v < n) (hpq : p.val < q.val)
    (fan : FanInTwo C)
    (normal : ∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1)
    (back : ∀ j g, C.gates[j]? = some g → ∀ i ∈ g.inputs, i < n + j)
    (pand : (C.gates.get p).op = GateOp.and) (pread : v ∈ (C.gates.get p).inputs)
    (qread : n + p.val ∈ (C.gates.get q).inputs)
    (noalias : ∀ j, j < n + q.val → ¬ ∀ x : Fin n → Bool,
      (C.wires (List.ofFn x)).getD (n + q.val) false = (C.wires (List.ofFn x)).getD j false) :
    v ∉ (C.gates.get q).inputs := by
  apply Consumer.consumer_avoids_raw_input
    (fun (x : Fin n → Bool) i => (C.wires (List.ofFn x)).getD i false)
    (C.gates.get p) (C.gates.get q) n v p.val q.val hv hpq pand pread qread
    (fan _ (List.get_mem _ q)).1 (fan _ (List.get_mem _ q)).2
    (normal _ (List.get_mem _ q))
  · intro x
    exact global_gate_value n C.gates p (List.ofFn x) (by simp)
      (back p.val (C.gates.get p) (by simp))
  · intro x
    exact global_gate_value n C.gates q (List.ofFn x) (by simp)
      (back q.val (C.gates.get q) (by simp))
  · exact noalias

lemma normGate_eq_self (g : Gate) (hn : g.op = GateOp.not → g.inputs.length ≤ 1) :
    normGate g = g := by
  obtain ⟨op, ins⟩ := g
  cases op <;> simp only [normGate]
  rw [List.take_of_length_le (hn rfl)]

lemma normal_map_eq (gs : List Gate)
    (hn : ∀ g ∈ gs, g.op = GateOp.not → g.inputs.length ≤ 1) :
    gs.map normGate = gs := by
  calc
    gs.map normGate = gs.map (fun g => g) :=
      List.map_congr_left (fun g hg => normGate_eq_self g (hn g hg))
    _ = gs := List.map_id' gs

end NandRestriction

namespace Transport

def table : Fin 10 → Fin 10 → Fin 10 := ![
  ![7, 9, 6, 8, 5, 2, 4, 1, 3, 0],
  ![8, 5, 7, 9, 6, 3, 0, 2, 4, 1],
  ![9, 6, 8, 5, 7, 4, 1, 3, 0, 2],
  ![5, 7, 9, 6, 8, 0, 2, 4, 1, 3],
  ![6, 8, 5, 7, 9, 1, 3, 0, 2, 4],
  ![1, 2, 3, 4, 0, 6, 7, 8, 9, 5],
  ![2, 3, 4, 0, 1, 7, 8, 9, 5, 6],
  ![3, 4, 0, 1, 2, 8, 9, 5, 6, 7],
  ![4, 0, 1, 2, 3, 9, 5, 6, 7, 8],
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9]]

def invTable : Fin 10 → Fin 10 → Fin 10 := ![
  ![9, 7, 5, 8, 6, 4, 2, 0, 3, 1],
  ![6, 9, 7, 5, 8, 1, 4, 2, 0, 3],
  ![8, 6, 9, 7, 5, 3, 1, 4, 2, 0],
  ![5, 8, 6, 9, 7, 0, 3, 1, 4, 2],
  ![7, 5, 8, 6, 9, 2, 0, 3, 1, 4],
  ![4, 0, 1, 2, 3, 9, 5, 6, 7, 8],
  ![3, 4, 0, 1, 2, 8, 9, 5, 6, 7],
  ![2, 3, 4, 0, 1, 7, 8, 9, 5, 6],
  ![1, 2, 3, 4, 0, 6, 7, 8, 9, 5],
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9]]

lemma inverse_left : ∀ v i, invTable v (table v i) = i := by decide +kernel
lemma inverse_right : ∀ v i, table v (invTable v i) = i := by decide +kernel

def relabel (v : Fin 10) : Equiv.Perm (Fin 10) where
  toFun := table v
  invFun := invTable v
  left_inv := inverse_left v
  right_inv := inverse_right v

lemma relabel_last : ∀ v, relabel v 9 = v := by decide +kernel

def edge (x : Fin 10 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)

lemma edge_relabel (v : Fin 10) (x : Fin 10 → Bool) :
    edge (x ∘ relabel v) = edge x := by
  fin_cases v <;> simp [edge, relabel, table, Bool.and_comm] <;> ac_rfl

lemma edge_relabel_symm (v : Fin 10) (x : Fin 10 → Bool) :
    edge (x ∘ (relabel v).symm) = edge x := by
  have h := edge_relabel v (x ∘ (relabel v).symm)
  have he : (x ∘ (relabel v).symm) ∘ relabel v = x := by
    funext i
    simp
  rw [he] at h
  exact h.symm

lemma relabel_symm_vertex (v : Fin 10) : (relabel v).symm v = 9 := by
  apply (relabel v).injective
  simp [relabel_last]

def cofactorInput (v : Fin 10) (b : Bool) (y : Fin 9 → Bool) : Fin 10 → Bool :=
  (Fin.lastCases b y) ∘ (relabel v).symm

lemma cofactorInput_at_vertex (v : Fin 10) (b : Bool) (y : Fin 9 → Bool) :
    cofactorInput v b y v = b := by
  change Fin.lastCases b y ((relabel v).symm v) = b
  rw [relabel_symm_vertex]
  exact Fin.lastCases_last

lemma cofactor_false (v : Fin 10) (y : Fin 9 → Bool) :
    edge (cofactorInput v false y) =
      ((y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 3 && y 4) ||
        (y 4 && y 0) || (y 0 && y 5) || (y 1 && y 6) || (y 2 && y 7) ||
        (y 3 && y 8) || (y 5 && y 7) || (y 6 && y 8) || (y 8 && y 5)) := by
  rw [cofactorInput, edge_relabel_symm]
  change ((y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 3 && y 4) ||
        (y 4 && y 0) || (y 0 && y 5) || (y 1 && y 6) || (y 2 && y 7) ||
        (y 3 && y 8) || (y 4 && false) || (y 5 && y 7) || (y 7 && false) ||
        (false && y 6) || (y 6 && y 8) || (y 8 && y 5)) = _
  simp only [Bool.and_false, Bool.false_and, Bool.or_false]

lemma cofactor_true (v : Fin 10) (y : Fin 9 → Bool) :
    edge (cofactorInput v true y) =
      (y 4 || y 6 || y 7 || (y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) ||
        (y 0 && y 5) || (y 3 && y 8) || (y 8 && y 5)) := by
  rw [cofactorInput, edge_relabel_symm]
  change ((y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 3 && y 4) ||
        (y 4 && y 0) || (y 0 && y 5) || (y 1 && y 6) || (y 2 && y 7) ||
        (y 3 && y 8) || (y 4 && true) || (y 5 && y 7) || (y 7 && true) ||
        (true && y 6) || (y 6 && y 8) || (y 8 && y 5)) = _
  cases h4 : y 4 <;> cases h6 : y 6 <;> cases h7 : y 7 <;> simp

lemma cofactorInput_surjective (v : Fin 10) (b : Bool) (x : Fin 10 → Bool)
    (hx : x v = b) : ∃ y : Fin 9 → Bool, cofactorInput v b y = x := by
  let y : Fin 9 → Bool := fun i => x (relabel v i.castSucc)
  have he : (Fin.lastCases b y : Fin 10 → Bool) = x ∘ relabel v := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · change Fin.lastCases b y (Fin.last 9) = x (relabel v 9)
      rw [Fin.lastCases_last, relabel_last]
      exact hx.symm
    · rw [Fin.lastCases_castSucc]
      rfl
  refine ⟨y, ?_⟩
  funext i
  simp only [cofactorInput, he, Function.comp_apply, Equiv.apply_symm_apply]

lemma cofactor_nonconstant (v : Fin 10) (b : Bool) :
    ∃ x y : Fin 10 → Bool,
      x v = b ∧ y v = b ∧ edge x = false ∧ edge y = true := by
  refine ⟨cofactorInput v b (fun _ => false), cofactorInput v b (fun _ => true),
    cofactorInput_at_vertex v b _, cofactorInput_at_vertex v b _, ?_, ?_⟩ <;>
    cases b <;> simp [cofactor_false, cofactor_true]

end Transport

end PEqualNP.Outside.L_meta_2373_aux
