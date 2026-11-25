import PEqualNP.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1479

def BinaryAO (n : ℕ) (C : Circuit) : Prop :=
  ∀ j (g : Gate), C.gates[j]? = some g →
    (g.op = .and ∨ g.op = .or) ∧
      ∃ a b : ℕ, g.inputs = [a,b] ∧ a ≠ b ∧ a < n+j ∧ b < n+j

def binaryGateCheck (n j : ℕ) (g : Gate) : Bool :=
  match g.op, g.inputs with
  | .and, [a,b] => decide (a ≠ b ∧ a < n+j ∧ b < n+j)
  | .or, [a,b] => decide (a ≠ b ∧ a < n+j ∧ b < n+j)
  | _, _ => false

lemma binaryGateCheck_sound {n j : ℕ} {g : Gate}
    (h : binaryGateCheck n j g = true) :
    (g.op = .and ∨ g.op = .or) ∧
      ∃ a b : ℕ, g.inputs = [a,b] ∧ a ≠ b ∧ a < n+j ∧ b < n+j := by
  unfold binaryGateCheck at h
  split at h
  · rename_i a b hop hin
    exact ⟨Or.inl hop,a,b,hin,of_decide_eq_true h⟩
  · rename_i a b hop hin
    exact ⟨Or.inr hop,a,b,hin,of_decide_eq_true h⟩
  · contradiction

lemma binaryAO_of_check {n : ℕ} {C : Circuit}
    (h : ∀ j : Fin C.gates.length, binaryGateCheck n j C.gates[j] = true) :
    BinaryAO n C := by
  intro j g hj
  obtain ⟨hlt,heq⟩ := List.getElem?_eq_some_iff.mp hj
  subst g
  exact binaryGateCheck_sound (h ⟨j,hlt⟩)

def DerivativeTrace (n : ℕ) (C : Circuit) (base seed : Fin n → Bool)
    (d : ℕ → Bool) : Prop :=
  (∀ i : Fin n, d i.val = seed i) ∧
  ∀ j (g : Gate) a b, C.gates[j]? = some g → g.inputs = [a,b] →
    (g.op = .and → d (n+j) =
      (((C.wires (List.ofFn base)).getD a false && d b) ||
        (d a && (C.wires (List.ofFn base)).getD b false))) ∧
    (g.op = .or → d (n+j) = (d a || d b))

lemma derivativeTrace_exists {n : ℕ} {C : Circuit} (normal : BinaryAO n C)
    (base seed : Fin n → Bool) : ∃ d : ℕ → Bool, DerivativeTrace n C base seed d := by
  classical
  let step (m : ℕ) (prev : (i : ℕ) → i < m → Bool) : Bool :=
    if h : m < n then seed ⟨m,h⟩ else
    let g := C.gates[m-n]?.getD ⟨GateOp.or,[]⟩
    let a := g.inputs[0]?.getD 0
    let b := g.inputs[1]?.getD 0
    if ha : a < m then if hb : b < m then
      if g.op = .and then
        ((C.wires (List.ofFn base)).getD a false && prev b hb) ||
          (prev a ha && (C.wires (List.ofFn base)).getD b false)
      else prev a ha || prev b hb
    else false else false
  let d (m : ℕ) : Bool := Nat.strongRecOn m step
  have unfoldD (m : ℕ) : d m = step m (fun i _ => d i) := Nat.strongRecOn_eq step m
  refine ⟨d,?_,?_⟩
  · intro i
    rw [unfoldD]
    simp [step,i.isLt]
  · intro j g a b hj hab
    obtain ⟨_,u,v,huv,_,hu,hv⟩ := normal j g hj
    rw [hab] at huv
    simp only [List.cons.injEq,and_true] at huv
    obtain ⟨rfl,rfl⟩ := huv
    have big : ¬ n+j < n := by omega
    have eqj : n+j-n = j := by omega
    constructor <;> intro hop <;> rw [unfoldD] <;>
      simp [step,big,eqj,hj,hab,hu,hv,hop]

lemma derivativeTrace_dark_and {n : ℕ} {C : Circuit} (normal : BinaryAO n C)
    (base seed : Fin n → Bool) (j a b : ℕ)
    (atGate : C.gates[j]? = some ⟨.and,[a,b]⟩)
    (left : (C.wires (List.ofFn base)).getD a false = false)
    (right : (C.wires (List.ofFn base)).getD b false = false) :
    ∃ d : ℕ → Bool, DerivativeTrace n C base seed d ∧ d (n+j) = false := by
  obtain ⟨d,inputs,gates⟩ := derivativeTrace_exists normal base seed
  refine ⟨d,⟨inputs,gates⟩,?_⟩
  rw [(gates j _ a b atGate rfl).1 rfl,left,right]
  simp

def traceGateCheck (n : ℕ) (C : Circuit) (base : Fin n → Bool)
    (values : List Bool) (j : ℕ) : Bool :=
  let g := C.gates[j]?.getD ⟨.or,[]⟩
  let wires := C.wires (List.ofFn base)
  match g.op, g.inputs with
  | .and, [a,b] => decide (values.getD (n+j) false =
      ((wires.getD a false && values.getD b false) ||
        (values.getD a false && wires.getD b false)))
  | .or, [a,b] => decide (values.getD (n+j) false =
      (values.getD a false || values.getD b false))
  | _, _ => false

lemma derivativeTrace_of_check {n : ℕ} {C : Circuit} {base seed : Fin n → Bool}
    (values : List Bool)
    (inputs : ∀ i : Fin n, values.getD i.val false = seed i)
    (gates : ∀ j : Fin C.gates.length, traceGateCheck n C base values j = true) :
    DerivativeTrace n C base seed (fun i => values.getD i false) := by
  refine ⟨inputs,?_⟩
  intro j g a b hj hab
  obtain ⟨hlt,_⟩ := List.getElem?_eq_some_iff.mp hj
  have h := gates ⟨j,hlt⟩
  change traceGateCheck n C base values j = true at h
  constructor <;> intro hop <;> simpa [traceGateCheck,hj,hab,hop] using h

def fanoIncident (p l : Fin 7) : Prop := p = l ∨ p = l+1 ∨ p = l+3

def fanoHit (x : Fin 14 → Bool) : Prop :=
  ∃ p l : Fin 7, fanoIncident p l ∧
    x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true

def singletonInput {n : ℕ} (a : Fin n) : Fin n → Bool := fun i => decide (i=a)

def pairInputLocal {n : ℕ} (a b : Fin n) : Fin n → Bool :=
  fun i => decide (i=a ∨ i=b)

lemma point_ne_line (p l : Fin 7) : Fin.castAdd 7 p ≠ Fin.natAdd 7 l := by
  intro h
  have hval := congrArg Fin.val h
  change p.val = 7+l.val at hval
  have hp := p.isLt
  omega

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
lemma fano_no_four_cycle (p q l k : Fin 7) :
    fanoIncident p l → fanoIncident p k → fanoIncident q l → fanoIncident q k →
      p=q ∨ l=k := by
  unfold fanoIncident
  decide +revert

lemma fano_pair_iff (a b : Fin 14) :
    fanoHit (pairInputLocal a b) ↔
      ∃ p l : Fin 7, fanoIncident p l ∧
        ((a=Fin.castAdd 7 p ∧ b=Fin.natAdd 7 l) ∨
          (a=Fin.natAdd 7 l ∧ b=Fin.castAdd 7 p)) := by
  constructor
  · rintro ⟨p,l,hpl,hp,hl⟩
    have hp' : Fin.castAdd 7 p=a ∨ Fin.castAdd 7 p=b := of_decide_eq_true hp
    have hl' : Fin.natAdd 7 l=a ∨ Fin.natAdd 7 l=b := of_decide_eq_true hl
    refine ⟨p,l,hpl,?_⟩
    rcases hp' with hp' | hp' <;> rcases hl' with hl' | hl'
    · exact False.elim (point_ne_line p l (hp'.trans hl'.symm))
    · exact Or.inl ⟨hp'.symm,hl'.symm⟩
    · exact Or.inr ⟨hl'.symm,hp'.symm⟩
    · exact False.elim (point_ne_line p l (hp'.trans hl'.symm))
  · rintro ⟨p,l,hpl,h|h⟩
    · rcases h with ⟨rfl,rfl⟩
      exact ⟨p,l,hpl,by simp [pairInputLocal],by simp [pairInputLocal]⟩
    · rcases h with ⟨rfl,rfl⟩
      exact ⟨p,l,hpl,by simp [pairInputLocal],by simp [pairInputLocal]⟩

lemma singleton_le_pair_left {n : ℕ} (a b : Fin n) :
    singletonInput a ≤ pairInputLocal a b := by
  intro i
  by_cases h : i=a
  · simp [singletonInput,pairInputLocal,h]
  · simp [singletonInput,h]

lemma singleton_le_pair_right {n : ℕ} (a b : Fin n) :
    singletonInput b ≤ pairInputLocal a b := by
  intro i
  by_cases h : i=b
  · simp [singletonInput,pairInputLocal,h]
  · simp [singletonInput,h]

lemma final_and_singleton_cross
    (f g : (Fin 14 → Bool) → Bool) (hf : Monotone f) (hg : Monotone g)
    (correct : ∀ x, (f x && g x)=true ↔ fanoHit x)
    (a b : Fin 14) (ha : f (singletonInput a)=true)
    (hb : g (singletonInput b)=true) :
    ∃ p l : Fin 7, fanoIncident p l ∧
      ((a=Fin.castAdd 7 p ∧ b=Fin.natAdd 7 l) ∨
        (a=Fin.natAdd 7 l ∧ b=Fin.castAdd 7 p)) := by
  apply (fano_pair_iff a b).mp
  apply (correct _).mp
  have hfa := hf (singleton_le_pair_left a b)
  have hgb := hg (singleton_le_pair_right a b)
  rw [ha] at hfa
  rw [hb] at hgb
  simp only [Bool.and_eq_true_iff]
  exact ⟨Bool.eq_true_of_true_le hfa,Bool.eq_true_of_true_le hgb⟩

lemma final_and_singleton_disjoint
    (f g : (Fin 14 → Bool) → Bool) (hf : Monotone f) (hg : Monotone g)
    (correct : ∀ x, (f x && g x)=true ↔ fanoHit x)
    (a : Fin 14) : ¬ (f (singletonInput a)=true ∧ g (singletonInput a)=true) := by
  rintro ⟨ha,hb⟩
  obtain ⟨p,l,_,h|h⟩ := final_and_singleton_cross f g hf hg correct a a ha hb
  · exact point_ne_line p l (h.1.symm.trans h.2)
  · exact point_ne_line p l (h.2.symm.trans h.1)


def fanoSumAdjacent : Fin 7 ⊕ Fin 7 → Fin 7 ⊕ Fin 7 → Prop
  | Sum.inl p, Sum.inr l => fanoIncident p l
  | Sum.inr l, Sum.inl p => fanoIncident p l
  | _, _ => False

lemma fano_sum_no_four_cycle (a b c d : Fin 7 ⊕ Fin 7) :
    fanoSumAdjacent a c → fanoSumAdjacent a d →
      fanoSumAdjacent b c → fanoSumAdjacent b d → a=b ∨ c=d := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp only [fanoSumAdjacent,Sum.inl.injEq,Sum.inr.injEq]
  all_goals try tauto
  · exact fano_no_four_cycle _ _ _ _
  · intro hca hda hcb hdb
    exact (fano_no_four_cycle _ _ _ _ hca hcb hda hdb).symm

def fanoAdjacent (a b : Fin 14) : Prop :=
  fanoSumAdjacent (finSumFinEquiv.symm a) (finSumFinEquiv.symm b)

lemma fano_adjacent_no_four_cycle (a b c d : Fin 14)
    (hac : fanoAdjacent a c) (had : fanoAdjacent a d)
    (hbc : fanoAdjacent b c) (hbd : fanoAdjacent b d) : a=b ∨ c=d := by
  rcases fano_sum_no_four_cycle _ _ _ _ hac had hbc hbd with h | h
  · exact Or.inl (finSumFinEquiv.symm.injective h)
  · exact Or.inr (finSumFinEquiv.symm.injective h)

lemma final_and_singleton_adjacent
    (f g : (Fin 14 → Bool) → Bool) (hf : Monotone f) (hg : Monotone g)
    (correct : ∀ x, (f x && g x)=true ↔ fanoHit x)
    (a b : Fin 14) (ha : f (singletonInput a)=true)
    (hb : g (singletonInput b)=true) : fanoAdjacent a b := by
  obtain ⟨p,l,hpl,h|h⟩ := final_and_singleton_cross f g hf hg correct a b ha hb
  · rcases h with ⟨rfl,rfl⟩
    simpa only [fanoAdjacent,finSumFinEquiv_symm_apply_castAdd,
      finSumFinEquiv_symm_apply_natAdd,fanoSumAdjacent] using hpl
  · rcases h with ⟨rfl,rfl⟩
    simpa only [fanoAdjacent,finSumFinEquiv_symm_apply_castAdd,
      finSumFinEquiv_symm_apply_natAdd,fanoSumAdjacent] using hpl

lemma final_and_singleton_support_thin
    (f g : (Fin 14 → Bool) → Bool) (hf : Monotone f) (hg : Monotone g)
    (correct : ∀ x, (f x && g x)=true ↔ fanoHit x) :
    {a : Fin 14 | f (singletonInput a)=true}.Subsingleton ∨
      {b : Fin 14 | g (singletonInput b)=true}.Subsingleton := by
  classical
  by_cases h : ∃ a b : Fin 14,
      f (singletonInput a)=true ∧ f (singletonInput b)=true ∧ a≠b
  · obtain ⟨a,b,ha,hb,hab⟩ := h
    right
    intro c hc d hd
    exact (fano_adjacent_no_four_cycle a b c d
      (final_and_singleton_adjacent f g hf hg correct a c ha hc)
      (final_and_singleton_adjacent f g hf hg correct a d ha hd)
      (final_and_singleton_adjacent f g hf hg correct b c hb hc)
      (final_and_singleton_adjacent f g hf hg correct b d hb hd)).resolve_left hab
  · left
    intro a ha b hb
    by_contra hab
    exact h ⟨a,b,ha,hb,hab⟩

def baseline : Circuit := ⟨[
  ⟨.or,[0,1]⟩,
  ⟨.or,[14,3]⟩,
  ⟨.and,[15,7]⟩,
  ⟨.or,[1,2]⟩,
  ⟨.or,[17,4]⟩,
  ⟨.and,[18,8]⟩,
  ⟨.or,[2,3]⟩,
  ⟨.or,[20,5]⟩,
  ⟨.and,[21,9]⟩,
  ⟨.or,[3,4]⟩,
  ⟨.or,[23,6]⟩,
  ⟨.and,[24,10]⟩,
  ⟨.or,[4,5]⟩,
  ⟨.or,[26,0]⟩,
  ⟨.and,[27,11]⟩,
  ⟨.or,[5,6]⟩,
  ⟨.or,[29,1]⟩,
  ⟨.and,[30,12]⟩,
  ⟨.or,[6,0]⟩,
  ⟨.or,[32,2]⟩,
  ⟨.and,[33,13]⟩,
  ⟨.or,[16,19]⟩,
  ⟨.or,[35,22]⟩,
  ⟨.or,[36,25]⟩,
  ⟨.or,[37,28]⟩,
  ⟨.or,[38,31]⟩,
  ⟨.or,[39,34]⟩], 40⟩

def baselineFormula (x : Fin 14 → Bool) : Bool :=
  ((x 0 || x 1 || x 3) && x 7) ||
  ((x 1 || x 2 || x 4) && x 8) ||
  ((x 2 || x 3 || x 5) && x 9) ||
  ((x 3 || x 4 || x 6) && x 10) ||
  ((x 4 || x 5 || x 0) && x 11) ||
  ((x 5 || x 6 || x 1) && x 12) ||
  ((x 6 || x 0 || x 2) && x 13)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
lemma baseline_eval_formula (x : Fin 14 → Bool) :
    baseline.eval (List.ofFn x) = baselineFormula x := by
  simp [baseline,baselineFormula,Circuit.eval,Circuit.wires,GateOp.eval,List.ofFn_succ]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
lemma baseline_formula_spec (x : Fin 14 → Bool) :
    baselineFormula x = true ↔ ∃ u t : Fin 7,
      (u = t ∨ u = t + 1 ∨ u = t + 3) ∧
        x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true := by
  constructor
  · intro h
    simp only [baselineFormula,Bool.or_eq_true,Bool.and_eq_true,or_assoc] at h
    rcases h with h | h | h | h | h | h | h
    · rcases h with ⟨hp | hp | hp,hl⟩
      · exact ⟨0,0,by decide,hp,hl⟩
      · exact ⟨1,0,by decide,hp,hl⟩
      · exact ⟨3,0,by decide,hp,hl⟩
    · rcases h with ⟨hp | hp | hp,hl⟩
      · exact ⟨1,1,by decide,hp,hl⟩
      · exact ⟨2,1,by decide,hp,hl⟩
      · exact ⟨4,1,by decide,hp,hl⟩
    · rcases h with ⟨hp | hp | hp,hl⟩
      · exact ⟨2,2,by decide,hp,hl⟩
      · exact ⟨3,2,by decide,hp,hl⟩
      · exact ⟨5,2,by decide,hp,hl⟩
    · rcases h with ⟨hp | hp | hp,hl⟩
      · exact ⟨3,3,by decide,hp,hl⟩
      · exact ⟨4,3,by decide,hp,hl⟩
      · exact ⟨6,3,by decide,hp,hl⟩
    · rcases h with ⟨hp | hp | hp,hl⟩
      · exact ⟨4,4,by decide,hp,hl⟩
      · exact ⟨5,4,by decide,hp,hl⟩
      · exact ⟨0,4,by decide,hp,hl⟩
    · rcases h with ⟨hp | hp | hp,hl⟩
      · exact ⟨5,5,by decide,hp,hl⟩
      · exact ⟨6,5,by decide,hp,hl⟩
      · exact ⟨1,5,by decide,hp,hl⟩
    · rcases h with ⟨hp | hp | hp,hl⟩
      · exact ⟨6,6,by decide,hp,hl⟩
      · exact ⟨0,6,by decide,hp,hl⟩
      · exact ⟨2,6,by decide,hp,hl⟩
  · rintro ⟨u,t,hinc,hp,hl⟩
    fin_cases u <;> fin_cases t <;> norm_num at hinc
    all_goals simp_all [baselineFormula]

lemma baseline_correct (x : Fin 14 → Bool) :
    baseline.eval (List.ofFn x) = true ↔ ∃ u t : Fin 7,
      (u = t ∨ u = t + 1 ∨ u = t + 3) ∧
        x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true := by
  rw [baseline_eval_formula]
  exact baseline_formula_spec x

def fanoNeighborSet (s : Finset (Fin 7)) : Finset (Fin 7) :=
  Finset.univ.filter fun l => ∃ p ∈ s, p = l ∨ p = l + 1 ∨ p = l + 3

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
lemma fano_strict_hall : ∀ s : Finset (Fin 7),
    s.Nonempty → s ≠ Finset.univ → s.card < (fanoNeighborSet s).card := by
  decide

def nearCircuit : Circuit := ⟨[
  ⟨.or,[8,7]⟩,
  ⟨.or,[14,12]⟩,
  ⟨.and,[1,15]⟩,
  ⟨.or,[9,8]⟩,
  ⟨.or,[17,13]⟩,
  ⟨.and,[2,18]⟩,
  ⟨.or,[10,9]⟩,
  ⟨.or,[20,7]⟩,
  ⟨.and,[3,21]⟩,
  ⟨.or,[11,10]⟩,
  ⟨.or,[23,8]⟩,
  ⟨.and,[4,24]⟩,
  ⟨.or,[12,11]⟩,
  ⟨.or,[26,9]⟩,
  ⟨.and,[5,27]⟩,
  ⟨.or,[13,12]⟩,
  ⟨.or,[29,10]⟩,
  ⟨.and,[6,30]⟩,
  ⟨.or,[16,19]⟩,
  ⟨.or,[32,22]⟩,
  ⟨.or,[33,25]⟩,
  ⟨.or,[34,28]⟩,
  ⟨.or,[35,31]⟩,
  ⟨.or,[7,11]⟩,
  ⟨.or,[37,13]⟩,
  ⟨.or,[36,0]⟩,
  ⟨.or,[36,38]⟩,
  ⟨.and,[39,40]⟩], 41⟩

def nearH (x : Fin 14 → Bool) : Bool :=
  (x 1 && (x 8 || x 7 || x 12)) ||
  (x 2 && (x 9 || x 8 || x 13)) ||
  (x 3 && (x 10 || x 9 || x 7)) ||
  (x 4 && (x 11 || x 10 || x 8)) ||
  (x 5 && (x 12 || x 11 || x 9)) ||
  (x 6 && (x 13 || x 12 || x 10))

def nearN (x : Fin 14 → Bool) : Bool := x 7 || x 11 || x 13

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
lemma near_eval_formula (x : Fin 14 → Bool) :
    nearCircuit.eval (List.ofFn x) = ((nearH x || x 0) && (nearH x || nearN x)) := by
  simp [nearCircuit,nearH,nearN,Circuit.eval,Circuit.wires,GateOp.eval,List.ofFn_succ]

lemma near_normal : BinaryAO 14 nearCircuit := by
  apply binaryAO_of_check
  decide

lemma bool_absorption (a b c : Bool) : ((a || b) && (a || c)) = (a || (b && c)) := by
  cases a <;> cases b <;> cases c <;> rfl

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
lemma near_formula_spec (x : Fin 14 → Bool) :
    (nearH x || (x 0 && nearN x)) = true ↔ ∃ u t : Fin 7,
      (u = t ∨ u = t + 1 ∨ u = t + 3) ∧
        x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true := by
  constructor
  · intro h
    simp only [nearH,nearN,Bool.or_eq_true,Bool.and_eq_true,or_assoc] at h
    rcases h with h | h | h | h | h | h | h
    · rcases h with ⟨hp,hl | hl | hl⟩
      · exact ⟨1,1,by decide,hp,hl⟩
      · exact ⟨1,0,by decide,hp,hl⟩
      · exact ⟨1,5,by decide,hp,hl⟩
    · rcases h with ⟨hp,hl | hl | hl⟩
      · exact ⟨2,2,by decide,hp,hl⟩
      · exact ⟨2,1,by decide,hp,hl⟩
      · exact ⟨2,6,by decide,hp,hl⟩
    · rcases h with ⟨hp,hl | hl | hl⟩
      · exact ⟨3,3,by decide,hp,hl⟩
      · exact ⟨3,2,by decide,hp,hl⟩
      · exact ⟨3,0,by decide,hp,hl⟩
    · rcases h with ⟨hp,hl | hl | hl⟩
      · exact ⟨4,4,by decide,hp,hl⟩
      · exact ⟨4,3,by decide,hp,hl⟩
      · exact ⟨4,1,by decide,hp,hl⟩
    · rcases h with ⟨hp,hl | hl | hl⟩
      · exact ⟨5,5,by decide,hp,hl⟩
      · exact ⟨5,4,by decide,hp,hl⟩
      · exact ⟨5,2,by decide,hp,hl⟩
    · rcases h with ⟨hp,hl | hl | hl⟩
      · exact ⟨6,6,by decide,hp,hl⟩
      · exact ⟨6,5,by decide,hp,hl⟩
      · exact ⟨6,3,by decide,hp,hl⟩
    · rcases h with ⟨hp,hl | hl | hl⟩
      · exact ⟨0,0,by decide,hp,hl⟩
      · exact ⟨0,4,by decide,hp,hl⟩
      · exact ⟨0,6,by decide,hp,hl⟩
  · rintro ⟨u,t,hinc,hp,hl⟩
    fin_cases u <;> fin_cases t <;> norm_num at hinc
    all_goals simp_all [nearH,nearN]

lemma near_correct (x : Fin 14 → Bool) :
    nearCircuit.eval (List.ofFn x) = true ↔ ∃ u t : Fin 7,
      (u = t ∨ u = t + 1 ∨ u = t + 3) ∧
        x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true := by
  rw [near_eval_formula,bool_absorption]
  exact near_formula_spec x

lemma relaxed_28 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, C.size ≤ 28 ∧ (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j) ∧ (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧ x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true) ∧ ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧ (∃ v : ℕ → Bool, (∀ my : Fin 7, v my.val = false ∧ v (7 + my.val) = decide (my = l)) ∧ (∀ (ky : ℕ) (hy : PEqualNP.CircuitLowerBounds.Gate) (cy dy : ℕ), C.gates[ky]? = some hy → hy.inputs = [cy, dy] → (hy.op = PEqualNP.CircuitLowerBounds.GateOp.and → v (14 + ky) = (((C.wires (List.ofFn (fun iy : Fin 14 => decide (iy = Fin.castAdd 7 p)))).getD cy false && v dy) || (v cy && (C.wires (List.ofFn (fun ey : Fin 14 => decide (ey = Fin.castAdd 7 p)))).getD dy false))) ∧ (hy.op = PEqualNP.CircuitLowerBounds.GateOp.or → v (14 + ky) = (v cy || v dy))) ∧ v C.output = false) ∧ (∃ w : ℕ → Bool, (∀ mx : Fin 7, w mx.val = decide (mx = p) ∧ w (7 + mx.val) = false) ∧ (∀ (kx : ℕ) (hx : PEqualNP.CircuitLowerBounds.Gate) (cx dx : ℕ), C.gates[kx]? = some hx → hx.inputs = [cx, dx] → (hx.op = PEqualNP.CircuitLowerBounds.GateOp.and → w (14 + kx) = (((C.wires (List.ofFn (fun ix : Fin 14 => decide (ix = Fin.natAdd 7 l)))).getD cx false && w dx) || (w cx && (C.wires (List.ofFn (fun ex : Fin 14 => decide (ex = Fin.natAdd 7 l)))).getD dx false))) ∧ (hx.op = PEqualNP.CircuitLowerBounds.GateOp.or → w (14 + kx) = (w cx || w dx))) ∧ w C.output = false) := by
  refine ⟨nearCircuit,by decide,near_normal,near_correct,1,1,Or.inl rfl,?_,?_⟩
  · obtain ⟨d,hd,hout⟩ := derivativeTrace_dark_and near_normal
      (fun i : Fin 14 => decide (i = Fin.castAdd 7 (1 : Fin 7)))
      (fun i : Fin 14 => decide (i = Fin.natAdd 7 (1 : Fin 7)))
      27 39 40 (by rfl) (by decide) (by decide)
    refine ⟨d,?_,hd.2,hout⟩
    intro m
    exact ⟨(hd.1 (Fin.castAdd 7 m)).trans (by fin_cases m <;> decide),
      (hd.1 (Fin.natAdd 7 m)).trans (by fin_cases m <;> decide)⟩
  · obtain ⟨d,hd,hout⟩ := derivativeTrace_dark_and near_normal
      (fun i : Fin 14 => decide (i = Fin.natAdd 7 (1 : Fin 7)))
      (fun i : Fin 14 => decide (i = Fin.castAdd 7 (1 : Fin 7)))
      27 39 40 (by rfl) (by decide) (by decide)
    refine ⟨d,?_,hd.2,hout⟩
    intro m
    exact ⟨(hd.1 (Fin.castAdd 7 m)).trans (by fin_cases m <;> decide),
      (hd.1 (Fin.natAdd 7 m)).trans (by fin_cases m <;> decide)⟩

lemma baseline_size : baseline.size = 27 := rfl

lemma baseline_normal : BinaryAO 14 baseline := by
  apply binaryAO_of_check
  decide

end PEqualNP.Outside.L_meta_1479
