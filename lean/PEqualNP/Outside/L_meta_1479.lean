import PEqualNP.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Data.Fintype.Card

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

lemma fano_cover_seven (a b : Finset (Fin 7))
    (cover : ∀ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) → p ∈ a ∨ l ∈ b)
    (bound : a.card + b.card ≤ 7) :
    (a = Finset.univ ∧ b = ∅) ∨ (a = ∅ ∧ b = Finset.univ) := by
  classical
  by_cases ha : a = Finset.univ
  · left
    refine ⟨ha,Finset.card_eq_zero.mp ?_⟩
    subst a
    simp only [Finset.card_univ,Fintype.card_fin] at bound
    omega
  by_cases hz : a = ∅
  · right
    refine ⟨hz,Finset.eq_univ_of_forall ?_⟩
    intro l
    have h := cover l l (Or.inl rfl)
    simpa [hz] using h
  have hne : (aᶜ).Nonempty := by
    by_contra h
    apply ha
    apply Finset.eq_univ_of_forall
    intro p
    by_contra hp
    exact h ⟨p,Finset.mem_compl.mpr hp⟩
  have hproper : aᶜ ≠ Finset.univ := by
    intro h
    apply hz
    apply Finset.ext
    intro p
    simp
    intro hp
    have hc : p ∈ aᶜ := by rw [h]; exact Finset.mem_univ p
    exact (Finset.mem_compl.mp hc) hp
  have hstrict := fano_strict_hall aᶜ hne hproper
  have hsub : fanoNeighborSet aᶜ ⊆ b := by
    intro l hl
    simp only [fanoNeighborSet,Finset.mem_filter,Finset.mem_univ,true_and] at hl
    obtain ⟨p,hp,he⟩ := hl
    exact (cover p l he).resolve_left (Finset.mem_compl.mp hp)
  have hn := Finset.card_le_card hsub
  have hacard : a.card ≤ 7 := by simpa using Finset.card_le_univ a
  have hcomp : (aᶜ).card = 7 - a.card := by rw [Finset.card_compl]; rfl
  omega

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

lemma binaryAO_eval_mono {n : ℕ} {C : Circuit} (normal : BinaryAO n C)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) :
    C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true := by
  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w
  have hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      ∃ a b : ℕ, g.inputs = [a,b] := by
    intro g hg
    obtain ⟨j,hj,he⟩ := List.mem_iff_getElem.mp hg
    obtain ⟨ho,a,b,hab,_,_,_⟩ := normal j g (List.getElem?_eq_some_iff.mpr ⟨hj,he⟩)
    exact ⟨ho,a,b,hab⟩
  have stepMono (u v : List Bool) (g : Gate)
      (hg : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a,b])
      (hlen : u.length = v.length)
      (h : ∀ i, u.getD i false = true → v.getD i false = true) :
      ∀ i, (step u g).getD i false = true → (step v g).getD i false = true := by
    intro i hi
    by_cases hlt : i < u.length
    · change (u ++ [_]).getD i false = true at hi
      change (v ++ [_]).getD i false = true
      rw [List.getD_append _ _ _ _ hlt] at hi
      rw [List.getD_append _ _ _ _ (by omega)]
      exact h i hi
    · change (u ++ [_]).getD i false = true at hi
      change (v ++ [_]).getD i false = true
      rw [List.getD_append_right _ _ _ _ (by omega)] at hi
      rw [List.getD_append_right _ _ _ _ (by omega), ← hlen]
      by_cases hz : i-u.length = 0
      · simp only [hz, List.getD_cons_zero] at hi ⊢
        obtain ⟨ho,a,b,hab⟩ := hg
        rcases ho with ho | ho
        · rw [ho, hab] at hi ⊢
          change ([u.getD a false, u.getD b false].all id) = true at hi
          change ([v.getD a false, v.getD b false].all id) = true
          simp only [List.all_cons, List.all_nil, Bool.and_true, id_eq, Bool.and_eq_true] at hi ⊢
          exact ⟨h a hi.1, h b hi.2⟩
        · rw [ho, hab] at hi ⊢
          change ([u.getD a false, u.getD b false].any id) = true at hi
          change ([v.getD a false, v.getD b false].any id) = true
          simp only [List.any_cons, List.any_nil, Bool.or_false, id_eq, Bool.or_eq_true] at hi ⊢
          exact hi.elim (fun ha => Or.inl (h a ha)) (fun hb => Or.inr (h b hb))
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
        contradiction
  have runMono : ∀ gs : List Gate,
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a,b]) →
      ∀ (u v : List Bool), u.length = v.length →
      (∀ i, u.getD i false = true → v.getD i false = true) →
      ∀ i, (run gs u).getD i false = true → (run gs v).getD i false = true := by
    intro gs
    induction gs with
    | nil => intro hg u v hlen h i hi; exact h i hi
    | cons g gs ih =>
      intro hg u v hlen h i hi
      change (run gs (step u g)).getD i false = true at hi
      change (run gs (step v g)).getD i false = true
      exact ih (fun k hk => hg k (by simp [hk])) _ _
        (by simp [step, hlen]) (stepMono u v g (hg g (by simp)) hlen h) i hi
  have evalMono (x y : Fin n → Bool) (h : ∀ i, x i = true → y i = true) :
      C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true := by
    apply runMono C.gates hG _ _ (by simp) ?_ C.output
    intro i hi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hi ⊢
    split at hi
    · rename_i hlt
      simp [hlt] at hi ⊢
      exact h _ hi
    · simp at hi
  exact evalMono x y hxy

lemma binaryAO_monotone {n : ℕ} {C : Circuit} (normal : BinaryAO n C) :
    Monotone (fun x : Fin n → Bool => C.eval (List.ofFn x)) := by
  intro x y hxy
  have imp := binaryAO_eval_mono normal x y (fun i hi => by
    have h := hxy i
    rw [hi] at h
    exact Bool.eq_true_of_true_le h)
  cases hx : C.eval (List.ofFn x) <;> cases hy : C.eval (List.ofFn y) <;> simp_all


def boundaryFanoHit (x : Fin 14 → Bool) : Prop :=
  ∃ u t : Fin 7, (u = t ∨ u = t+1 ∨ u = t+3) ∧
    x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true

def bitRow (mask : ℕ) (i : Fin 14) : Bool := mask.testBit i.val

def positiveMasks : List ℕ := [129, 130, 136, 258, 260, 272, 516, 520, 544, 1032, 1040, 1088, 2064, 2080, 2049, 4128, 4160, 4098, 8256, 8193, 8196]

def negativeMasks : List ℕ := [127, 244, 361, 480, 595, 720, 833, 1063, 1188, 1313, 1539, 2126, 2244, 2376, 2626, 3008, 3078, 4125, 4244, 4361, 4625, 5125, 5889, 6156, 7300, 8250, 8368, 8488, 8722, 9250, 9632, 10250, 11778, 12312, 12944, 14600, 16256]

def allowedLine (points : Fin 7 → Bool) (t : Fin 7) : Bool :=
  !(points t || points (t+1) || points (t+3))

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma positiveMasks_cover : ∀ u t : Fin 7, (u = t ∨ u = t+1 ∨ u = t+3) →
    ∃ m ∈ positiveMasks, ∀ i : Fin 14,
      bitRow m i = decide (i = Fin.castAdd 7 u ∨ i = Fin.natAdd 7 t) := by
  decide

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma negativeMasks_cover : ∀ points : Fin 7 → Bool,
    ∃ m ∈ negativeMasks,
      (∀ u : Fin 7, points u = true → bitRow m (Fin.castAdd 7 u) = true) ∧
      (∀ t : Fin 7, allowedLine points t = true → bitRow m (Fin.natAdd 7 t) = true) := by
  decide

lemma boundary_correct {C : Circuit} (normal : BinaryAO 14 C)
    (positive : ∀ m ∈ positiveMasks, C.eval (List.ofFn (bitRow m)) = true)
    (negative : ∀ m ∈ negativeMasks, C.eval (List.ofFn (bitRow m)) = false) :
    ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ boundaryFanoHit x := by
  intro x
  constructor
  · intro yes
    by_contra nohit
    obtain ⟨m,hm,hpoints,hlines⟩ := negativeMasks_cover
      (fun u => x (Fin.castAdd 7 u))
    have below : ∀ i, x i = true → bitRow m i = true := by
      refine Fin.addCases (m := 7) (n := 7) ?_ ?_
      · intro u hu
        exact hpoints u hu
      · intro t ht
        apply hlines t
        have off (u : Fin 7) (hinc : u = t ∨ u = t+1 ∨ u = t+3) :
            x (Fin.castAdd 7 u) = false := by
          cases h : x (Fin.castAdd 7 u) with
          | false => rfl
          | true => exact False.elim (nohit ⟨u,t,hinc,h,ht⟩)
        simp [allowedLine,off t (Or.inl rfl),
          off (t+1) (Or.inr (Or.inl rfl)),off (t+3) (Or.inr (Or.inr rfl))]
    have bad := binaryAO_eval_mono normal x (bitRow m) below yes
    rw [negative m hm] at bad
    contradiction
  · rintro ⟨u,t,hinc,hpoint,hline⟩
    obtain ⟨m,hm,hrow⟩ := positiveMasks_cover u t hinc
    apply binaryAO_eval_mono normal (bitRow m) x ?_ (positive m hm)
    intro i hi
    rw [hrow i] at hi
    rcases of_decide_eq_true hi with rfl | rfl
    · exact hpoint
    · exact hline

lemma boundary_correct_of_checks {C : Circuit} (normal : BinaryAO 14 C)
    (positive : positiveMasks.all (fun m => C.eval (List.ofFn (bitRow m))) = true)
    (negative : negativeMasks.all (fun m => !(C.eval (List.ofFn (bitRow m)))) = true) :
    ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ boundaryFanoHit x := by
  apply boundary_correct normal
  · exact List.all_eq_true.mp positive
  · intro m hm
    have h := List.all_eq_true.mp negative m hm
    cases hc : C.eval (List.ofFn (bitRow m)) <;> simp_all

lemma positiveMasks_valid : ∀ m ∈ positiveMasks, boundaryFanoHit (bitRow m) := by
  let : DecidablePred boundaryFanoHit := fun x => by unfold boundaryFanoHit; infer_instance
  have checks : positiveMasks.all (fun m => decide (boundaryFanoHit (bitRow m))) = true := by decide
  intro m hm
  exact of_decide_eq_true (List.all_eq_true.mp checks m hm)

lemma negativeMasks_valid : ∀ m ∈ negativeMasks, ¬ boundaryFanoHit (bitRow m) := by
  let : DecidablePred boundaryFanoHit := fun x => by unfold boundaryFanoHit; infer_instance
  have checks : negativeMasks.all (fun m => decide (¬ boundaryFanoHit (bitRow m))) = true := by decide
  intro m hm
  exact of_decide_eq_true (List.all_eq_true.mp checks m hm)

def supportWireStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma support_run_extends (gs : List Gate) (w : List Bool) :
    ∃ t : List Bool, gs.foldl supportWireStep w = w++t ∧ t.length=gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[],by simp,rfl⟩
  | cons g gs ih =>
    obtain ⟨t,ht,hlen⟩ := ih (supportWireStep w g)
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false)::t,?_,?_⟩
    · simpa [supportWireStep,List.append_assoc] using ht
    · simp [hlen]

lemma support_wire_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    (C.wires (List.ofFn x)).getD i.val false = x i := by
  obtain ⟨t,ht,_⟩ := support_run_extends C.gates (List.ofFn x)
  change (C.gates.foldl supportWireStep (List.ofFn x)).getD i.val false = _
  rw [ht,List.getD_append _ _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD]

lemma support_wire_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool)
    (j : ℕ) (g : Gate) (a b : ℕ) (hj : C.gates[j]?=some g)
    (hab : g.inputs=[a,b]) (ha : a<n+j) (hb : b<n+j) :
    (C.wires (List.ofFn x)).getD (n+j) false =
      g.op.eval [(C.wires (List.ofFn x)).getD a false,
        (C.wires (List.ofFn x)).getD b false] := by
  have hlt := (List.getElem?_eq_some_iff.mp hj).1
  have split : C.gates = C.gates.take j ++ g :: C.gates.drop (j+1) := by
    have h := List.take_append_drop j C.gates
    rw [List.drop_eq_getElem?_toList_append,hj] at h
    simpa using h.symm
  let pre := (C.gates.take j).foldl supportWireStep (List.ofFn x)
  have plen : pre.length=n+j := by
    obtain ⟨t,ht,hlen⟩ := support_run_extends (C.gates.take j) (List.ofFn x)
    change ((C.gates.take j).foldl supportWireStep (List.ofFn x)).length=n+j
    rw [ht,List.length_append,List.length_ofFn,hlen,List.length_take]
    omega
  obtain ⟨t,ht,_⟩ := support_run_extends (C.gates.drop (j+1)) (supportWireStep pre g)
  have full : C.wires (List.ofFn x) =
      pre ++ g.op.eval (g.inputs.map fun i => pre.getD i false)::t := by
    change C.gates.foldl supportWireStep (List.ofFn x) = _
    rw [split,List.foldl_append,List.foldl_cons]
    simpa [pre,supportWireStep,List.append_assoc] using ht
  have preserve (i : ℕ) (hi : i<n+j) :
      (C.wires (List.ofFn x)).getD i false = pre.getD i false := by
    rw [full,List.getD_append _ _ _ _ (by omega)]
  rw [preserve a ha,preserve b hb,full]
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp [plen,hab]

lemma derivative_support_of_bounds {n : ℕ} {C : Circuit}
    (normal : BinaryAO n C) (base seed target : Fin n → Bool) (d : ℕ → Bool)
    (trace : DerivativeTrace n C base seed d)
    (hbase : ∀ i, base i=true → target i=true)
    (hseed : ∀ i, seed i=true → target i=true) :
    ∀ w, w<n+C.gates.length →
      ((C.wires (List.ofFn base)).getD w false=true →
        (C.wires (List.ofFn target)).getD w false=true) ∧
      (d w=true → (C.wires (List.ofFn target)).getD w false=true) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hin : w<n
    · rw [support_wire_input C base ⟨w,hin⟩,
        support_wire_input C target ⟨w,hin⟩,trace.1 ⟨w,hin⟩]
      exact ⟨hbase _,hseed _⟩
    · have hj : w-n<C.gates.length := by omega
      let g : Gate := C.gates[w-n]
      have hget : C.gates[w-n]?=some g :=
        List.getElem?_eq_some_iff.mpr ⟨hj,rfl⟩
      obtain ⟨hop,a,b,hab,_,ha,hb⟩ := normal (w-n) g hget
      have heq : n+(w-n)=w := by omega
      have ia := ih a (by omega) (by omega)
      have ib := ih b (by omega) (by omega)
      have bv := support_wire_gate C base (w-n) g a b hget hab ha hb
      have tv := support_wire_gate C target (w-n) g a b hget hab ha hb
      have dv := trace.2 (w-n) g a b hget hab
      rcases hop with hop | hop
      · have bv' : (C.wires (List.ofFn base)).getD w false =
            ((C.wires (List.ofFn base)).getD a false &&
              (C.wires (List.ofFn base)).getD b false) := by
          simpa [heq,hop,GateOp.eval] using bv
        have tv' : (C.wires (List.ofFn target)).getD w false =
            ((C.wires (List.ofFn target)).getD a false &&
              (C.wires (List.ofFn target)).getD b false) := by
          simpa [heq,hop,GateOp.eval] using tv
        have dv' : d w =
            (((C.wires (List.ofFn base)).getD a false && d b) ||
              (d a && (C.wires (List.ofFn base)).getD b false)) := by
          simpa [heq] using dv.1 hop
        rw [bv',tv',dv']
        simp only [Bool.and_eq_true_iff,Bool.or_eq_true_iff]
        constructor
        · intro h
          exact ⟨ia.1 h.1,ib.1 h.2⟩
        · rintro (h|h)
          · exact ⟨ia.1 h.1,ib.2 h.2⟩
          · exact ⟨ia.2 h.1,ib.1 h.2⟩
      · have bv' : (C.wires (List.ofFn base)).getD w false =
            ((C.wires (List.ofFn base)).getD a false ||
              (C.wires (List.ofFn base)).getD b false) := by
          simpa [heq,hop,GateOp.eval] using bv
        have tv' : (C.wires (List.ofFn target)).getD w false =
            ((C.wires (List.ofFn target)).getD a false ||
              (C.wires (List.ofFn target)).getD b false) := by
          simpa [heq,hop,GateOp.eval] using tv
        have dv' : d w=(d a || d b) := by simpa [heq] using dv.2 hop
        rw [bv',tv',dv']
        simp only [Bool.or_eq_true_iff]
        exact ⟨Or.imp ia.1 ib.1,Or.imp ia.2 ib.2⟩

lemma derivative_support {n : ℕ} {C : Circuit} (normal : BinaryAO n C)
    (base seed : Fin n → Bool) (d : ℕ → Bool)
    (trace : DerivativeTrace n C base seed d) (w : ℕ) (hw : w<n+C.gates.length) :
    d w=true →
      (C.wires (List.ofFn (fun i => base i || seed i))).getD w false=true := by
  exact (derivative_support_of_bounds normal base seed (fun i => base i || seed i) d trace
    (fun i hi => by simp [hi]) (fun i hi => by simp [hi]) w hw).2

lemma derivative_false_of_pair_false {n : ℕ} {C : Circuit}
    (normal : BinaryAO n C) (a b : Fin n) (d : ℕ → Bool)
    (trace : DerivativeTrace n C
      (fun i => decide (i=a)) (fun i => decide (i=b)) d)
    (w : ℕ) (hw : w<n+C.gates.length)
    (off : (C.wires (List.ofFn (fun i : Fin n => decide (i=a ∨ i=b)))).getD w false=false) :
    d w=false := by
  cases hd : d w with
  | false => rfl
  | true =>
    have ht := derivative_support normal _ _ d trace w hw hd
    have heq : (fun i : Fin n => decide (i=a) || decide (i=b)) =
        (fun i : Fin n => decide (i=a ∨ i=b)) := by
      funext i
      simp
    rw [heq,off] at ht
    contradiction

lemma baseline_size : baseline.size = 27 := rfl

lemma baseline_normal : BinaryAO 14 baseline := by
  apply binaryAO_of_check
  decide

lemma substitution_wires_length {n : ℕ} (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n+C.gates.length := by
  obtain ⟨t,ht,hlen⟩ := support_run_extends C.gates (List.ofFn x)
  change (C.gates.foldl supportWireStep (List.ofFn x)).length = _
  rw [ht,List.length_append,List.length_ofFn,hlen]

lemma single_gate_wires_mono {n : ℕ} {C D : Circuit} (normal : BinaryAO n C)
    (j : ℕ) (same : ∀ k, k ≠ j → D.gates[k]? = C.gates[k]?)
    (x : Fin n → Bool)
    (changed : (C.wires (List.ofFn x)).getD (n+j) false = true →
      (D.wires (List.ofFn x)).getD (n+j) false = true) :
    ∀ w, (C.wires (List.ofFn x)).getD w false = true →
      (D.wires (List.ofFn x)).getD w false = true := by
  have bounded : ∀ w, w < n+C.gates.length →
      (C.wires (List.ofFn x)).getD w false = true →
        (D.wires (List.ofFn x)).getD w false = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw
      by_cases hin : w<n
      · rw [support_wire_input C x ⟨w,hin⟩,support_wire_input D x ⟨w,hin⟩]
        exact id
      · have hk : w-n<C.gates.length := by omega
        have heq : n+(w-n)=w := by omega
        by_cases hkj : w-n=j
        · have eqw : w=n+j := by omega
          simpa only [eqw] using changed
        · let g : Gate := C.gates[w-n]
          have hC : C.gates[w-n]? = some g :=
            List.getElem?_eq_some_iff.mpr ⟨hk,rfl⟩
          have hD : D.gates[w-n]? = some g := (same (w-n) hkj).trans hC
          obtain ⟨hop,a,b,hab,_,ha,hb⟩ := normal (w-n) g hC
          have ia := ih a (by omega) (by omega)
          have ib := ih b (by omega) (by omega)
          have cv := support_wire_gate C x (w-n) g a b hC hab ha hb
          have dv := support_wire_gate D x (w-n) g a b hD hab ha hb
          rcases hop with hop | hop
          · have cv' : (C.wires (List.ofFn x)).getD w false =
                ((C.wires (List.ofFn x)).getD a false &&
                  (C.wires (List.ofFn x)).getD b false) := by
              simpa [heq,hop,GateOp.eval] using cv
            have dv' : (D.wires (List.ofFn x)).getD w false =
                ((D.wires (List.ofFn x)).getD a false &&
                  (D.wires (List.ofFn x)).getD b false) := by
              simpa [heq,hop,GateOp.eval] using dv
            rw [cv',dv']
            simp only [Bool.and_eq_true_iff]
            exact fun h => ⟨ia h.1,ib h.2⟩
          · have cv' : (C.wires (List.ofFn x)).getD w false =
                ((C.wires (List.ofFn x)).getD a false ||
                  (C.wires (List.ofFn x)).getD b false) := by
              simpa [heq,hop,GateOp.eval] using cv
            have dv' : (D.wires (List.ofFn x)).getD w false =
                ((D.wires (List.ofFn x)).getD a false ||
                  (D.wires (List.ofFn x)).getD b false) := by
              simpa [heq,hop,GateOp.eval] using dv
            rw [cv',dv']
            simp only [Bool.or_eq_true_iff]
            exact Or.imp ia ib
  intro w h
  by_cases hw : w < n+C.gates.length
  · exact bounded w hw h
  · have hlen := substitution_wires_length C x
    rw [List.getD_eq_default _ _ (by omega)] at h
    contradiction

lemma single_gate_wires_eq {n : ℕ} {C D : Circuit}
    (normalC : BinaryAO n C) (normalD : BinaryAO n D)
    (j : ℕ) (same : ∀ k, k ≠ j → D.gates[k]? = C.gates[k]?)
    (x : Fin n → Bool)
    (changed : (C.wires (List.ofFn x)).getD (n+j) false =
      (D.wires (List.ofFn x)).getD (n+j) false) :
    ∀ w, (C.wires (List.ofFn x)).getD w false =
      (D.wires (List.ofFn x)).getD w false := by
  have forward := single_gate_wires_mono normalC j same x (by rw [changed]; exact id)
  have backward := single_gate_wires_mono normalD j (fun k hk => (same k hk).symm) x
    (by rw [changed]; exact id)
  intro w
  rw [Bool.eq_iff_iff]
  exact ⟨forward w,backward w⟩

lemma single_gate_eval_mono {n : ℕ} {C D : Circuit} (normal : BinaryAO n C)
    (j : ℕ) (same : ∀ k, k ≠ j → D.gates[k]? = C.gates[k]?)
    (out : D.output = C.output) (x : Fin n → Bool)
    (changed : (C.wires (List.ofFn x)).getD (n+j) false = true →
      (D.wires (List.ofFn x)).getD (n+j) false = true) :
    C.eval (List.ofFn x) = true → D.eval (List.ofFn x) = true := by
  unfold Circuit.eval
  rw [out]
  exact single_gate_wires_mono normal j same x changed C.output

lemma derivative_transport_one_change {n : ℕ} {C D : Circuit} (j : ℕ)
    (normalD : BinaryAO n D) (hlen : D.gates.length=C.gates.length)
    (same : ∀ k, k≠j → D.gates[k]?=C.gates[k]?)
    (base seed : Fin n → Bool) (d : ℕ → Bool)
    (trace : DerivativeTrace n C base seed d)
    (values : ∀ i, i<n+C.gates.length →
      (C.wires (List.ofFn base)).getD i false = (D.wires (List.ofFn base)).getD i false)
    (changed : ∀ (g : Gate) (a b : ℕ), D.gates[j]?=some g → g.inputs=[a,b] →
      (g.op=.and → d (n+j) =
        (((D.wires (List.ofFn base)).getD a false && d b) ||
          (d a && (D.wires (List.ofFn base)).getD b false))) ∧
      (g.op=.or → d (n+j)=(d a || d b))) :
    DerivativeTrace n D base seed d := by
  refine ⟨trace.1,?_⟩
  intro k g a b hk hab
  by_cases heq : k=j
  · subst k
    exact changed g a b hk hab
  · have hold : C.gates[k]?=some g := (same k heq).symm.trans hk
    have old := trace.2 k g a b hold hab
    obtain ⟨_,u,v,huv,_,hu,hv⟩ := normalD k g hk
    rw [hab] at huv
    simp only [List.cons.injEq,and_true] at huv
    obtain ⟨rfl,rfl⟩ := huv
    have hlt := (List.getElem?_eq_some_iff.mp hk).1
    have ha : a<n+C.gates.length := by omega
    have hb : b<n+C.gates.length := by omega
    constructor
    · intro hop
      rw [←values a ha,←values b hb]
      exact old.1 hop
    · exact old.2

lemma derivative_transport_input_and {n : ℕ} {C D : Circuit} (j : ℕ)
    (normalD : BinaryAO n D) (hlen : D.gates.length=C.gates.length)
    (same : ∀ k, k≠j → D.gates[k]?=C.gates[k]?)
    (base seed : Fin n → Bool) (d : ℕ → Bool)
    (trace : DerivativeTrace n C base seed d)
    (values : ∀ i, i<n+C.gates.length →
      (C.wires (List.ofFn base)).getD i false = (D.wires (List.ofFn base)).getD i false)
    (u v : Fin n) (newGate : D.gates[j]?=some ⟨.and,[u.val,v.val]⟩)
    (oldZero : d (n+j)=false)
    (newZero : ((base u && seed v) || (seed u && base v))=false) :
    DerivativeTrace n D base seed d := by
  apply derivative_transport_one_change j normalD hlen same base seed d trace values
  intro g a b hg hab
  have hident : g=(⟨.and,[u.val,v.val]⟩ : Gate) := Option.some.inj (hg.symm.trans newGate)
  subst g
  simp only [List.cons.injEq,and_true] at hab
  obtain ⟨rfl,rfl⟩ := hab
  constructor
  · intro _
    rw [oldZero,support_wire_input D base u,support_wire_input D base v,
      trace.1 u,trace.1 v]
    exact newZero.symm
  · intro h
    cases h

def replaceInputAnd {n : ℕ} (C : Circuit) (j : ℕ) (u v : Fin n) : Circuit :=
  ⟨C.gates.set j ⟨.and,[u.val,v.val]⟩,C.output⟩

lemma replaceInputAnd_length {n : ℕ} (C : Circuit) (j : ℕ) (u v : Fin n) :
    (replaceInputAnd C j u v).gates.length=C.gates.length := by
  simp [replaceInputAnd]

lemma replaceInputAnd_other {n : ℕ} (C : Circuit) (j : ℕ) (u v : Fin n)
    (k : ℕ) (hk : k≠j) : (replaceInputAnd C j u v).gates[k]?=C.gates[k]? := by
  exact List.getElem?_set_ne hk.symm

lemma replaceInputAnd_at {n : ℕ} (C : Circuit) (j : ℕ) (u v : Fin n)
    (hj : j<C.gates.length) :
    (replaceInputAnd C j u v).gates[j]?=some ⟨.and,[u.val,v.val]⟩ := by
  exact List.getElem?_set_self hj

lemma replaceInputAnd_normal {n : ℕ} {C : Circuit} (normal : BinaryAO n C)
    (j : ℕ) (hj : j<C.gates.length) (u v : Fin n) (huv : u≠v) :
    BinaryAO n (replaceInputAnd C j u v) := by
  intro k g hk
  by_cases heq : k=j
  · subst k
    have hident : g=(⟨.and,[u.val,v.val]⟩ : Gate) :=
      Option.some.inj (hk.symm.trans (replaceInputAnd_at C j u v hj))
    subst g
    refine ⟨Or.inl rfl,u.val,v.val,rfl,?_,?_,?_⟩
    · exact fun h => huv (Fin.ext h)
    · have hu := u.isLt
      omega
    · have hv := v.isLt
      omega
  · apply normal k g
    exact (replaceInputAnd_other C j u v k heq).symm.trans hk

lemma replaceInputAnd_value {n : ℕ} (C : Circuit) (j : ℕ) (u v : Fin n)
    (hj : j<C.gates.length) (x : Fin n → Bool) :
    ((replaceInputAnd C j u v).wires (List.ofFn x)).getD (n+j) false = (x u && x v) := by
  rw [support_wire_gate (replaceInputAnd C j u v) x j ⟨.and,[u.val,v.val]⟩
    u.val v.val (replaceInputAnd_at C j u v hj) rfl
    (by have h:=u.isLt; omega) (by have h:=v.isLt; omega)]
  rw [support_wire_input (replaceInputAnd C j u v) x u,
    support_wire_input (replaceInputAnd C j u v) x v]
  simp [GateOp.eval]

lemma repair_point_line_distinct (p l : Fin 7) : Fin.castAdd 7 p ≠ Fin.natAdd 7 l := by
  intro h
  have hval := congrArg Fin.val h
  change p.val=7+l.val at hval
  have hp := p.isLt
  omega

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
lemma fano_replacement_singleton_dark (r p l : Fin 7) :
    (decide (Fin.castAdd 7 r = Fin.castAdd 7 p) &&
      decide (Fin.natAdd 7 r = Fin.castAdd 7 p)) = false ∧
    (decide (Fin.castAdd 7 r = Fin.natAdd 7 l) &&
      decide (Fin.natAdd 7 r = Fin.natAdd 7 l)) = false := by
  decide +revert

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
lemma fano_replacement_trace_dark (p l : Fin 7) :
    ∃ r : Fin 7,
      ((decide (Fin.castAdd 7 r = Fin.castAdd 7 p) &&
          decide (Fin.natAdd 7 r = Fin.natAdd 7 l)) ||
        (decide (Fin.castAdd 7 r = Fin.natAdd 7 l) &&
          decide (Fin.natAdd 7 r = Fin.castAdd 7 p))) = false ∧
      ((decide (Fin.castAdd 7 r = Fin.natAdd 7 l) &&
          decide (Fin.natAdd 7 r = Fin.castAdd 7 p)) ||
        (decide (Fin.castAdd 7 r = Fin.castAdd 7 p) &&
          decide (Fin.natAdd 7 r = Fin.natAdd 7 l))) = false := by
  decide +revert

def fanoCircuitCorrect (C : Circuit) : Prop :=
  ∀ x : Fin 14 → Bool, C.eval (List.ofFn x)=true ↔ fanoHit x

def fanoGateSupported (C : Circuit) (j : ℕ) : Prop :=
  ∃ p l : Fin 7, fanoIncident p l ∧
    (C.wires (List.ofFn (pairInputLocal (Fin.castAdd 7 p) (Fin.natAdd 7 l)))).getD
      (14+j) false=true

lemma base_false_of_pair_false {n : ℕ} {C : Circuit}
    (normal : BinaryAO n C) (a b : Fin n) (d : ℕ → Bool)
    (trace : DerivativeTrace n C (singletonInput a) (singletonInput b) d)
    (w : ℕ) (hw : w<n+C.gates.length)
    (off : (C.wires (List.ofFn (pairInputLocal a b))).getD w false=false) :
    (C.wires (List.ofFn (singletonInput a))).getD w false=false := by
  have imp := (derivative_support_of_bounds normal (singletonInput a) (singletonInput b)
    (pairInputLocal a b) d trace
    (fun i hi => by
      have h : i=a := of_decide_eq_true hi
      simp [pairInputLocal,h])
    (fun i hi => by
      have h : i=b := of_decide_eq_true hi
      simp [pairInputLocal,h]) w hw).1
  cases h : (C.wires (List.ofFn (singletonInput a))).getD w false with
  | false => rfl
  | true =>
    have ht := imp h
    rw [off] at ht
    contradiction

lemma fano_repair_one_gate {C : Circuit} (normal : BinaryAO 14 C)
    (correct : fanoCircuitCorrect C) (j : ℕ) (hj : j<C.gates.length)
    (unsupported : ¬ fanoGateSupported C j) (p l : Fin 7) (incident : fanoIncident p l)
    (d e : ℕ → Bool)
    (td : DerivativeTrace 14 C (singletonInput (Fin.castAdd 7 p))
      (singletonInput (Fin.natAdd 7 l)) d)
    (te : DerivativeTrace 14 C (singletonInput (Fin.natAdd 7 l))
      (singletonInput (Fin.castAdd 7 p)) e) :
    ∃ D : Circuit, BinaryAO 14 D ∧ fanoCircuitCorrect D ∧
      D.gates.length=C.gates.length ∧ D.output=C.output ∧
      DerivativeTrace 14 D (singletonInput (Fin.castAdd 7 p))
        (singletonInput (Fin.natAdd 7 l)) d ∧
      DerivativeTrace 14 D (singletonInput (Fin.natAdd 7 l))
        (singletonInput (Fin.castAdd 7 p)) e ∧
      fanoGateSupported D j ∧ (∀ k, fanoGateSupported C k → fanoGateSupported D k) := by
  obtain ⟨r,hrd,hre⟩ := fano_replacement_trace_dark p l
  let D := replaceInputAnd C j (Fin.castAdd 7 r) (Fin.natAdd 7 r)
  have normalD : BinaryAO 14 D := replaceInputAnd_normal normal j hj _ _
    (repair_point_line_distinct r r)
  have hlen : D.gates.length=C.gates.length := replaceInputAnd_length C j _ _
  have same : ∀ k, k≠j → D.gates[k]?=C.gates[k]? := replaceInputAnd_other C j _ _
  have atj : D.gates[j]?=some ⟨.and,[(Fin.castAdd 7 r).val,(Fin.natAdd 7 r).val]⟩ :=
    replaceInputAnd_at C j _ _ hj
  have off (u t : Fin 7) (hit : fanoIncident u t) :
      (C.wires (List.ofFn (pairInputLocal (Fin.castAdd 7 u) (Fin.natAdd 7 t)))).getD
        (14+j) false=false := by
    cases h : (C.wires (List.ofFn (pairInputLocal (Fin.castAdd 7 u) (Fin.natAdd 7 t)))).getD
        (14+j) false with
    | false => rfl
    | true => exact False.elim (unsupported ⟨u,t,hit,h⟩)
  have grow (u t : Fin 7) (hit : fanoIncident u t) :
      ∀ w, (C.wires (List.ofFn (pairInputLocal (Fin.castAdd 7 u) (Fin.natAdd 7 t)))).getD w false=true →
        (D.wires (List.ofFn (pairInputLocal (Fin.castAdd 7 u) (Fin.natAdd 7 t)))).getD w false=true := by
    apply single_gate_wires_mono normal j same
    rw [off u t hit]
    simp
  have correctD : fanoCircuitCorrect D := by
    intro x
    constructor
    · intro hx
      by_contra nohit
      have prod : (x (Fin.castAdd 7 r) && x (Fin.natAdd 7 r))=false := by
        cases h : (x (Fin.castAdd 7 r) && x (Fin.natAdd 7 r)) with
        | false => rfl
        | true =>
          have h' : x (Fin.castAdd 7 r)=true ∧ x (Fin.natAdd 7 r)=true := by simpa using h
          exact False.elim (nohit ⟨r,r,Or.inl rfl,h'.1,h'.2⟩)
      have newzero : (D.wires (List.ofFn x)).getD (14+j) false=false := by
        rw [replaceInputAnd_value C j _ _ hj x]
        exact prod
      have oldtrue := single_gate_eval_mono normalD j (fun k hk => (same k hk).symm)
        (by rfl) x (by rw [newzero]; simp) hx
      exact nohit ((correct x).mp oldtrue)
    · rintro ⟨u,t,hit,hp,hl⟩
      let z := pairInputLocal (Fin.castAdd 7 u) (Fin.natAdd 7 t)
      have oldtrue : C.eval (List.ofFn z)=true := (correct z).mpr
        ⟨u,t,hit,by simp [z,pairInputLocal],by simp [z,pairInputLocal]⟩
      have newtrue : D.eval (List.ofFn z)=true := grow u t hit C.output oldtrue
      apply binaryAO_eval_mono normalD z x ?_ newtrue
      intro i hi
      have hor : i=Fin.castAdd 7 u ∨ i=Fin.natAdd 7 t := of_decide_eq_true hi
      rcases hor with rfl | rfl
      · exact hp
      · exact hl
  have bound : 14+j<14+C.gates.length := by omega
  have offmarked := off p l incident
  have offreverse :
      (C.wires (List.ofFn (pairInputLocal (Fin.natAdd 7 l) (Fin.castAdd 7 p)))).getD
        (14+j) false=false := by
    have heq : pairInputLocal (Fin.natAdd 7 l) (Fin.castAdd 7 p) =
        pairInputLocal (Fin.castAdd 7 p) (Fin.natAdd 7 l) := by
      funext i
      simp [pairInputLocal,or_comm]
    rw [heq]
    exact offmarked
  have oldbasep := base_false_of_pair_false normal _ _ d td (14+j) bound offmarked
  have oldbasel := base_false_of_pair_false normal _ _ e te (14+j) bound offreverse
  have oldd := derivative_false_of_pair_false normal _ _ d td (14+j) bound offmarked
  have olde := derivative_false_of_pair_false normal _ _ e te (14+j) bound offreverse
  have newbasep : (D.wires (List.ofFn (singletonInput (Fin.castAdd 7 p)))).getD (14+j) false=false := by
    rw [replaceInputAnd_value C j _ _ hj]
    exact (fano_replacement_singleton_dark r p l).1
  have newbasel : (D.wires (List.ofFn (singletonInput (Fin.natAdd 7 l)))).getD (14+j) false=false := by
    rw [replaceInputAnd_value C j _ _ hj]
    exact (fano_replacement_singleton_dark r p l).2
  have valuesp := single_gate_wires_eq normal normalD j same
    (singletonInput (Fin.castAdd 7 p)) (oldbasep.trans newbasep.symm)
  have valuesl := single_gate_wires_eq normal normalD j same
    (singletonInput (Fin.natAdd 7 l)) (oldbasel.trans newbasel.symm)
  have tdD := derivative_transport_input_and j normalD hlen same _ _ d td
    (fun i _ => valuesp i) (Fin.castAdd 7 r) (Fin.natAdd 7 r) atj oldd hrd
  have teD := derivative_transport_input_and j normalD hlen same _ _ e te
    (fun i _ => valuesl i) (Fin.castAdd 7 r) (Fin.natAdd 7 r) atj olde hre
  refine ⟨D,normalD,correctD,hlen,rfl,tdD,teD,?_,?_⟩
  · refine ⟨r,r,Or.inl rfl,?_⟩
    rw [replaceInputAnd_value C j _ _ hj]
    simp [pairInputLocal]
  · rintro k ⟨u,t,hit,h⟩
    exact ⟨u,t,hit,grow u t hit (14+k) h⟩

lemma fano_supported_normal_form_of_repair (p l : Fin 7) (d e : ℕ → Bool)
    (advance : ∀ A : Circuit, BinaryAO 14 A → fanoCircuitCorrect A →
      DerivativeTrace 14 A (singletonInput (Fin.castAdd 7 p))
        (singletonInput (Fin.natAdd 7 l)) d →
      DerivativeTrace 14 A (singletonInput (Fin.natAdd 7 l))
        (singletonInput (Fin.castAdd 7 p)) e →
      ∀ j : ℕ, j < A.gates.length → ¬ fanoGateSupported A j →
      ∃ B : Circuit, BinaryAO 14 B ∧ fanoCircuitCorrect B ∧
        B.gates.length = A.gates.length ∧ B.output = A.output ∧
        DerivativeTrace 14 B (singletonInput (Fin.castAdd 7 p))
          (singletonInput (Fin.natAdd 7 l)) d ∧
        DerivativeTrace 14 B (singletonInput (Fin.natAdd 7 l))
          (singletonInput (Fin.castAdd 7 p)) e ∧
        fanoGateSupported B j ∧
        ∀ k : ℕ, fanoGateSupported A k → fanoGateSupported B k)
    (C : Circuit) (normal : BinaryAO 14 C) (correct : fanoCircuitCorrect C)
    (traceD : DerivativeTrace 14 C (singletonInput (Fin.castAdd 7 p))
      (singletonInput (Fin.natAdd 7 l)) d)
    (traceE : DerivativeTrace 14 C (singletonInput (Fin.natAdd 7 l))
      (singletonInput (Fin.castAdd 7 p)) e) :
    ∃ D : Circuit, BinaryAO 14 D ∧ fanoCircuitCorrect D ∧
      D.gates.length = C.gates.length ∧ D.output = C.output ∧
      DerivativeTrace 14 D (singletonInput (Fin.castAdd 7 p))
        (singletonInput (Fin.natAdd 7 l)) d ∧
      DerivativeTrace 14 D (singletonInput (Fin.natAdd 7 l))
        (singletonInput (Fin.castAdd 7 p)) e ∧
      ∀ j : ℕ, j < D.gates.length → fanoGateSupported D j := by
  classical
  let Valid (A : Circuit) : Prop := BinaryAO 14 A ∧ fanoCircuitCorrect A ∧
    A.gates.length = C.gates.length ∧ A.output = C.output ∧
    DerivativeTrace 14 A (singletonInput (Fin.castAdd 7 p))
      (singletonInput (Fin.natAdd 7 l)) d ∧
    DerivativeTrace 14 A (singletonInput (Fin.natAdd 7 l))
      (singletonInput (Fin.castAdd 7 p)) e
  have initial : Valid C := ⟨normal,correct,rfl,rfl,traceD,traceE⟩
  have step (A : Circuit) (valid : Valid A) (j : Fin C.gates.length)
      (absent : ¬ fanoGateSupported A j.val) :
      ∃ B : Circuit, Valid B ∧ fanoGateSupported B j.val ∧
        ∀ k : ℕ, fanoGateSupported A k → fanoGateSupported B k := by
    obtain ⟨normalA,correctA,lengthA,outputA,traceDA,traceEA⟩ := valid
    have bound : j.val < A.gates.length := by rw [lengthA]; exact j.isLt
    obtain ⟨B,normalB,correctB,lengthB,outputB,traceDB,traceEB,supported,preserve⟩ :=
      advance A normalA correctA traceDA traceEA j.val bound absent
    exact ⟨B,⟨normalB,correctB,lengthB.trans lengthA,outputB.trans outputA,traceDB,traceEB⟩,
      supported,preserve⟩
  have collect (s : Finset (Fin C.gates.length)) :
      ∃ D : Circuit, Valid D ∧ ∀ i ∈ s, fanoGateSupported D i.val := by
    induction s using Finset.induction_on with
    | empty => exact ⟨C,initial,by simp⟩
    | @insert i s outside ih =>
      obtain ⟨A,validA,supportedA⟩ := ih
      obtain ⟨B,validB,supportedI,preserve⟩ :
          ∃ B : Circuit, Valid B ∧ fanoGateSupported B i.val ∧
            ∀ k : ℕ, fanoGateSupported A k → fanoGateSupported B k := by
        by_cases already : fanoGateSupported A i.val
        · exact ⟨A,validA,already,fun _ h => h⟩
        · exact step A validA i already
      refine ⟨B,validB,?_⟩
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact supportedI
      · exact preserve k.val (supportedA k hk)
  obtain ⟨D,validD,allD⟩ := collect Finset.univ
  obtain ⟨normalD,correctD,lengthD,outputD,traceDD,traceED⟩ := validD
  refine ⟨D,normalD,correctD,lengthD,outputD,traceDD,traceED,?_⟩
  intro j hj
  exact allD ⟨j,by omega⟩ (Finset.mem_univ _)

lemma fano_supported_normal_form {C : Circuit} (normal : BinaryAO 14 C)
    (correct : fanoCircuitCorrect C) (p l : Fin 7) (incident : fanoIncident p l)
    (d e : ℕ → Bool)
    (traceD : DerivativeTrace 14 C (singletonInput (Fin.castAdd 7 p))
      (singletonInput (Fin.natAdd 7 l)) d)
    (traceE : DerivativeTrace 14 C (singletonInput (Fin.natAdd 7 l))
      (singletonInput (Fin.castAdd 7 p)) e) :
    ∃ D : Circuit, BinaryAO 14 D ∧ fanoCircuitCorrect D ∧
      D.gates.length = C.gates.length ∧ D.output = C.output ∧
      DerivativeTrace 14 D (singletonInput (Fin.castAdd 7 p))
        (singletonInput (Fin.natAdd 7 l)) d ∧
      DerivativeTrace 14 D (singletonInput (Fin.natAdd 7 l))
        (singletonInput (Fin.castAdd 7 p)) e ∧
      ∀ j : ℕ, j < D.gates.length → fanoGateSupported D j := by
  exact fano_supported_normal_form_of_repair p l d e
    (fun A normalA correctA traceDA traceEA j hj absent =>
      fano_repair_one_gate normalA correctA j hj absent p l incident d e traceDA traceEA)
    C normal correct traceD traceE

lemma fano_supported_gate_zero_and {C : Circuit} (normal : BinaryAO 14 C)
    (a b : ℕ) (first : C.gates[0]?=some ⟨.and,[a,b]⟩)
    (supported : fanoGateSupported C 0) :
    ∃ p l : Fin 7, fanoIncident p l ∧
      ((a=p.val ∧ b=7+l.val) ∨ (a=7+l.val ∧ b=p.val)) := by
  obtain ⟨_,u,v,huv,hne,hu,hv⟩ := normal 0 ⟨.and,[a,b]⟩ first
  simp only [List.cons.injEq,and_true] at huv
  obtain ⟨rfl,rfl⟩ := huv
  have ha : a<14 := by omega
  have hb : b<14 := by omega
  obtain ⟨p,l,hpl,hon⟩ := supported
  rw [support_wire_gate C (pairInputLocal (Fin.castAdd 7 p) (Fin.natAdd 7 l))
    0 ⟨.and,[a,b]⟩ a b first rfl (by omega) (by omega)] at hon
  rw [support_wire_input C _ ⟨a,ha⟩,support_wire_input C _ ⟨b,hb⟩] at hon
  have choices : (a=p.val ∨ a=7+l.val) ∧ (b=p.val ∨ b=7+l.val) := by
    simpa [GateOp.eval,pairInputLocal,Fin.ext_iff,Nat.add_comm] using hon
  refine ⟨p,l,hpl,?_⟩
  rcases choices with ⟨hap|hal,hbp|hbl⟩
  · exact False.elim (hne (hap.trans hbp.symm))
  · exact Or.inl ⟨hap,hbl⟩
  · exact Or.inr ⟨hal,hbp⟩
  · exact False.elim (hne (hal.trans hbl.symm))

end PEqualNP.Outside.L_meta_1479
