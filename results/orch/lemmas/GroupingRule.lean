import Mathlib

namespace PEqualNP.Outside.L_meta_1677.RankBase
namespace PetersenScratch
def pairInput {n : ℕ} (i j : Fin n) (base : Fin n → Bool) (a b : Bool) (k : Fin n) : Bool :=
  if k = i then a else if k = j then b else base k
end PetersenScratch
open PetersenScratch
def Forbid {n : Nat} (F : (Fin n → Bool) → Bool) (i j : Fin n) : Prop :=
  ∀ a o, (∀ u v, F (pairInput i j a u v) = (u && v)) →
    (∀ u v, F (pairInput i j o u v) = (u || v)) → False
def Grouping {n : Nat} (r : Nat) (F : (Fin n → Bool) → Bool) :=
  { label : Fin n → Fin (r+1) //
    (∀ i j, label i = label j → Forbid F i j) ∧
    (∀ k, ∃ code : (Fin n → Bool) → Bool,
      (∀ x y, (∀ i, label i ≤ k → x i = y i) → code x = code y) ∧
      (∀ x y, (∀ i, label i ≠ k → x i = y i) → code x = code y → F x = F y)) }

def Grouping.label {n r : Nat} {F : (Fin n → Bool) → Bool}
    (g : Grouping r F) : Fin n → Fin (r+1) := g.val

lemma Grouping.pair {n r : Nat} {F : (Fin n → Bool) → Bool}
    (g : Grouping r F) : ∀ i j, g.label i = g.label j → Forbid F i j := g.property.1

lemma Grouping.cut {n r : Nat} {F : (Fin n → Bool) → Bool}
    (g : Grouping r F) : ∀ k, ∃ code : (Fin n → Bool) → Bool,
      (∀ x y, (∀ i, g.label i ≤ k → x i = y i) → code x = code y) ∧
      (∀ x y, (∀ i, g.label i ≠ k → x i = y i) → code x = code y → F x = F y) :=
  g.property.2

namespace RankRules

abbrev Rule (n : Nat) :=
  (Fin n × Fin n × Nat × Nat) ⊕
    (Fin n × Fin n × Fin n × Nat × Nat × Nat × Bool × Bool)

def Rule.square {n : Nat} (i j : Fin n) (a o : Nat) : Rule n :=
  Sum.inl (i,j,a,o)

def Rule.cube {n : Nat} (i j k : Fin n) (a b c : Nat) (bit sign : Bool) : Rule n :=
  Sum.inr (i,j,k,a,b,c,bit,sign)

def row {n : Nat} (m : Nat) : Fin n → Bool := fun i => m.testBit i.val

def accepts {n r : Nat} (label : Fin n → Fin r) : Rule n → Bool
  | Sum.inl (i,j,_,_) => label i != label j
  | Sum.inr (i,j,k,_,_,_,_,_) => (label i != label j) || decide (label k ≤ label i)

end RankRules
end PEqualNP.Outside.L_meta_1677.RankBase

namespace PEqualNP.Outside.L_meta_1677.FrontRanks

abbrev Word := BitVec 512

def fits (mono desired ground sample : Bool) : Bool :=
  if mono then if desired then !ground || sample else !sample || ground else ground == sample

def pinMask (mono desired sample : Bool) (w : Word) : Word :=
  if fits mono desired false sample then
    if fits mono desired true sample then BitVec.allOnes 512 else ~~~w
  else if fits mono desired true sample then w else 0

def mask (mono desired : Bool) : (ws : List Word) → (Fin ws.length → Bool) → Word
  | [], _ => BitVec.allOnes 512
  | w :: ws, x => pinMask mono desired (x 0) w &&& mask mono desired ws (fun i => x i.succ)

def forced (target : Word) (mono desired : Bool) (ws : List Word) (x : Fin ws.length → Bool) : Bool :=
  decide ((mask mono desired ws x &&& (if desired then target else ~~~target)) ≠ (0 : Word))

theorem mask_spec (mono b) (p : Fin 512) (ws : List Word) (x : Fin ws.length → Bool) :
    (mask mono b ws x).getLsbD p.val = true ↔
      ∀ i, fits mono b ((ws.get i).getLsbD p.val) (x i) = true := by
  induction ws with
  | nil =>
    change (BitVec.allOnes 512).getLsbD p.val = true ↔ _
    simp only [BitVec.getLsbD_allOnes, p.isLt, decide_true, true_iff]
    intro i
    exact Fin.elim0 i
  | cons w ws ih =>
    have pin : (pinMask mono b (x 0) w).getLsbD p.val =
        fits mono b (w.getLsbD p.val) (x 0) := by
      cases mono <;> cases b <;> cases q : x 0 <;>
        simp only [pinMask, fits, q, Bool.not_false, Bool.not_true, Bool.false_or,
          Bool.true_or, Bool.or_false, Bool.or_true, Bool.false_eq_true, Bool.true_eq_false,
          ite_false, ite_true, beq_false, beq_true, BitVec.getLsbD_allOnes, BitVec.getLsbD_not,
          BitVec.getLsbD_zero, p.isLt, decide_true, Bool.true_and]
    simp only [mask,BitVec.getLsbD_and,Bool.and_eq_true,ih,pin]
    constructor
    · intro ⟨h0,hs⟩ i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact h0
      · exact hs j
    · intro h
      exact ⟨h 0, fun i => h i.succ⟩

theorem forced_sound {ws : List Word} {target : Word} {mono : Bool}
    (F : (Fin ws.length → Bool) → Bool)
    (agree : ∀ p : Fin 512, F (fun i => (ws.get i).getLsbD p.val) = target.getLsbD p.val)
    (mon : mono = true → Monotone F) (b : Bool) (x) (h : forced target mono b ws x = true) :
    F x = b := by
  let bits := mask mono b ws x &&& (if b then target else ~~~target)
  have nzero : bits ≠ 0 := of_decide_eq_true h
  obtain ⟨p,hp⟩ : ∃ p : Fin 512, bits.getLsbD p.val = true := by
    by_contra! hbad
    apply nzero
    apply BitVec.eq_of_getElem_eq
    intro i hi
    have hh := hbad ⟨i,hi⟩
    simpa [BitVec.getLsbD_eq_getElem hi] using hh
  change (mask mono b ws x &&& (if b then target else ~~~target)).getLsbD p.val = true at hp
  simp only [BitVec.getLsbD_and, Bool.and_eq_true] at hp
  have fh := (mask_spec mono b p ws x).mp hp.1
  have ground : F (fun i => (ws.get i).getLsbD p.val) = b := by
    rw [agree]; cases b <;> simpa [p.isLt] using hp.2
  cases hm : mono with
  | false =>
    have eq : (fun i => (ws.get i).getLsbD p.val) = x := by
      funext i; simpa [fits,hm] using fh i
    rwa [eq] at ground
  | true =>
    cases b with
    | false =>
      have le : x ≤ fun i => (ws.get i).getLsbD p.val := by
        intro i
        have hi := fh i
        cases q : x i <;> cases v : (ws.get i).getLsbD p.val <;> simp_all [fits]
      have bound := mon hm le
      rw [ground] at bound
      cases e : F x <;> simp_all
      exact (by decide : ¬ true ≤ false) bound
    | true =>
      have le : (fun i => (ws.get i).getLsbD p.val) ≤ x := by
        intro i
        have hi := fh i
        cases q : x i <;> cases v : (ws.get i).getLsbD p.val <;> simp_all [fits]
      have bound := mon hm le
      rw [ground] at bound
      cases e : F x <;> simp_all
      exact (by decide : ¬ true ≤ false) bound
end PEqualNP.Outside.L_meta_1677.FrontRanks

namespace PEqualNP.Outside.L_meta_1677.FrontRanks
open RankBase RankBase.RankRules RankBase.PetersenScratch

def checksRule (target : Word) (mono : Bool) (ws : List Word) : Rule ws.length → Bool :=
  let checkValue := fun x b => forced target mono b ws x
  fun
  | Sum.inl (i,j,a,o) =>
      [false,true].all fun u => [false,true].all fun v =>
        checkValue (pairInput i j (row a) u v) (u && v) &&
        checkValue (pairInput i j (row o) u v) (u || v)
  | Sum.inr (i,j,k,a,b,c,bit,sign) =>
      let hi m := Function.update (row m) k bit
      ((List.finRange ws.length).all fun v => v == i || v == j ||
        (row a v == row b v && row b v == row c v)) &&
      checkValue (row a) false &&
      checkValue (row b) true &&
      checkValue (hi a) sign &&
      checkValue (hi b) sign &&
      checkValue (hi c) (!sign)

theorem checksRule_sound {target : Word} {mono : Bool} {ws : List Word} {r : Nat}
    (F : (Fin ws.length → Bool) → Bool)
    (agree : ∀ p : Fin 512, F (fun i => (ws.get i).getLsbD p.val) = target.getLsbD p.val)
    (mon : mono = true → Monotone F) (group : Grouping r F) {rule : Rule ws.length}
    (h : checksRule target mono ws rule = true) : accepts group.label rule = true := by
  have evaluation {x b} (e : forced target mono b ws x = true) : F x = b :=
    forced_sound F agree mon b x e
  rcases rule with ⟨i,j,a,o⟩ | ⟨i,j,k,a,b,c,bit,sign⟩
  ·
    apply bne_iff_ne.mpr
    intro eq
    have all (u v : Bool) := List.all_eq_true.mp
      (List.all_eq_true.mp h u (by cases u <;> decide)) v (by cases v <;> decide)
    exact group.pair i j eq (row a) (row o)
      (fun u v => by
        have both := all u v
        simp only [Bool.and_eq_true] at both
        exact evaluation both.1)
      (fun u v => by
        have both := all u v
        simp only [Bool.and_eq_true] at both
        exact evaluation both.2)
  ·
    simp only [accepts, Bool.or_eq_true, bne_iff_ne, decide_eq_true_eq]
    by_cases eq : group.label i = group.label j
    · right
      by_contra nl
      have high := lt_of_not_ge nl
      simp only [checksRule, Bool.and_eq_true] at h
      obtain ⟨⟨⟨⟨⟨same,va⟩,vb⟩,vha⟩,vhb⟩,vhc⟩ := h
      obtain ⟨code,lower,upper⟩ := group.cut (group.label i)
      let upd (m : Nat) := Function.update (row m) k bit
      have noChange (m : Nat) : code (upd m) = code (row m) := by
        apply lower
        intro u hu
        apply Function.update_of_ne
        intro e
        subst u
        exact (not_le_of_gt high) hu
      have share {u} (hu : group.label u ≠ group.label i) :
          row a u = row b u ∧ row b u = row c u := by
        have s := List.all_eq_true.mp same u (List.mem_finRange u)
        have ei : u ≠ i := fun e => hu (e ▸ rfl)
        have ej : u ≠ j := fun e => hu (e ▸ eq.symm)
        simpa [ei,ej] using s
      have ab : code (row a) ≠ code (row b) := by
        intro e
        have bad := upper _ _ (fun _ hu => (share hu).1) e
        rw [evaluation va,evaluation vb] at bad
        contradiction
      have lift {p q : Nat} (off : ∀ u, group.label u ≠ group.label i → row p u = row q u) :
          ∀ u, group.label u ≠ group.label i → upd p u = upd q u := by
        intro u hu
        by_cases e : u = k
        · subst u; simp [upd]
        · simpa only [upd,Function.update_of_ne e] using off u hu
      have ac : code (row a) ≠ code (row c) := by
        intro e
        have bad := upper _ _ (lift fun _ hu => (share hu).1.trans (share hu).2)
          ((noChange a).trans (e.trans (noChange c).symm))
        change F (Function.update (row a) k bit) = F (Function.update (row c) k bit) at bad
        rw [evaluation vha,evaluation vhc] at bad
        cases sign <;> cases bad
      have bc : code (row b) ≠ code (row c) := by
        intro e
        have bad := upper _ _ (lift fun _ hu => (share hu).2)
          ((noChange b).trans (e.trans (noChange c).symm))
        change F (Function.update (row b) k bit) = F (Function.update (row c) k bit) at bad
        rw [evaluation vhb,evaluation vhc] at bad
        cases sign <;> cases bad
      cases ha : code (row a) <;> cases hb : code (row b) <;> cases hc : code (row c) <;> simp_all
    · exact Or.inl eq
def checkAssigned {n r : Nat} (labels : Fin n → Option (Fin r)) : Rule n → Bool
  | Sum.inl (i,j,_,_) =>
    match labels i, labels j with
    | some a, some b => a != b
    | _, _ => true
  | Sum.inr (i,j,k,_,_,_,_,_) =>
    match labels i, labels j, labels k with
    | some a, some b, some c => (a != b) || decide (c ≤ a)
    | _, _, _ => true

def seek {n r} : List (Fin n × List (Rule n)) → (Fin n → Option (Fin r)) → Bool
  | [], _ => true
  | (i,group)::rest, labels => (List.finRange r).any fun v =>
    let after := Function.update labels i (some v)
    group.all (checkAssigned after) && seek rest after

def weight {n : Nat} (u : Fin n) : Rule n → Nat
  | Sum.inl (i,j,_,_) => if u==i || u==j then 6 else 0
  | Sum.inr (i,j,k,_,_,_,_,_) => if u==i || u==j then 2 else if u==k then 1 else 0

def lastPosition {n : Nat} (order : List (Fin n)) : Rule n → Nat
  | Sum.inl (i,j,_,_) => max (order.idxOf i) (order.idxOf j)
  | Sum.inr (i,j,k,_,_,_,_,_) => max (order.idxOf i) (max (order.idxOf j) (order.idxOf k))

def addWeight {n : Nat} (x : Fin n × Nat) : List (Fin n × Nat) → List (Fin n × Nat)
  | [] => [x]
  | y::ys => if x.2 ≥ y.2 then x::y::ys else y::addWeight x ys

def sortWeights {n : Nat} : List (Fin n × Nat) → List (Fin n × Nat)
  | [] => []
  | x::xs => addWeight x (sortWeights xs)

def weightedOrder {n : Nat} (rules : List (Rule n)) :=
  (sortWeights ((List.finRange n).map fun i => (i,(rules.map (weight i)).sum))).map Prod.fst

def weightedStages {n : Nat} (rules : List (Rule n)) :=
  let order := weightedOrder rules
  order.map fun i => (i,rules.filter fun p => lastPosition order p == order.idxOf i)

def readFin (n x : Nat) : Option (Fin n) :=
  if h : x < n then some ⟨x,h⟩ else none

def ruleCode (n w : Nat) : Option (Rule n) := do
  let i ← readFin n (w &&& 15)
  let j ← readFin n ((w >>> 4) &&& 15)
  let k := (w >>> 8) &&& 15
  let pay := w >>> 12
  let raw := pay &&& 4095
  if k == 15 then
    return Rule.square i j raw (pay >>> 12)
  else
    let pivot ← readFin n k
    let corner (m : Nat) := raw ||| ((m &&& 1) <<< i.val) ||| (((m >>> 1) &&& 1) <<< j.val)
    return Rule.cube i j pivot (corner (pay >>> 12)) (corner (pay >>> 14))
      (corner (pay >>> 16)) (!(raw.testBit k)) (pay.testBit 18)

def readRules (n : Nat) : Nat → Nat → List (Rule n)
  | 0, _ => []
  | c+1, w =>
    (ruleCode n (w &&& 0xfffffffff)).toList ++ readRules n c (w >>> 36)

namespace Digits

def field (word offset : Nat) := (word >>> offset) % 16

def Rep {n r} (label : Fin n → Fin r) (trail : List (Fin n)) (s : Nat) : Prop :=
  ∀ (j : Nat) (h : j < trail.length), field s (4*j) = (label trail[j]).val

theorem rep_push {n r s} {label : Fin n → Fin r} {trail : List (Fin n)}
    (rep : Rep label trail s) (i : Fin n) (size : r ≤ 16) :
    Rep label (i::trail) (16*s+(label i).val) := by
  have small := (label i).isLt
  intro j h
  cases j with
  | zero =>
    simp only [Nat.mul_zero,Nat.shiftRight_zero,field,List.getElem_cons_zero]
    omega
  | succ j =>
    have div : (16*s+(label i).val) >>> 4 = s := by
      rw [Nat.shiftRight_eq_div_pow]
      change (16*s+(label i).val)/16=s
      omega
    have off : 4*(j+1)=4+4*j := by omega
    simp only [field,off,Nat.shiftRight_add,div,List.getElem_cons_succ]
    exact rep j (by simpa using h)

abbrev Test := Nat × Nat × Nat

def compileTest {n} (trail : List (Fin n)) : Rule n → Option Test
  | Sum.inl (i,j,_,_) =>
    if trail.idxOf i < trail.length && trail.idxOf j < trail.length then
      some (4*trail.idxOf i,4*trail.idxOf j,0) else none
  | Sum.inr (i,j,k,_,_,_,_,_) =>
    if trail.idxOf i < trail.length && trail.idxOf j < trail.length && trail.idxOf k < trail.length then
      some (4*trail.idxOf i,4*trail.idxOf j,4*trail.idxOf k+1) else none

def evaluate (word : Nat) (t : Test) : Bool :=
  let a := field word t.1
  a != field word t.2.1 || (t.2.2 != 0 && decide (field word (t.2.2-1) ≤ a))

theorem compile_sound {n r s} {label : Fin n → Fin r} {trail : List (Fin n)}
    (rep : Rep label trail s) {rule : Rule n} (valid : accepts label rule = true)
    {t} (compiled : compileTest trail rule = some t) : evaluate s t = true := by
  have lookup (i : Fin n) (h : trail.idxOf i < trail.length) :
      field s (4*trail.idxOf i) = (label i).val := by
    simpa only [List.getElem_idxOf h] using rep (trail.idxOf i) h
  rcases rule with ⟨i,j,a,o⟩ | ⟨i,j,k,a,b,c,bit,sign⟩
  ·
    simp only [compileTest] at compiled
    split at compiled
    next test =>
      simp only [Bool.and_eq_true,decide_eq_true_eq] at test
      cases compiled
      simpa [evaluate,lookup i test.1,lookup j test.2,accepts,Fin.ext_iff] using valid
    next => contradiction
  ·
    simp only [compileTest] at compiled
    split at compiled
    next test =>
      simp only [Bool.and_eq_true,decide_eq_true_eq] at test
      cases compiled
      simpa [evaluate,lookup i test.1.1,lookup j test.1.2,lookup k test.2,accepts,Fin.ext_iff] using valid
    next => contradiction

def stages {n} (trail : List (Fin n)) : List (Fin n × List (Rule n)) → List (List Test)
  | [] => []
  | (i,rs)::more => rs.filterMap (compileTest (i::trail)) :: stages (i::trail) more

def search (r : Nat) : List (List Test) → Nat → Bool
  | [], _ => true
  | tests::more, word => (List.range r).any fun v =>
    let next := 16*word+v
    tests.all (evaluate next) && search r more next

theorem search_sound {n r} {label : Fin n → Fin r} (hr : r ≤ 16)
    (ss : List (Fin n × List (Rule n))) (ok : ∀ stage ∈ ss, ∀ p ∈ stage.2, accepts label p = true)
    {trail s} (rep : Rep label trail s) : search r (stages trail ss) s = true := by
  induction ss generalizing trail s with
  | nil => rfl
  | cons head rest ih =>
    obtain ⟨i,rs⟩ := head
    apply List.any_eq_true.mpr
    refine ⟨(label i).val, List.mem_range.mpr (label i).isLt, ?_⟩
    have now := rep_push rep i hr
    simp only [Bool.and_eq_true]
    constructor
    · apply List.all_eq_true.mpr
      intro t ht
      obtain ⟨rule,mem,eq⟩ := List.mem_filterMap.mp ht
      exact compile_sound now (ok (i,rs) List.mem_cons_self rule mem) eq
    · exact ih (fun stage h p hp => ok stage (List.mem_cons_of_mem _ h) p hp) now

def fast {n} (r : Nat) (rules : List (Rule n)) : Bool :=
  if r ≤ 16 then search r (stages [] (weightedStages rules)) 0 else true

theorem fast_sound {n r} {label : Fin n → Fin r} {rules : List (Rule n)}
    (good : ∀ p ∈ rules, accepts label p = true) : fast r rules = true := by
  unfold fast
  split
  next hr =>
    apply search_sound (label:=label) hr
    · intro stage hst p hp
      unfold weightedStages at hst
      obtain ⟨_,_,rfl⟩ := List.mem_map.mp hst
      exact good p (List.mem_filter.mp hp).1
    · intro j h
      simp at h
  next => rfl

end Digits

def rankCheck (target : Word) (mono : Bool) (ws : List Word) (r code count : Nat) : Bool :=
  let rules := readRules ws.length count code
  rules.all (checksRule target mono ws) && !(Digits.fast (r+1) rules)

theorem rankCheck_sound {target : Word} {mono : Bool} {ws : List Word} {r code count : Nat}
    (F : (Fin ws.length → Bool) → Bool)
    (agree : ∀ p : Fin 512, F (fun i => (ws.get i).getLsbD p.val) = target.getLsbD p.val)
    (mon : mono = true → Monotone F) (group : Grouping r F)
    (h : rankCheck target mono ws r code count = true) : False := by
  let rules := readRules ws.length count code
  have pass : rules.all (checksRule target mono ws) = true ∧ Digits.fast (r+1) rules = false := by
    simpa only [rankCheck, Bool.and_eq_true, Bool.not_eq_true'] using h
  have accept (claim : Rule ws.length) (hc : claim ∈ rules) : accepts group.label claim = true :=
    checksRule_sound F agree mon group (List.all_eq_true.mp pass.1 _ hc)
  have found : Digits.fast (r+1) rules = true :=
    Digits.fast_sound (r:=r+1) (label:=group.label) accept
  rw [pass.2] at found
  contradiction

end PEqualNP.Outside.L_meta_1677.FrontRanks

namespace PEqualNP.Outside.L_meta_1677.FrontRanks
open RankBase RankBase.RankRules

def readPrefixField (format : Nat → Nat × (Nat → Nat)) (read : Nat → Nat → Nat)
    (kind p raw : Nat) : Nat × Nat :=
  let t := format kind
  let ent := t.2 (read p t.1)
  let value := ent &&& 8191
  let next := p+(ent >>> 13)
  if value == 4096 then (read next raw,next+raw) else (value,next)

def insertZeroAt (x i : Nat) : Nat :=
  (x &&& ((1 <<< i)-1)) ||| ((x >>> i) <<< (i+1))

def expandRow (x h : Nat) : Nat :=
  let i := h &&& 15
  let j := (h >>> 4) &&& 15
  insertZeroAt (insertZeroAt x (min i j)) (max i j)

def huffCodes (n : Nat) (f : Nat → Nat × (Nat → Nat)) (read : Nat → Nat → Nat) :
    Nat → Nat → Nat
  | 0, _ => 0
  | count+1, p =>
    let item := if read p 1 == 1 then
        ((f 4).2 (read (p+1) 10),p+11)
      else
        let hdr := readPrefixField f read 0 (p+1) 12
        let base := readPrefixField f read 1 hdr.2 (n-2)
        let square := hdr.1 >>> 8 == 15
        let tail := readPrefixField f read (if square then 3 else 2) base.2 (if square then n-2 else 7)
        let z := if square then expandRow tail.1 hdr.1 else tail.1
        (hdr.1 ||| (expandRow base.1 hdr.1 <<< 12) ||| (z <<< 24),tail.2)
    item.1 ||| (huffCodes n f read count item.2 <<< 36)

def rankHuffCheck (target : Word) (mono : Bool) (ws : List Word) (r : Nat)
    (format : Nat → Nat × (Nat → Nat)) (read : Nat → Nat → Nat) (tag p : Nat) : Bool :=
  if tag == 0 then false else if tag == 1 then
    forced target mono false ws (row (read p ws.length)) &&
      forced target mono true ws (row (read p ws.length))
  else
    rankCheck target mono ws r (huffCodes ws.length format read (tag-2) p) (tag-2)

theorem rankHuffCheck_sound {target : Word} {mono : Bool} {ws : List Word} {r tag p : Nat}
    {format : Nat → Nat × (Nat → Nat)} {read : Nat → Nat → Nat}
    (F : (Fin ws.length → Bool) → Bool)
    (agree : ∀ p : Fin 512, F (fun i => (ws.get i).getLsbD p.val) = target.getLsbD p.val)
    (mon : mono = true → Monotone F) (group : Grouping r F)
    (h : rankHuffCheck target mono ws r format read tag p = true) : False := by
  unfold rankHuffCheck at h
  split at h
  · contradiction
  split at h
  · simp only [Bool.and_eq_true] at h
    have no := forced_sound F agree mon false _ h.1
    have yes := forced_sound F agree mon true _ h.2
    rw [no] at yes
    contradiction
  · exact rankCheck_sound F agree mon group h

end PEqualNP.Outside.L_meta_1677.FrontRanks

