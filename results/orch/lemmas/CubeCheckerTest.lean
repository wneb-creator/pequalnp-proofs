import Mathlib.Order.Monotone.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Data.Bool.Basic
import Mathlib.Logic.Function.Basic

namespace PEqualNP.Outside.L_meta_1677.RankBase
namespace PetersenScratch
def pairInput {n : ℕ} (i j : Fin n) (base : Fin n → Bool) (a b : Bool) (k : Fin n) : Bool :=
  if k = i then a else if k = j then b else base k
end PetersenScratch
open PetersenScratch
def Forbid {n : Nat} (F : (Fin n → Bool) → Bool) (i j : Fin n) : Prop :=
  ∀ a o, (∀ u v, F (pairInput i j a u v) = (u && v)) →
    (∀ u v, F (pairInput i j o u v) = (u || v)) → False
def Grouping {n:Nat} (r:Nat) (F:(Fin n → Bool) → Bool) :=
 { label:Fin n → Fin (r+1) //
   (∀ i j, label i = label j → Forbid F i j) ∧
   (∀ k, ∃ code:(Fin n → Bool) → Bool,
     (∀ x y, (∀ i, label i ≤ k → x i = y i) → code x = code y) ∧
     (∀ x y, (∀ i, label i ≠ k → x i = y i) → code x = code y → F x = F y)) }
def Grouping.label {n r:Nat} {F:(Fin n → Bool) → Bool}
   (g:Grouping r F):Fin n → Fin (r+1) := g.val
lemma Grouping.pair {n r:Nat} {F:(Fin n → Bool) → Bool}
   (g:Grouping r F):∀ i j, g.label i = g.label j → Forbid F i j := g.property.1
lemma Grouping.cut {n r:Nat} {F:(Fin n → Bool) → Bool}
   (g:Grouping r F):∀ k, ∃ code:(Fin n → Bool) → Bool,
     (∀ x y, (∀ i, g.label i ≤ k → x i = y i) → code x = code y) ∧
     (∀ x y, (∀ i, g.label i ≠ k → x i = y i) → code x = code y → F x = F y) :=
 g.property.2
namespace RankRules
abbrev Rule (n:Nat) :=
 (Fin n × Fin n × Nat × Nat) ⊕
   (Fin n × Fin n × Fin n × Nat × Nat × Nat × Bool × Bool)
def Rule.square {n:Nat} (i j:Fin n) (a o:Nat):Rule n :=
 Sum.inl (i,j,a,o)
def Rule.cube {n:Nat} (i j k:Fin n) (a b c:Nat) (bit sign:Bool):Rule n :=
 Sum.inr (i,j,k,a,b,c,bit,sign)
def row {n:Nat} (m:Nat):Fin n → Bool := fun i => m.testBit i.val
def accepts {n r:Nat} (label:Fin n → Fin r):Rule n → Bool
 | Sum.inl (i,j,_,_) => label i != label j
 | Sum.inr (i,j,k,_,_,_,_,_) => (label i != label j) || decide (label k ≤ label i)
end RankRules
end PEqualNP.Outside.L_meta_1677.RankBase
namespace PEqualNP.Outside.L_meta_1677.FrontRanks
abbrev Word := BitVec 512
def fits (mono desired ground sample:Bool):Bool :=
 if mono then if desired then !ground || sample else !sample || ground else ground == sample
def pinMask (mono desired sample:Bool) (w:Word):Word :=
 if fits mono desired false sample then
   if fits mono desired true sample then BitVec.allOnes 512 else ~~~w
 else if fits mono desired true sample then w else 0
def mask (mono desired:Bool):(ws:List Word) → (Fin ws.length → Bool) → Word
 | [], _ => BitVec.allOnes 512
 | w :: ws, x => pinMask mono desired (x 0) w &&& mask mono desired ws (fun i => x i.succ)
def forced (target:Word) (mono desired:Bool) (ws:List Word) (x:Fin ws.length → Bool):Bool :=
 decide ((mask mono desired ws x &&& (if desired then target else ~~~target)) ≠ (0:Word))
theorem mask_spec (mono b) (p:Fin 512) (ws:List Word) (x:Fin ws.length → Bool) :
   (mask mono b ws x).getLsbD p.val = true ↔
     ∀ i, fits mono b ((ws.get i).getLsbD p.val) (x i) = true := by
 induction ws with
 | nil =>
   change (BitVec.allOnes 512).getLsbD p.val = true ↔ _
   simp only [BitVec.getLsbD_allOnes, p.isLt, decide_true, true_iff]
   intro i
   exact Fin.elim0 i
 | cons w ws ih =>
   have pin:(pinMask mono b (x 0) w).getLsbD p.val =
       fits mono b (w.getLsbD p.val) (x 0) := by
     cases mono <;> cases b <;> cases q:x 0 <;>
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
theorem forced_sound {ws:List Word} {target:Word} {mono:Bool}
   (F:(Fin ws.length → Bool) → Bool)
   (agree:∀ p:Fin 512, F (fun i => (ws.get i).getLsbD p.val) = target.getLsbD p.val)
   (mon:mono = true → Monotone F) (b:Bool) (x) (h:forced target mono b ws x = true) :
   F x = b := by
 let bits := mask mono b ws x &&& (if b then target else ~~~target)
 have nzero:bits ≠ 0 := of_decide_eq_true h
 obtain ⟨p,hp⟩:∃ p:Fin 512, bits.getLsbD p.val = true := by
   by_contra! hbad
   apply nzero
   apply BitVec.eq_of_getElem_eq
   intro i hi
   have hh := hbad ⟨i,hi⟩
   simpa [BitVec.getLsbD_eq_getElem hi] using hh
 change (mask mono b ws x &&& (if b then target else ~~~target)).getLsbD p.val = true at hp
 simp only [BitVec.getLsbD_and, Bool.and_eq_true] at hp
 have fh := (mask_spec mono b p ws x).mp hp.1
 have ground:F (fun i => (ws.get i).getLsbD p.val) = b := by
   rw [agree]; cases b <;> simpa [p.isLt] using hp.2
 cases hm:mono with
 | false =>
   have eq:(fun i => (ws.get i).getLsbD p.val) = x := by
     funext i; simpa [fits,hm] using fh i
   rwa [eq] at ground
 | true =>
   cases b with
   | false =>
     have le:x ≤ fun i => (ws.get i).getLsbD p.val := by
       intro i
       have hi := fh i
       cases q:x i <;> cases v:(ws.get i).getLsbD p.val <;> simp_all [fits]
     have bound := mon hm le
     rw [ground] at bound
     cases e:F x <;> simp_all
     exact (by decide:¬ true ≤ false) bound
   | true =>
     have le:(fun i => (ws.get i).getLsbD p.val) ≤ x := by
       intro i
       have hi := fh i
       cases q:x i <;> cases v:(ws.get i).getLsbD p.val <;> simp_all [fits]
     have bound := mon hm le
     rw [ground] at bound
     cases e:F x <;> simp_all
     exact (by decide:¬ true ≤ false) bound
end PEqualNP.Outside.L_meta_1677.FrontRanks
namespace PEqualNP.Outside.L_meta_1677.FrontRanks
open RankBase RankBase.RankRules RankBase.PetersenScratch
theorem monoUpdate {n : Nat} (F : (Fin n → Bool) → Bool) (mon : Monotone F)
    (x : Fin n → Bool) (k : Fin n) (b : Bool) (hx : F x = b) :
    F (Function.update x k b) = b := by
  cases b with
  | false =>
    have smaller : Function.update x k false ≤ x := by
      intro j
      by_cases e : j = k
      · subst j; simp only [Function.update_self]; exact Bool.false_le _
      · simpa only [Function.update_of_ne e] using (le_rfl : x j ≤ x j)
    have h := mon smaller
    rw [hx] at h
    cases e : F (Function.update x k false) with
    | false => rfl
    | true => exact ((by decide : ¬ (true : Bool) ≤ false) (by simpa only [e] using h)).elim
  | true =>
    have larger : x ≤ Function.update x k true := by
      intro j
      by_cases e : j = k
      · subst j; simp only [Function.update_self]; exact Bool.le_true _
      · simpa only [Function.update_of_ne e] using (le_rfl : x j ≤ x j)
    have h := mon larger
    rw [hx] at h
    cases e : F (Function.update x k true) with
    | false => exact ((by decide : ¬ (true : Bool) ≤ false) (by simpa only [e] using h)).elim
    | true => rfl
theorem pairDiag {n : Nat} (i j : Fin n) (base : Fin n → Bool) (u v : Bool) :
    Function.update (pairInput i j base u v) j u = pairInput i j base u u := by
  funext k
  by_cases hj : k = j
  · subst k
    simp [pairInput]
  · rw [Function.update_of_ne hj]
    simp only [pairInput,hj,ite_false]
theorem squareCorners {n : Nat} (F : (Fin n → Bool) → Bool) (mon : Monotone F)
    (i j : Fin n) (a o : Fin n → Bool)
    (a01 : F (pairInput i j a false true) = false)
    (a10 : F (pairInput i j a true false) = false)
    (a11 : F (pairInput i j a true true) = true)
    (o00 : F (pairInput i j o false false) = false)
    (o01 : F (pairInput i j o false true) = true)
    (o10 : F (pairInput i j o true false) = true) :
    (∀ u v, F (pairInput i j a u v) = (u && v)) ∧
      (∀ u v, F (pairInput i j o u v) = (u || v)) := by
  have a00 := monoUpdate F mon (pairInput i j a false true) j false a01
  have o11 := monoUpdate F mon (pairInput i j o true false) j true o10
  rw [pairDiag] at a00 o11
  constructor
  · intro u v
    cases u <;> cases v
    · exact a00
    · exact a01
    · exact a10
    · exact a11
  · intro u v
    cases u <;> cases v
    · exact o00
    · exact o01
    · exact o10
    · exact o11
def checksRule (target:Word) (mono:Bool) (ws:List Word):Rule ws.length → Bool :=
 let checkValue := fun x b => forced target mono b ws x
 fun
 | Sum.inl (i,j,a,o) =>
     if mono then
       checkValue (pairInput i j (row a) false true) false &&
       checkValue (pairInput i j (row a) true false) false &&
       checkValue (pairInput i j (row a) true true) true &&
       checkValue (pairInput i j (row o) false false) false &&
       checkValue (pairInput i j (row o) false true) true &&
       checkValue (pairInput i j (row o) true false) true
     else
       [false,true].all fun u => [false,true].all fun v =>
         checkValue (pairInput i j (row a) u v) (u && v) &&
         checkValue (pairInput i j (row o) u v) (u || v)
 | Sum.inr (i,j,k,a,b,c,bit,sign) =>
     let hi m := Function.update (row m) k bit
     ((List.finRange ws.length).all fun v => v == i || v == j ||
       (row a v == row b v && row b v == row c v)) &&
     checkValue (row a) false &&
     checkValue (row b) true &&
     (if mono && !bit && !sign then true else checkValue (hi a) sign) &&
     (if mono && bit && sign then true else checkValue (hi b) sign) &&
     checkValue (hi c) (!sign)
theorem checksRule_sound {target:Word} {mono:Bool} {ws:List Word} {r:Nat}
   (F:(Fin ws.length → Bool) → Bool)
   (agree:∀ p:Fin 512, F (fun i => (ws.get i).getLsbD p.val) = target.getLsbD p.val)
   (mon:mono = true → Monotone F) (group:Grouping r F) {rule:Rule ws.length}
   (h:checksRule target mono ws rule = true):accepts group.label rule = true := by
 have evaluation {x b} (e:forced target mono b ws x = true):F x = b :=
   forced_sound F agree mon b x e
 rcases rule with ⟨i,j,a,o⟩ | ⟨i,j,k,a,b,c,bit,sign⟩
 ·
   apply bne_iff_ne.mpr
   intro eq
   cases mono with
   | false =>
     simp only [checksRule, Bool.false_eq_true, ite_false] at h
     have all (u v:Bool) := List.all_eq_true.mp
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
   | true =>
     simp only [checksRule, ite_true, Bool.and_eq_true] at h
     obtain ⟨⟨⟨⟨⟨a01,a10⟩,a11⟩,o00⟩,o01⟩,o10⟩ := h
     have vals := squareCorners F (mon rfl) i j (row a) (row o)
       (evaluation a01) (evaluation a10) (evaluation a11)
       (evaluation o00) (evaluation o01) (evaluation o10)
     exact group.pair i j eq (row a) (row o) vals.1 vals.2
 ·
   simp only [accepts, Bool.or_eq_true, bne_iff_ne, decide_eq_true_eq]
   by_cases eq:group.label i = group.label j
   · right
     by_contra nl
     have high := lt_of_not_ge nl
     simp only [checksRule, Bool.and_eq_true] at h
     obtain ⟨⟨⟨⟨⟨same,va⟩,vb⟩,vha⟩,vhb⟩,vhc⟩ := h
     have evalA : F (Function.update (row a) k bit) = sign := by
       split at vha
       next skip =>
         simp only [Bool.not_eq_true'] at skip
         rcases skip with ⟨⟨hm,rfl⟩,rfl⟩
         exact monoUpdate F (mon hm) (row a) k false (evaluation va)
       next => exact evaluation vha
     have evalB : F (Function.update (row b) k bit) = sign := by
       split at vhb
       next skip =>
         rcases skip with ⟨⟨hm,rfl⟩,rfl⟩
         exact monoUpdate F (mon hm) (row b) k true (evaluation vb)
       next => exact evaluation vhb
     obtain ⟨code,lower,upper⟩ := group.cut (group.label i)
     let upd (m:Nat) := Function.update (row m) k bit
     have noChange (m:Nat):code (upd m) = code (row m) := by
       apply lower
       intro u hu
       apply Function.update_of_ne
       intro e
       subst u
       exact (not_le_of_gt high) hu
     have share {u} (hu:group.label u ≠ group.label i) :
         row a u = row b u ∧ row b u = row c u := by
       have s := List.all_eq_true.mp same u (List.mem_finRange u)
       have ei:u ≠ i := fun e => hu (e ▸ rfl)
       have ej:u ≠ j := fun e => hu (e ▸ eq.symm)
       simpa [ei,ej] using s
     have ab:code (row a) ≠ code (row b) := by
       intro e
       have bad := upper _ _ (fun _ hu => (share hu).1) e
       rw [evaluation va,evaluation vb] at bad
       contradiction
     have lift {p q:Nat} (off:∀ u, group.label u ≠ group.label i → row p u = row q u) :
         ∀ u, group.label u ≠ group.label i → upd p u = upd q u := by
       intro u hu
       by_cases e:u = k
       · subst u; simp [upd]
       · simpa only [upd,Function.update_of_ne e] using off u hu
     have ac:code (row a) ≠ code (row c) := by
       intro e
       have bad := upper _ _ (lift fun _ hu => (share hu).1.trans (share hu).2)
         ((noChange a).trans (e.trans (noChange c).symm))
       change F (Function.update (row a) k bit) = F (Function.update (row c) k bit) at bad
       rw [evalA,evaluation vhc] at bad
       cases sign <;> cases bad
     have bc:code (row b) ≠ code (row c) := by
       intro e
       have bad := upper _ _ (lift fun _ hu => (share hu).2)
         ((noChange b).trans (e.trans (noChange c).symm))
       change F (Function.update (row b) k bit) = F (Function.update (row c) k bit) at bad
       rw [evalB,evaluation vhc] at bad
       cases sign <;> cases bad
     cases ha:code (row a) <;> cases hb:code (row b) <;> cases hc:code (row c) <;> simp_all
   · exact Or.inl eq

end PEqualNP.Outside.L_meta_1677.FrontRanks
