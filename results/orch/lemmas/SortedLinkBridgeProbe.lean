import PEqualNP.Defs

-- The live-wire checker and the smaller graph certificates are adapted from the project proofs
-- L_meta_1667 and L_meta_1677, distributed under Apache-2.0.
-- Each root search considers all nine inputs. Restriction bounds and conflicting truth-table
-- rows eliminate children, and checked graph permutations identify equivalent states.
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_670.Projection
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
abbrev BoundPool := Sig × Nat × Nat × List Sig
abbrev Bits := BitVec 278
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

abbrev Cov := Bits × Bits × Bits

abbrev CovPair := Cov × Bool
abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List (List Sig))
noncomputable def force {β : Type} (n : Nat) (f : Nat → β) : β := Nat.rec (f 0) (fun k _ => f (Nat.succ k)) n
theorem force_eq {β : Type} (n : Nat) (f : Nat → β) : force n f = f n := by cases n <;> rfl
noncomputable def forceMap {α β : Type} (f : α → Nat) (l : List α) : (List Nat → β) → β :=
  List.rec (fun k => k []) (fun a _ ih k => force (f a) fun x => ih fun xs => k (x::xs)) l
theorem forceMap_eq {α β : Type} (f : α → Nat) (l : List α) (k : List Nat → β) : forceMap f l k = k (l.map f) := by
  induction l generalizing k with
  | nil => rfl
  | cons a l ih =>
    change force (f a) (fun x => forceMap f l fun xs => k (x::xs)) = _
    rw [force_eq,ih]
    rfl
noncomputable def anyEq (m : Nat) (l : List Nat) : Bool := List.rec false (fun v _ ih => or (Nat.beq m v) ih) l
def zN (op x y : Nat) : Nat := cond (Nat.beq op 0) (Nat.land x y) (cond (Nat.beq op 1) (Nat.lor x y)
  (cond (Nat.beq op 2) (Nat.xor x (Nat.land x y)) (Nat.xor y (Nat.land x y))))
abbrev QS := Nat × Nat × Nat × Nat × Nat × List Nat × List Nat × Bool
def kwN (v : Nat) : Nat :=
  let n := v % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
abbrev Lane := NodeContext × Nat × Nat × List QS × List Nat × Nat
theorem anyEq_iff (m : Nat) (l : List Nat) : anyEq m l=true ↔ m ∈ l := by
  induction l with
  | nil => simp [anyEq]
  | cons a l ih =>
    change or (Nat.beq m a) (anyEq m l)=true ↔ _
    rw [Bool.or_eq_true,ih,Nat.beq_eq,List.mem_cons]
def keptLink (x y : Nat) (ka kb : Bool) (v : Nat) : Bool :=
  (ka || !(Nat.beq v x)) && (kb || !(Nat.beq v y))

noncomputable def sortedLinkCheck (xs ys : List Nat) (x y z : Nat) (ka kb : Bool) : Bool :=
  anyEq z ys &&
    ((z :: xs.filter (keptLink x y ka kb)).mergeSort Nat.ble == ys.mergeSort Nat.ble)

noncomputable def oldLinkCheck (xs ys : List Nat) (x y z : Nat) (ka kb : Bool) : Bool :=
  anyEq z ys &&
    (xs.all fun v => ((!ka) && (Nat.beq v x)) || ((!kb) && (Nat.beq v y)) || anyEq v ys) &&
    (ys.all fun v => (Nat.beq v z) || (((ka || !(Nat.beq v x)) && (kb || !(Nat.beq v y))) && anyEq v xs))

theorem sortedLinkCheck_sound {xs ys : List Nat} {x y z : Nat} {ka kb : Bool}
    (h : sortedLinkCheck xs ys x y z ka kb = true) :
    oldLinkCheck xs ys x y z ka kb = true := by
  have hh : anyEq z ys=true ∧
      ((z :: xs.filter (keptLink x y ka kb)).mergeSort Nat.ble == ys.mergeSort Nat.ble)=true := by
    simpa only [sortedLinkCheck,Bool.and_eq_true] using h
  have hz := hh.1
  have he : (z :: xs.filter (keptLink x y ka kb)).mergeSort Nat.ble = ys.mergeSort Nat.ble :=
    by simpa only [beq_iff_eq] using hh.2
  have hm (v : Nat) : v ∈ z :: xs.filter (keptLink x y ka kb) ↔ v ∈ ys := by
    have hh := congrArg (fun l : List Nat => v ∈ l) he
    simpa only [List.mem_mergeSort] using Iff.of_eq hh
  have nf (a b : Nat) (hne : a ≠ b) : Nat.beq a b = false := by
    cases he : Nat.beq a b with
    | false => rfl
    | true => exact False.elim (hne (by simpa only [Nat.beq_eq] using he))
  simp only [oldLinkCheck,Bool.and_eq_true,List.all_eq_true,Bool.or_eq_true,anyEq_iff,
    Nat.beq_eq,beq_iff_eq,Bool.not_eq_true']
  refine ⟨⟨(anyEq_iff z ys).mp hz,?_⟩,?_⟩
  · intro v hv
    by_cases hx : ka=false ∧ v=x
    · exact Or.inl (Or.inl hx)
    by_cases hy : kb=false ∧ v=y
    · exact Or.inl (Or.inr hy)
    apply Or.inr
    apply (hm v).mp
    apply List.mem_cons_of_mem
    apply List.mem_filter.mpr
    refine ⟨hv,?_⟩
    cases ka <;> cases kb <;> simp_all [keptLink,nf]
  · intro v hv
    rcases List.mem_cons.mp ((hm v).mpr hv) with he | hk
    · exact Or.inl he
    obtain ⟨hx,hk⟩ := List.mem_filter.mp hk
    apply Or.inr
    exact ⟨by simpa only [keptLink,Bool.and_eq_true,Bool.or_eq_true,Bool.not_eq_true',Nat.beq_eq,beq_iff_eq] using hk,hx⟩


noncomputable def linkAt (fl : Nat → Option (List Nat)) (l : Lane) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (l.2.2.2.2.1.getD i 0) fun x => force (l.2.2.2.2.1.getD j 0) fun y => force (zN op x y) fun z =>
  Option.rec false (fun ys => forceMap (fun v => v) ys fun ys =>
    and (anyEq z ys) (and (l.2.2.2.2.1.all fun v => or (and (not ka) (Nat.beq v x)) (or (and (not kb) (Nat.beq v y)) (anyEq v ys)))
      (ys.all fun v => or (Nat.beq v z) (and (and (or ka (not (Nat.beq v x))) (or kb (not (Nat.beq v y)))) (anyEq v l.2.2.2.2.1)))))
    (fl (Nat.add (kwN z) (Nat.sub (Nat.sub l.2.2.2.2.2 (cond ka 0 (kwN x))) (cond kb 0 (kwN y)))))
noncomputable def linkAtSorted (fl : Nat → Option (List Nat)) (l : Lane) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (l.2.2.2.2.1.getD i 0) fun x => force (l.2.2.2.2.1.getD j 0) fun y => force (zN op x y) fun z =>
  Option.rec false (fun ys => forceMap (fun v => v) ys fun ys =>
    sortedLinkCheck l.2.2.2.2.1 ys x y z ka kb)
    (fl (Nat.add (kwN z) (Nat.sub (Nat.sub l.2.2.2.2.2 (cond ka 0 (kwN x))) (cond kb 0 (kwN y)))))

theorem linkAtSorted_sound {fl : Nat → Option (List Nat)} {l : Lane} {i j op : Nat} {ka kb : Bool}
    (h : linkAtSorted fl l i j op ka kb=true) : linkAt fl l i j op ka kb=true := by
  simp only [linkAtSorted,linkAt,force_eq,forceMap_eq,List.map_id'] at h ⊢
  generalize hq : fl _ = q at h ⊢
  cases q with
  | none => exact h
  | some ys =>
    simpa only [oldLinkCheck,Bool.and_assoc,Bool.or_assoc] using sortedLinkCheck_sound h

end PEqualNP.Outside.L_meta_670.Projection

open PEqualNP.Outside.L_meta_670.Projection

