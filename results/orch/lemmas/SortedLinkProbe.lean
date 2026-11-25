import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_670.SortedLink

noncomputable def anyEq (m : Nat) (l : List Nat) : Bool := List.rec false (fun v _ ih => or (Nat.beq m v) ih) l

theorem anyEq_iff (m : Nat) (l : List Nat) : anyEq m l=true ↔ m ∈ l := by
  induction l with
  | nil => simp [anyEq]
  | cons a l ih =>
    change or (Nat.beq m a) (anyEq m l)=true ↔ _
    rw [Bool.or_eq_true,ih,Nat.beq_eq,List.mem_cons]

def keptLink (x y : Nat) (ka kb : Bool) (v : Nat) : Bool :=
  (ka || !(v == x)) && (kb || !(v == y))

noncomputable def sortedLinkCheck (xs ys : List Nat) (x y z : Nat) (ka kb : Bool) : Bool :=
  anyEq z ys &&
    ((z :: xs.filter (keptLink x y ka kb)).mergeSort Nat.ble == ys.mergeSort Nat.ble)

noncomputable def oldLinkCheck (xs ys : List Nat) (x y z : Nat) (ka kb : Bool) : Bool :=
  anyEq z ys &&
    (xs.all fun v => ((!ka) && (v == x)) || ((!kb) && (v == y)) || anyEq v ys) &&
    (ys.all fun v => (v == z) || (((ka || !(v == x)) && (kb || !(v == y))) && anyEq v xs))

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
  simp only [oldLinkCheck,Bool.and_eq_true,List.all_eq_true,Bool.or_eq_true,anyEq_iff,
    beq_iff_eq,Bool.not_eq_true']
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
    cases ka <;> cases kb <;> simp_all [keptLink]
  · intro v hv
    rcases List.mem_cons.mp ((hm v).mpr hv) with he | hk
    · exact Or.inl he
    obtain ⟨hx,hk⟩ := List.mem_filter.mp hk
    apply Or.inr
    exact ⟨by simpa only [keptLink,Bool.and_eq_true,Bool.or_eq_true,Bool.not_eq_true',beq_iff_eq] using hk,hx⟩

end PEqualNP.Outside.L_meta_670.SortedLink
