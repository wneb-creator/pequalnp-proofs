import RectangleRun

namespace PEqualNP.Outside.L_meta_2373.RectangleMaskCheck

open Live1024 RectangleRun

def rowScore {p q : Nat} (weight : Fin p → Fin q → Int)
    (rows : Finset (Fin p)) (cols : Finset (Fin q)) : Int :=
  ∑ c ∈ cols, max (∑ r ∈ rows, weight r c) 0

def colScore {p q : Nat} (weight : Fin p → Fin q → Int)
    (rows : Finset (Fin p)) (cols : Finset (Fin q)) : Int :=
  ∑ r ∈ rows, max (∑ c ∈ cols, weight r c) 0

def check {p q : Nat} (weight : Fin p → Fin q → Int)
    (rows : Finset (Fin p)) (cols : Finset (Fin q)) (cap : Int) : Bool :=
  if rows.card ≤ cols.card then
    decide (∀ S ∈ rows.powerset, rowScore weight S cols ≤ cap)
  else decide (∀ T ∈ cols.powerset, colScore weight rows T ≤ cap)

lemma check_sound {p q : Nat} (weight : Fin p → Fin q → Int)
    (rows : Finset (Fin p)) (cols : Finset (Fin q)) (cap : Int)
    (valid : check weight rows cols cap = true)
    (S : Finset (Fin p)) (T : Finset (Fin q)) (hs : S ⊆ rows) (ht : T ⊆ cols) :
    RectangleRun.rect weight S T ≤ cap := by
  unfold check at valid
  split_ifs at valid with small
  · have upper : rowScore weight S cols ≤ cap :=
      (of_decide_eq_true valid) S (Finset.mem_powerset.mpr hs)
    calc
      RectangleRun.rect weight S T = ∑ c ∈ T, ∑ r ∈ S, weight r c := by
        unfold RectangleRun.rect
        rw [Finset.sum_comm]
      _ ≤ ∑ c ∈ T, max (∑ r ∈ S, weight r c) 0 :=
        Finset.sum_le_sum (fun _ _ => le_max_left _ _)
      _ ≤ rowScore weight S cols :=
        Finset.sum_le_sum_of_subset_of_nonneg ht (fun _ _ _ => le_max_right _ _)
      _ ≤ cap := upper
  · have upper : colScore weight rows T ≤ cap :=
      (of_decide_eq_true valid) T (Finset.mem_powerset.mpr ht)
    calc
      RectangleRun.rect weight S T ≤ ∑ r ∈ S, max (∑ c ∈ T, weight r c) 0 :=
        Finset.sum_le_sum (fun _ _ => le_max_left _ _)
      _ ≤ colScore weight rows T :=
        Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => le_max_right _ _)
      _ ≤ cap := upper

lemma bounds_of_check {R : Type} {p q : Nat} (P : Fin p → R) (N : Fin q → R)
    (weight : Fin p → Fin q → Int) (rows : Finset (Fin p)) (cols : Finset (Fin q))
    (v : Wire R) (cap : Int) (valid : check weight rows cols cap = true)
    (positive : ∀ r, v (P r) = true → r ∈ rows)
    (negative : ∀ c, v (N c) = false → c ∈ cols) : Bounds P N weight v cap := by
  intro S T hs ht
  exact check_sound weight rows cols cap valid S T
    (fun r hr => positive r (hs r hr)) (fun c hc => negative c (ht c hc))

lemma bounds_empty_positive {R : Type} {p q : Nat} (P : Fin p → R) (N : Fin q → R)
    (weight : Fin p → Fin q → Int) (v : Wire R) (empty : ∀ r, v (P r) = false) :
    Bounds P N weight v 0 := by
  intro S T hs ht
  have eq : S = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro r hr
    exact Bool.false_ne_true ((empty r).symm.trans (hs r hr))
  simp [eq, RectangleRun.rect]

lemma bounds_empty_negative {R : Type} {p q : Nat} (P : Fin p → R) (N : Fin q → R)
    (weight : Fin p → Fin q → Int) (v : Wire R) (empty : ∀ c, v (N c) = true) :
    Bounds P N weight v 0 := by
  intro S T hs ht
  have eq : T = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro c hc
    exact Bool.false_ne_true ((ht c hc).symm.trans (empty c))
  simp [eq, RectangleRun.rect]

end PEqualNP.Outside.L_meta_2373.RectangleMaskCheck
