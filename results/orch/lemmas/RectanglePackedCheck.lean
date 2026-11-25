import RectangleRun

namespace PEqualNP.Outside.L_meta_2373.RectanglePackedCheck

open Live1024 RectangleRun

def rowScore (w : Nat → Nat → Int) (rows cols : List Nat) : Int :=
  cols.foldl (fun total c => total + max (rows.foldl (fun acc r => acc + w r c) 0) 0) 0

def rowCheck (w : Nat → Nat → Int) : List Nat → List Nat → List Nat → Int → Bool
  | [], selected, cols, cap => decide (rowScore w selected cols ≤ cap)
  | r :: rest, selected, cols, cap =>
      rowCheck w rest selected cols cap && rowCheck w rest (r :: selected) cols cap

def check (w : Nat → Nat → Int) (rows cols : List Nat) (cap : Int) : Bool :=
  if rows.length ≤ cols.length then rowCheck w rows [] cols cap
  else rowCheck (fun c r => w r c) cols [] rows cap

lemma foldl_add_sum {α : Type} (f : α → Int) (xs : List α) (z : Int) :
    xs.foldl (fun acc x => acc + f x) z = z + (xs.map f).sum := by
  induction xs generalizing z with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih, add_assoc]

lemma sum_map_toFinset {α : Type} [DecidableEq α] (f : α → Int)
    (xs : List α) (hn : xs.Nodup) :
    (xs.map f).sum = ∑ x ∈ xs.toFinset, f x := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have h := List.nodup_cons.mp hn
    have hx : x ∉ xs.toFinset := by simpa using h.1
    rw [List.map_cons, List.sum_cons, List.toFinset_cons, Finset.sum_insert hx, ih h.2]

lemma rowScore_finset (w : Nat → Nat → Int) (rows cols : List Nat)
    (hr : rows.Nodup) (hc : cols.Nodup) :
    rowScore w rows cols =
      ∑ c ∈ cols.toFinset, max (∑ r ∈ rows.toFinset, w r c) 0 := by
  unfold rowScore
  rw [foldl_add_sum, zero_add, sum_map_toFinset _ _ hc]
  apply Finset.sum_congr rfl
  intro c h
  rw [foldl_add_sum, zero_add, sum_map_toFinset _ _ hr]

lemma rowCheck_filter (w : Nat → Nat → Int) (remaining selected cols : List Nat)
    (cap : Int) (S : Finset Nat) (valid : rowCheck w remaining selected cols cap = true) :
    rowScore w ((remaining.filter (fun r => decide (r ∈ S))).reverse ++ selected) cols ≤ cap := by
  induction remaining generalizing selected with
  | nil =>
    simpa only [List.filter_nil, List.reverse_nil, List.nil_append, rowCheck,
      decide_eq_true_eq] using valid
  | cons r rest ih =>
    have both : rowCheck w rest selected cols cap = true ∧
        rowCheck w rest (r :: selected) cols cap = true := by
      simpa only [rowCheck, Bool.and_eq_true] using valid
    by_cases hr : r ∈ S
    · have chosen := ih (r :: selected) both.2
      simpa [hr, List.reverse_cons, List.append_assoc] using chosen
    · have skipped := ih selected both.1
      simpa [hr] using skipped

lemma rowCheck_sound (w : Nat → Nat → Int) (rows cols : List Nat) (cap : Int)
    (hr : rows.Nodup) (hc : cols.Nodup) (valid : rowCheck w rows [] cols cap = true)
    (S T : Finset Nat) (hs : S ⊆ rows.toFinset) (ht : T ⊆ cols.toFinset) :
    (∑ r ∈ S, ∑ c ∈ T, w r c) ≤ cap := by
  have selected := rowCheck_filter w rows [] cols cap S valid
  have nodup : ((rows.filter (fun r => decide (r ∈ S))).reverse).Nodup := by
    simpa using hr.filter (fun r => decide (r ∈ S))
  have chosenSet : ((rows.filter (fun r => decide (r ∈ S))).reverse).toFinset = S := by
    ext r
    simp only [List.mem_toFinset, List.mem_reverse, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨List.mem_toFinset.mp (hs h), h⟩⟩
  simp only [List.append_nil] at selected
  rw [rowScore_finset _ _ _ nodup hc, chosenSet] at selected
  calc
    (∑ r ∈ S, ∑ c ∈ T, w r c) = ∑ c ∈ T, ∑ r ∈ S, w r c := Finset.sum_comm
    _ ≤ ∑ c ∈ T, max (∑ r ∈ S, w r c) 0 :=
      Finset.sum_le_sum (fun _ _ => le_max_left _ _)
    _ ≤ ∑ c ∈ cols.toFinset, max (∑ r ∈ S, w r c) 0 :=
      Finset.sum_le_sum_of_subset_of_nonneg ht (fun _ _ _ => le_max_right _ _)
    _ ≤ cap := selected

lemma check_sound (w : Nat → Nat → Int) (rows cols : List Nat) (cap : Int)
    (hr : rows.Nodup) (hc : cols.Nodup) (valid : check w rows cols cap = true)
    (S T : Finset Nat) (hs : S ⊆ rows.toFinset) (ht : T ⊆ cols.toFinset) :
    (∑ r ∈ S, ∑ c ∈ T, w r c) ≤ cap := by
  unfold check at valid
  split_ifs at valid with small
  · exact rowCheck_sound w rows cols cap hr hc valid S T hs ht
  · have transposed := rowCheck_sound (fun c r => w r c) cols rows cap hc hr valid T S ht hs
    rwa [Finset.sum_comm] at transposed

lemma sum_image_val {n : Nat} (S : Finset (Fin n)) (f : Nat → Int) :
    (∑ i ∈ S.image Fin.val, f i) = ∑ i ∈ S, f i.val := by
  apply Finset.sum_image
  intro a ha b hb hab
  exact Fin.ext hab

lemma bounds_of_check {R : Type} {p q : Nat} (P : Fin p → R) (N : Fin q → R)
    (w : Nat → Nat → Int) (rows cols : List Nat) (v : Wire R) (cap : Int)
    (hr : rows.Nodup) (hc : cols.Nodup) (valid : check w rows cols cap = true)
    (positive : ∀ r, v (P r) = true → r.val ∈ rows)
    (negative : ∀ c, v (N c) = false → c.val ∈ cols) :
    Bounds P N (fun r c => w r.val c.val) v cap := by
  intro S T hs ht
  have rowsSub : S.image Fin.val ⊆ rows.toFinset := by
    intro r h
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h
    exact List.mem_toFinset.mpr (positive i (hs i hi))
  have colsSub : T.image Fin.val ⊆ cols.toFinset := by
    intro c h
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h
    exact List.mem_toFinset.mpr (negative i (ht i hi))
  have upper := check_sound w rows cols cap hr hc valid _ _ rowsSub colsSub
  rw [sum_image_val] at upper
  simp_rw [sum_image_val] at upper
  exact upper

end PEqualNP.Outside.L_meta_2373.RectanglePackedCheck
