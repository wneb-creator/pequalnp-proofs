import PetersenSeventeenFull

namespace PEqualNP.Outside.L_meta_2373.RectangleRun

open Live1024

lemma run_length_le {R : Type} {u goal k} {roots : List (Wire R)}
    (h : Run u goal k roots) : roots.length ≤ k + 1 := by
  induction h using Run.ind with
  | stop => simp
  | perm p _ ih => simpa only [← p.length_eq] using ih
  | two op hd ka kb h ih =>
    cases ka <;> cases kb <;> simp [kept] at ih ⊢ <;> omega

lemma run_tight_measure {R : Type} (M : Wire R → Int)
    (subadd : ∀ d, allowed false d → ∀ a b, M (comb d a b) ≤ M a + M b)
    {goal k roots} (h : Run false goal k roots) (tight : roots.length = k + 1) :
    M goal ≤ (roots.map M).sum := by
  induction h using Run.ind with
  | stop => simp
  | perm p h ih =>
    have bound := ih (p.length_eq.trans tight)
    simpa only [(p.map M).sum_eq] using bound
  | @two s a b rest op hd ka kb h ih =>
    have len := run_length_le h
    have keeps : ka = false ∧ kb = false := by
      cases ka <;> cases kb <;> simp [kept] at len tight ⊢ <;> omega
    obtain ⟨rfl, rfl⟩ := keeps
    simp only [kept, Bool.false_eq_true, ite_false] at h ih
    have tailtight : (comb op a b :: rest).length = s + 1 := by
      simp only [List.length_cons] at tight ⊢
      omega
    have bound := ih tailtight
    calc
      M goal ≤ M (comb op a b) + (rest.map M).sum := by simpa using bound
      _ ≤ (M a + M b) + (rest.map M).sum := by
        have h := subadd op hd a b
        omega
      _ = ((a :: b :: rest).map M).sum := by simp [Int.add_assoc]

def rect {p q : Nat} (weight : Fin p → Fin q → Int)
    (S : Finset (Fin p)) (T : Finset (Fin q)) : Int := ∑ r ∈ S, ∑ c ∈ T, weight r c

def Bounds {R : Type} {p q : Nat} (P : Fin p → R) (N : Fin q → R)
    (weight : Fin p → Fin q → Int) (v : Wire R) (cap : Int) : Prop :=
  ∀ (S : Finset (Fin p)) (T : Finset (Fin q)),
    (∀ r ∈ S, v (P r) = true) → (∀ c ∈ T, v (N c) = false) → rect weight S T ≤ cap

lemma rect_union_left {p q : Nat} (weight : Fin p → Fin q → Int)
    (S U : Finset (Fin p)) (T : Finset (Fin q)) (h : Disjoint S U) :
    rect weight (S ∪ U) T = rect weight S T + rect weight U T := by
  exact Finset.sum_union h

lemma rect_union_right {p q : Nat} (weight : Fin p → Fin q → Int)
    (S : Finset (Fin p)) (T U : Finset (Fin q)) (h : Disjoint T U) :
    rect weight S (T ∪ U) = rect weight S T + rect weight S U := by
  simp only [rect, Finset.sum_union h, Finset.sum_add_distrib]

lemma bounds_and {R : Type} {p q : Nat} {P : Fin p → R} {N : Fin q → R}
    {weight : Fin p → Fin q → Int} {a b : Wire R} {ca cb : Int}
    (ha : Bounds P N weight a ca) (hb : Bounds P N weight b cb) :
    Bounds P N weight (combine false a b) (ca + cb) := by
  intro S T hs ht
  let T0 := T.filter (fun c => a (N c) = false)
  let T1 := T.filter (fun c => a (N c) = true)
  have part : T0 ∪ T1 = T := by
    ext c
    simp only [T0, T1, Finset.mem_union, Finset.mem_filter]
    cases a (N c) <;> simp
  have disj : Disjoint T0 T1 := by
    apply Finset.disjoint_left.mpr
    intro c hc hd
    have h0 := (Finset.mem_filter.mp hc).2
    have h1 := (Finset.mem_filter.mp hd).2
    exact Bool.false_ne_true (h0.symm.trans h1)
  have left := ha S T0
    (fun r hr => (Bool.and_eq_true_iff.mp (hs r hr)).1)
    (fun c hc => (Finset.mem_filter.mp hc).2)
  have right := hb S T1
    (fun r hr => (Bool.and_eq_true_iff.mp (hs r hr)).2)
    (fun c hc => by
      obtain ⟨hc, ah⟩ := Finset.mem_filter.mp hc
      have h := ht c hc
      change (a (N c) && b (N c)) = false at h
      simpa only [ah, Bool.true_and] using h)
  rw [← part, rect_union_right weight S T0 T1 disj]
  exact add_le_add left right

lemma bounds_or {R : Type} {p q : Nat} {P : Fin p → R} {N : Fin q → R}
    {weight : Fin p → Fin q → Int} {a b : Wire R} {ca cb : Int}
    (ha : Bounds P N weight a ca) (hb : Bounds P N weight b cb) :
    Bounds P N weight (combine true a b) (ca + cb) := by
  intro S T hs ht
  let S0 := S.filter (fun r => a (P r) = true)
  let S1 := S.filter (fun r => a (P r) = false)
  have part : S0 ∪ S1 = S := by
    ext r
    simp only [S0, S1, Finset.mem_union, Finset.mem_filter]
    cases a (P r) <;> simp
  have disj : Disjoint S0 S1 := by
    apply Finset.disjoint_left.mpr
    intro r hr hd
    have h0 := (Finset.mem_filter.mp hr).2
    have h1 := (Finset.mem_filter.mp hd).2
    exact Bool.false_ne_true (h1.symm.trans h0)
  have left := ha S0 T
    (fun r hr => (Finset.mem_filter.mp hr).2)
    (fun c hc => (Bool.or_eq_false_iff.mp (ht c hc)).1)
  have right := hb S1 T
    (fun r hr => by
      obtain ⟨hr, ah⟩ := Finset.mem_filter.mp hr
      have h := hs r hr
      change (a (P r) || b (P r)) = true at h
      simpa only [ah, Bool.false_or] using h)
    (fun c hc => (Bool.or_eq_false_iff.mp (ht c hc)).2)
  rw [← part, rect_union_left weight S0 S1 T disj]
  exact add_le_add left right

noncomputable def score {R : Type} {p q : Nat} (P : Fin p → R) (N : Fin q → R)
    (weight : Fin p → Fin q → Int) (v : Wire R)
    (st : Finset (Fin p) × Finset (Fin q)) : Int := by
  classical
  exact if (∀ r ∈ st.1, v (P r) = true) ∧ (∀ c ∈ st.2, v (N c) = false)
    then rect weight st.1 st.2 else 0

noncomputable def measure {R : Type} {p q : Nat} (P : Fin p → R) (N : Fin q → R)
    (weight : Fin p → Fin q → Int) (v : Wire R) : Int := by
  classical
  exact Finset.univ.sup' Finset.univ_nonempty (score P N weight v)

lemma bounds_measure {R : Type} {p q : Nat} (P : Fin p → R) (N : Fin q → R)
    (weight : Fin p → Fin q → Int) (v : Wire R) :
    Bounds P N weight v (measure P N weight v) := by
  classical
  intro S T hs ht
  have bound := Finset.le_sup' (f := score P N weight v) (Finset.mem_univ (S,T))
  have valid : (∀ r ∈ S, v (P r) = true) ∧ (∀ c ∈ T, v (N c) = false) := ⟨hs, ht⟩
  simpa only [score, if_pos valid, measure] using bound

lemma measure_le {R : Type} {p q : Nat} {P : Fin p → R} {N : Fin q → R}
    {weight : Fin p → Fin q → Int} {v : Wire R} {cap : Int}
    (h : Bounds P N weight v cap) : measure P N weight v ≤ cap := by
  classical
  have nonneg : 0 ≤ cap := by simpa [rect] using h ∅ ∅ (by simp) (by simp)
  apply (Finset.sup'_le_iff Finset.univ_nonempty (score P N weight v)).mpr
  intro st _
  unfold score
  split_ifs with valid
  · exact h st.1 st.2 valid.1 valid.2
  · exact nonneg

lemma measure_subadditive {R : Type} {p q : Nat} (P : Fin p → R) (N : Fin q → R)
    (weight : Fin p → Fin q → Int) (d : Nat) (hd : allowed false d) (a b : Wire R) :
    measure P N weight (comb d a b) ≤ measure P N weight a + measure P N weight b := by
  have small : d < 2 := by simpa [allowed] using hd
  have cases : d = 0 ∨ d = 1 := by omega
  rcases cases with rfl | rfl
  · exact measure_le (by simpa [comb] using bounds_and (bounds_measure P N weight a) (bounds_measure P N weight b))
  · exact measure_le (by simpa [comb] using bounds_or (bounds_measure P N weight a) (bounds_measure P N weight b))

lemma tight_run_bound {R : Type} {p q : Nat} (P : Fin p → R) (N : Fin q → R)
    (weight : Fin p → Fin q → Int) {goal k roots} (h : Run false goal k roots)
    (tight : roots.length = k + 1) :
    Bounds P N weight goal ((roots.map (measure P N weight)).sum) := by
  intro S T hs ht
  exact (bounds_measure P N weight goal S T hs ht).trans
    (run_tight_measure (measure P N weight) (measure_subadditive P N weight) h tight)

lemma tight_run_uniform {R : Type} {p q : Nat} (P : Fin p → R) (N : Fin q → R)
    (weight : Fin p → Fin q → Int) {goal k roots cap} (h : Run false goal k roots)
    (tight : roots.length = k + 1) (leaves : ∀ v ∈ roots, Bounds P N weight v cap)
    (positive : ∀ r, goal (P r) = true) (negative : ∀ c, goal (N c) = false) :
    rect weight Finset.univ Finset.univ ≤ (roots.length : Int) * cap := by
  have bound := tight_run_bound P N weight h tight Finset.univ Finset.univ
    (fun r _ => positive r) (fun c _ => negative c)
  have leafsum : (roots.map (measure P N weight)).sum ≤ (roots.length : Int) * cap := by
    clear h tight bound
    induction roots with
    | nil => simp
    | cons a rest ih =>
      have one := measure_le (leaves a (by simp))
      have tail := ih (fun v hv => leaves v (by simp [hv]))
      simpa [Int.add_mul, Int.add_comm, Int.add_left_comm, Int.add_assoc] using add_le_add one tail
  exact bound.trans leafsum

end PEqualNP.Outside.L_meta_2373.RectangleRun
