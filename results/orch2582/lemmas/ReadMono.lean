import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2582_aux.ReadMono

open PEqualNP.CircuitLowerBounds PEqualNP.ReadK

def CapLift (k : ℕ) (A B : List (List ℕ)) : Prop :=
  ∀ u ∈ A, ∃ v ∈ B, u = v.map (fun x => min x (k + 1))

lemma mem_insert (acc : List (List ℕ)) (v x : List ℕ) :
    x ∈ insertNew acc v ↔ x ∈ acc ∨ x = v := by
  unfold insertNew
  split_ifs with hv
  · constructor
    · exact Or.inl
    · rintro (hx | rfl)
      · exact hx
      · exact hv
  · simp

lemma mem_insert_fold (l acc : List (List ℕ)) (x : List ℕ) :
    x ∈ l.foldl insertNew acc ↔ x ∈ acc ∨ x ∈ l := by
  induction l generalizing acc with
  | nil => simp
  | cons v vs ih =>
    simp only [List.foldl_cons, List.mem_cons]
    rw [ih, mem_insert]
    tauto

lemma mem_and (k : ℕ) (A B : List (List ℕ)) (w : List ℕ) :
    w ∈ andStep k A B ↔ ∃ p ∈ A, ∃ q ∈ B, capAdd k p q = w := by
  unfold andStep
  rw [mem_insert_fold]
  simp

lemma cap_add_map (k l : ℕ) (hkl : k ≤ l) (u v : List ℕ) :
    capAdd k (u.map (fun x => min x (k + 1)))
      (v.map (fun x => min x (k + 1))) =
      (capAdd l u v).map (fun x => min x (k + 1)) := by
  induction u generalizing v with
  | nil => simp [capAdd]
  | cons a u ih =>
    cases v with
    | nil => simp [capAdd]
    | cons b v =>
      simp only [capAdd, List.map_cons, List.zipWith_cons_cons]
      congr 1
      · omega
      · exact ih v

lemma lift_empty (k : ℕ) : CapLift k [] [] := by
  simp [CapLift]

lemma lift_insert_fold {k : ℕ} {A B X Y : List (List ℕ)}
    (hAB : CapLift k A B) (hXY : CapLift k X Y) :
    CapLift k (X.foldl insertNew A) (Y.foldl insertNew B) := by
  intro u hu
  rw [mem_insert_fold] at hu
  rcases hu with hu | hu
  · obtain ⟨v, hv, huv⟩ := hAB u hu
    exact ⟨v, (mem_insert_fold _ _ _).2 (Or.inl hv), huv⟩
  · obtain ⟨v, hv, huv⟩ := hXY u hu
    exact ⟨v, (mem_insert_fold _ _ _).2 (Or.inr hv), huv⟩

lemma lift_and {k l : ℕ} (hkl : k ≤ l) {A B X Y : List (List ℕ)}
    (hAB : CapLift k A B) (hXY : CapLift k X Y) :
    CapLift k (andStep k A X) (andStep l B Y) := by
  intro u hu
  obtain ⟨p, hp, q, hq, rfl⟩ := (mem_and _ _ _ _).1 hu
  obtain ⟨p', hp', rfl⟩ := hAB p hp
  obtain ⟨q', hq', rfl⟩ := hXY q hq
  exact ⟨capAdd l p' q', (mem_and _ _ _ _).2 ⟨p', hp', q', hq', rfl⟩,
    cap_add_map k l hkl p' q'⟩

lemma lift_or_fold {k : ℕ} {X Y : List (List (List ℕ))}
    (hXY : List.Forall₂ (CapLift k) X Y) {A B : List (List ℕ)}
    (hAB : CapLift k A B) :
    CapLift k (X.foldl (fun acc L => L.foldl insertNew acc) A)
      (Y.foldl (fun acc L => L.foldl insertNew acc) B) := by
  induction hXY generalizing A B with
  | nil => exact hAB
  | cons h htail ih => exact ih (lift_insert_fold hAB h)

lemma lift_and_fold {k l : ℕ} (hkl : k ≤ l) {X Y : List (List (List ℕ))}
    (hXY : List.Forall₂ (CapLift k) X Y) {A B : List (List ℕ)}
    (hAB : CapLift k A B) :
    CapLift k (X.foldl (andStep k) A) (Y.foldl (andStep l) B) := by
  induction hXY generalizing A B with
  | nil => exact hAB
  | cons h htail ih => exact ih (lift_and hkl hAB h)

lemma forall₂_getD {α β : Type} {R : α → β → Prop} {A : List α} {B : List β}
    (h : List.Forall₂ R A B) (i : ℕ) (a : α) (b : β) (hab : R a b) :
    R (A.getD i a) (B.getD i b) := by
  induction h generalizing i with
  | nil => simpa using hab
  | cons h htail ih =>
    cases i with
    | zero => simpa using h
    | succ i => simpa using ih i

lemma lift_leaf (S : List ℕ) (k l i : ℕ) :
    CapLift k (leafVectors S k i) (leafVectors S l i) := by
  unfold leafVectors
  split_ifs with hi
  · intro u hu
    simp only [List.mem_singleton] at hu
    subst u
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    simp only [List.map_map]
    apply List.map_congr_left
    intro j hj
    split_ifs <;> simp_all
  · exact lift_empty k

def gateVectors (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate) :
    List (List ℕ) :=
  let ins := g.inputs.map fun i => R.getD i []
  match g.op with
  | GateOp.or => ins.foldl (fun acc A => A.foldl insertNew acc) []
  | GateOp.and => ins.foldl (andStep k) [S.map fun _ => 0]
  | _ => []

lemma lift_gate {k l : ℕ} (hkl : k ≤ l) (S : List ℕ)
    {A B : List (List (List ℕ))} (hAB : List.Forall₂ (CapLift k) A B) (g : Gate) :
    CapLift k (gateVectors S k A g) (gateVectors S l B g) := by
  have hi : List.Forall₂ (CapLift k)
      (g.inputs.map fun i => A.getD i []) (g.inputs.map fun i => B.getD i []) := by
    induction g.inputs with
    | nil => exact .nil
    | cons i is ih =>
      exact .cons (forall₂_getD hAB i [] [] (lift_empty k)) ih
  have hz : CapLift k [S.map fun _ => 0] [S.map fun _ => 0] := by
    intro u hu
    simp only [List.mem_singleton] at hu
    subst u
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    simp
  unfold gateVectors
  cases g.op with
  | and => exact lift_and_fold hkl hi hz
  | or => exact lift_or_fold hi (lift_empty k)
  | not => exact lift_empty k
  | maj => exact lift_empty k
  | mod m => exact lift_empty k

lemma lift_gates {k l : ℕ} (hkl : k ≤ l) (S : List ℕ) (gs : List Gate)
    {A B : List (List (List ℕ))} (hAB : List.Forall₂ (CapLift k) A B) :
    List.Forall₂ (CapLift k)
      (gs.foldl (fun R g => R ++ [gateVectors S k R g]) A)
      (gs.foldl (fun R g => R ++ [gateVectors S l R g]) B) := by
  induction gs generalizing A B with
  | nil => exact hAB
  | cons g gs ih =>
    exact ih (List.rel_append hAB (.cons (lift_gate hkl S hAB g) .nil))

lemma lift_vectors (C : Circuit) (n : ℕ) (S : List ℕ) {k l : ℕ} (hkl : k ≤ l) :
    List.Forall₂ (CapLift k) (readVectors C n S k) (readVectors C n S l) := by
  apply lift_gates hkl S C.gates
  induction List.range n with
  | nil => exact .nil
  | cons i is ih => exact .cons (lift_leaf S k l i) ih

theorem readsAtMost_mono (C : Circuit) (n : ℕ) (S : List ℕ) {k l : ℕ}
    (hkl : k ≤ l) (h : readsAtMost C n S k = true) :
    readsAtMost C n S l = true := by
  unfold readsAtMost at h ⊢
  obtain ⟨u, hu, hgood⟩ := List.any_eq_true.1 h
  obtain ⟨v, hv, rfl⟩ :=
    forall₂_getD (lift_vectors C n S hkl) C.output [] [] (lift_empty k) u hu
  apply List.any_eq_true.2
  refine ⟨v, hv, List.all_eq_true.2 ?_⟩
  intro a ha
  have ht := List.all_eq_true.1 hgood (min a (k + 1)) (List.mem_map_of_mem ha)
  simp only [decide_eq_true_eq] at ht ⊢
  omega

theorem isReadK_mono (C : Circuit) (n : ℕ) {k l : ℕ} (hkl : k ≤ l)
    (h : IsReadK n C k) : IsReadK n C l := by
  intro S hS
  exact readsAtMost_mono C n (setList S) hkl (h S hS)

end PEqualNP.Outside.L_meta_2582_aux.ReadMono
