import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1884

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def graph (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def adjacent (i j : Fin 10) : Bool :=
  (([50,69,138,276,521,385,770,548,104,208] : List ℕ).getD i.val 0).testBit j.val

def pinned (j k v : Fin 10) (a b : Bool) (w : Fin 10) : Bool :=
  if w = j then a else if w = k then b else decide (w = v)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
lemma pivotal_probes :
    ∀ (i j k : Fin 10) (a b : Bool), i ≠ j → i ≠ k → j ≠ k →
      ¬ (a = true ∧ b = true ∧ adjacent j k = true) →
      ∃ v : Fin 10, ∀ z : Bool,
        graph (Function.update (pinned j k v a b) i z) = z := by
  decide +kernel

lemma pivotal : ∀ (i j k : Fin 10) (a b : Bool), i ≠ j → i ≠ k → j ≠ k →
    ¬ (a = true ∧ b = true ∧ adjacent j k = true) →
    ∃ x : Fin 10 → Bool, x j = a ∧ x k = b ∧
      ∀ z : Bool, graph (Function.update x i z) = z := by
  intro i j k a b hij hik hjk hpin
  obtain ⟨v,hv⟩ := pivotal_probes i j k a b hij hik hjk hpin
  exact ⟨pinned j k v a b, by simp [pinned], by simp [pinned,Ne.symm hjk], hv⟩


set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
lemma graph_eq_adjacent : ∀ x : Fin 10 → Bool,
    graph x = decide (∃ i j : Fin 10, x i = true ∧ x j = true ∧ adjacent i j = true) := by
  let edges : List (Fin 10 × Fin 10) :=
    [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),
      (5,7),(7,9),(9,6),(6,8),(8,5)]
  have table : ∀ i j : Fin 10, adjacent i j = true ↔ (i,j) ∈ edges ∨ (j,i) ∈ edges := by
    decide +kernel
  intro x
  have heq : graph x = edges.any (fun e => x e.1 && x e.2) := by
    simp [edges,graph,Bool.or_assoc]
  rw [heq]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true,Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨⟨i,j⟩,he,hi,hj⟩
    exact ⟨i,j,hi,hj,(table i j).mpr (Or.inl he)⟩
  · rintro ⟨i,j,hi,hj,ha⟩
    rcases (table i j).mp ha with he | he
    · exact ⟨(i,j),he,hi,hj⟩
    · exact ⟨(j,i),he,hj,hi⟩

lemma pivotal_adjacent : ∀ (i j k : Fin 10) (a b : Bool), i ≠ j → i ≠ k → j ≠ k →
    ¬ (a = true ∧ b = true ∧ adjacent j k = true) →
    ∃ x : Fin 10 → Bool, x j = a ∧ x k = b ∧ ∀ z : Bool,
      decide (∃ p l : Fin 10, Function.update x i z p = true ∧
        Function.update x i z l = true ∧ adjacent p l = true) = z := by
  intro i j k a b hij hik hjk hpin
  obtain ⟨x,hxj,hxk,hx⟩ := pivotal i j k a b hij hik hjk hpin
  exact ⟨x,hxj,hxk,fun z => (graph_eq_adjacent _).symm.trans (hx z)⟩

def vertexDeleted (x : Fin 9 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
  x 5 && x 7 || x 6 && x 8 || x 8 && x 5

def extendNine (x : Fin 9 → Bool) (i : Fin 10) : Bool :=
  if h : i.val < 9 then x ⟨i.val,h⟩ else false

lemma cofactor_nine (x : Fin 9 → Bool) : graph (extendNine x) = vertexDeleted x := by
  simp [graph,vertexDeleted,extendNine]

set_option maxHeartbeats 1000000 in
lemma cofactor_zero_true : ∀ x : Fin 10 → Bool,
    graph (Function.update x 0 true) =
      (x 1 || x 4 || x 5 ||
        (x 2 && x 3 || x 3 && x 8 || x 8 && x 6 ||
          x 6 && x 9 || x 9 && x 7 || x 7 && x 2)) := by
  decide +kernel

lemma degree_three : ∀ i : Fin 10,
    (Finset.univ.filter fun j => adjacent i j = true).card = 3 := by
  decide +kernel

lemma no_triangles : ∀ i j k : Fin 10,
    adjacent i j = true → adjacent i k = true → adjacent j k = false := by
  decide +kernel

lemma common_neighbors : ∀ i j : Fin 10, i ≠ j →
    (Finset.univ.filter fun k => adjacent i k = true ∧ adjacent j k = true).card =
      if adjacent i j then 0 else 1 := by
  decide +kernel

lemma essential_probe : ∀ i : Fin 10, ∃ v : Fin 10, ∀ z : Bool,
    graph (Function.update (fun w => decide (w = v)) i z) = z := by
  decide +kernel


lemma one_pin_probes : ∀ (i j : Fin 10) (b : Bool), i ≠ j →
    ∃ v : Fin 10, ∀ z : Bool,
      graph (Function.update (pinned j j v b b) i z) = z := by
  decide +kernel

lemma one_pin_pivotal (i j : Fin 10) (b : Bool) (hij : i ≠ j) :
    ∃ x : Fin 10 → Bool, x j = b ∧ ∀ z : Bool,
      graph (Function.update x i z) = z := by
  obtain ⟨v,hv⟩ := one_pin_probes i j b hij
  exact ⟨pinned j j v b b,by simp [pinned],hv⟩

lemma no_and_funnel (i j : Fin 10) (hij : i ≠ j) :
    ¬ ∃ H : Bool → (Fin 10 → Bool) → Bool, ∀ x : Fin 10 → Bool,
      graph x = H (x i && x j) (Function.update x i false) := by
  rintro ⟨H,hH⟩
  obtain ⟨x,hx,hp⟩ := one_pin_pivotal i j false hij
  have eq : graph (Function.update x i false) = graph (Function.update x i true) := by
    rw [hH,hH]
    simp [Function.update_of_ne (Ne.symm hij),hx]
  rw [hp false,hp true] at eq
  cases eq

lemma no_or_funnel (i j : Fin 10) (hij : i ≠ j) :
    ¬ ∃ H : Bool → (Fin 10 → Bool) → Bool, ∀ x : Fin 10 → Bool,
      graph x = H (x i || x j) (Function.update x i false) := by
  rintro ⟨H,hH⟩
  obtain ⟨x,hx,hp⟩ := one_pin_pivotal i j true hij
  have eq : graph (Function.update x i false) = graph (Function.update x i true) := by
    rw [hH,hH]
    simp [Function.update_of_ne (Ne.symm hij),hx]
  rw [hp false,hp true] at eq
  cases eq


def moveNine (i j : Fin 10) : Fin 10 :=
  (([[2,3,8,6,1,7,4,5,9,0],
    [4,3,8,5,0,9,2,6,7,1],
    [0,4,9,6,1,5,3,7,8,2],
    [1,0,5,7,2,6,4,8,9,3],
    [1,2,7,5,0,6,3,9,8,4],
    [1,2,3,4,0,6,7,8,9,5],
    [0,4,3,2,1,5,9,8,7,6],
    [1,0,4,3,2,6,5,9,8,7],
    [2,1,0,4,3,7,6,5,9,8],
    [0,1,2,3,4,5,6,7,8,9]] : List (List (Fin 10))).getD i.val []).getD j.val 0

lemma moveNine_injective : ∀ i : Fin 10, Function.Injective (moveNine i) := by
  decide +kernel

lemma moveNine_last : ∀ i : Fin 10, moveNine i 9 = i := by
  decide +kernel

lemma moveNine_adjacent : ∀ i a b : Fin 10,
    adjacent (moveNine i a) (moveNine i b) = adjacent a b := by
  decide +kernel

lemma graph_moveNine (i : Fin 10) (x : Fin 10 → Bool) :
    graph (x ∘ moveNine i) = graph x := by
  rw [graph_eq_adjacent,graph_eq_adjacent]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq,Function.comp_apply]
  constructor
  · rintro ⟨a,b,ha,hb,hab⟩
    exact ⟨moveNine i a,moveNine i b,ha,hb,(moveNine_adjacent i a b).trans hab⟩
  · rintro ⟨a,b,ha,hb,hab⟩
    have hs := Finite.surjective_of_injective (moveNine_injective i)
    obtain ⟨a,rfl⟩ := hs a
    obtain ⟨b,rfl⟩ := hs b
    exact ⟨a,b,ha,hb,(moveNine_adjacent i a b).symm.trans hab⟩

lemma cofactor_any_vertex (i : Fin 10) (x : Fin 10 → Bool) :
    graph (Function.update x i false) =
      vertexDeleted (fun j : Fin 9 => x (moveNine i j.castSucc)) := by
  rw [← graph_moveNine i (Function.update x i false)]
  have hfun : (Function.update x i false) ∘ moveNine i =
      extendNine (fun j : Fin 9 => x (moveNine i j.castSucc)) := by
    funext j
    by_cases hj : j = 9
    · subst j
      simp [Function.comp_apply,moveNine_last,extendNine]
    · have hjlt : j.val < 9 := by omega
      have hne : moveNine i j ≠ i := by
        intro h
        apply hj
        apply moveNine_injective i
        exact h.trans (moveNine_last i).symm
      simp only [Function.comp_apply,Function.update_of_ne hne,extendNine,dif_pos hjlt]
      rfl
  rw [hfun,cofactor_nine]

def deleteZeroOrder (i : Fin 9) : Fin 9 :=
  ([1,2,7,5,0,6,3,4,8] : List (Fin 9)).getD i.val 0

lemma deleteZeroOrder_injective : Function.Injective deleteZeroOrder := by
  decide +kernel

lemma cofactor_zero_canonical : ∀ x : Fin 9 → Bool,
    graph (Fin.cons false x) = vertexDeleted (x ∘ deleteZeroOrder) := by
  decide +kernel

end PEqualNP.Outside.L_meta_1884
