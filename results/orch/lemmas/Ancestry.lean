import PEqualNP.Outside.L_meta_1024

namespace PEqualNP.Outside.L_meta_1024_aux.Ancestry

open PEqualNP.CircuitLowerBounds

def step (w : List (Finset ℕ)) (g : Gate) : List (Finset ℕ) :=
  w ++ [insert w.length (g.inputs.toFinset.biUnion fun i => w.getD i ∅)]

def run (gs : List Gate) : List (Finset ℕ) :=
  gs.foldl step (List.ofFn fun i : Fin 13 => ({i.val} : Finset ℕ))

def anc (gs : List Gate) (i : ℕ) : Finset ℕ := (run gs).getD i ∅

lemma fold_length (gs : List Gate) (w : List (Finset ℕ)) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp only [List.foldl_cons, ih, List.length_cons, step,
      List.length_append, List.length_cons, List.length_nil]; omega

lemma run_length (gs : List Gate) : (run gs).length = 13 + gs.length := by
  simp [run, fold_length]

lemma anc_nil (i : ℕ) : anc [] i = if i < 13 then {i} else ∅ := by
  have hgen {n : ℕ} (k : ℕ) :
      (List.ofFn fun p : Fin n => ({p.val} : Finset ℕ)).getD k ∅ =
        if k < n then {k} else ∅ := by
    by_cases hk : k < n <;> simp [List.getD_eq_getElem?_getD, hk]
  exact hgen i

lemma anc_snoc (gs : List Gate) (g : Gate) (i : ℕ) :
    anc (gs ++ [g]) i = if i = 13 + gs.length then
      insert i (g.inputs.toFinset.biUnion fun j => anc gs j) else anc gs i := by
  unfold anc run
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, step]
  have hl : (gs.foldl step (List.ofFn fun i : Fin 13 => ({i.val} : Finset ℕ))).length =
      13 + gs.length := by rw [fold_length]; simp
  rcases lt_trichotomy i (13 + gs.length) with h | h | h
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  · rw [if_pos h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp only [hl, h, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by rw [List.length_append, hl]; simp only [List.length_singleton]; omega),
      List.getElem?_eq_none (by omega)]

lemma anc_invalid (gs : List Gate) (i : ℕ) (hi : 13 + gs.length ≤ i) : anc gs i = ∅ := by
  exact List.getD_eq_default _ _ (by simpa only [run_length] using hi)

lemma anc_input (gs : List Gate) (i : ℕ) (hi : i < 13) : anc gs i = {i} := by
  induction gs using List.reverseRecOn with
  | nil => simp [anc_nil, hi]
  | append_singleton gs g ih => rw [anc_snoc, if_neg (by omega), ih]

lemma anc_bound (gs : List Gate) (i j : ℕ) (hj : j ∈ anc gs i) :
    j ≤ i ∧ j < 13 + gs.length := by
  induction gs using List.reverseRecOn generalizing i j with
  | nil =>
    rw [anc_nil] at hj
    split_ifs at hj with hi
    · have he : j = i := by simpa using hj
      subst j
      exact ⟨le_rfl, by simpa using hi⟩
    · simp at hj
  | append_singleton gs g ih =>
    rw [anc_snoc] at hj
    by_cases hi : i = 13 + gs.length
    · rw [if_pos hi] at hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · simp only [List.length_append, List.length_singleton]; omega
      · obtain ⟨k, hk, hj⟩ := Finset.mem_biUnion.mp hj
        have hb := ih k j hj
        simp only [List.length_append, List.length_singleton]
        omega
    · rw [if_neg hi] at hj
      have hb := ih i j hj
      simp only [List.length_append, List.length_singleton]
      omega

lemma ancestor_trans (gs : List Gate) (i j : ℕ) (hj : j ∈ anc gs i) :
    anc gs j ⊆ anc gs i := by
  induction gs using List.reverseRecOn generalizing i j with
  | nil =>
    have hb := anc_bound [] i j hj
    rw [anc_input [] j (by simpa using hb.2)]
    exact Finset.singleton_subset_iff.mpr hj
  | append_singleton gs g ih =>
    have hb := anc_bound (gs ++ [g]) i j hj
    by_cases hij : j = i
    · subst j; exact Finset.Subset.refl _
    by_cases hi : i = 13 + gs.length
    · rw [anc_snoc gs g i, if_pos hi] at hj ⊢
      have hjold : j < 13 + gs.length := by omega
      rw [anc_snoc, if_neg (by omega)]
      obtain ⟨k, hk, hjk⟩ := Finset.mem_biUnion.mp ((Finset.mem_insert.mp hj).resolve_left hij)
      intro p hp
      exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨k, hk, ih k j hjk hp⟩)
    · rw [anc_snoc gs g i, if_neg hi] at hj ⊢
      have hjold := (anc_bound gs i j hj).2
      rw [anc_snoc, if_neg (by omega)]
      exact ih i j hj

lemma depends_mem {M : ℕ} (P : Finset ℕ) (gs : List Gate) (i : ℕ) (t : Fin M)
    (ht : Cut.Depends 13 P gs i t) : t.val ∈ anc gs i := by
  induction gs using List.reverseRecOn generalizing i t with
  | nil =>
    obtain ⟨x, y, hxy, hne⟩ := ht
    rw [Cut.cutVal_nil, Cut.cutVal_nil] at hne
    by_cases hi : i < 13
    · simp only [hi, ite_true] at hne
      have he := Cut.source_dep x y i t hxy hne
      simp [anc_nil, hi, he]
    · simp [hi] at hne
  | append_singleton gs g ih =>
    obtain ⟨x, y, hxy, hne⟩ := ht
    rw [Cut.cutVal_snoc, Cut.cutVal_snoc] at hne
    by_cases hi : i = 13 + gs.length
    · rw [if_pos hi, if_pos hi] at hne
      rw [anc_snoc, if_pos hi]
      by_cases hp : i ∈ P
      · simp only [← hi, hp, ite_true] at hne
        have he := Cut.source_dep x y i t hxy hne
        simpa only [he] using Finset.mem_insert_self i (g.inputs.toFinset.biUnion fun j => anc gs j)
      · simp only [← hi, hp, ite_false] at hne
        have hex : ∃ j ∈ g.inputs,
            Cut.cutVal 13 P gs x j ≠ Cut.cutVal 13 P gs y j := by
          by_contra! hh
          apply hne
          congr 1
          exact List.map_congr_left hh
        obtain ⟨j, hj, hne⟩ := hex
        exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr
          ⟨j, by simpa using hj, ih j t ⟨x, y, hxy, hne⟩⟩)
    · rw [if_neg hi, if_neg hi] at hne
      rw [anc_snoc, if_neg hi]
      exact ih i t ⟨x, y, hxy, hne⟩

lemma components (S : Finset (Fin 13)) (gs : List Gate)
    (hg : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    ∃ (label : Fin 13 → ℕ) (wire : ℕ → ℕ),
      S.card ≤ (S.image label).card + gs.length ∧
      (∀ p : Fin 13, wire p.val = label p) ∧
      ∀ i j, j ∈ anc gs i → wire j = wire i := by
  classical
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨Fin.val, id, ?_, fun _ => rfl, ?_⟩
    · simp [Finset.card_image_of_injective _ Fin.val_injective]
    · intro i j hj
      rw [anc_nil] at hj
      split_ifs at hj with hi
      · simpa using hj
      · simp at hj
  | append_singleton gs g ih =>
    obtain ⟨label, wire, hc, hr, ha⟩ := ih (fun q hq => hg q (by simp [hq]))
    obtain ⟨a, b, hins⟩ := Cut.two_inputs g.inputs (hg g (by simp))
    let merge (k : ℕ) := if k = wire b then wire a else k
    have hma : merge (wire a) = wire a := by simp [merge]
    have hmb : merge (wire b) = wire a := by simp [merge]
    refine ⟨merge ∘ label, fun i => if i = 13 + gs.length then wire a else merge (wire i),
      ?_, ?_, ?_⟩
    · have hsub : S.image label ⊆ insert (wire b) (S.image (merge ∘ label)) := by
        intro v hv
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hv
        by_cases he : label t = wire b
        · simp [he]
        · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨t, ht, by simp [merge, he]⟩)
      have hcard := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
      simp only [List.length_append, List.length_singleton]
      omega
    · intro p
      change (if p.val = 13 + gs.length then wire a else merge (wire p.val)) = merge (label p)
      rw [if_neg (by omega), hr]
    · intro i j hj
      change (if j = 13 + gs.length then wire a else merge (wire j)) =
        (if i = 13 + gs.length then wire a else merge (wire i))
      rw [anc_snoc] at hj
      by_cases hi : i = 13 + gs.length
      · rw [if_pos hi] at hj ⊢
        rcases Finset.mem_insert.mp hj with rfl | hj
        · simp [hi]
        · obtain ⟨k, hk, hjk⟩ := Finset.mem_biUnion.mp hj
          have hjold := (anc_bound gs k j hjk).2
          rw [if_neg (by omega), ha k j hjk]
          rcases hins k (by simpa using hk) with rfl | rfl
          · exact hma
          · exact hmb
      · rw [if_neg hi] at hj ⊢
        have hjold := (anc_bound gs i j hj).2
        rw [if_neg (by omega), ha i j hj]

end PEqualNP.Outside.L_meta_1024_aux.Ancestry
