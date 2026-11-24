import PEqualNP.Outside.L_meta_1024

namespace PEqualNP.Outside.L_meta_1024_aux.PairSurcharge

open PEqualNP.CircuitLowerBounds

noncomputable def core {n : ℕ} (gs : List Gate) (i : ℕ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun p => Global.val gs (Global.eof p) i = true)

lemma mem_core {n : ℕ} (gs : List Gate) (i : ℕ) (p : Fin n) :
    p ∈ core gs i ↔ Global.val gs (Global.eof p) i = true := by
  classical
  simp [core]

lemma val_raw {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (p : Fin n) :
    Global.val gs x p.val = x p := by
  exact PEqualNP.Outside.L_meta_1024_aux.val_input gs x p

lemma val_invalid {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ)
    (hi : n + gs.length ≤ i) : Global.val gs x i = false := by
  exact PEqualNP.Outside.L_meta_1024_aux.val_beyond gs x i hi

lemma cnt_mem {n : ℕ} (gs : List Gate) (S : Finset (Fin n)) (i : ℕ)
    (hcnt : Global.Cnt S gs i) : i ∈ Global.D S gs := by
  classical
  obtain ⟨hz, u, v, huv, hu, hv⟩ := hcnt
  have hn : n ≤ i := by
    by_contra! hi
    have hu' : (⟨i, hi⟩ : Fin n) = u := by
      have he := val_raw gs (Global.eof u) ⟨i, hi⟩
      rw [he] at hu
      simpa [Global.eof] using hu
    have hv' : (⟨i, hi⟩ : Fin n) = v := by
      have he := val_raw gs (Global.eof v) ⟨i, hi⟩
      rw [he] at hv
      simpa [Global.eof] using hv
    exact huv (hu'.symm.trans hv')
  have hi : i < n + gs.length := by
    by_contra! hbad
    rw [val_invalid gs (Global.eof u) i hbad] at hu
    contradiction
  exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hn, hi⟩, hz, u, v, huv, hu, hv⟩

lemma core_large_mem {n : ℕ} (gs : List Gate) (S : Finset (Fin n)) (i : ℕ)
    (hz : Global.val gs (Global.Zof S) i = false) (hc : 1 < (core (n := n) gs i).card) :
    i ∈ Global.D S gs := by
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hc
  exact cnt_mem gs S i ⟨hz, u, v, huv, (mem_core gs i u).mp hu, (mem_core gs i v).mp hv⟩

lemma wire_eq_gate {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (j : ℕ) (hj : j < gs.length) :
    Global.val gs x (n + j) = gs[j].op.eval (gs[j].inputs.map
      (fun i => if i < n + j then Global.val gs x i else false)) := by
  induction gs using List.reverseRecOn generalizing j with
  | nil => simp at hj
  | append_singleton gs g ih =>
    by_cases hlast : j = gs.length
    · subst j
      rw [Global.val_snoc, ite_eq_left rfl]
      have hget : (gs ++ [g])[gs.length]'(by simp) = g := by simp
      rw [hget]
      apply congrArg g.op.eval
      apply List.map_congr_left
      intro i _
      by_cases hi : i < n + gs.length
      · rw [ite_eq_left hi, Global.val_snoc, ite_eq_right (by omega)]
      · rw [ite_eq_right hi, val_invalid _ _ _ (by omega)]
    · have hjold : j < gs.length := by simp only [List.length_append, List.length_singleton] at hj; omega
      rw [Global.val_snoc, ite_eq_right (by omega), List.getElem_append_left hjold, ih j hjold]
      apply congrArg gs[j].op.eval
      apply List.map_congr_left
      intro i _
      by_cases hi : i < n + j
      · simp only [ite_eq_left hi]
        rw [Global.val_snoc, ite_eq_right (by omega)]
      · simp only [ite_eq_right hi]

lemma overlapping_pair_charge {n : ℕ} (S : Finset (Fin n)) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hS : S.card = 4) (o i j : ℕ) (r q₁ q₂ : Fin n)
    (hz : Global.val gs (Global.Zof S) o = false) (ho : core gs o = S)
    (hi : i ∈ Global.D S gs) (hj : j ∈ Global.D S gs) (hij : i ≠ j)
    (hci : core gs i = {r, q₁}) (hcj : core gs j = {r, q₂}) :
    4 ≤ (Global.D S gs).card := by
  classical
  by_contra! hsmall
  have hoD : o ∈ Global.D S gs := core_large_mem gs S o hz (by rw [ho, hS]; decide)
  have hio : i ≠ o := by
    intro he
    have hh : (core (n := n) gs i).card ≤ 2 := by rw [hci]; exact Finset.card_le_two
    rw [he, ho, hS] at hh
    omega
  have hjo : j ≠ o := by
    intro he
    have hh : (core (n := n) gs j).card ≤ 2 := by rw [hcj]; exact Finset.card_le_two
    rw [he, ho, hS] at hh
    omega
  have hsub : ({i, j, o} : Finset ℕ) ⊆ Global.D S gs := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl <;> assumption
  have hthree : ({i, j, o} : Finset ℕ).card = 3 := by simp [hij, hio, hjo]
  have hD : Global.D S gs = {i, j, o} :=
    (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
  have hoi := (Finset.mem_filter.mp hoD).1
  have hon : n ≤ o := (Finset.mem_Ico.mp hoi).1
  have hob : o < n + gs.length := (Finset.mem_Ico.mp hoi).2
  let k := o - n
  have hk : k < gs.length := by dsimp [k]; omega
  have hok : n + k = o := by dsimp [k]; omega
  let f : (Fin n → Bool) → ℕ → Bool :=
    fun x a => if a < o then Global.val gs x a else false
  have hformula (x : Fin n → Bool) :
      gs[k].op.eval (gs[k].inputs.map (f x)) = Global.val gs x o := by
    simpa only [hok, f] using (wire_eq_gate gs x k hk).symm
  obtain ⟨hop, hlen⟩ := hg gs[k] (List.getElem_mem hk)
  rcases Global.gate_cases gs[k] hop hlen f (Global.Zof S) with hall | ⟨a, b, hab⟩
  · obtain ⟨p, hp⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
    have ht : Global.val gs (Global.eof p) o = true := (mem_core gs o p).mp (ho.symm ▸ hp)
    have hf := hall (Global.eof p)
    rw [hformula] at hf
    rw [hf] at ht
    contradiction
  · obtain ⟨ha, hb, hcover⟩ := hab (by rw [hformula]; exact hz)
    let C : ℕ → Finset (Fin n) := fun a => Finset.univ.filter (fun p => f (Global.eof p) a = true)
    have hclass (a : ℕ) (ha : f (Global.Zof S) a = false) :
        (C a = {r, q₁} ∨ C a = {r, q₂}) ∨ (C a).card ≤ 1 := by
      by_cases hcard : (C a).card ≤ 1
      · exact Or.inr hcard
      have hlt : a < o := by
        by_contra! hn
        have he : C a = ∅ := by ext p; simp [C, f, Nat.not_lt.mpr hn]
        simp [he] at hcard
      have hC : C a = core gs a := by ext p; simp [C, f, hlt, core]
      have haz : Global.val gs (Global.Zof S) a = false := by simpa only [f, ite_eq_left hlt] using ha
      have haD := core_large_mem gs S a haz (by rw [← hC]; omega)
      rw [hD] at haD
      simp only [Finset.mem_insert, Finset.mem_singleton] at haD
      rcases haD with rfl | rfl | he
      · exact Or.inl (Or.inl (hC.trans hci))
      · exact Or.inl (Or.inr (hC.trans hcj))
      · omega
    have hSC : S ⊆ C a ∪ C b := by
      intro p hp
      have ht : Global.val gs (Global.eof p) o = true := (mem_core gs o p).mp (ho.symm ▸ hp)
      have hh := hcover (Global.eof p) (by rw [hformula]; exact ht)
      simpa only [C, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] using hh
    have hunion : (C a ∪ C b).card ≤ 3 := by
      rcases hclass a ha with (hA | hA) | hA <;>
        rcases hclass b hb with (hB | hB) | hB
      · rw [hA, hB]
        simpa using (show ({r, q₁} : Finset (Fin n)).card ≤ 3 from Finset.card_le_two.trans (by decide))
      · rw [hA, hB]
        have hs : ({r, q₁} ∪ {r, q₂} : Finset (Fin n)) ⊆ {r, q₁, q₂} := by
          intro p hp
          simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hp ⊢
          tauto
        exact (Finset.card_le_card hs).trans Finset.card_le_three
      · have hh := Finset.card_union_le (C a) (C b)
        have hhA : (C a).card ≤ 2 := by rw [hA]; exact Finset.card_le_two
        omega
      · rw [hA, hB]
        have hs : ({r, q₂} ∪ {r, q₁} : Finset (Fin n)) ⊆ {r, q₁, q₂} := by
          intro p hp
          simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hp ⊢
          tauto
        exact (Finset.card_le_card hs).trans Finset.card_le_three
      · rw [hA, hB]
        simpa using (show ({r, q₂} : Finset (Fin n)).card ≤ 3 from Finset.card_le_two.trans (by decide))
      · have hh := Finset.card_union_le (C a) (C b)
        have hhA : (C a).card ≤ 2 := by rw [hA]; exact Finset.card_le_two
        omega
      · have hh := Finset.card_union_le (C a) (C b)
        have hhB : (C b).card ≤ 2 := by rw [hB]; exact Finset.card_le_two
        omega
      · have hh := Finset.card_union_le (C a) (C b)
        have hhB : (C b).card ≤ 2 := by rw [hB]; exact Finset.card_le_two
        omega
      · have hh := Finset.card_union_le (C a) (C b)
        omega
    have hh := Finset.card_le_card hSC
    omega

lemma ordinary_overlapping_pair_charge {n : ℕ} (S : Finset (Fin n)) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hS : S.card = 4) (o i j : ℕ) (r q₁ q₂ : Fin n)
    (hcorrect : ∀ x : Fin n → Bool,
      Global.val gs x o = decide (∃ p ∈ S, x p = true))
    (hi : i ∈ Global.D S gs) (hj : j ∈ Global.D S gs) (hij : i ≠ j)
    (hci : ∀ p : Fin n, Global.val gs (Global.eof p) i = true ↔ p = r ∨ p = q₁)
    (hcj : ∀ p : Fin n, Global.val gs (Global.eof p) j = true ↔ p = r ∨ p = q₂) :
    4 ≤ (Global.D S gs).card := by
  classical
  apply overlapping_pair_charge S gs hg hS o i j r q₁ q₂
  · rw [hcorrect]
    simp [Global.Zof]
  · ext p
    rw [mem_core, hcorrect]
    simp [Global.eof]
  · exact hi
  · exact hj
  · exact hij
  · ext p
    rw [mem_core, hci]
    simp
  · ext p
    rw [mem_core, hcj]
    simp

end PEqualNP.Outside.L_meta_1024_aux.PairSurcharge
