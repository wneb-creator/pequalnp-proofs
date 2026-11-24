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


namespace PEqualNP.Outside.L_meta_1024_aux.MissingRawWitness

open PEqualNP.CircuitLowerBounds

noncomputable def rawSet (gs : List Gate) (E : Finset (Fin (13 + gs.length))) : Finset (Fin 13) := by
  classical
  exact Finset.univ.filter (fun p => Bridge.rawIndex gs p ∈ E)

lemma mem_rawSet (gs : List Gate) (E : Finset (Fin (13 + gs.length))) (p : Fin 13) :
    p ∈ rawSet gs E ↔ Bridge.rawIndex gs p ∈ E := by
  classical
  simp [rawSet]

lemma raw_injective (gs : List Gate) : Function.Injective (Bridge.rawIndex gs) := by
  intro p q hpq
  apply Fin.ext
  exact congrArg (fun t : Fin (13 + gs.length) => t.val) hpq

lemma positive_avoiding (w p : Fin 13) (hp : p ∈ Support.line w)
    (R : Finset (Fin 13)) (hR : R.card ≤ 3) (hpR : p ∉ R) :
    ∃ x : Fin 13 → Bool, Support.Band x ∧ Support.target w x = true ∧
      x p = true ∧ (∀ q ∈ Support.line w, q ≠ p → x q = false) ∧
      ∀ q ∈ R, x q = false := by
  classical
  let O := Finset.univ \ Support.line w
  have hO : O.card = 9 := by
    dsimp [O]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Clamp.line_card]
    decide
  have havail : 6 ≤ (O \ R).card := by
    have hh := Finset.le_card_sdiff R O
    rw [hO] at hh
    omega
  obtain ⟨Y, hYsub, hYcard⟩ := Finset.exists_subset_card_eq havail
  have hYO : Y ⊆ O := fun q hq => (Finset.mem_sdiff.mp (hYsub hq)).1
  have hYR : ∀ q ∈ Y, q ∉ R := fun q hq => (Finset.mem_sdiff.mp (hYsub hq)).2
  have hpY : p ∉ Y := by
    intro hh
    exact (Finset.mem_sdiff.mp (hYO hh)).2 hp
  let U := insert p Y
  have hU : U.card = 7 := by simp [U, hpY, hYcard]
  let x := Clamp.fromTrue U
  have hxband : Support.Band x := by
    right
    have hzero : Support.zeroSet x = Finset.univ \ U := by
      ext q
      simp [Support.zeroSet, x, Clamp.fromTrue]
    rw [hzero, Finset.card_sdiff_of_subset (Finset.subset_univ _), hU]
    decide
  have hxp : x p = true := by simp [x, Clamp.fromTrue, U]
  refine ⟨x, hxband, ?_, hxp, ?_, ?_⟩
  · exact decide_eq_true_iff.mpr ⟨p, hp, hxp⟩
  · intro q hq hqp
    have hqY : q ∉ Y := by
      intro hh
      exact (Finset.mem_sdiff.mp (hYO hh)).2 hq
    simp [x, Clamp.fromTrue, U, hqp, hqY]
  · intro q hq
    have hqp : q ≠ p := fun he => hpR (he ▸ hq)
    have hqY : q ∉ Y := fun hy => hYR q hy hq
    simp [x, Clamp.fromTrue, U, hqp, hqY]

lemma true_foreign (gs : List Gate) (w p : Fin 13) (P : Finset ℕ)
    (E : Finset (Fin (13 + gs.length)))
    (hallowed : ∀ i ∈ E, i.val < 13 ∨ i.val ∈ P)
    (hpaid : ∀ i ∈ P, ∃ q : Fin 13,
      q ∉ Support.line w ∧ Global.val gs (Global.eof q) i = true)
    (hpnot : Bridge.rawIndex gs p ∉ E)
    (x : Fin 13 → Bool)
    (hline : ∀ q ∈ Support.line w, q ≠ p → x q = false) :
    ∀ i ∈ E, Global.val gs x i.val = true →
      ∃ q : Fin 13, q ∉ Support.line w ∧ Global.val gs (Clamp.singleton q) i.val = true := by
  intro i hi hit
  rcases hallowed i hi with hiraw | hipaid
  · let q : Fin 13 := ⟨i.val, hiraw⟩
    have hidx : Bridge.rawIndex gs q = i := by apply Fin.ext; rfl
    have hqtrue : x q = true := by
      rw [Bridge.val_input gs x q] at hit
      exact hit
    have hqout : q ∉ Support.line w := by
      intro hql
      by_cases hqp : q = p
      · subst p
        exact hpnot (hidx.symm ▸ hi)
      · rw [hline q hql hqp] at hqtrue
        contradiction
    refine ⟨q, hqout, ?_⟩
    have he := Bridge.val_input gs (Clamp.singleton q) q
    simpa [Clamp.singleton] using he
  · exact hpaid i.val hipaid

lemma raw_card_le_two (gs : List Gate) (w p : Fin 13) (hp : p ∈ Support.line w)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (P : Finset ℕ) (E : Finset (Fin (13 + gs.length)))
    (hE : E.card ≤ 11)
    (hallowed : ∀ i ∈ E, i.val < 13 ∨ i.val ∈ P)
    (hpaid : ∀ i ∈ P, ∃ q : Fin 13,
      q ∉ Support.line w ∧ Global.val gs (Global.eof q) i = true)
    (F : (Fin (13 + gs.length) → Bool) → Bool)
    (hmono : ∀ a b, (∀ i, a i = true → b i = true) → F a = true → F b = true)
    (hsupport : ∀ a b, (∀ i ∈ E, a i = b i) → F a = F b)
    (hcorrect : ∀ x : Fin 13 → Bool, Support.Band x →
      F (fun i => Global.val gs x i.val) = Support.target w x)
    (hpnot : Bridge.rawIndex gs p ∉ E) : (rawSet gs E).card ≤ 2 := by
  classical
  by_contra! hlarge
  have hthree : 3 ≤ (rawSet gs E).card := by omega
  obtain ⟨R, hRsub, hRcard⟩ := Finset.exists_subset_card_eq hthree
  have hpR : p ∉ R := fun h => hpnot ((mem_rawSet gs E p).mp (hRsub h))
  obtain ⟨x, hxband, hxpos, _, hxline, hxR⟩ := positive_avoiding w p hp R (by omega) hpR
  let K := R.image (Bridge.rawIndex gs)
  have hKcard : K.card = 3 := by
    rw [Finset.card_image_of_injective _ (raw_injective gs)]
    exact hRcard
  have hKE : K ⊆ E := by
    intro i hi
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hi
    exact (mem_rawSet gs E q).mp (hRsub hq)
  have hKfalse : ∀ i ∈ K, Global.val gs x i.val = false := by
    intro i hi
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hi
    change Global.val gs x q.val = false
    rw [Bridge.val_input gs x q]
    exact hxR q hq
  have hcount : (E.filter (fun i => Global.val gs x i.val = true)).card ≤ 8 := by
    have hs : E.filter (fun i => Global.val gs x i.val = true) ⊆ E \ K := by
      intro i hi
      obtain ⟨hiE, hit⟩ := Finset.mem_filter.mp hi
      refine Finset.mem_sdiff.mpr ⟨hiE, ?_⟩
      intro hiK
      rw [hKfalse i hiK] at hit
      contradiction
    have hh := Finset.card_le_card hs
    rw [Finset.card_sdiff_of_subset hKE, hKcard] at hh
    omega
  apply Clamp9.positive_frontier_impossible w E F (fun i x => Global.val gs x i.val)
    hmono hsupport _ hcorrect x hxband hxpos hcount
    (true_foreign gs w p P E hallowed hpaid hpnot x hxline)
  intro i _ a b hab ha
  exact Bridge.val_mono gs hg a b hab i.val ha

lemma positive_kills_raw (gs : List Gate) (w p : Fin 13) (hp : p ∈ Support.line w)
    (E : Finset (Fin (13 + gs.length))) (hraw : (rawSet gs E).card ≤ 2)
    (hpnot : Bridge.rawIndex gs p ∉ E) :
    ∃ x : Fin 13 → Bool, Support.Band x ∧ Support.target w x = true ∧
      ∀ i ∈ E, i.val < 13 → Global.val gs x i.val = false := by
  have hpR : p ∉ rawSet gs E := fun h => hpnot ((mem_rawSet gs E p).mp h)
  obtain ⟨x, hxband, hxpos, _, _, hxR⟩ := positive_avoiding w p hp (rawSet gs E) (by omega) hpR
  refine ⟨x, hxband, hxpos, ?_⟩
  intro i hi hiraw
  let q : Fin 13 := ⟨i.val, hiraw⟩
  have hidx : Bridge.rawIndex gs q = i := by apply Fin.ext; rfl
  have hqR : q ∈ rawSet gs E := (mem_rawSet gs E q).mpr (hidx.symm ▸ hi)
  rw [Bridge.val_input gs x q]
  exact hxR q hqR

def negative (w q : Fin 13) : Fin 13 → Bool :=
  Clamp.fromTrue ((Finset.univ \ Support.line w).erase q)

lemma negative_band (w q : Fin 13) (hq : q ∉ Support.line w) : Support.Band (negative w q) := by
  apply Clamp.fromTrue_band
  have hqO : q ∈ Finset.univ \ Support.line w := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hq⟩
  rw [Finset.card_erase_of_mem hqO, Finset.card_sdiff_of_subset (Finset.subset_univ _), Clamp.line_card]
  decide

lemma negative_false (w q : Fin 13) : Support.target w (negative w q) = false := by
  apply Clamp.fromTrue_misses
  exact Finset.erase_subset _ _

lemma paid_separator (gs : List Gate) (w q : Fin 13) (hq : q ∉ Support.line w)
    (P : Finset ℕ) (E : Finset (Fin (13 + gs.length)))
    (hallowed : ∀ i ∈ E, i.val < 13 ∨ i.val ∈ P)
    (F : (Fin (13 + gs.length) → Bool) → Bool)
    (hmono : ∀ a b, (∀ i, a i = true → b i = true) → F a = true → F b = true)
    (hsupport : ∀ a b, (∀ i ∈ E, a i = b i) → F a = F b)
    (hcorrect : ∀ x : Fin 13 → Bool, Support.Band x →
      F (fun i => Global.val gs x i.val) = Support.target w x)
    (x : Fin 13 → Bool) (hxband : Support.Band x) (hxpos : Support.target w x = true)
    (hxraw : ∀ i ∈ E, i.val < 13 → Global.val gs x i.val = false) :
    ∃ i ∈ E, i.val ∈ P ∧ Global.val gs x i.val = true ∧
      Global.val gs (negative w q) i.val = false := by
  classical
  have hpos : F (fun i => Global.val gs x i.val) = true := (hcorrect x hxband).trans hxpos
  have hneg : F (fun i => Global.val gs (negative w q) i.val) = false :=
    (hcorrect _ (negative_band w q hq)).trans (negative_false w q)
  have hex : ∃ i ∈ E, Global.val gs x i.val = true ∧
      Global.val gs (negative w q) i.val = false := by
    by_contra! hnone
    have hh := Clamp.supported_mono F E hmono hsupport
      (fun i => Global.val gs x i.val) (fun i => Global.val gs (negative w q) i.val)
      (by
        intro i hi hit
        have hn := hnone i hi hit
        cases he : Global.val gs (negative w q) i.val <;> simp_all) hpos
    rw [hneg] at hh
    contradiction
  obtain ⟨i, hi, hit, hif⟩ := hex
  refine ⟨i, hi, ?_, hit, hif⟩
  rcases hallowed i hi with hiraw | hipaid
  · rw [hxraw i hi hiraw] at hit
    contradiction
  · exact hipaid

lemma pair_core_of_negative (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w a q : Fin 13) (haw : a ≠ w) (hq : q ∉ Support.line w)
    (i : ℕ) (hi : i ∈ Global.D (Global.line a) gs)
    (hneg : Global.val gs (negative w q) i = false) :
    ∃ r : Fin 13, r ∈ Support.line w ∧ r ∈ Global.line a ∧
      ∀ p : Fin 13, Global.val gs (Global.eof p) i = true ↔ p = r ∨ p = q := by
  classical
  obtain ⟨label, hinv, _⟩ := Global.main_inv (Global.line a) gs hg
  obtain ⟨hz, u, v, huv, hu, hv⟩ := (Finset.mem_filter.mp hi).2
  obtain ⟨r, hrw, hra⟩ := (Bridge.pair_geometry w a haw.symm).2
  have hsub (p : Fin 13) (hp : Global.val gs (Global.eof p) i = true) : p = r ∨ p = q := by
    by_cases hpq : p = q
    · exact Or.inr hpq
    have hpa : p ∈ Global.line a := (hinv i p p hz hp hp).1
    have hpw : p ∈ Support.line w := by
      by_contra hpw
      have hrow : ∀ t : Fin 13, Global.eof p t = true → negative w q t = true := by
        intro t ht
        have htp : t = p := by simpa [Global.eof] using ht
        subst t
        simp [negative, Clamp.fromTrue, hpq, hpw]
      have hh := Bridge.val_mono gs (fun g hm => (hg g hm).1)
        (Global.eof p) (negative w q) hrow i hp
      rw [hneg] at hh
      contradiction
    exact Or.inl ((Finset.card_le_one.mp (Global.line_intersection a w haw))
      p (Finset.mem_inter.mpr ⟨hpa, hpw⟩) r (Finset.mem_inter.mpr ⟨hra, hrw⟩))
  have hboth : Global.val gs (Global.eof r) i = true ∧ Global.val gs (Global.eof q) i = true := by
    rcases hsub u hu with hur | huq <;> rcases hsub v hv with hvr | hvq
    · exact (huv (hur.trans hvr.symm)).elim
    · exact ⟨hur ▸ hu, hvq ▸ hv⟩
    · exact ⟨hvr ▸ hv, huq ▸ hu⟩
    · exact (huv (huq.trans hvq.symm)).elim
  refine ⟨r, hrw, hra, ?_⟩
  intro p
  constructor
  · exact hsub p
  · rintro (rfl | rfl)
    · exact hboth.1
    · exact hboth.2

lemma paid_pair_witnesses (gs : List Gate) (w p : Fin 13) (hp : p ∈ Support.line w)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (P : Finset ℕ) (E : Finset (Fin (13 + gs.length)))
    (hE : E.card ≤ 11)
    (hallowed : ∀ i ∈ E, i.val < 13 ∨ i.val ∈ P)
    (hpaid : ∀ i ∈ P, ∃ q : Fin 13,
      q ∉ Support.line w ∧ Global.val gs (Global.eof q) i = true)
    (howner : ∀ i ∈ P, ∃ a : Fin 13, a ≠ w ∧ i ∈ Global.D (Global.line a) gs)
    (F : (Fin (13 + gs.length) → Bool) → Bool)
    (hmono : ∀ a b, (∀ i, a i = true → b i = true) → F a = true → F b = true)
    (hsupport : ∀ a b, (∀ i ∈ E, a i = b i) → F a = F b)
    (hcorrect : ∀ x : Fin 13 → Bool, Support.Band x →
      F (fun i => Global.val gs x i.val) = Support.target w x)
    (hpnot : Bridge.rawIndex gs p ∉ E) :
    (rawSet gs E).card ≤ 2 ∧
      ∃ pick : {q : Fin 13 // q ∉ Support.line w} → Fin (13 + gs.length),
        Function.Injective pick ∧
        ∀ q, pick q ∈ E ∧ (pick q).val ∈ P ∧
          ∃ a r : Fin 13, a ≠ w ∧ r ∈ Support.line w ∧ r ∈ Global.line a ∧
            (pick q).val ∈ Global.D (Global.line a) gs ∧
            ∀ t : Fin 13, Global.val gs (Global.eof t) (pick q).val = true ↔
              t = r ∨ t = q.val := by
  classical
  have hraw := raw_card_le_two gs w p hp (fun g hm => (hg g hm).1) P E hE
    hallowed hpaid F hmono hsupport hcorrect hpnot
  obtain ⟨x, hxband, hxpos, hxraw⟩ := positive_kills_raw gs w p hp E hraw hpnot
  let Q := {q : Fin 13 // q ∉ Support.line w}
  have hwit (q : Q) : ∃ i : Fin (13 + gs.length), i ∈ E ∧ i.val ∈ P ∧
      ∃ a r : Fin 13, a ≠ w ∧ r ∈ Support.line w ∧ r ∈ Global.line a ∧
        i.val ∈ Global.D (Global.line a) gs ∧
        ∀ t : Fin 13, Global.val gs (Global.eof t) i.val = true ↔ t = r ∨ t = q.val := by
    obtain ⟨i, hi, hip, _, hif⟩ := paid_separator gs w q.val q.property P E hallowed F
      hmono hsupport hcorrect x hxband hxpos hxraw
    obtain ⟨a, haw, hia⟩ := howner i.val hip
    obtain ⟨r, hrw, hra, hcore⟩ := pair_core_of_negative gs hg w a q.val haw q.property i.val hia hif
    exact ⟨i, hi, hip, a, r, haw, hrw, hra, hia, hcore⟩
  let pick : Q → Fin (13 + gs.length) := fun q => Classical.choose (hwit q)
  have hspec (q : Q) : pick q ∈ E ∧ (pick q).val ∈ P ∧
      ∃ a r : Fin 13, a ≠ w ∧ r ∈ Support.line w ∧ r ∈ Global.line a ∧
        (pick q).val ∈ Global.D (Global.line a) gs ∧
        ∀ t : Fin 13, Global.val gs (Global.eof t) (pick q).val = true ↔ t = r ∨ t = q.val :=
    Classical.choose_spec (hwit q)
  refine ⟨hraw, pick, ?_, hspec⟩
  intro q₁ q₂ he
  obtain ⟨_, _, a₁, r₁, _, _, _, _, hc₁⟩ := hspec q₁
  obtain ⟨_, _, a₂, r₂, _, hr₂, _, _, hc₂⟩ := hspec q₂
  have ht : Global.val gs (Global.eof q₁.val) (pick q₁).val = true :=
    (hc₁ q₁.val).mpr (Or.inr rfl)
  rw [he] at ht
  rcases (hc₂ q₁.val).mp ht with hbad | hqeq
  · exact (q₁.property (hbad.symm ▸ hr₂)).elim
  · exact Subtype.ext hqeq

end PEqualNP.Outside.L_meta_1024_aux.MissingRawWitness


namespace PEqualNP.Outside.L_meta_1024_aux.Clamp11

open PEqualNP.CircuitLowerBounds

lemma fromTrue_seven (X : Finset (Fin 13)) (hX : X.card = 7) :
    Support.Band (Clamp.fromTrue X) := by
  right
  have he : Support.zeroSet (Clamp.fromTrue X) = Finset.univ \ X := by
    ext p
    simp [Support.zeroSet, Clamp.fromTrue]
  rw [he, Finset.card_sdiff_of_subset (Finset.subset_univ _), hX]
  decide

set_option maxHeartbeats 2000000 in
lemma missing_raw_impossible (gs : List Gate) (out : Fin 13 → ℕ) (w : Fin 13)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (W : Finset (Fin 13)) (hW : W.card = 8) (hw : w ∉ W)
    (hordinary : ∀ a ∈ W, ∀ x : Fin 13 → Bool,
      Global.val gs x (out a) = Support.target a x)
    (P : Finset ℕ) (hP : P = W.biUnion (fun a => Global.D (Global.line a) gs))
    (E : Finset (Fin (13 + gs.length))) (hbudget : E.card + P.card ≤ 35)
    (hallowed : ∀ i ∈ E, i.val < 13 ∨ i.val ∈ P)
    (F : (Fin (13 + gs.length) → Bool) → Bool)
    (hmono : ∀ a b, (∀ i, a i = true → b i = true) → F a = true → F b = true)
    (hsupport : ∀ a b, (∀ i ∈ E, a i = b i) → F a = F b)
    (hcorrect : ∀ x : Fin 13 → Bool, Support.Band x →
      F (fun i => Global.val gs x i.val) = Support.target w x)
    (p : Fin 13) (hp : p ∈ Support.line w) (hpnot : Bridge.rawIndex gs p ∉ E) : False := by
  classical
  have hown (i : ℕ) (hi : i ∈ P) : ∃ a ∈ W, i ∈ Global.D (Global.line a) gs := by
    rw [hP] at hi
    exact Finset.mem_biUnion.mp hi
  have howner (i : ℕ) (hi : i ∈ P) : ∃ a : Fin 13, a ≠ w ∧ i ∈ Global.D (Global.line a) gs := by
    obtain ⟨a, ha, hia⟩ := hown i hi
    exact ⟨a, fun he => hw (he ▸ ha), hia⟩
  have hpaid (i : ℕ) (hi : i ∈ P) : ∃ q : Fin 13,
      q ∉ Support.line w ∧ Global.val gs (Global.eof q) i = true := by
    obtain ⟨a, haw, hia⟩ := howner i hi
    exact Charges.charge_outside gs hg w a haw i hia
  have hcounts (a : Fin 13) (ha : a ∈ W) : 3 ≤ (Global.D (Global.line a) gs).card :=
    Charges.ordinary_charge_count gs (out a) a hg (hordinary a ha)
  have hdisj : ∀ a ∈ W, ∀ b ∈ W, a ≠ b →
      Disjoint (Global.D (Global.line a) gs) (Global.D (Global.line b) gs) := by
    intro a _ b _ hab
    exact Charges.disjoint_charges gs hg a b hab
  have hPsum : P.card = ∑ a ∈ W, (Global.D (Global.line a) gs).card := by
    rw [hP, Finset.card_biUnion hdisj]
  have hP24 : 24 ≤ P.card := by
    have hh := Finset.sum_le_sum hcounts
    rw [← hPsum] at hh
    simpa [hW] using hh
  have hE11 : E.card ≤ 11 := by omega
  obtain ⟨hraw, pick, hpick, hspec⟩ := MissingRawWitness.paid_pair_witnesses gs w p hp hg P E
    hE11 hallowed hpaid howner F hmono hsupport hcorrect hpnot
  let Q := {q : Fin 13 // q ∉ Support.line w}
  have hQ : Fintype.card Q = 9 := by
    dsimp [Q]
    rw [Fintype.card_subtype_compl]
    simp [Clamp.line_card]
  let owner : Q → {a : Fin 13 // a ∈ W} := fun q =>
    ⟨Classical.choose (hown (pick q).val (hspec q).2.1),
      (Classical.choose_spec (hown (pick q).val (hspec q).2.1)).1⟩
  have hownerD (q : Q) : (pick q).val ∈ Global.D (Global.line (owner q).val) gs :=
    (Classical.choose_spec (hown (pick q).val (hspec q).2.1)).2
  have hninj : ¬ Function.Injective owner := by
    intro hinj
    have hh := Fintype.card_le_of_injective owner hinj
    rw [hQ, Fintype.card_coe, hW] at hh
    omega
  change ¬ ∀ q₁ q₂, owner q₁ = owner q₂ → q₁ = q₂ at hninj
  push Not at hninj
  obtain ⟨q₁, q₂, hownerEq, hqne⟩ := hninj
  let a := (owner q₁).val
  have haW : a ∈ W := (owner q₁).property
  have haw : a ≠ w := fun he => hw (he ▸ haW)
  have hiD : (pick q₁).val ∈ Global.D (Global.line a) gs := hownerD q₁
  have hjD : (pick q₂).val ∈ Global.D (Global.line a) gs := by
    have hh := hownerD q₂
    rw [← hownerEq] at hh
    exact hh
  have hij : (pick q₁).val ≠ (pick q₂).val := by
    intro he
    exact hqne (hpick (Fin.ext he))
  obtain ⟨hiE, _, a₁, r₁, _, hr₁, _, _, hc₁⟩ := hspec q₁
  obtain ⟨hjE, _, a₂, r₂, _, hr₂, _, _, hc₂⟩ := hspec q₂
  obtain ⟨label, hinv, _⟩ := Global.main_inv (Global.line a) gs hg
  have hz₁ := (Finset.mem_filter.mp hiD).2.1
  have hz₂ := (Finset.mem_filter.mp hjD).2.1
  have ht₁ := (hc₁ r₁).mpr (Or.inl rfl)
  have ht₂ := (hc₂ r₂).mpr (Or.inl rfl)
  have hr₁a : r₁ ∈ Global.line a := (hinv _ r₁ r₁ hz₁ ht₁ ht₁).1
  have hr₂a : r₂ ∈ Global.line a := (hinv _ r₂ r₂ hz₂ ht₂ ht₂).1
  have hrEq : r₁ = r₂ := (Finset.card_le_one.mp (Global.line_intersection a w haw))
    r₁ (Finset.mem_inter.mpr ⟨hr₁a, hr₁⟩) r₂ (Finset.mem_inter.mpr ⟨hr₂a, hr₂⟩)
  have hDa : 4 ≤ (Global.D (Global.line a) gs).card := by
    apply PairSurcharge.ordinary_overlapping_pair_charge (Global.line a) gs hg
      (Global.line_card a) (out a) (pick q₁).val (pick q₂).val r₁ q₁.val q₂.val
      (hordinary a haW) hiD hjD hij hc₁
    intro t
    simpa only [hrEq] using hc₂ t
  have hP25 : 25 ≤ P.card := by
    have hh : (∑ b ∈ W, (3 + if b = a then 1 else 0 : ℕ)) ≤
        ∑ b ∈ W, (Global.D (Global.line b) gs).card := by
      apply Finset.sum_le_sum
      intro b hb
      by_cases hba : b = a
      · subst b
        simpa using hDa
      · simpa [hba] using hcounts b hb
    have hleft : (∑ b ∈ W, (3 + if b = a then 1 else 0 : ℕ)) = 25 := by
      simp [Finset.sum_add_distrib, hW, haW]
    rw [hleft, ← hPsum] at hh
    exact hh
  have hE10 : E.card ≤ 10 := by omega
  have hdiff : 3 ≤ (Support.line w \ Global.line a).card := by
    rw [Finset.card_sdiff, Clamp.line_card]
    have hh := Global.line_intersection a w haw
    change (Global.line a ∩ Support.line w).card ≤ 1 at hh
    omega
  obtain ⟨p', hp'diff, hp'raw⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show (MissingRawWitness.rawSet gs E).card < (Support.line w \ Global.line a).card by omega)
  have hp'w := (Finset.mem_sdiff.mp hp'diff).1
  have hp'a := (Finset.mem_sdiff.mp hp'diff).2
  have hp'not : Bridge.rawIndex gs p' ∉ E := fun h => hp'raw ((MissingRawWitness.mem_rawSet gs E p').mpr h)
  obtain ⟨hXcard, hp'X, hXa, hXonly⟩ := OneAnd.separating_row w a haw.symm p' hp'w hp'a
  let X := OneAnd.separatingRow w a p'
  let x := Clamp.fromTrue X
  have hxband : Support.Band x := fromTrue_seven X hXcard
  have hxpos : Support.target w x = true := by
    apply decide_eq_true_iff.mpr
    exact ⟨p', hp'w, by simpa [x, Clamp.fromTrue] using hp'X⟩
  have hxline : ∀ q ∈ Support.line w, q ≠ p' → x q = false := by
    intro q hqw hqp
    have hn : q ∉ X := fun hqX => hqp (hXonly q hqw hqX)
    simp [x, Clamp.fromTrue, hn]
  have hxZ : ∀ q : Fin 13, x q = true → Global.Zof (Global.line a) q = true := by
    intro q hq
    have hqX : q ∈ X := by simpa [x, Clamp.fromTrue] using hq
    have hqa : q ∉ Global.line a := fun hqa => Finset.disjoint_left.mp hXa hqa hqX
    simpa [Global.Zof] using hqa
  have hzraw (i : ℕ) (hi : i ∈ Global.D (Global.line a) gs) : Global.val gs x i = false := by
    have hzero := (Finset.mem_filter.mp hi).2.1
    cases he : Global.val gs x i
    · rfl
    · have hh := Bridge.val_mono gs (fun g hm => (hg g hm).1) x
        (Global.Zof (Global.line a)) hxZ i he
      rw [hzero] at hh
      contradiction
  have hKsub : ({pick q₁, pick q₂} : Finset (Fin (13 + gs.length))) ⊆ E := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact hiE
    · exact hjE
  have hKcard : ({pick q₁, pick q₂} : Finset (Fin (13 + gs.length))).card = 2 :=
    Finset.card_pair (fun he => hqne (hpick he))
  have hfront : (E.filter (fun i => Global.val gs x i.val = true)).card ≤ 8 := by
    have hs : E.filter (fun i => Global.val gs x i.val = true) ⊆ E \ {pick q₁, pick q₂} := by
      intro i hi
      obtain ⟨hiE', hit⟩ := Finset.mem_filter.mp hi
      refine Finset.mem_sdiff.mpr ⟨hiE', ?_⟩
      intro hiK
      simp only [Finset.mem_insert, Finset.mem_singleton] at hiK
      rcases hiK with rfl | rfl
      · rw [hzraw _ hiD] at hit
        contradiction
      · rw [hzraw _ hjD] at hit
        contradiction
    have hh := Finset.card_le_card hs
    rw [Finset.card_sdiff_of_subset hKsub, hKcard] at hh
    omega
  apply Clamp9.positive_frontier_impossible w E F (fun i x => Global.val gs x i.val)
    hmono hsupport _ hcorrect x hxband hxpos hfront
    (MissingRawWitness.true_foreign gs w p' P E hallowed hpaid hp'not x hxline)
  intro i _ y z hyz hy
  exact Bridge.val_mono gs (fun g hm => (hg g hm).1) y z hyz i.val hy

lemma raw_line_members (gs : List Gate) (out : Fin 13 → ℕ) (w : Fin 13)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (W : Finset (Fin 13)) (hW : W.card = 8) (hw : w ∉ W)
    (hordinary : ∀ a ∈ W, ∀ x : Fin 13 → Bool,
      Global.val gs x (out a) = Support.target a x)
    (P : Finset ℕ) (hP : P = W.biUnion (fun a => Global.D (Global.line a) gs))
    (E : Finset (Fin (13 + gs.length))) (hbudget : E.card + P.card ≤ 35)
    (hallowed : ∀ i ∈ E, i.val < 13 ∨ i.val ∈ P)
    (F : (Fin (13 + gs.length) → Bool) → Bool)
    (hmono : ∀ a b, (∀ i, a i = true → b i = true) → F a = true → F b = true)
    (hsupport : ∀ a b, (∀ i ∈ E, a i = b i) → F a = F b)
    (hcorrect : ∀ x : Fin 13 → Bool, Support.Band x →
      F (fun i => Global.val gs x i.val) = Support.target w x)
    (p : Fin 13) (hp : p ∈ Support.line w) : Bridge.rawIndex gs p ∈ E := by
  classical
  by_contra hpnot
  exact missing_raw_impossible gs out w hg W hW hw hordinary P hP E hbudget hallowed F
    hmono hsupport hcorrect p hp hpnot

end PEqualNP.Outside.L_meta_1024_aux.Clamp11
