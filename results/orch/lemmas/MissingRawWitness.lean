import PEqualNP.Outside.L_meta_1024

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
