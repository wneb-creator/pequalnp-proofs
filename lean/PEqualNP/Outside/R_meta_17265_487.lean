import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm Finset

theorem PEqualNP.Outside.R_meta_17265_487
  (acyclic : ∀ (n m : ℕ) (E : Finset (Fin n × Fin m)) (C : Circuit),
    (SimpleGraph.fromRel (fun a b : Fin (n+m) => ∃ e ∈ E, a=Fin.castAdd m e.1 ∧ b=Fin.natAdd n e.2)).IsAcyclic → IsAO2 (n+m) C → (∀ x, circuitFun (n+m) C x = decide (∃ e ∈ E, x (Fin.castAdd m e.1)=true ∧ x (Fin.natAdd n e.2)=true)) → ∃ (P : Finset (Fin n)) (Q : Finset (Fin m)), (∀ e ∈ E, e.1∈P ∨ e.2∈Q) ∧
      E.card + P.card + Q.card ≤ C.size + 1)
  (light : ∀ (n m : ℕ) (E : Finset (Fin n × Fin m)) (C : Circuit),
    E.card ≤ 10 → ((E.image Prod.fst).card ≤ 4 ∨ (E.image Prod.snd).card ≤ 4) →
    ¬ (SimpleGraph.fromRel (fun a b : Fin (n+m) => ∃ e ∈ E, a=Fin.castAdd m e.1 ∧ b=Fin.natAdd n e.2)).IsAcyclic → (∀ p q l s, p ≠ q → l ≠ s → ¬((p,l)∈E ∧ (p,s)∈E ∧ (q,l)∈E ∧ (q,s)∈E)) → IsAO2 (n+m) C → (∀ x, circuitFun (n+m) C x = decide (∃ e ∈ E, x (Fin.castAdd m e.1)=true ∧ x (Fin.natAdd n e.2)=true)) → ∃ (P : Finset (Fin n)) (Q : Finset (Fin m)), (∀ e ∈ E, e.1∈P ∨ e.2∈Q) ∧
      E.card + P.card + Q.card ≤ C.size + 1)
  (residual : ∀ (E : Finset (Fin 10 × Fin 10)) (C : Circuit), 5 ≤ (E.image Prod.fst).card →
    5 ≤ (E.image Prod.snd).card → E.card ≤ 10 →
    (∀ e ∈ E, ∃ d ∈ E, d ≠ e ∧ (d.1=e.1 ∨ d.2=e.2)) →
    (∀ p q l s, p ≠ q → l ≠ s → ¬((p,l)∈E ∧ (p,s)∈E ∧ (q,l)∈E ∧ (q,s)∈E)) → IsAO2 20 C → C.size ≤ 14 → (∀ x, circuitFun (20) C x = decide (∃ e ∈ E, x (Fin.castAdd 10 e.1)=true ∧ x (Fin.natAdd 10 e.2)=true)) → ∃ (P : Finset (Fin 10)) (Q : Finset (Fin 10)), (∀ e ∈ E, e.1∈P ∨ e.2∈Q) ∧
      E.card + P.card + Q.card ≤ C.size + 1) :
  ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   have x5 : Finset (Fin x1 × Fin x2) → Finset (Fin (x1 + x2)) := fun (x5 : Finset (Fin x1 × Fin x2)) => x5.biUnion fun (x6 : Fin x1 × Fin x2) => {Fin.castAdd x2 x6.1, Fin.natAdd x1 x6.2};   (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬((x6, x8) ∈ x3 ∧ (x6, x9) ∈ x3 ∧ (x7, x8) ∈ x3 ∧ (x7, x9) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x4 → (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 x8 = Decidable.decide (∃ x9 ∈ x3, x8 (Fin.castAdd x2 x9.1) = Bool.true ∧ x8 (Fin.natAdd x1 x9.2) = Bool.true)) → (¬∃ (x9 : Finset (Fin x1 × Fin x2)) (x10 : Finset (Fin x1 × Fin x2)) (x11 : Fin (x1 + x2)), x9.Nonempty ∧ x9 ∪ x10 = x3 ∧ Disjoint (x5 x9) (x5 x10) ∧ ∀ x12 ∈ x9, Fin.castAdd x2 x12.1 = x11 ∨ Fin.natAdd x1 x12.2 = x11) → x3.card ≤ (10 : ℕ) → ∃ (x11 : Finset (Fin x1)) (x12 : Finset (Fin x2)), (∀ x13 ∈ x3, x13.1 ∈ x11 ∨ x13.2 ∈ x12) ∧ x3.card + x11.card + x12.card ≤ x4.size + (1 : ℕ) := by
  classical
  intro n m E C
  dsimp only
  intro free ao spec noStar small
  by_cases forest : (SimpleGraph.fromRel (fun a b : Fin (n+m) => ∃ e ∈ E, a=Fin.castAdd m e.1 ∧ b=Fin.natAdd n e.2)).IsAcyclic
  · exact acyclic n m E C forest ao spec
  by_cases thin : (E.image Prod.fst).card ≤ 4 ∨ (E.image Prod.snd).card ≤ 4
  · exact light n m E C small thin forest free ao spec
  have side {α β : Type} [DecidableEq α] [DecidableEq β] (E : Finset (α × β))
      (P : Finset α) (Q : Finset β)
      (hmin : ∀ (P' : Finset α) (Q' : Finset β), (∀ e ∈ E, e.1 ∈ P' ∨ e.2 ∈ Q') →
        P.card + Q.card ≤ P'.card + Q'.card)
      (hcov : ∀ e ∈ E, e.1 ∈ P ∨ e.2 ∈ Q) :
      ∃ f : {p // p ∈ P} → β, Function.Injective f ∧ ∀ p, (p.val, f p) ∈ E ∧ f p ∉ Q := by
    let t : {p // p ∈ P} → Finset β :=
      fun p => ((E.filter (fun e => e.1 = p.val)).image Prod.snd) \ Q
    have hall : ∀ S : Finset {p // p ∈ P}, S.card ≤ (S.biUnion t).card := by
      intro S
      have hsub : S.image Subtype.val ⊆ P := by
        intro x hx
        obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hx
        exact p.property
      have hc := hmin (P \ S.image Subtype.val) (Q ∪ S.biUnion t) (by
        intro e he
        rcases hcov e he with h | h
        · by_cases hS : e.1 ∈ S.image Subtype.val
          · right
            by_cases hq : e.2 ∈ Q
            · exact Finset.mem_union_left _ hq
            · apply Finset.mem_union_right
              obtain ⟨p, hp, hpe⟩ := Finset.mem_image.mp hS
              rw [Finset.mem_biUnion]
              refine ⟨p, hp, ?_⟩
              show e.2 ∈ ((E.filter (fun e => e.1 = p.val)).image Prod.snd) \ Q
              rw [Finset.mem_sdiff]
              exact ⟨Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hpe.symm⟩, rfl⟩, hq⟩
          · left
            exact Finset.mem_sdiff.mpr ⟨h, hS⟩
        · right
          exact Finset.mem_union_left _ h)
      have h1 : (P \ S.image Subtype.val).card + (S.image Subtype.val).card = P.card :=
        Finset.card_sdiff_add_card_eq_card hsub
      have h2 : (S.image Subtype.val).card = S.card :=
        Finset.card_image_of_injective S Subtype.val_injective
      have h3 := Finset.card_union_le Q (S.biUnion t)
      omega
    obtain ⟨f, hinj, hf⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hall
    refine ⟨f, hinj, fun p => ?_⟩
    have := hf p
    have h' : f p ∈ ((E.filter (fun e => e.1 = p.val)).image Prod.snd) \ Q := this
    rw [Finset.mem_sdiff] at h'
    obtain ⟨e, he, hef⟩ := Finset.mem_image.mp h'.1
    obtain ⟨heE, hep⟩ := Finset.mem_filter.mp he
    refine ⟨?_, h'.2⟩
    have : e = (p.val, f p) := Prod.ext hep hef
    rw [← this]
    exact heE

  have konig {α β : Type} [DecidableEq α] [DecidableEq β] (E : Finset (α × β)) :
      ∃ (M : Finset (α × β)) (P : Finset α) (Q : Finset β), M ⊆ E ∧
        (∀ e ∈ M, ∀ e' ∈ M, e.1 = e'.1 → e = e') ∧ (∀ e ∈ M, ∀ e' ∈ M, e.2 = e'.2 → e = e') ∧
        (∀ e ∈ E, e.1 ∈ P ∨ e.2 ∈ Q) ∧ P.card + Q.card ≤ M.card := by
    classical
    have hex : ∃ k : ℕ, ∃ (P : Finset α) (Q : Finset β),
        (∀ e ∈ E, e.1 ∈ P ∨ e.2 ∈ Q) ∧ P.card + Q.card = k :=
      ⟨_, E.image Prod.fst, ∅, fun e he => Or.inl (Finset.mem_image_of_mem _ he), rfl⟩
    obtain ⟨P, Q, hcov, hk⟩ := Nat.find_spec hex
    have hmin : ∀ (P' : Finset α) (Q' : Finset β), (∀ e ∈ E, e.1 ∈ P' ∨ e.2 ∈ Q') →
        P.card + Q.card ≤ P'.card + Q'.card := by
      intro P' Q' h
      rw [hk]
      exact Nat.find_min' hex ⟨P', Q', h, rfl⟩
    obtain ⟨f, hfi, hf⟩ := side E P Q hmin hcov
    have hswap : ∀ (a : α) (b : β), (b, a) ∈ E.image Prod.swap ↔ (a, b) ∈ E := by
      intro a b
      constructor
      · intro h
        obtain ⟨e, he, hab⟩ := Finset.mem_image.mp h
        have : e = (a, b) := by
          rw [← Prod.swap_swap e, hab]; rfl
        rw [← this]; exact he
      · intro h
        exact Finset.mem_image.mpr ⟨(a, b), h, rfl⟩
    obtain ⟨g, hgi, hg⟩ := side (E.image Prod.swap) Q P (by
        intro Q' P' h
        have := hmin P' Q' (fun e he => by
          have := h (e.2, e.1) ((hswap e.1 e.2).mpr he)
          exact this.symm)
        omega) (by
        intro e he
        have h1 : (e.2, e.1) ∈ E := (hswap e.2 e.1).mp he
        exact (hcov _ h1).symm)
    have hg' : ∀ q : {q // q ∈ Q}, (g q, q.val) ∈ E ∧ g q ∉ P :=
      fun q => ⟨(hswap _ _).mp (hg q).1, (hg q).2⟩
    let M1 : Finset (α × β) := P.attach.image (fun p => (p.val, f p))
    let M2 : Finset (α × β) := Q.attach.image (fun q => (g q, q.val))
    have m1 : ∀ e ∈ M1, ∃ p : {p // p ∈ P}, e = (p.val, f p) := by
      intro e he
      obtain ⟨p, _, hp⟩ := Finset.mem_image.mp he
      exact ⟨p, hp.symm⟩
    have m2 : ∀ e ∈ M2, ∃ q : {q // q ∈ Q}, e = (g q, q.val) := by
      intro e he
      obtain ⟨q, _, hq⟩ := Finset.mem_image.mp he
      exact ⟨q, hq.symm⟩
    refine ⟨M1 ∪ M2, P, Q, ?_, ?_, ?_, hcov, ?_⟩
    · intro e he
      rcases Finset.mem_union.mp he with h | h
      · obtain ⟨p, rfl⟩ := m1 e h
        exact (hf p).1
      · obtain ⟨q, rfl⟩ := m2 e h
        exact (hg' q).1
    · intro e he e' he' h
      rcases Finset.mem_union.mp he with h1 | h1 <;> rcases Finset.mem_union.mp he' with h2 | h2
      · obtain ⟨p, rfl⟩ := m1 e h1
        obtain ⟨p', rfl⟩ := m1 e' h2
        have : p = p' := Subtype.ext h
        rw [this]
      · obtain ⟨p, rfl⟩ := m1 e h1
        obtain ⟨q, rfl⟩ := m2 e' h2
        exfalso
        apply (hg' q).2
        have h' : p.val = g q := h
        rw [← h']
        exact p.property
      · obtain ⟨q, rfl⟩ := m2 e h1
        obtain ⟨p, rfl⟩ := m1 e' h2
        exfalso
        apply (hg' q).2
        have h' : g q = p.val := h
        rw [h']
        exact p.property
      · obtain ⟨q, rfl⟩ := m2 e h1
        obtain ⟨q', rfl⟩ := m2 e' h2
        have : q = q' := hgi h
        rw [this]
    · intro e he e' he' h
      rcases Finset.mem_union.mp he with h1 | h1 <;> rcases Finset.mem_union.mp he' with h2 | h2
      · obtain ⟨p, rfl⟩ := m1 e h1
        obtain ⟨p', rfl⟩ := m1 e' h2
        have : p = p' := hfi h
        rw [this]
      · obtain ⟨p, rfl⟩ := m1 e h1
        obtain ⟨q, rfl⟩ := m2 e' h2
        exfalso
        apply (hf p).2
        have h' : f p = q.val := h
        rw [h']
        exact q.property
      · obtain ⟨q, rfl⟩ := m2 e h1
        obtain ⟨p, rfl⟩ := m1 e' h2
        exfalso
        apply (hf p).2
        have h' : q.val = f p := h
        rw [← h']
        exact q.property
      · obtain ⟨q, rfl⟩ := m2 e h1
        obtain ⟨q', rfl⟩ := m2 e' h2
        have : q = q' := Subtype.ext h
        rw [this]
    · have hd : Disjoint M1 M2 := by
        rw [Finset.disjoint_left]
        intro e h1 h2
        obtain ⟨p, rfl⟩ := m1 e h1
        obtain ⟨q, hq⟩ := m2 _ h2
        apply (hg' q).2
        have h' : p.val = g q := congrArg Prod.fst hq
        rw [← h']
        exact p.property
      have c1 : M1.card = P.card := by
        rw [Finset.card_image_of_injective _ (fun p p' h => Subtype.ext (congrArg Prod.fst h)),
          Finset.card_attach]
      have c2 : M2.card = Q.card := by
        rw [Finset.card_image_of_injective _ (fun q q' h => Subtype.ext (congrArg Prod.snd h)),
          Finset.card_attach]
      rw [Finset.card_union_of_disjoint hd, c1, c2]
  have neighbor (e) (he : e∈E) : ∃ d∈E, d≠e ∧ (d.1=e.1 ∨ d.2=e.2) := by
    by_contra no
    apply noStar
    refine ⟨{e},E.erase e,Fin.castAdd m e.1,Finset.singleton_nonempty _,?_,?_,?_⟩
    · ext d; by_cases h : d=e
      · subst d; simp [he]
      · simp [h]
    · apply Finset.disjoint_left.mpr
      intro v hv hd
      obtain ⟨d,hd,hv'⟩ := Finset.mem_biUnion.mp hd
      have hd' := Finset.mem_erase.mp hd
      simp only [Finset.singleton_biUnion,Finset.mem_insert,Finset.mem_singleton] at hv
      simp only [Finset.mem_insert,Finset.mem_singleton] at hv'
      rcases hv with hv|hv <;> rcases hv' with hz|hz
      · exact no ⟨d,hd'.2,hd'.1,Or.inl (Fin.castAdd_inj.mp (hz.symm.trans hv))⟩
      · have eq := congrArg Fin.val (hv.symm.trans hz)
        change e.1.val = n+d.2.val at eq
        have := e.1.isLt; omega
      · have eq := congrArg Fin.val (hz.symm.trans hv)
        change d.1.val = n+e.2.val at eq
        have := d.1.isLt; omega
      · have eq := congrArg Fin.val (hz.symm.trans hv)
        change n+d.2.val = n+e.2.val at eq
        exact no ⟨d,hd'.2,hd'.1,Or.inr (Fin.ext (by omega))⟩
    · intro d hd; obtain rfl := Finset.mem_singleton.mp hd; exact Or.inl rfl
  obtain ⟨M,P,Q,sub,rows,cols,cover,cost⟩ := konig E
  let D := E \ M
  have hits (e) (he : e∈M) : e.1 ∈ D.image Prod.fst ∨ e.2 ∈ D.image Prod.snd := by
    obtain ⟨d,hd,ne,eq⟩ := neighbor e (sub he)
    have hd' : d∈D := Finset.mem_sdiff.mpr ⟨hd,fun hm =>
      ne (eq.elim (rows d hm e he) (cols d hm e he))⟩
    exact eq.elim (fun h => Or.inl (h ▸ Finset.mem_image_of_mem Prod.fst hd'))
      (fun h => Or.inr (h ▸ Finset.mem_image_of_mem Prod.snd hd'))
  let X := M.filter fun e => e.1 ∈ D.image Prod.fst
  let Y := M.filter fun e => e.1 ∉ D.image Prod.fst
  have xc : X.card ≤ D.card := by
    have inj : Set.InjOn Prod.fst (↑X : Set (Fin n × Fin m)) := by
      intro e he d hd; exact rows e (Finset.mem_filter.mp he).1 d (Finset.mem_filter.mp hd).1
    rw [← Finset.card_image_of_injOn inj]
    apply (Finset.card_le_card (t:=D.image Prod.fst) _).trans Finset.card_image_le
    intro x hx; obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hx; exact (Finset.mem_filter.mp he).2
  have yc : Y.card ≤ D.card := by
    have inj : Set.InjOn Prod.snd (↑Y : Set (Fin n × Fin m)) := by
      intro e he d hd; exact cols e (Finset.mem_filter.mp he).1 d (Finset.mem_filter.mp hd).1
    rw [← Finset.card_image_of_injOn inj]
    apply (Finset.card_le_card (t:=D.image Prod.snd) _).trans Finset.card_image_le
    intro x hx; obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hx
    exact (hits e (Finset.mem_filter.mp he).1).resolve_left (Finset.mem_filter.mp he).2
  have total : X.card + Y.card = M.card := Finset.card_filter_add_card_filter_not _
  have avail : D.card+M.card=E.card := Finset.card_sdiff_add_card_eq_card sub
  by_cases enough : 15 ≤ C.size
  · exact ⟨P,Q,cover,by omega⟩
  have code {α : Type} [DecidableEq α] (S : Finset α) (sz : S.card ≤ 10) :
      ∃ f : α → Fin 10, Set.InjOn f (↑S : Set α) := by
    let emb : S → Fin 10 := fun s => Fin.castLE (by simpa using sz) (Fintype.equivFin S s)
    let f := fun x => if h : x∈S then emb ⟨x,h⟩ else 0
    refine ⟨f,?_⟩
    intro x hx y hy eq
    change x∈S at hx
    change y∈S at hy
    have eq' : emb ⟨x,hx⟩=emb ⟨y,hy⟩ := by simpa [f,hx,hy] using eq
    exact congrArg Subtype.val ((Fintype.equivFin S).injective (Fin.ext (congrArg (fun z : Fin 10 => z.val) eq')))
  obtain ⟨a,ai⟩ := code (E.image Prod.fst) (Finset.card_image_le.trans small)
  obtain ⟨b,bi⟩ := code (E.image Prod.snd) (Finset.card_image_le.trans small)
  let f := fun e : Fin n × Fin m => (a e.1,b e.2)
  let B := E.image f
  have am {e} (he : e∈E) : e.1∈E.image Prod.fst := Finset.mem_image_of_mem _ he
  have bm {e} (he : e∈E) : e.2∈E.image Prod.snd := Finset.mem_image_of_mem _ he
  have inj : Set.InjOn f (↑E : Set (Fin n × Fin m)) := fun _ hp _ hq eq =>
    Prod.ext (ai (am hp) (am hq) (congrArg Prod.fst eq)) (bi (bm hp) (bm hq) (congrArg Prod.snd eq))
  have ec : B.card=E.card := Finset.card_image_of_injOn inj
  have mr : B.image Prod.fst=(E.image Prod.fst).image a := by simp [B,f,Finset.image_image,Function.comp_def]
  have mc : B.image Prod.snd=(E.image Prod.snd).image b := by simp [B,f,Finset.image_image,Function.comp_def]
  have r5 : 5≤(B.image Prod.fst).card := by rw [mr,Finset.card_image_of_injOn ai]; omega
  have c5 : 5≤(B.image Prod.snd).card := by rw [mc,Finset.card_image_of_injOn bi]; omega
  have nb (i) (hi : i∈B) : ∃ j∈B, j≠i ∧ (j.1=i.1 ∨ j.2=i.2) := by
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨d,hd,ne,adj⟩ := neighbor e he
    exact ⟨f d,Finset.mem_image_of_mem _ hd,fun h => ne (inj hd he h),
      adj.elim (fun h => Or.inl (congrArg a h)) (fun h => Or.inr (congrArg b h))⟩
  have bf : ∀ p q l s, p ≠ q → l ≠ s → ¬((p,l)∈B ∧ (p,s)∈B ∧ (q,l)∈B ∧ (q,s)∈B) := by
    intro p q l s hp hl quad
    obtain ⟨w,x,y,z⟩ := quad
    obtain ⟨w,hw,ew⟩ := Finset.mem_image.mp w; obtain ⟨x,hx,ex⟩ := Finset.mem_image.mp x
    obtain ⟨y,hy,ey⟩ := Finset.mem_image.mp y; obtain ⟨z,hz,ez⟩ := Finset.mem_image.mp z
    have rwx : w.1=x.1 := ai (am hw) (am hx) ((congrArg Prod.fst ew).trans (congrArg Prod.fst ex).symm)
    have ryz : y.1=z.1 := ai (am hy) (am hz) ((congrArg Prod.fst ey).trans (congrArg Prod.fst ez).symm)
    have cwy : w.2=y.2 := bi (bm hw) (bm hy) ((congrArg Prod.snd ew).trans (congrArg Prod.snd ey).symm)
    have cxz : x.2=z.2 := bi (bm hx) (bm hz) ((congrArg Prod.snd ex).trans (congrArg Prod.snd ez).symm)
    apply free w.1 y.1 w.2 x.2
    · intro e; apply hp; exact (congrArg Prod.fst ew).symm.trans ((congrArg a e).trans (congrArg Prod.fst ey))
    · intro e; apply hl; exact (congrArg Prod.snd ew).symm.trans ((congrArg b e).trans (congrArg Prod.snd ex))
    · exact ⟨hw,rwx ▸ hx,cwy ▸ hy,ryz ▸ cxz ▸ hz⟩

  have getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by simp
  let wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
    if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m


  let relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
    ⟨g.op, g.inputs.map (wmap n m π)⟩


  let relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
    ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩


  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]


  let Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
    n ≤ W.length ∧ W'.length + n = W.length + m ∧
      ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

  have rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
      (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
    obtain ⟨h1, h2, h3⟩ := h
    have hv : (relGate n m π g).op.eval
        ((relGate n m π g).inputs.map fun i => W'.getD i false)
        = g.op.eval (g.inputs.map fun i => W.getD i false) := by
      simp only [relGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro a _
      exact h3 a
    refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
    intro w
    simp only [step, hv]
    rcases Nat.lt_trichotomy w W.length with hw | hw | hw
    · have hlt : wmap n m π w < W'.length := by
        unfold wmap
        split
        · have := (π ⟨w, by assumption⟩).2; omega
        · omega
      rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
      exact h3 w
    · have he : wmap n m π w = W'.length := by
        unfold wmap
        split
        · omega
        · omega
      rw [he, hw, getD_snoc_eq, getD_snoc_eq]
    · have hge : W'.length + 1 ≤ wmap n m π w := by
        unfold wmap
        split
        · omega
        · omega
      rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

  have rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
      ∀ W W' : List Bool, Rel n m π W W' →
        Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
    induction gs with
    | nil => intro W W' h; exact h
    | cons g gs ih =>
      intro W W' h
      exact ih _ _ (rel_step n m π W W' g h)

  have rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
      Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
    refine ⟨by simp, by simp; omega, ?_⟩
    intro w
    unfold wmap
    split
    · rename_i hw
      rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
      simp
    · rename_i hw
      rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]
  let π : Fin (n+m) → Fin 20 :=
    Fin.addCases (fun p => Fin.castAdd 10 (a p)) (fun l => Fin.natAdd 10 (b l))
  let C' := relabel (n+m) 20 π C
  have cs : C'.size=C.size := by
    change (C.gates.map (relGate (n+m) 20 π)).length = C.gates.length
    exact List.length_map _
  have ao' : IsAO2 20 C' := by
    obtain ⟨ops,back,fan⟩ := ao
    refine ⟨?_,?_,?_⟩
    · intro g hg
      obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hg
      exact ops v hv
    · intro j hj t ht
      have sj : j<C.gates.length := by simpa [C',relabel] using hj
      have get : gateAt C' j = relGate (n+m) 20 π (gateAt C j) := by
        change (C.gates.map (relGate (n+m) 20 π)).getD j _ =
          relGate (n+m) 20 π (C.gates.getD j _)
        simp [sj]
      rw [get] at ht
      obtain ⟨z,hz,rfl⟩ := List.mem_map.mp ht
      have h := back j sj z hz
      dsimp only [wmap]
      split
      · have hπ := (π ⟨z,by assumption⟩).isLt;omega
      · omega
    · intro g hg
      obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hg
      simpa [relGate] using fan v hv
  have fn (x : Fin 20 → Bool) : circuitFun 20 C' x =
      decide (∃ e ∈ B, x (Fin.castAdd 10 e.1)=true ∧ x (Fin.natAdd 10 e.2)=true) := by
    have trans := (rel_fold (n+m) 20 π C.gates _ _ (rel_init (n+m) 20 π x)).2.2 C.output
    change circuitFun 20 C' x = circuitFun (n+m) C (x ∘ π) at trans
    rw [trans,spec]
    apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨e,he,hp,hl⟩
      exact ⟨f e,Finset.mem_image_of_mem _ he,by simpa [f,π] using hp,by simpa [f,π] using hl⟩
    · rintro ⟨_,hb,hp,hl⟩
      obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hb
      exact ⟨e,he,by simpa [f,π] using hp,by simpa [f,π] using hl⟩
  obtain ⟨U,V,uv,pay⟩ := residual B C' r5 c5 (ec ▸ small) nb bf ao' (by omega) fn
  let U' := (E.image Prod.fst).filter fun p => a p∈U
  let V' := (E.image Prod.snd).filter fun l => b l∈V
  have uc : U'.card≤U.card := by
    have ii : Set.InjOn a (↑U' : Set (Fin n)) := fun x hx y hy => ai (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1
    rw [← Finset.card_image_of_injOn ii]
    apply Finset.card_le_card; intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy; exact (Finset.mem_filter.mp hx).2
  have vc : V'.card≤V.card := by
    have ii : Set.InjOn b (↑V' : Set (Fin m)) := fun x hx y hy => bi (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1
    rw [← Finset.card_image_of_injOn ii]
    apply Finset.card_le_card; intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy; exact (Finset.mem_filter.mp hx).2
  refine ⟨U',V',?_,by omega⟩
  intro e he
  exact (uv (f e) (Finset.mem_image_of_mem _ he)).elim
    (fun hp => Or.inl (Finset.mem_filter.mpr ⟨am he,hp⟩))
    (fun hl => Or.inr (Finset.mem_filter.mpr ⟨bm he,hl⟩))
