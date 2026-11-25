import PEqualNP.Defs.AndCountCircuit

namespace PEqualNP.Outside.L_meta_1031_aux.UniqueBareCover

open PEqualNP.AndCount

lemma side_eq {n k : ℕ} (U V B : Finset (Fin n)) (F : Finset (Fin k))
    (i : Fin k) (f h : Fin k → Bool)
    (hB : (∃ v ∈ B, v ∈ U) ↔ ∃ v ∈ B, v ∈ V)
    (hval : ∀ j, f j = h j) :
    AndCountCircuit.sideTrue U B F i f = AndCountCircuit.sideTrue V B F i h := by
  apply Bool.eq_iff_iff.mpr
  simp only [AndCountCircuit.sideTrue, decide_eq_true_eq]
  exact or_congr hB (by simp only [hval])

lemma fuel_eq {n : ℕ} (C : AndCountCircuit n) (U V : Finset (Fin n))
    (hL : ∀ i, (∃ v ∈ C.leftVars i, v ∈ U) ↔ ∃ v ∈ C.leftVars i, v ∈ V)
    (hR : ∀ i, (∃ v ∈ C.rightVars i, v ∈ U) ↔ ∃ v ∈ C.rightVars i, v ∈ V) :
    ∀ fuel i, C.gateValFuel U fuel i = C.gateValFuel V fuel i := by
  intro fuel
  induction fuel with
  | zero => intro i; rfl
  | succ fuel ih =>
    intro i
    simp only [AndCountCircuit.gateValFuel]
    rw [side_eq U V (C.leftVars i) (C.leftGates i) i _ _ (hL i) ih,
      side_eq U V (C.rightVars i) (C.rightGates i) i _ _ (hR i) ih]

lemma eval_eq {n : ℕ} (C : AndCountCircuit n) (hout : C.outVars = ∅)
    (U V : Finset (Fin n))
    (hL : ∀ i, (∃ v ∈ C.leftVars i, v ∈ U) ↔ ∃ v ∈ C.leftVars i, v ∈ V)
    (hR : ∀ i, (∃ v ∈ C.rightVars i, v ∈ U) ↔ ∃ v ∈ C.rightVars i, v ∈ V) :
    C.eval U = C.eval V := by
  simp only [AndCountCircuit.eval, AndCountCircuit.gateVal, hout,
    fuel_eq C U V hL hR, Finset.notMem_empty, false_and, exists_false, false_or]

lemma eval_true_has_raw {n : ℕ} (C : AndCountCircuit n) (hout : C.outVars = ∅)
    (U : Finset (Fin n)) (ht : C.eval U = true) :
    ∃ i, (∃ v ∈ C.leftVars i, v ∈ U) ∧ (∃ v ∈ C.rightVars i, v ∈ U) := by
  classical
  by_contra hn
  have hz : ∀ fuel i, C.gateValFuel U fuel i = false := by
    intro fuel
    induction fuel with
    | zero => intro i; rfl
    | succ fuel ih =>
      intro i
      apply Bool.eq_false_iff.mpr
      intro hit
      apply hn
      refine ⟨i, ?_⟩
      simpa only [AndCountCircuit.gateValFuel, AndCountCircuit.sideTrue,
        Bool.and_eq_true, decide_eq_true_eq, ih, Bool.false_eq_true, and_false,
        exists_false, or_false] using hit
  simp [AndCountCircuit.eval, AndCountCircuit.gateVal, hout, hz] at ht

lemma pair_left_hit {n : ℕ} (C : AndCountCircuit n)
    (disj : ∀ i, Disjoint (C.leftVars i) (C.rightVars i))
    (unique : ∀ v i j, (v ∈ C.leftVars i ∨ v ∈ C.rightVars i) →
      (v ∈ C.leftVars j ∨ v ∈ C.rightVars j) → i = j)
    (i j : Fin C.size) (u v : Fin n) (hu : u ∈ C.leftVars i) (hv : v ∈ C.rightVars i) :
    (∃ z ∈ C.leftVars j, z ∈ ({u, v} : Finset (Fin n))) ↔ j = i := by
  constructor
  · rintro ⟨z, hz, hzuv⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hzuv
    rcases hzuv with rfl | rfl
    · exact unique z j i (Or.inl hz) (Or.inl hu)
    · have hji := unique z j i (Or.inl hz) (Or.inr hv)
      subst j
      exact False.elim (Finset.disjoint_left.mp (disj i) hz hv)
  · rintro rfl
    exact ⟨u, hu, by simp⟩

lemma pair_right_hit {n : ℕ} (C : AndCountCircuit n)
    (disj : ∀ i, Disjoint (C.leftVars i) (C.rightVars i))
    (unique : ∀ v i j, (v ∈ C.leftVars i ∨ v ∈ C.rightVars i) →
      (v ∈ C.leftVars j ∨ v ∈ C.rightVars j) → i = j)
    (i j : Fin C.size) (u v : Fin n) (hu : u ∈ C.leftVars i) (hv : v ∈ C.rightVars i) :
    (∃ z ∈ C.rightVars j, z ∈ ({u, v} : Finset (Fin n))) ↔ j = i := by
  constructor
  · rintro ⟨z, hz, hzuv⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hzuv
    rcases hzuv with rfl | rfl
    · have hji := unique z j i (Or.inr hz) (Or.inl hu)
      subst j
      exact False.elim (Finset.disjoint_left.mp (disj i) hu hz)
    · exact unique z j i (Or.inr hz) (Or.inr hv)
  · rintro rfl
    exact ⟨v, hv, by simp⟩

lemma pair_cross_eq {n : ℕ} (C : AndCountCircuit n) (hout : C.outVars = ∅)
    (disj : ∀ i, Disjoint (C.leftVars i) (C.rightVars i))
    (unique : ∀ v i j, (v ∈ C.leftVars i ∨ v ∈ C.rightVars i) →
      (v ∈ C.leftVars j ∨ v ∈ C.rightVars j) → i = j)
    (i : Fin C.size) (u v p q : Fin n)
    (hu : u ∈ C.leftVars i) (hv : v ∈ C.rightVars i)
    (hp : p ∈ C.leftVars i) (hq : q ∈ C.rightVars i) :
    C.eval {u, v} = C.eval {p, q} := by
  apply eval_eq C hout
  · intro j
    exact (pair_left_hit C disj unique i j u v hu hv).trans
      (pair_left_hit C disj unique i j p q hp hq).symm
  · intro j
    exact (pair_right_hit C disj unique i j u v hu hv).trans
      (pair_right_hit C disj unique i j p q hp hq).symm

lemma computes_pair {n : ℕ} (C : AndCountCircuit n) (G : SimpleGraph (Fin n))
    (computes : C.Computes G) (u v : Fin n) : C.eval {u, v} = true ↔ G.Adj u v := by
  rw [computes {u, v}]
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact False.elim (G.ne_of_adj hab rfl)
    · exact hab
    · exact hab.symm
    · exact False.elim (G.ne_of_adj hab rfl)
  · intro h
    exact ⟨u, by simp, v, by simp, h⟩

lemma edge_has_raw {n : ℕ} (C : AndCountCircuit n) (hout : C.outVars = ∅)
    (disj : ∀ i, Disjoint (C.leftVars i) (C.rightVars i))
    (G : SimpleGraph (Fin n)) (computes : C.Computes G)
    (u v : Fin n) (huv : G.Adj u v) :
    ∃ i, (u ∈ C.leftVars i ∧ v ∈ C.rightVars i) ∨
      (v ∈ C.leftVars i ∧ u ∈ C.rightVars i) := by
  obtain ⟨i, ⟨p, hp, hpv⟩, ⟨q, hq, hqv⟩⟩ :=
    eval_true_has_raw C hout {u, v} ((computes_pair C G computes u v).mpr huv)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hpv hqv
  rcases hpv with rfl | rfl <;> rcases hqv with rfl | rfl
  · exact False.elim (Finset.disjoint_left.mp (disj i) hp hq)
  · exact ⟨i, Or.inl ⟨hp, hq⟩⟩
  · exact ⟨i, Or.inr ⟨hp, hq⟩⟩
  · exact False.elim (Finset.disjoint_left.mp (disj i) hp hq)

lemma unique_bare_biclique_cover {n : ℕ} (C : AndCountCircuit n) (G : SimpleGraph (Fin n))
    (computes : C.Computes G) (hout : C.outVars = ∅)
    (disj : ∀ i, Disjoint (C.leftVars i) (C.rightVars i))
    (unique : ∀ v i j, (v ∈ C.leftVars i ∨ v ∈ C.rightVars i) →
      (v ∈ C.leftVars j ∨ v ∈ C.rightVars j) → i = j) :
    ∃ X Y : Fin C.size → Finset (Fin n),
      (∀ i, ∀ a ∈ X i, ∀ b ∈ Y i, G.Adj a b) ∧
      ∀ a b, G.Adj a b → ∃ i, (a ∈ X i ∧ b ∈ Y i) ∨ (b ∈ X i ∧ a ∈ Y i) := by
  classical
  let good (i : Fin C.size) := ∃ u ∈ C.leftVars i, ∃ v ∈ C.rightVars i, G.Adj u v
  let X (i : Fin C.size) := if good i then C.leftVars i else ∅
  let Y (i : Fin C.size) := if good i then C.rightVars i else ∅
  refine ⟨X, Y, ?_, ?_⟩
  · intro i p hp q hq
    by_cases hg : good i
    · have hp' : p ∈ C.leftVars i := by simpa only [X, ite_eq_left hg] using hp
      have hq' : q ∈ C.rightVars i := by simpa only [Y, ite_eq_left hg] using hq
      obtain ⟨u, hu, v, hv, huv⟩ := hg
      have heval := (computes_pair C G computes u v).mpr huv
      rw [pair_cross_eq C hout disj unique i u v p q hu hv hp' hq'] at heval
      exact (computes_pair C G computes p q).mp heval
    · simp [X, hg] at hp
  · intro u v huv
    obtain ⟨i, h⟩ := edge_has_raw C hout disj G computes u v huv
    refine ⟨i, ?_⟩
    rcases h with ⟨hu, hv⟩ | ⟨hv, hu⟩
    · have hg : good i := ⟨u, hu, v, hv, huv⟩
      exact Or.inl ⟨by simpa only [X, ite_eq_left hg] using hu,
        by simpa only [Y, ite_eq_left hg] using hv⟩
    · have hg : good i := ⟨v, hv, u, hu, huv.symm⟩
      exact Or.inr ⟨by simpa only [X, ite_eq_left hg] using hv,
        by simpa only [Y, ite_eq_left hg] using hu⟩

end PEqualNP.Outside.L_meta_1031_aux.UniqueBareCover

namespace PEqualNP.Outside.L_meta_1031_aux.UniqueBareCover

lemma biclique_center {n : ℕ} [Nonempty (Fin n)] (G : SimpleGraph (Fin n))
    (no4 : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    (X Y : Finset (Fin n)) (complete : ∀ a ∈ X, ∀ b ∈ Y, G.Adj a b) :
    ∃ c : Fin n, ∀ a ∈ X, ∀ b ∈ Y, a = c ∨ b = c := by
  classical
  by_cases hx : X.Nonempty
  · obtain ⟨a, ha⟩ := hx
    by_cases hsingleton : ∀ c ∈ X, c = a
    · exact ⟨a, fun c hc _ _ => Or.inl (hsingleton c hc)⟩
    · push Not at hsingleton
      obtain ⟨c, hc, hca⟩ := hsingleton
      by_cases hy : Y.Nonempty
      · obtain ⟨b, hb⟩ := hy
        refine ⟨b, ?_⟩
        intro p hp q hq
        have h := no4 a b c q (complete a ha b hb) (complete c hc b hb).symm
          (complete c hc q hq) (complete a ha q hq).symm
        exact Or.inr ((h.resolve_left (Ne.symm hca)).symm)
      · exact ⟨a, fun _ _ b hb => False.elim (hy ⟨b, hb⟩)⟩
  · exact ⟨Classical.arbitrary (Fin n), fun a ha _ _ => False.elim (hx ⟨a, ha⟩)⟩

lemma biclique_cover_to_vertex_cover {n k : ℕ} (G : SimpleGraph (Fin n))
    (no4 : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    (X Y : Fin k → Finset (Fin n))
    (complete : ∀ i, ∀ a ∈ X i, ∀ b ∈ Y i, G.Adj a b)
    (cover : ∀ a b, G.Adj a b → ∃ i, (a ∈ X i ∧ b ∈ Y i) ∨
      (b ∈ X i ∧ a ∈ Y i)) :
    ∃ S : Finset (Fin n), S.card ≤ k ∧ ∀ a b, G.Adj a b → a ∈ S ∨ b ∈ S := by
  classical
  by_cases hn : Nonempty (Fin n)
  · let _ : Nonempty (Fin n) := hn
    have hc : ∀ i, ∃ c : Fin n, ∀ a ∈ X i, ∀ b ∈ Y i, a = c ∨ b = c :=
      fun i => biclique_center G no4 (X i) (Y i) (complete i)
    choose c hc using hc
    refine ⟨Finset.univ.image c, ?_, ?_⟩
    · exact (Finset.card_image_le).trans (by simp)
    · intro a b hab
      obtain ⟨i, h⟩ := cover a b hab
      have hci : c i ∈ Finset.univ.image c := Finset.mem_image.mpr ⟨i, by simp, rfl⟩
      rcases h with ⟨ha, hb⟩ | ⟨hb, ha⟩
      · rcases hc i a ha b hb with rfl | rfl
        · exact Or.inl hci
        · exact Or.inr hci
      · rcases hc i b hb a ha with rfl | rfl
        · exact Or.inr hci
        · exact Or.inl hci
  · refine ⟨∅, by simp, ?_⟩
    intro a
    exact False.elim (hn ⟨a⟩)

lemma unique_bare_vertex_cover {n : ℕ} (C : PEqualNP.AndCount.AndCountCircuit n)
    (G : SimpleGraph (Fin n))
    (no4 : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    (computes : C.Computes G) (hout : C.outVars = ∅)
    (disj : ∀ i, Disjoint (C.leftVars i) (C.rightVars i))
    (unique : ∀ v i j, (v ∈ C.leftVars i ∨ v ∈ C.rightVars i) →
      (v ∈ C.leftVars j ∨ v ∈ C.rightVars j) → i = j) :
    ∃ S : Finset (Fin n), S.card ≤ C.size ∧
      ∀ a b, G.Adj a b → a ∈ S ∨ b ∈ S := by
  obtain ⟨X, Y, complete, cover⟩ := unique_bare_biclique_cover C G computes hout disj unique
  exact biclique_cover_to_vertex_cover G no4 X Y complete cover

end PEqualNP.Outside.L_meta_1031_aux.UniqueBareCover
