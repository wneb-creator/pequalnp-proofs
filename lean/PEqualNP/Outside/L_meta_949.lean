import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Push
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_949_aux.ExistingProof

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

section CircuitCore

private def IsMIS {n : ℕ} (G : SimpleGraph (Fin n)) (I : Finset (Fin n)) : Prop :=
  (∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w) ∧ (∀ u : Fin n, u ∉ I → ∃ v ∈ I, G.Adj u v)

private def Fits {n : ℕ} (G : SimpleGraph (Fin n)) (C : AndCountCircuit n) : Prop :=
  ∀ I : Finset (Fin n), IsMIS G I →
    C.eval I = false ∧ ∀ u : Fin n, u ∉ I → C.eval (insert u I) = true

private def HasBicliqueCover {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) : Prop :=
  ∃ (X Y : Fin k → Finset (Fin n)),
    (∀ i : Fin k, ∀ a ∈ X i, ∀ b ∈ Y i, G.Adj a b) ∧
    (∀ a b : Fin n, G.Adj a b → ∃ i : Fin k, (a ∈ X i ∧ b ∈ Y i) ∨ (b ∈ X i ∧ a ∈ Y i))

private lemma exists_mis_supset {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (hS : ∀ v ∈ S, ∀ w ∈ S, ¬ G.Adj v w) :
    ∃ I : Finset (Fin n), S ⊆ I ∧ IsMIS G I := by
  classical
  have key : ∀ k : ℕ, ∀ S : Finset (Fin n), n - S.card ≤ k →
      (∀ v ∈ S, ∀ w ∈ S, ¬ G.Adj v w) → ∃ I : Finset (Fin n), S ⊆ I ∧ IsMIS G I := by
    intro k
    induction k with
    | zero =>
      intro S hk hI
      refine ⟨S, Finset.Subset.rfl, hI, ?_⟩
      intro u hu
      have hcard : S.card < n := by
        have hlt : S.card < (Finset.univ : Finset (Fin n)).card :=
          Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
            ⟨Finset.subset_univ S, fun heq => hu (by rw [heq]; exact Finset.mem_univ u)⟩)
        simpa using hlt
      omega
    | succ k ih =>
      intro S hk hI
      by_cases hmax : ∀ u : Fin n, u ∉ S → ∃ v ∈ S, G.Adj u v
      · exact ⟨S, Finset.Subset.rfl, hI, hmax⟩
      · push_neg at hmax
        obtain ⟨u, huS, hno⟩ := hmax
        have hI' : ∀ v ∈ insert u S, ∀ w ∈ insert u S, ¬ G.Adj v w := by
          intro v hv w hw
          rcases Finset.mem_insert.mp hv with rfl | hvS
          · rcases Finset.mem_insert.mp hw with rfl | hwS
            · exact fun h => G.ne_of_adj h rfl
            · exact hno w hwS
          · rcases Finset.mem_insert.mp hw with rfl | hwS
            · exact fun hadj => hno v hvS ((G.adj_comm _ _).mpr hadj)
            · exact hI v hvS w hwS
        have hcard : (insert u S).card = S.card + 1 := Finset.card_insert_of_notMem huS
        obtain ⟨I, hsub, hmis⟩ := ih (insert u S) (by omega) hI'
        exact ⟨I, (Finset.subset_insert u S).trans hsub, hmis⟩
  exact key (n - S.card) S le_rfl hS

private lemma exists_mis_mem {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) :
    ∃ I : Finset (Fin n), v ∈ I ∧ IsMIS G I := by
  have hS : ∀ a ∈ ({v} : Finset (Fin n)), ∀ b ∈ ({v} : Finset (Fin n)), ¬ G.Adj a b := by
    intro a ha b hb
    rw [Finset.mem_singleton.mp ha, Finset.mem_singleton.mp hb]
    exact fun h => G.ne_of_adj h rfl
  obtain ⟨I, hsub, hmis⟩ := exists_mis_supset G {v} hS
  exact ⟨I, hsub (Finset.mem_singleton_self v), hmis⟩

private lemma exists_mis_pair {n : ℕ} (G : SimpleGraph (Fin n)) {a b : Fin n} (h : ¬ G.Adj a b) :
    ∃ I : Finset (Fin n), a ∈ I ∧ b ∈ I ∧ IsMIS G I := by
  have hS : ∀ x ∈ ({a, b} : Finset (Fin n)), ∀ y ∈ ({a, b} : Finset (Fin n)), ¬ G.Adj x y := by
    intro x hx y hy
    rcases Finset.mem_insert.mp hx with rfl | hx
    · rcases Finset.mem_insert.mp hy with rfl | hy
      · exact fun hadj => G.ne_of_adj hadj rfl
      · rw [Finset.mem_singleton.mp hy]; exact h
    · rw [Finset.mem_singleton.mp hx]
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact fun hadj => h ((G.adj_comm _ _).mpr hadj)
      · rw [Finset.mem_singleton.mp hy]; exact fun hadj => G.ne_of_adj hadj rfl
  obtain ⟨I, hsub, hmis⟩ := exists_mis_supset G {a, b} hS
  exact ⟨I, hsub (by simp), hsub (by simp), hmis⟩

private lemma mis_apart {n : ℕ} {G : SimpleGraph (Fin n)} {I J : Finset (Fin n)}
    (hI : IsMIS G I) (hJ : IsMIS G J) (hne : I ≠ J) :
    ∃ v ∈ J, v ∉ I := by
  by_contra hsub
  push_neg at hsub
  apply hne
  apply Finset.Subset.antisymm
  · intro u hu
    by_contra huJ
    obtain ⟨v, hvJ, hadj⟩ := hJ.2 u huJ
    exact hI.1 u hu v (hsub v hvJ) hadj
  · exact hsub

private lemma sideTrue_congr {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v w : Fin k → Bool) (h : ∀ j, j < i → v j = w j) :
    sideTrue U B F i v = sideTrue U B F i w := by
  unfold sideTrue
  refine decide_eq_decide.mpr ?_
  constructor
  · rintro (h1 | ⟨j, hj, hji, hv⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨j, hj, hji, by rw [← h j hji]; exact hv⟩
  · rintro (h1 | ⟨j, hj, hji, hv⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨j, hj, hji, by rw [h j hji]; exact hv⟩

private lemma sideTrue_iff {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v : Fin k → Bool) :
    sideTrue U B F i v = true ↔ ((∃ x ∈ B, x ∈ U) ∨ ∃ j ∈ F, j < i ∧ v j = true) := by
  unfold sideTrue
  exact decide_eq_true_iff

private lemma sideTrue_mono {n k : ℕ} (U U' B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v w : Fin k → Bool) (hU : U ⊆ U') (h : ∀ j, j < i → v j = true → w j = true)
    (hs : sideTrue U B F i v = true) : sideTrue U' B F i w = true := by
  rw [sideTrue_iff] at hs ⊢
  rcases hs with ⟨x, hx, hxU⟩ | ⟨j, hj, hji, hv⟩
  · exact Or.inl ⟨x, hx, hU hxU⟩
  · exact Or.inr ⟨j, hj, hji, h j hji hv⟩

private lemma fuel_succ {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ d : ℕ, ∀ i : Fin C.size, i.val < d →
      gateValFuel C U (d + 1) i = gateValFuel C U d i := by
  intro d
  induction d with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
  | succ d ih =>
    intro i hi
    show (sideTrue U (C.leftVars i) (C.leftGates i) i (gateValFuel C U (d + 1)) &&
        sideTrue U (C.rightVars i) (C.rightGates i) i (gateValFuel C U (d + 1))) =
      (sideTrue U (C.leftVars i) (C.leftGates i) i (gateValFuel C U d) &&
        sideTrue U (C.rightVars i) (C.rightGates i) i (gateValFuel C U d))
    have hc : ∀ j : Fin C.size, j < i → gateValFuel C U (d + 1) j = gateValFuel C U d j := by
      intro j hji
      exact ih j (by have : j.val < i.val := hji; omega)
    rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ hc,
      sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ hc]

private lemma gateVal_rec {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal U i = (sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) &&
      sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U)) :=
  (fuel_succ C U C.size i i.isLt).symm

private lemma eval_iff {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    C.eval U = true ↔ ((∃ v ∈ C.outVars, v ∈ U) ∨ ∃ j ∈ C.outGates, C.gateVal U j = true) := by
  unfold AndCountCircuit.eval
  exact decide_eq_true_iff

private lemma gateVal_mono {n : ℕ} (C : AndCountCircuit n) {U U' : Finset (Fin n)} (hU : U ⊆ U')
    (i : Fin C.size) (h : C.gateVal U i = true) : C.gateVal U' i = true := by
  have key : ∀ d : ℕ, ∀ i : Fin C.size, gateValFuel C U d i = true → gateValFuel C U' d i = true := by
    intro d
    induction d with
    | zero => intro i hi; simp [gateValFuel] at hi
    | succ d ih =>
      intro i hi
      simp only [gateValFuel, Bool.and_eq_true] at hi ⊢
      exact ⟨sideTrue_mono U U' _ _ i _ _ hU (fun j _ => ih j) hi.1,
        sideTrue_mono U U' _ _ i _ _ hU (fun j _ => ih j) hi.2⟩
  exact key C.size i h

private lemma eval_mono {n : ℕ} (C : AndCountCircuit n) {U U' : Finset (Fin n)} (hU : U ⊆ U')
    (h : C.eval U = true) : C.eval U' = true := by
  rw [eval_iff] at h ⊢
  rcases h with ⟨v, hv, hvU⟩ | ⟨j, hj, hg⟩
  · exact Or.inl ⟨v, hv, hU hvU⟩
  · exact Or.inr ⟨j, hj, gateVal_mono C hU j hg⟩

private def sv {n : ℕ} (C : AndCountCircuit n) (X : Finset (Fin n)) (i : Fin C.size) (s : Bool) : Bool :=
  sideTrue X (cond s (C.rightVars i) (C.leftVars i)) (cond s (C.rightGates i) (C.leftGates i)) i
    (C.gateVal X)

private def varsOf {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) (s : Bool) : Finset (Fin n) :=
  cond s (C.rightVars i) (C.leftVars i)

private def gatesOf {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) (s : Bool) : Finset (Fin C.size) :=
  cond s (C.rightGates i) (C.leftGates i)

private lemma gate_false_iff {n : ℕ} (C : AndCountCircuit n) (X : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal X i = false ↔ (sv C X i false = false ∨ sv C X i true = false) := by
  rw [gateVal_rec, Bool.and_eq_false_iff]
  rfl

private lemma sv_hit_mem {n : ℕ} (C : AndCountCircuit n) {X : Finset (Fin n)} {v : Fin n}
    (hvX : v ∈ X) (i : Fin C.size) (s : Bool) (hv : v ∈ varsOf C i s) :
    sv C X i s = true := by
  exact (sideTrue_iff _ _ _ _ _).mpr (Or.inl ⟨v, hv, hvX⟩)

private lemma sv_merge {n : ℕ} (C : AndCountCircuit n) (X Y : Finset (Fin n)) (i : Fin C.size)
    (s : Bool) (hX : sv C X i s = false) (hY : sv C Y i s = false)
    (ih : ∀ j : Fin C.size, j < i → C.gateVal X j = false → C.gateVal Y j = false →
      C.gateVal (X ∪ Y) j = false) : sv C (X ∪ Y) i s = false := by
  rw [← Bool.not_eq_true] at hX hY ⊢
  unfold sv at hX hY ⊢
  rw [sideTrue_iff] at hX hY ⊢
  rintro (⟨x, hx, hxU⟩ | ⟨j, hj, hji, hv⟩)
  · rcases Finset.mem_union.mp hxU with h | h
    · exact hX (Or.inl ⟨x, hx, h⟩)
    · exact hY (Or.inl ⟨x, hx, h⟩)
  · have h1 : C.gateVal X j = false := by
      rw [← Bool.not_eq_true]; exact fun hh => hX (Or.inr ⟨j, hj, hji, hh⟩)
    have h2 : C.gateVal Y j = false := by
      rw [← Bool.not_eq_true]; exact fun hh => hY (Or.inr ⟨j, hj, hji, hh⟩)
    rw [ih j hji h1 h2] at hv
    exact Bool.noConfusion hv

private lemma merge_eval_gen {n : ℕ} (C : AndCountCircuit n) (X Y : Finset (Fin n))
    (f : Fin C.size → Bool)
    (hfX : ∀ i : Fin C.size, C.gateVal X i = false → sv C X i (f i) = false)
    (hfY : ∀ i : Fin C.size, C.gateVal Y i = false → sv C Y i (f i) = false)
    (h1 : C.eval X = false) (h2 : C.eval Y = false) : C.eval (X ∪ Y) = false := by
  have hgate : ∀ m : ℕ, ∀ i : Fin C.size, i.val < m →
      C.gateVal X i = false → C.gateVal Y i = false → C.gateVal (X ∪ Y) i = false := by
    intro m
    induction m with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
    | succ m ih =>
      intro i hi hX hY
      have ih' : ∀ j : Fin C.size, j < i → C.gateVal X j = false → C.gateVal Y j = false →
          C.gateVal (X ∪ Y) j = false := by
        intro j hji; exact ih j (by have : j.val < i.val := hji; omega)
      have hm := sv_merge C X Y i (f i) (hfX i hX) (hfY i hY) ih'
      rw [gate_false_iff]
      cases hfi : f i with
      | false => rw [hfi] at hm; exact Or.inl hm
      | true => rw [hfi] at hm; exact Or.inr hm
  rw [← Bool.not_eq_true, eval_iff] at h1 h2 ⊢
  rintro (⟨x, hx, hxU⟩ | ⟨j, hj, hv⟩)
  · rcases Finset.mem_union.mp hxU with h | h
    · exact h1 (Or.inl ⟨x, hx, h⟩)
    · exact h2 (Or.inl ⟨x, hx, h⟩)
  · have g1 : C.gateVal X j = false := by
      rw [← Bool.not_eq_true]; exact fun hh => h1 (Or.inr ⟨j, hj, hh⟩)
    have g2 : C.gateVal Y j = false := by
      rw [← Bool.not_eq_true]; exact fun hh => h2 (Or.inr ⟨j, hj, hh⟩)
    rw [hgate (j.val + 1) j (Nat.lt_succ_self _) g1 g2] at hv
    exact Bool.noConfusion hv

private lemma eval_union_mis_true {n : ℕ} {G : SimpleGraph (Fin n)} {C : AndCountCircuit n}
    (hfit : Fits G C) {I J : Finset (Fin n)} (hI : IsMIS G I) (hJ : IsMIS G J) (hne : I ≠ J) :
    C.eval (I ∪ J) = true := by
  obtain ⟨v, hvJ, hvI⟩ := mis_apart hI hJ hne
  exact eval_mono C (Finset.insert_subset (Finset.mem_union_right _ hvJ) Finset.subset_union_left)
    ((hfit I hI).2 v hvI)

private lemma outVars_empty {n : ℕ} {G : SimpleGraph (Fin n)} {C : AndCountCircuit n}
    (hfit : Fits G C) : C.outVars = ∅ := by
  ext v
  simp only [Finset.notMem_empty, iff_false]
  intro hv
  obtain ⟨I, hvI, hmis⟩ := exists_mis_mem G v
  have h1 : C.eval I = true := (eval_iff C I).mpr (Or.inl ⟨v, hv, hvI⟩)
  rw [(hfit I hmis).1] at h1
  exact Bool.noConfusion h1

-- Strip singletons so no gate fires on any singleton {v}, hence leftVars i and rightVars i are disjoint.
private def singSet {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) : Finset (Fin n) :=
  Finset.univ.filter (fun v => C.gateVal {v} i = true)

private def stripCircuit {n : ℕ} (C : AndCountCircuit n) : AndCountCircuit n where
  size := C.size
  leftVars i := (C.leftVars i ∪ ((C.leftGates i).filter (fun j => j < i)).biUnion (singSet C)) \ singSet C i
  leftGates := C.leftGates
  rightVars i := (C.rightVars i ∪ ((C.rightGates i).filter (fun j => j < i)).biUnion (singSet C)) \ singSet C i
  rightGates := C.rightGates
  outVars := C.outVars ∪ C.outGates.biUnion (singSet C)
  outGates := C.outGates

private lemma strip_size {n : ℕ} (C : AndCountCircuit n) : (stripCircuit C).size = C.size := rfl

private lemma strip_wf {n : ℕ} {C : AndCountCircuit n} (hC : C.WellFormed) :
    (stripCircuit C).WellFormed := hC

private lemma strip_sing_false {n : ℕ} (C : AndCountCircuit n) (v : Fin n) :
    ∀ (m : ℕ) (i : Fin C.size), i.val < m → (stripCircuit C).gateVal {v} i = false := by
  intro m
  induction m with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi
    rw [Bool.eq_false_iff]
    intro htrue
    rw [gateVal_rec (stripCircuit C) {v} i, Bool.and_eq_true] at htrue
    unfold sideTrue at htrue
    simp only [decide_eq_true_eq] at htrue
    have hLv : v ∈ (stripCircuit C).leftVars i := by
      rcases htrue.1 with ⟨w, hw, hwv⟩ | ⟨j, _, hji, hjv⟩
      · rwa [Finset.mem_singleton.mp hwv] at hw
      · rw [ih j (by have : j.val < i.val := hji; omega)] at hjv; exact Bool.noConfusion hjv
    have hRv : v ∈ (stripCircuit C).rightVars i := by
      rcases htrue.2 with ⟨w, hw, hwv⟩ | ⟨j, _, hji, hjv⟩
      · rwa [Finset.mem_singleton.mp hwv] at hw
      · rw [ih j (by have : j.val < i.val := hji; omega)] at hjv; exact Bool.noConfusion hjv
    simp only [stripCircuit, Finset.mem_sdiff, Finset.mem_union, Finset.mem_biUnion,
      Finset.mem_filter, singSet, Finset.mem_univ, true_and] at hLv hRv
    have hCv : C.gateVal {v} i = true := by
      rw [gateVal_rec C {v} i, Bool.and_eq_true, sideTrue_iff, sideTrue_iff]
      constructor
      · rcases hLv.1 with hv | ⟨j, ⟨hjF, hji⟩, hjv⟩
        · exact Or.inl ⟨v, hv, Finset.mem_singleton_self v⟩
        · exact Or.inr ⟨j, hjF, hji, hjv⟩
      · rcases hRv.1 with hv | ⟨j, ⟨hjF, hji⟩, hjv⟩
        · exact Or.inl ⟨v, hv, Finset.mem_singleton_self v⟩
        · exact Or.inr ⟨j, hjF, hji, hjv⟩
    exact hLv.2 hCv

private lemma strip_disjoint {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) :
    Disjoint ((stripCircuit C).leftVars i) ((stripCircuit C).rightVars i) := by
  rw [Finset.disjoint_left]
  intro v hL hR
  have hf := strip_sing_false C v C.size i i.isLt
  have ht : (stripCircuit C).gateVal {v} i = true := by
    rw [gateVal_rec (stripCircuit C) {v} i, Bool.and_eq_true]
    unfold sideTrue
    simp only [decide_eq_true_eq]
    exact ⟨Or.inl ⟨v, hL, Finset.mem_singleton_self v⟩, Or.inl ⟨v, hR, Finset.mem_singleton_self v⟩⟩
  rw [hf] at ht
  exact Bool.noConfusion ht

private lemma strip_gateVal_iff {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (m : ℕ) (i : Fin C.size), i.val < m →
      (C.gateVal U i = true ↔ (∃ v ∈ U, v ∈ singSet C i) ∨ (stripCircuit C).gateVal U i = true) := by
  intro m
  induction m with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi
    constructor
    · intro hC
      by_cases hsing : ∃ v ∈ U, v ∈ singSet C i
      · exact Or.inl hsing
      · right
        rw [gateVal_rec C U i, Bool.and_eq_true, sideTrue_iff, sideTrue_iff] at hC
        rw [gateVal_rec (stripCircuit C) U i, Bool.and_eq_true]
        unfold sideTrue
        simp only [decide_eq_true_eq]
        have liftSide : ∀ (B : Finset (Fin n)) (F : Finset (Fin C.size)),
            ((∃ x ∈ B, x ∈ U) ∨ ∃ j ∈ F, j < i ∧ C.gateVal U j = true) →
            ((∃ x ∈ (B ∪ (F.filter (fun j => j < i)).biUnion (singSet C)) \ singSet C i, x ∈ U) ∨
              ∃ j ∈ F, j < i ∧ (stripCircuit C).gateVal U j = true) := by
          intro B F hs
          rcases hs with ⟨x, hxB, hxU⟩ | ⟨j, hjF, hji, hjval⟩
          · left
            refine ⟨x, Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ hxB, fun hxs => hsing ⟨x, hxU, hxs⟩⟩, hxU⟩
          · rcases (ih j (by have : j.val < i.val := hji; omega)).mp hjval with ⟨x, hxU, hxs⟩ | hjstrip
            · left
              refine ⟨x, Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ (Finset.mem_biUnion.mpr
                ⟨j, Finset.mem_filter.mpr ⟨hjF, hji⟩, hxs⟩), fun hx2 => hsing ⟨x, hxU, hx2⟩⟩, hxU⟩
            · exact Or.inr ⟨j, hjF, hji, hjstrip⟩
        exact ⟨liftSide (C.leftVars i) (C.leftGates i) hC.1,
          liftSide (C.rightVars i) (C.rightGates i) hC.2⟩
    · rintro (⟨v, hvU, hvs⟩ | hS)
      · simp only [singSet, Finset.mem_filter, Finset.mem_univ, true_and] at hvs
        exact gateVal_mono C (Finset.singleton_subset_iff.mpr hvU) i hvs
      · rw [gateVal_rec (stripCircuit C) U i, Bool.and_eq_true] at hS
        unfold sideTrue at hS
        simp only [decide_eq_true_eq] at hS
        rw [gateVal_rec C U i, Bool.and_eq_true, sideTrue_iff, sideTrue_iff]
        have dropSide : ∀ (B : Finset (Fin n)) (F : Finset (Fin C.size)),
            ((∃ x ∈ (B ∪ (F.filter (fun j => j < i)).biUnion (singSet C)) \ singSet C i, x ∈ U) ∨
              ∃ j ∈ F, j < i ∧ (stripCircuit C).gateVal U j = true) →
            ((∃ x ∈ B, x ∈ U) ∨ ∃ j ∈ F, j < i ∧ C.gateVal U j = true) := by
          intro B F hs
          rcases hs with ⟨x, hx, hxU⟩ | ⟨j, hjF, hji, hjstrip⟩
          · have hx1 := (Finset.mem_sdiff.mp hx).1
            rcases Finset.mem_union.mp hx1 with hxB | hxb
            · exact Or.inl ⟨x, hxB, hxU⟩
            · obtain ⟨j, hjf, hxs⟩ := Finset.mem_biUnion.mp hxb
              obtain ⟨hjF, hji⟩ := Finset.mem_filter.mp hjf
              simp only [singSet, Finset.mem_filter, Finset.mem_univ, true_and] at hxs
              exact Or.inr ⟨j, hjF, hji, gateVal_mono C (Finset.singleton_subset_iff.mpr hxU) j hxs⟩
          · exact Or.inr ⟨j, hjF, hji, (ih j (by have : j.val < i.val := hji; omega)).mpr (Or.inr hjstrip)⟩
        exact ⟨dropSide (C.leftVars i) (C.leftGates i) hS.1,
          dropSide (C.rightVars i) (C.rightGates i) hS.2⟩

private lemma strip_eval {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    (stripCircuit C).eval U = C.eval U := by
  apply Bool.eq_iff_iff.mpr
  rw [eval_iff, eval_iff]
  constructor
  · rintro (⟨v, hv, hvU⟩ | ⟨j, hj, hjval⟩)
    · rcases Finset.mem_union.mp hv with hv0 | hvb
      · exact Or.inl ⟨v, hv0, hvU⟩
      · obtain ⟨j, hjO, hvs⟩ := Finset.mem_biUnion.mp hvb
        simp only [singSet, Finset.mem_filter, Finset.mem_univ, true_and] at hvs
        exact Or.inr ⟨j, hjO, gateVal_mono C (Finset.singleton_subset_iff.mpr hvU) j hvs⟩
    · exact Or.inr ⟨j, hj, (strip_gateVal_iff C U C.size j j.isLt).mpr (Or.inr hjval)⟩
  · rintro (⟨v, hv, hvU⟩ | ⟨j, hj, hjval⟩)
    · exact Or.inl ⟨v, Finset.mem_union_left _ hv, hvU⟩
    · rcases (strip_gateVal_iff C U C.size j j.isLt).mp hjval with ⟨v, hvU, hvs⟩ | hjs
      · exact Or.inl ⟨v, Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j, hj, hvs⟩), hvU⟩
      · exact Or.inr ⟨j, hj, hjs⟩

private lemma strip_fits {n : ℕ} {G : SimpleGraph (Fin n)} {C : AndCountCircuit n} (h : Fits G C) :
    Fits G (stripCircuit C) := by
  intro I hI
  rw [strip_eval C I]
  refine ⟨(h I hI).1, fun u hu => ?_⟩
  rw [strip_eval C (insert u I)]
  exact (h I hI).2 u hu

-- Generic code-based upper bound on families of distinct MIS.
private lemma mis_code_bound {n : ℕ} {G : SimpleGraph (Fin n)} {C : AndCountCircuit n}
    (hfit : Fits G C) (S : Finset (Finset (Fin n))) (hS : ∀ I ∈ S, IsMIS G I)
    (F : Finset (Fin C.size)) (fixed : Fin C.size → Bool)
    (hfix : ∀ I ∈ S, ∀ i ∈ F, C.gateVal I i = false → sv C I i (fixed i) = false) :
    S.card ≤ 2 ^ (Finset.univ \ F).card := by
  classical
  let codeFn : {I // I ∈ S} → ({i : Fin C.size // i ∈ Finset.univ \ F} → Bool) :=
    fun I i => sv C I.1 i.1 false
  have hinj : Function.Injective codeFn := by
    intro ⟨I, hI⟩ ⟨J, hJ⟩ heq
    apply Subtype.ext
    by_contra hne
    let f : Fin C.size → Bool := fun i => if i ∈ F then fixed i else sv C I i false
    have hfI : ∀ i : Fin C.size, C.gateVal I i = false → sv C I i (f i) = false := by
      intro i hi
      by_cases hiF : i ∈ F
      · simp only [f, ite_eq_left hiF]
        exact hfix I hI i hiF hi
      · simp only [f, ite_eq_right hiF]
        cases hb : sv C I i false with
        | false => exact hb
        | true =>
          rw [gate_false_iff] at hi
          rcases hi with h0 | h1
          · rw [hb] at h0; exact Bool.noConfusion h0
          · exact h1
    have hfJ : ∀ i : Fin C.size, C.gateVal J i = false → sv C J i (f i) = false := by
      intro i hi
      by_cases hiF : i ∈ F
      · simp only [f, ite_eq_left hiF]
        exact hfix J hJ i hiF hi
      · simp only [f, ite_eq_right hiF]
        have hiNF : i ∈ Finset.univ \ F := Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hiF⟩
        have hEq := congrFun heq ⟨i, hiNF⟩
        change sv C I i false = sv C J i false at hEq
        rw [hEq]
        cases hb : sv C J i false with
        | false => exact hb
        | true =>
          rw [gate_false_iff] at hi
          rcases hi with h0 | h1
          · rw [hb] at h0; exact Bool.noConfusion h0
          · exact h1
    have h0 := merge_eval_gen C I J f hfI hfJ (hfit I (hS I hI)).1 (hfit J (hS J hJ)).1
    have h1 := eval_union_mis_true hfit (hS I hI) (hS J hJ) hne
    rw [h0] at h1
    exact Bool.noConfusion h1
  have hcard := Fintype.card_le_of_injective codeFn hinj
  simp only [Fintype.card_coe, Fintype.card_fun, Fintype.card_bool] at hcard
  exact hcard

private lemma familyBound {n : ℕ} {G : SimpleGraph (Fin n)} {C : AndCountCircuit n}
    (hfit : Fits G C) (S : Finset (Finset (Fin n))) (hS : ∀ I ∈ S, IsMIS G I) :
    S.card ≤ 2 ^ C.size := by
  have h := mis_code_bound hfit S hS ∅ (fun _ => false) (by simp)
  simpa using h

-- If v appears in gate i (left or right), then on every MIS I containing v with gateVal I i = false,
-- sv C I i (!side) = false.
private lemma hit_side_fix {n : ℕ} (C : AndCountCircuit n) {v : Fin n} {I : Finset (Fin n)}
    (hvI : v ∈ I) (i : Fin C.size) (s : Bool) (hv : v ∈ varsOf C i s)
    (hg : C.gateVal I i = false) : sv C I i (!s) = false := by
  have hhit : sv C I i s = true := sv_hit_mem C hvI i s hv
  rw [gate_false_iff] at hg
  cases s with
  | false =>
    rcases hg with h0 | h1
    · rw [hhit] at h0; exact Bool.noConfusion h0
    · exact h1
  | true =>
    rcases hg with h0 | h1
    · exact h0
    · rw [hhit] at h1; exact Bool.noConfusion h1

private def usedGates {n : ℕ} (C : AndCountCircuit n) (v : Fin n) : Finset (Fin C.size) :=
  Finset.univ.filter (fun i : Fin C.size => v ∈ C.leftVars i ∨ v ∈ C.rightVars i)

private lemma vertex_mis_bound {n : ℕ} {G : SimpleGraph (Fin n)} {C : AndCountCircuit n}
    (hfit : Fits G C) (v : Fin n) (S : Finset (Finset (Fin n)))
    (hS : ∀ I ∈ S, IsMIS G I ∧ v ∈ I) :
    S.card ≤ 2 ^ (C.size - (usedGates C v).card) := by
  classical
  let F := usedGates C v
  let fixed : Fin C.size → Bool := fun i => if v ∈ C.leftVars i then true else false
  have hfix : ∀ I ∈ S, ∀ i ∈ F, C.gateVal I i = false → sv C I i (fixed i) = false := by
    intro I hI i hiF hg
    have hvI := (hS I hI).2
    have hmem : v ∈ C.leftVars i ∨ v ∈ C.rightVars i := (Finset.mem_filter.mp hiF).2
    by_cases hL : v ∈ C.leftVars i
    · simp only [fixed, ite_eq_left hL]
      exact hit_side_fix C hvI i false hL hg
    · simp only [fixed, ite_eq_right hL]
      have hR : v ∈ C.rightVars i := hmem.resolve_left hL
      exact hit_side_fix C hvI i true hR hg
  have hb := mis_code_bound hfit S (fun I hI => (hS I hI).1) F fixed hfix
  have hcard : (Finset.univ \ F).card = C.size - F.card := by
    rw [Finset.card_sdiff]; simp
  rw [hcard] at hb
  exact hb

-- If v is absent from C.outVars and from all gates' leftVars/rightVars, then inserting v does not change eval.
private lemma eval_insert_unused {n : ℕ} (C : AndCountCircuit n) (v : Fin n)
    (hov : v ∉ C.outVars) (hg : usedGates C v = ∅) (U : Finset (Fin n)) :
    C.eval (insert v U) = C.eval U := by
  have hno : ∀ i : Fin C.size, v ∉ C.leftVars i ∧ v ∉ C.rightVars i := by
    intro i
    have hi : i ∉ usedGates C v := by rw [hg]; simp
    simp only [usedGates, Finset.mem_filter, Finset.mem_univ, true_and, not_or] at hi
    exact hi
  have hgate : ∀ d : ℕ, ∀ i : Fin C.size,
      gateValFuel C (insert v U) d i = gateValFuel C U d i := by
    intro d
    induction d with
    | zero => intro _; rfl
    | succ d ih =>
      intro i
      simp only [gateValFuel]
      have hside : ∀ (B : Finset (Fin n)) (F : Finset (Fin C.size)), v ∉ B →
          sideTrue (insert v U) B F i (gateValFuel C (insert v U) d) =
          sideTrue U B F i (gateValFuel C U d) := by
        intro B F hvB
        unfold sideTrue
        refine decide_eq_decide.mpr ?_
        constructor
        · rintro (⟨x, hxB, hxU⟩ | ⟨j, hjF, hji, hjv⟩)
          · rcases Finset.mem_insert.mp hxU with rfl | hxU'
            · exact absurd hxB hvB
            · exact Or.inl ⟨x, hxB, hxU'⟩
          · rw [ih j] at hjv; exact Or.inr ⟨j, hjF, hji, hjv⟩
        · rintro (⟨x, hxB, hxU⟩ | ⟨j, hjF, hji, hjv⟩)
          · exact Or.inl ⟨x, hxB, Finset.mem_insert_of_mem hxU⟩
          · rw [← ih j] at hjv; exact Or.inr ⟨j, hjF, hji, hjv⟩
      rw [hside _ _ (hno i).1, hside _ _ (hno i).2]
  apply Bool.eq_iff_iff.mpr
  rw [eval_iff, eval_iff]
  constructor
  · rintro (⟨x, hxO, hxU⟩ | ⟨j, hjO, hjv⟩)
    · rcases Finset.mem_insert.mp hxU with rfl | hxU'
      · exact absurd hxO hov
      · exact Or.inl ⟨x, hxO, hxU'⟩
    · exact Or.inr ⟨j, hjO, by unfold gateVal at hjv ⊢; rwa [hgate] at hjv⟩
  · rintro (⟨x, hxO, hxU⟩ | ⟨j, hjO, hjv⟩)
    · exact Or.inl ⟨x, hxO, Finset.mem_insert_of_mem hxU⟩
    · exact Or.inr ⟨j, hjO, by unfold gateVal at hjv ⊢; rwa [hgate]⟩

private lemma usedGates_nonempty_of_not_isolated {n : ℕ} {G : SimpleGraph (Fin n)}
    {C : AndCountCircuit n} (hfit : Fits G C) (v : Fin n)
    (hni : ∃ I : Finset (Fin n), IsMIS G I ∧ v ∉ I) :
    1 ≤ (usedGates C v).card := by
  by_contra h0
  have hemp : usedGates C v = ∅ := Finset.card_eq_zero.mp (by omega)
  obtain ⟨I, hI, hvI⟩ := hni
  have hov : v ∉ C.outVars := by rw [outVars_empty hfit]; simp
  have heq := eval_insert_unused C v hov hemp I
  rw [(hfit I hI).1, (hfit I hI).2 v hvI] at heq
  exact Bool.noConfusion heq

-- If v appears ONLY on side s of gate g (and nowhere else, not on !s of g, not in outVars),
-- and C.eval I = false while C.eval (insert v I) = true, then sv C I g s = false AND sv C I g (!s) = true!
private lemma unique_read_trigger {n : ℕ} (C : AndCountCircuit n) (v : Fin n)
    (g : Fin C.size) (s : Bool) (hov : v ∉ C.outVars)
    (honly : ∀ i : Fin C.size, ∀ t : Bool, v ∈ varsOf C i t → i = g ∧ t = s)
    (I : Finset (Fin n)) (h0 : C.eval I = false) (h1 : C.eval (insert v I) = true) :
    sv C I g s = false ∧ sv C I g (!s) = true := by
  have hsame : ∀ (m : ℕ) (i : Fin C.size), i.val < m →
      (sv C I g s = true ∨ sv C I g (!s) = false) →
      C.gateVal (insert v I) i = C.gateVal I i := by
    intro m
    induction m with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
    | succ m ih =>
      intro i hi hcond
      have hside_eq : ∀ t : Bool, (i ≠ g ∨ t ≠ s) →
          sv C (insert v I) i t = sv C I i t := by
        intro t hne
        have hvnt : v ∉ varsOf C i t := by
          intro hmem
          have ⟨h1, h2⟩ := honly i t hmem
          rcases hne with h | h
          · exact h h1
          · exact h h2
        unfold sv
        refine decide_eq_decide.mpr ?_
        constructor
        · rintro (⟨x, hxB, hxU⟩ | ⟨j, hjF, hji, hjv⟩)
          · rcases Finset.mem_insert.mp hxU with rfl | hxU'
            · exact absurd hxB hvnt
            · exact Or.inl ⟨x, hxB, hxU'⟩
          · rw [ih j (by have : j.val < i.val := hji; omega) hcond] at hjv
            exact Or.inr ⟨j, hjF, hji, hjv⟩
        · rintro (⟨x, hxB, hxU⟩ | ⟨j, hjF, hji, hjv⟩)
          · exact Or.inl ⟨x, hxB, Finset.mem_insert_of_mem hxU⟩
          · rw [← ih j (by have : j.val < i.val := hji; omega) hcond] at hjv
            exact Or.inr ⟨j, hjF, hji, hjv⟩
      by_cases hig : i = g
      · subst i
        rw [gateVal_rec C (insert v I) g, gateVal_rec C I g]
        change (sv C (insert v I) g false && sv C (insert v I) g true) =
               (sv C I g false && sv C I g true)
        have hother : sv C (insert v I) g (!s) = sv C I g (!s) :=
          hside_eq (!s) (Or.inr (by cases s <;> decide))
        cases s with
        | false =>
          change sv C (insert v I) g true = sv C I g true at hother
          rw [hother]
          rcases hcond with hst | hsf
          · have hst' : sv C (insert v I) g false = true :=
              sideTrue_mono I (insert v I) _ _ g _ _ (Finset.subset_insert v I)
                (fun j _ => gateVal_mono C (Finset.subset_insert v I) j) hst
            rw [hst, hst']
          · change sv C I g true = false at hsf
            rw [hsf]; simp
        | true =>
          change sv C (insert v I) g false = sv C I g false at hother
          rw [hother]
          rcases hcond with hst | hsf
          · have hst' : sv C (insert v I) g true = true :=
              sideTrue_mono I (insert v I) _ _ g _ _ (Finset.subset_insert v I)
                (fun j _ => gateVal_mono C (Finset.subset_insert v I) j) hst
            rw [hst, hst']
          · change sv C I g false = false at hsf
            rw [hsf]; simp
      · rw [gateVal_rec C (insert v I) i, gateVal_rec C I i]
        change (sv C (insert v I) i false && sv C (insert v I) i true) =
               (sv C I i false && sv C I i true)
        rw [hside_eq false (Or.inl hig), hside_eq true (Or.inl hig)]
  by_contra hbad
  have hcond : sv C I g s = true ∨ sv C I g (!s) = false := by
    cases h1s : sv C I g s <;> cases h2s : sv C I g (!s)
    · exact Or.inr rfl
    · exact absurd ⟨h1s, h2s⟩ hbad
    · exact Or.inl rfl
    · exact Or.inl rfl
  have heq : C.eval (insert v I) = C.eval I := by
    apply Bool.eq_iff_iff.mpr
    rw [eval_iff, eval_iff]
    constructor
    · rintro (⟨x, hxO, hxU⟩ | ⟨j, hjO, hjv⟩)
      · rcases Finset.mem_insert.mp hxU with rfl | hxU'
        · exact absurd hxO hov
        · exact Or.inl ⟨x, hxO, hxU'⟩
      · rw [hsame C.size j j.isLt hcond] at hjv
        exact Or.inr ⟨j, hjO, hjv⟩
    · rintro (⟨x, hxO, hxU⟩ | ⟨j, hjO, hjv⟩)
      · exact Or.inl ⟨x, hxO, Finset.mem_insert_of_mem hxU⟩
      · rw [← hsame C.size j j.isLt hcond] at hjv
        exact Or.inr ⟨j, hjO, hjv⟩
  rw [h0, h1] at heq
  exact Bool.noConfusion heq

-- Kill lemma 1: non-isolated vertex v in > 2^(C.size - 1) MIS.
private lemma proj_vertex_kill {n : ℕ} {G : SimpleGraph (Fin n)} {C : AndCountCircuit n}
    (hfit : Fits G C) (v : Fin n) (hni : ∃ I, IsMIS G I ∧ v ∉ I)
    (S : Finset (Finset (Fin n))) (hS : ∀ I ∈ S, IsMIS G I ∧ v ∈ I)
    (hbig : 2 ^ (C.size - 1) < S.card) : False := by
  have hpos := usedGates_nonempty_of_not_isolated hfit v hni
  have hb := vertex_mis_bound hfit v S hS
  have hle : C.size - (usedGates C v).card ≤ C.size - 1 := by omega
  have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) hle
  omega

-- Kill lemma 2: two adjacent vertices a, b each in >= 3 MIS, plus an MIS I0 disjoint from {a, b} => C.size >= 4!
private lemma two_deg3_kill {n : ℕ} {G : SimpleGraph (Fin n)} {C : AndCountCircuit n}
    (hfit : Fits G C) (a b : Fin n) (hab : G.Adj a b)
    (I0 : Finset (Fin n)) (hI0 : IsMIS G I0) (ha0 : a ∉ I0) (hb0 : b ∉ I0)
    (Sa Sb : Finset (Finset (Fin n)))
    (hSa : ∀ I ∈ Sa, IsMIS G I ∧ a ∈ I) (hSb : ∀ I ∈ Sb, IsMIS G I ∧ b ∈ I)
    (hca : 3 ≤ Sa.card) (hcb : 3 ≤ Sb.card) : 4 ≤ C.size := by
  classical
  by_contra hlt
  have hsle : C.size ≤ 3 := by omega
  let D := stripCircuit C
  have hDfit : Fits G D := strip_fits hfit
  have hDsz : D.size ≤ 3 := hsle
  have hDsz_pos_a := usedGates_nonempty_of_not_isolated hDfit a ⟨I0, hI0, ha0⟩
  have hDsz_pos_b := usedGates_nonempty_of_not_isolated hDfit b ⟨I0, hI0, hb0⟩
  have hba := vertex_mis_bound hDfit a Sa hSa
  have hbb := vertex_mis_bound hDfit b Sb hSb
  have hua_le : (usedGates D a).card ≤ 1 := by
    by_contra hge
    have : D.size - (usedGates D a).card ≤ 1 := by omega
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) this
    omega
  have hub_le : (usedGates D b).card ≤ 1 := by
    by_contra hge
    have : D.size - (usedGates D b).card ≤ 1 := by omega
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) this
    omega
  have hua1 : (usedGates D a).card = 1 := by omega
  have hub1 : (usedGates D b).card = 1 := by omega
  obtain ⟨ga, hga_eq⟩ := Finset.card_eq_one.mp hua1
  obtain ⟨gb, hgb_eq⟩ := Finset.card_eq_one.mp hub1
  have hga_mem : a ∈ D.leftVars ga ∨ a ∈ D.rightVars ga := by
    have : ga ∈ usedGates D a := by rw [hga_eq]; simp
    exact (Finset.mem_filter.mp this).2
  have hgb_mem : b ∈ D.leftVars gb ∨ b ∈ D.rightVars gb := by
    have : gb ∈ usedGates D b := by rw [hgb_eq]; simp
    exact (Finset.mem_filter.mp this).2
  obtain ⟨sa, hsa⟩ : ∃ s : Bool, a ∈ varsOf D ga s := by
    rcases hga_mem with h | h
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩
  obtain ⟨sb, hsb⟩ : ∃ s : Bool, b ∈ varsOf D gb s := by
    rcases hgb_mem with h | h
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩
  have honly_a : ∀ i : Fin D.size, ∀ t : Bool, a ∈ varsOf D i t → i = ga ∧ t = sa := by
    intro i t ht
    have hi : i ∈ usedGates D a := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩
      cases t with
      | false => exact Or.inl ht
      | true => exact Or.inr ht
    rw [hga_eq, Finset.mem_singleton] at hi
    subst i
    refine ⟨rfl, ?_⟩
    by_contra hne
    have hdisj := strip_disjoint C ga
    cases sa <;> cases t
    · exact hne rfl
    · exact Finset.disjoint_left.mp hdisj hsa ht
    · exact Finset.disjoint_left.mp hdisj ht hsa
    · exact hne rfl
  have honly_b : ∀ i : Fin D.size, ∀ t : Bool, b ∈ varsOf D i t → i = gb ∧ t = sb := by
    intro i t ht
    have hi : i ∈ usedGates D b := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩
      cases t with
      | false => exact Or.inl ht
      | true => exact Or.inr ht
    rw [hgb_eq, Finset.mem_singleton] at hi
    subst i
    refine ⟨rfl, ?_⟩
    by_contra hne
    have hdisj := strip_disjoint C gb
    cases sb <;> cases t
    · exact hne rfl
    · exact Finset.disjoint_left.mp hdisj hsb ht
    · exact Finset.disjoint_left.mp hdisj ht hsb
    · exact hne rfl
  have hov_a : a ∉ D.outVars := by rw [outVars_empty hDfit]; simp
  have hov_b : b ∉ D.outVars := by rw [outVars_empty hDfit]; simp
  by_cases hgab : ga = gb
  · subst gb
    by_cases hsab : sa = sb
    · subst sb
      have hdisjS : Disjoint Sa Sb := by
        rw [Finset.disjoint_left]
        intro I hIa hIb
        exact (hSa I hIa).1.1 a (hSa I hIa).2 b (hSb I hIb).2 hab
      have hUcard : 6 ≤ (Sa ∪ Sb).card := by
        rw [Finset.card_union_of_disjoint hdisjS]; omega
      have hUbound := mis_code_bound hDfit (Sa ∪ Sb)
        (fun I hI => by rcases Finset.mem_union.mp hI with h | h; exact (hSa I h).1; exact (hSb I h).1)
        {ga} (fun _ => !sa) (by
          intro I hI i hi hg
          rw [Finset.mem_singleton.mp hi] at hg ⊢
          rcases Finset.mem_union.mp hI with hIa | hIb
          · exact hit_side_fix D (hSa I hIa).2 ga sa hsa hg
          · exact hit_side_fix D (hSb I hIb).2 ga sa hsb hg)
      have hrem : (Finset.univ \ ({ga} : Finset (Fin D.size))).card ≤ 2 := by
        rw [Finset.card_sdiff]; simp; omega
      have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hrem
      omega
    · have ht1 := unique_read_trigger D a ga sa hov_a honly_a I0 (hDfit I0 hI0).1 ((hDfit I0 hI0).2 a ha0)
      have ht2 := unique_read_trigger D b ga sb hov_b honly_b I0 (hDfit I0 hI0).1 ((hDfit I0 hI0).2 b hb0)
      have hsb_eq : sb = !sa := by cases sa <;> cases sb <;> simp_all
      rw [hsb_eq] at ht2
      rw [ht1.2] at ht2
      exact Bool.noConfusion ht2.1
  · -- ga != gb: on every I in Sb, a not in I, so adding a triggers ga => sv D I ga sa = false;
    -- AND b in I fixes gb to !sb!
    have hSb_bound := mis_code_bound hDfit Sb (fun I hI => (hSb I hI).1)
      {ga, gb} (fun i => if i = ga then sa else !sb) (by
        intro I hI i hi hg
        rcases Finset.mem_insert.mp hi with hi_eq | hgb'
        · rw [hi_eq]
          simp only [ite_true]
          have haI : a ∉ I := fun haIn => (hSb I hI).1.1 a haIn b (hSb I hI).2 hab
          exact (unique_read_trigger D a ga sa hov_a honly_a I
            (hDfit I (hSb I hI).1).1 ((hDfit I (hSb I hI).1).2 a haI)).1
        · rw [Finset.mem_singleton.mp hgb'] at hg ⊢
          have hne : gb ≠ ga := Ne.symm hgab
          simp only [ite_eq_right hne]
          exact hit_side_fix D (hSb I hI).2 gb sb hsb hg)
    have hcard2 : ({ga, gb} : Finset (Fin D.size)).card = 2 := Finset.card_pair hgab
    have hrem : (Finset.univ \ ({ga, gb} : Finset (Fin D.size))).card ≤ 1 := by
      rw [Finset.card_sdiff]; simp [hcard2]; omega
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hrem
    omega

-- Kill lemma 3: co-sun kill at C.size = 2!
private lemma cosun_kill {n : ℕ} {G : SimpleGraph (Fin n)} {C : AndCountCircuit n}
    (hC : C.WellFormed) (hfit : Fits G C) (hsz : C.size = 2)
    (I0 I1 I2 I3 : Finset (Fin n))
    (h0 : IsMIS G I0) (h1 : IsMIS G I1) (h2 : IsMIS G I2) (h3 : IsMIS G I3)
    (h01 : I0 ≠ I1) (h02 : I0 ≠ I2) (h03 : I0 ≠ I3) (h12 : I1 ≠ I2) (h13 : I1 ≠ I3) (h23 : I2 ≠ I3)
    (a b c : Fin n)
    (ha : a ∈ I0 ∧ a ∈ I3 ∧ a ∉ I1)
    (hb : b ∈ I1 ∧ b ∈ I3 ∧ b ∉ I2)
    (hc : c ∈ I2 ∧ c ∈ I3 ∧ c ∉ I0) : False := by
  classical
  let D := stripCircuit C
  have hDwf : D.WellFormed := strip_wf hC
  have hDfit : Fits G D := strip_fits hfit
  have hDsz : D.size = 2 := hsz
  have getGate : ∀ (v : Fin n) (Iv Jv : Finset (Fin n)),
      IsMIS G Iv → IsMIS G Jv → Iv ≠ Jv → v ∈ Iv → v ∈ I3 → Iv ≠ I3 → v ∉ Jv →
      ∃ (g : Fin D.size) (s : Bool), v ∈ varsOf D g s := by
    intro v Iv Jv hIv hJv _ hvIv hvI3 hIv3 hvJv
    have hpos := usedGates_nonempty_of_not_isolated hDfit v ⟨Jv, hJv, hvJv⟩
    obtain ⟨g, hg⟩ := Finset.card_pos.mp (by omega : 0 < (usedGates D v).card)
    have hmem := (Finset.mem_filter.mp hg).2
    rcases hmem with h | h
    · exact ⟨g, false, h⟩
    · exact ⟨g, true, h⟩
  obtain ⟨ga, sa, hsa⟩ := getGate a I0 I1 h0 h1 h01 ha.1 ha.2.1 h03 ha.2.2
  obtain ⟨gb, sb, hsb⟩ := getGate b I1 I2 h1 h2 h12 hb.1 hb.2.1 h13 hb.2.2
  obtain ⟨gc, sc, hsc⟩ := getGate c I2 I0 h2 h0 h02.symm hc.1 hc.2.1 h23 hc.2.2
  -- By pigeonhole among 3 elements ga, gb, gc in Fin D.size (card = 2), two are equal!
  have hpig : (ga = gb) ∨ (ga = gc) ∨ (gb = gc) := by
    have : ga.val < 2 ∧ gb.val < 2 ∧ gc.val < 2 := ⟨hDsz ▸ ga.isLt, hDsz ▸ gb.isLt, hDsz ▸ gc.isLt⟩
    by_cases h1 : ga.val = gb.val
    · exact Or.inl (Fin.ext h1)
    · by_cases h2 : ga.val = gc.val
      · exact Or.inr (Or.inl (Fin.ext h2))
      · exact Or.inr (Or.inr (Fin.ext (by omega)))
  have kill_pair : ∀ (g : Fin D.size) (u v : Fin n) (su sv_ : Bool) (Iu Iv Iw : Finset (Fin n)),
      IsMIS G Iu → IsMIS G Iv → IsMIS G Iw →
      Iu ≠ Iv → Iu ≠ I3 → Iv ≠ I3 → Iu ≠ Iw → Iv ≠ Iw → Iw ≠ I3 →
      u ∈ Iu → u ∈ I3 → v ∈ Iv → v ∈ I3 →
      u ∈ varsOf D g su → v ∈ varsOf D g sv_ → False := by
    intro g u v su sv_ Iu Iv Iw hIu hIv hIw huv hu3 hv3 huw hvw hw3 huu hu3m hvv hv3m hus hvs
    by_cases hsame : su = sv_
    · subst sv_
      let S : Finset (Finset (Fin n)) := {Iu, Iv, I3}
      have hScard : S.card = 3 := by
        simp [S, Finset.card_insert_of_notMem, huv, hu3, hv3]
      have hb := mis_code_bound hDfit S (by
        intro I hI
        simp only [S, Finset.mem_insert, Finset.mem_singleton] at hI
        rcases hI with rfl | rfl | rfl <;> assumption)
        {g} (fun _ => !su) (by
          intro I hI i hi hg
          rw [Finset.mem_singleton.mp hi] at hg ⊢
          simp only [S, Finset.mem_insert, Finset.mem_singleton] at hI
          rcases hI with rfl | rfl | rfl
          · exact hit_side_fix D huu g su hus hg
          · exact hit_side_fix D hvv g su hvs hg
          · exact hit_side_fix D hu3m g su hus hg)
      have hrem : (Finset.univ \ ({g} : Finset (Fin D.size))).card = 1 := by
        rw [Finset.card_sdiff]; simp [hDsz]
      rw [hScard, hrem] at hb
      omega
    · -- Opposite sides of g => gateVal D I3 g = true!
      have hg3 : D.gateVal I3 g = true := by
        rw [gateVal_rec D I3 g, Bool.and_eq_true]
        change sv D I3 g false = true ∧ sv D I3 g true = true
        cases su <;> cases sv_
        · exact absurd rfl hsame
        · exact ⟨sv_hit_mem D hu3m g false hus, sv_hit_mem D hv3m g true hvs⟩
        · exact ⟨sv_hit_mem D hv3m g false hvs, sv_hit_mem D hu3m g true hus⟩
        · exact absurd rfl hsame
      have hg_nout : g ∉ D.outGates := by
        intro hmem
        have htr : D.eval I3 = true := (eval_iff D I3).mpr (Or.inr ⟨g, hmem, hg3⟩)
        rw [(hDfit I3 h3).1] at htr
        exact Bool.noConfusion htr
      -- The other gate j != g must be the ONLY output gate!
      let j : Fin D.size := ⟨1 - g.val, by have := g.isLt; omega⟩
      have hgj : g ≠ j := by intro heq; have := congrArg Fin.val heq; simp [j] at this; omega
      have hall : ∀ k : Fin D.size, k = g ∨ k = j := by
        intro k
        have hk := k.isLt; have hg' := g.isLt
        by_cases hkg : k.val = g.val
        · exact Or.inl (Fin.ext hkg)
        · exact Or.inr (Fin.ext (by simp [j]; omega))
      have hj_out : j ∈ D.outGates := by
        have hne : D.eval (Iu ∪ I3) = true := eval_union_mis_true hDfit hIu h3 hu3
        rw [eval_iff, outVars_empty hDfit] at hne
        rcases hne with ⟨_, hmem, _⟩ | ⟨k, hk, _⟩
        · simp at hmem
        · rcases hall k with rfl | rfl
          · exact absurd hk hg_nout
          · exact hk
      have hj3_false : D.gateVal I3 j = false := by
        rw [← Bool.not_eq_true]
        intro ht
        have := (eval_iff D I3).mpr (Or.inr ⟨j, hj_out, ht⟩)
        rw [(hDfit I3 h3).1] at this
        exact Bool.noConfusion this
      -- One side sj of j is false on I3
      obtain ⟨sj, hsj⟩ : ∃ s : Bool, sv D I3 j s = false := by
        rw [gate_false_iff] at hj3_false
        rcases hj3_false with h | h
        · exact ⟨false, h⟩
        · exact ⟨true, h⟩
      -- If g < j and g in gatesOf D j sj, then since gateVal I3 g = true, sv D I3 j sj = true, contradiction!
      have hg_not_in_sj : ∀ k ∈ gatesOf D j sj, k < j → k ≠ g := by
        intro k hk hkj hkg
        rw [hkg] at hk hkj
        have ht : sv D I3 j sj = true := (sideTrue_iff _ _ _ _ _).mpr (Or.inr ⟨g, hk, hkj, hg3⟩)
        rw [hsj] at ht
        exact Bool.noConfusion ht
      -- In fact, NO gate k < j can be in gatesOf D j sj (since only gate != j is g!)
      have hno_gate_sj : ∀ k ∈ gatesOf D j sj, ¬ k < j := by
        intro k hk hkj
        rcases hall k with hkg | hkj'
        · exact hg_not_in_sj k hk hkj hkg
        · rw [hkj'] at hkj; exact lt_irrefl j hkj
      -- So for every I in {Iu, Iv, Iw}, since D.eval (I ∪ I3) = true, gate j must be true on I ∪ I3,
      -- so side sj of j is true on I ∪ I3; since it reads no gates < j and varsOf D j sj is disjoint from I3,
      -- varsOf D j sj must hit I!
      have hhit_I : ∀ I : Finset (Fin n), IsMIS G I → I ≠ I3 → sv D I j sj = true := by
        intro I hI hI3
        have ht : D.eval (I ∪ I3) = true := eval_union_mis_true hDfit hI h3 hI3
        rw [eval_iff, outVars_empty hDfit] at ht
        have hjt : D.gateVal (I ∪ I3) j = true := by
          rcases ht with ⟨_, hm, _⟩ | ⟨k, hk, hkv⟩
          · simp at hm
          · rcases hall k with hkg | hkj'
            · rw [hkg] at hk; exact absurd hk hg_nout
            · rwa [hkj'] at hkv
        have hsjt : sv D (I ∪ I3) j sj = true := by
          rw [gateVal_rec, Bool.and_eq_true] at hjt
          cases sj with
          | false => exact hjt.1
          | true => exact hjt.2
        rw [sv, sideTrue_iff] at hsjt
        rcases hsjt with ⟨x, hxV, hxU⟩ | ⟨k, hkF, hkj, _⟩
        · rcases Finset.mem_union.mp hxU with hxI | hx3
          · exact sv_hit_mem D hxI j sj hxV
          · have : sv D I3 j sj = true := sv_hit_mem D hx3 j sj hxV
            rw [hsj] at this; exact Bool.noConfusion this
        · exact absurd hkj (hno_gate_sj k hkF)
      -- Therefore on ALL 3 MIS {Iu, Iv, Iw}, side !sj of j must be false whenever gateVal I j = false!
      let S3 : Finset (Finset (Fin n)) := {Iu, Iv, Iw}
      have hS3card : S3.card = 3 := by
        simp [S3, Finset.card_insert_of_notMem, huv, huw, hvw]
      have hb := mis_code_bound hDfit S3 (by
        intro I hI
        simp only [S3, Finset.mem_insert, Finset.mem_singleton] at hI
        rcases hI with rfl | rfl | rfl <;> assumption)
        {j} (fun _ => !sj) (by
          intro I hI i hi hg
          rw [Finset.mem_singleton.mp hi] at hg ⊢
          have hht : sv D I j sj = true := by
            simp only [S3, Finset.mem_insert, Finset.mem_singleton] at hI
            rcases hI with hEq | hEq | hEq
            · rw [hEq]; exact hhit_I Iu hIu hu3
            · rw [hEq]; exact hhit_I Iv hIv hv3
            · rw [hEq]; exact hhit_I Iw hIw hw3
          rw [gate_false_iff] at hg
          cases sj with
          | false =>
            rcases hg with h0 | h1
            · rw [hht] at h0; exact Bool.noConfusion h0
            · exact h1
          | true =>
            rcases hg with h0 | h1
            · exact h0
            · rw [hht] at h1; exact Bool.noConfusion h1)
      have hrem : (Finset.univ \ ({j} : Finset (Fin D.size))).card = 1 := by
        rw [Finset.card_sdiff]; simp [hDsz]
      rw [hS3card, hrem] at hb
      omega
  rcases hpig with h | h | h
  · rw [← h] at hsb
    exact kill_pair ga a b sa sb I0 I1 I2 h0 h1 h2 h01 h03 h13 h02 h12 h23 ha.1 ha.2.1 hb.1 hb.2.1 hsa hsb
  · rw [← h] at hsc
    exact kill_pair ga a c sa sc I0 I2 I1 h0 h2 h1 h02 h03 h23 h01 h12.symm h13 ha.1 ha.2.1 hc.1 hc.2.1 hsa hsc
  · rw [← h] at hsc
    exact kill_pair gb b c sb sc I1 I2 I0 h1 h2 h0 h12 h13 h23 h01.symm h02.symm h03 hb.1 hb.2.1 hc.1 hc.2.1 hsb hsc

end CircuitCore

section Size0124

private lemma bc_mono {n : ℕ} {G : SimpleGraph (Fin n)} {k k' : ℕ} (hkk : k ≤ k')
    (h : HasBicliqueCover G k) : HasBicliqueCover G k' := by
  obtain ⟨X, Y, hbic, hcov⟩ := h
  refine ⟨fun i => if hi : i.val < k then X ⟨i.val, hi⟩ else ∅,
          fun i => if hi : i.val < k then Y ⟨i.val, hi⟩ else ∅, ?_, ?_⟩
  · intro i a ha b hb
    by_cases hi : i.val < k
    · simp only [dif_pos hi] at ha hb
      exact hbic ⟨i.val, hi⟩ a ha b hb
    · simp only [dif_neg hi] at ha
      exact absurd ha (Finset.notMem_empty a)
  · intro a b hab
    obtain ⟨i, hi⟩ := hcov a b hab
    refine ⟨⟨i.val, by omega⟩, ?_⟩
    simp only [dif_pos i.isLt]
    exact hi

private lemma bc_of_vc {n : ℕ} (G : SimpleGraph (Fin n)) (T : Finset (Fin n))
    (hvc : ∀ a b : Fin n, G.Adj a b → a ∈ T ∨ b ∈ T) :
    HasBicliqueCover G T.card := by
  classical
  let e : Fin T.card ≃ T := (Fintype.equivFinOfCardEq (Fintype.card_coe T)).symm
  refine ⟨fun i => {(e i).1}, fun i => Finset.univ.filter (fun b => G.Adj (e i).1 b), ?_, ?_⟩
  · intro i a ha b hb
    rw [Finset.mem_singleton.mp ha]
    exact (Finset.mem_filter.mp hb).2
  · intro a b hab
    rcases hvc a b hab with haT | hbT
    · refine ⟨e.symm ⟨a, haT⟩, Or.inl ⟨?_, ?_⟩⟩
      · simp only [Equiv.apply_symm_apply, Finset.mem_singleton]
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ b, by simpa using hab⟩
    · refine ⟨e.symm ⟨b, hbT⟩, Or.inr ⟨?_, ?_⟩⟩
      · simp only [Equiv.apply_symm_apply, Finset.mem_singleton]
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, by simpa using (G.adj_comm a b).mp hab⟩

private lemma bc_add_vertex {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) (k : ℕ)
    (hsub : ∃ (X Y : Fin k → Finset (Fin n)),
      (∀ i : Fin k, ∀ a ∈ X i, ∀ b ∈ Y i, G.Adj a b) ∧
      (∀ a b : Fin n, a ≠ v → b ≠ v → G.Adj a b →
        ∃ i : Fin k, (a ∈ X i ∧ b ∈ Y i) ∨ (b ∈ X i ∧ a ∈ Y i))) :
    HasBicliqueCover G (k + 1) := by
  classical
  obtain ⟨X, Y, hbic, hcov⟩ := hsub
  refine ⟨Fin.snoc X {v}, Fin.snoc Y (Finset.univ.filter (fun u => G.Adj v u)), ?_, ?_⟩
  · intro i
    refine Fin.lastCases ?_ ?_ i
    · intro a ha b hb
      simp only [Fin.snoc_last, Finset.mem_singleton, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      rw [ha]; exact hb
    · intro j a ha b hb
      simp only [Fin.snoc_castSucc] at ha hb
      exact hbic j a ha b hb
  · intro a b hab
    by_cases hav : a = v
    · subst hav
      refine ⟨Fin.last k, Or.inl ⟨by simp, by simp [hab]⟩⟩
    · by_cases hbv : b = v
      · subst hbv
        refine ⟨Fin.last k, Or.inr ⟨by simp, by simp [(G.adj_comm a b).mp hab]⟩⟩
      · obtain ⟨j, hj⟩ := hcov a b hav hbv hab
        exact ⟨j.castSucc, by simpa using hj⟩

private lemma size_ge_4_fin6 (G : SimpleGraph (Fin 6)) : HasBicliqueCover G 4 := by
  classical
  by_cases hne : ∃ u v : Fin 6, u ≠ v ∧ ¬ G.Adj u v
  · obtain ⟨u, v, huv, hna⟩ := hne
    let T : Finset (Fin 6) := Finset.univ \ {u, v}
    have hTcard : T.card = 4 := by
      simp [T, Finset.card_sdiff, Finset.card_pair huv]
    have hvc : ∀ a b : Fin 6, G.Adj a b → a ∈ T ∨ b ∈ T := by
      intro a b hab
      by_contra hboth
      push_neg at hboth
      have ha : a = u ∨ a = v := by
        have := hboth.1; simp only [T, Finset.mem_sdiff, Finset.mem_univ, true_and,
          Finset.mem_insert, Finset.mem_singleton, not_not] at this; exact this
      have hb : b = u ∨ b = v := by
        have := hboth.2; simp only [T, Finset.mem_sdiff, Finset.mem_univ, true_and,
          Finset.mem_insert, Finset.mem_singleton, not_not] at this; exact this
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact G.ne_of_adj hab rfl
      · exact hna hab
      · exact hna ((G.adj_comm _ _).mp hab)
      · exact G.ne_of_adj hab rfl
    rw [← hTcard]
    exact bc_of_vc G T hvc
  · push_neg at hne
    apply bc_mono (by omega : 3 ≤ 4)
    refine ⟨![{0, 1, 2}, {0, 3}, {1, 4}], ![{3, 4, 5}, {1, 2, 4, 5}, {2, 5}], ?_, ?_⟩
    · intro i a ha b hb
      apply hne a b
      intro hab; subst hab
      fin_cases i <;> simp at ha hb <;> omega
    · intro a b hab
      have hneab : a ≠ b := G.ne_of_adj hab
      fin_cases a <;> fin_cases b <;> simp_all <;> decide

private lemma size_eq_0 {n : ℕ} {G : SimpleGraph (Fin n)} {C : AndCountCircuit n}
    (hfit : Fits G C) (hsz : C.size = 0) : HasBicliqueCover G 0 := by
  refine ⟨fun i => Fin.elim0 (hsz ▸ i), fun i => Fin.elim0 (hsz ▸ i),
    fun i => Fin.elim0 (hsz ▸ i), ?_⟩
  intro a b hab
  obtain ⟨I, haI, hmis⟩ := exists_mis_mem G a
  have hbI : b ∉ I := fun hb => hmis.1 a haI b hb hab
  have htr := (hfit I hmis).2 b hbI
  rw [eval_iff, outVars_empty hfit] at htr
  rcases htr with ⟨_, hm, _⟩ | ⟨j, _, _⟩
  · simp at hm
  · exact absurd j.isLt (by omega)

private lemma size_eq_1 {n : ℕ} {G : SimpleGraph (Fin n)} {C : AndCountCircuit n}
    (hfit : Fits G C) (hsz : C.size = 1) : HasBicliqueCover G 1 := by
  let g0 : Fin C.size := ⟨0, by omega⟩
  have h1 : ∀ j : Fin C.size, j = g0 := fun j => Fin.ext (by have := j.isLt; omega)
  have hov := outVars_empty hfit
  by_cases h0out : g0 ∈ C.outGates
  · refine ⟨fun _ => C.leftVars g0, fun _ => C.rightVars g0, ?_, ?_⟩
    · intro _ a ha b hb
      by_contra hna
      obtain ⟨I, haI, hbI, hmis⟩ := exists_mis_pair G hna
      have hgt : C.gateVal I g0 = true := by
        rw [gateVal_rec, Bool.and_eq_true, sideTrue_iff, sideTrue_iff]
        exact ⟨Or.inl ⟨a, ha, haI⟩, Or.inl ⟨b, hb, hbI⟩⟩
      have hev : C.eval I = true := (eval_iff C I).mpr (Or.inr ⟨g0, h0out, hgt⟩)
      rw [(hfit I hmis).1] at hev
      exact Bool.noConfusion hev
    · intro a b hab
      have hcov_vert : ∀ u v : Fin n, G.Adj u v → u ∈ C.leftVars g0 ∨ u ∈ C.rightVars g0 := by
        intro u v huv
        obtain ⟨I, hvI, hmis⟩ := exists_mis_mem G v
        have huI : u ∉ I := fun hu => hmis.1 v hvI u hu ((G.adj_comm u v).mp huv)
        have htr := (hfit I hmis).2 u huI
        have hfa := (hfit I hmis).1
        rw [eval_iff, hov] at htr
        have hgt : C.gateVal (insert u I) g0 = true := by
          rcases htr with ⟨_, hm, _⟩ | ⟨j, _, hj⟩
          · simp at hm
          · rwa [h1 j] at hj
        have hgf : C.gateVal I g0 = false := by
          rw [← Bool.not_eq_true]; intro ht
          have := (eval_iff C I).mpr (Or.inr ⟨g0, h0out, ht⟩)
          rw [hfa] at this; exact Bool.noConfusion this
        rw [gateVal_rec, Bool.and_eq_true, sideTrue_iff, sideTrue_iff] at hgt
        rw [gateVal_rec, Bool.and_eq_false_iff] at hgf
        rcases hgf with hL | hR
        · rcases hgt.1 with ⟨x, hxL, hxU⟩ | ⟨j, _, hlt, _⟩
          · rcases Finset.mem_insert.mp hxU with rfl | hxI
            · exact Or.inl hxL
            · have : sideTrue I (C.leftVars g0) (C.leftGates g0) g0 (C.gateVal I) = true :=
                (sideTrue_iff _ _ _ _ _).mpr (Or.inl ⟨x, hxL, hxI⟩)
              rw [hL] at this; exact Bool.noConfusion this
          · exact absurd hlt (by have := h1 j; subst this; exact lt_irrefl g0)
        · rcases hgt.2 with ⟨x, hxR, hxU⟩ | ⟨j, _, hlt, _⟩
          · rcases Finset.mem_insert.mp hxU with rfl | hxI
            · exact Or.inr hxR
            · have : sideTrue I (C.rightVars g0) (C.rightGates g0) g0 (C.gateVal I) = true :=
                (sideTrue_iff _ _ _ _ _).mpr (Or.inl ⟨x, hxR, hxI⟩)
              rw [hR] at this; exact Bool.noConfusion this
          · exact absurd hlt (by have := h1 j; subst this; exact lt_irrefl g0)
      have haLR := hcov_vert a b hab
      have hbLR := hcov_vert b a ((G.adj_comm a b).mp hab)
      have hbic : ∀ x ∈ C.leftVars g0, ∀ y ∈ C.rightVars g0, G.Adj x y := by
        intro x hx y hy
        by_contra hna
        obtain ⟨I, hxI, hyI, hmis⟩ := exists_mis_pair G hna
        have hgt : C.gateVal I g0 = true := by
          rw [gateVal_rec, Bool.and_eq_true, sideTrue_iff, sideTrue_iff]
          exact ⟨Or.inl ⟨x, hx, hxI⟩, Or.inl ⟨y, hy, hyI⟩⟩
        have hev : C.eval I = true := (eval_iff C I).mpr (Or.inr ⟨g0, h0out, hgt⟩)
        rw [(hfit I hmis).1] at hev; exact Bool.noConfusion hev
      rcases haLR with haL | haR <;> rcases hbLR with hbL | hbR
      · exfalso
        obtain ⟨I, haI, hmis⟩ := exists_mis_mem G a
        have hbI : b ∉ I := fun hb => hmis.1 a haI b hb hab
        have hI_R : ∀ y ∈ C.rightVars g0, y ∉ I := by
          intro y hy hyI; exact hmis.1 a haI y hyI (hbic a haL y hy)
        have hb_nR : b ∉ C.rightVars g0 := fun hbR => G.ne_of_adj (hbic b hbL b hbR) rfl
        have htr := (hfit I hmis).2 b hbI
        rw [eval_iff, hov] at htr
        rcases htr with ⟨_, hm, _⟩ | ⟨j, _, hj⟩
        · simp at hm
        · rw [h1 j, gateVal_rec, Bool.and_eq_true, sideTrue_iff, sideTrue_iff] at hj
          rcases hj.2 with ⟨y, hyR, hyU⟩ | ⟨k, _, hlt, _⟩
          · rcases Finset.mem_insert.mp hyU with rfl | hyI
            · exact hb_nR hyR
            · exact hI_R y hyR hyI
          · exact absurd hlt (by have := h1 k; subst this; exact lt_irrefl g0)
      · exact ⟨0, Or.inl ⟨haL, hbR⟩⟩
      · exact ⟨0, Or.inr ⟨hbL, haR⟩⟩
      · exfalso
        obtain ⟨I, haI, hmis⟩ := exists_mis_mem G a
        have hbI : b ∉ I := fun hb => hmis.1 a haI b hb hab
        have hI_L : ∀ x ∈ C.leftVars g0, x ∉ I := by
          intro x hx hxI; exact hmis.1 x hxI a haI (hbic x hx a haR)
        have hb_nL : b ∉ C.leftVars g0 := fun hbL => G.ne_of_adj (hbic b hbL b hbR) rfl
        have htr := (hfit I hmis).2 b hbI
        rw [eval_iff, hov] at htr
        rcases htr with ⟨_, hm, _⟩ | ⟨j, _, hj⟩
        · simp at hm
        · rw [h1 j, gateVal_rec, Bool.and_eq_true, sideTrue_iff, sideTrue_iff] at hj
          rcases hj.1 with ⟨x, hxL, hxU⟩ | ⟨k, _, hlt, _⟩
          · rcases Finset.mem_insert.mp hxU with rfl | hxI
            · exact hb_nL hxL
            · exact hI_L x hxL hxI
          · exact absurd hlt (by have := h1 k; subst this; exact lt_irrefl g0)
  · apply bc_mono (by omega : 0 ≤ 1)
    refine ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i, ?_⟩
    intro a b hab
    obtain ⟨I, haI, hmis⟩ := exists_mis_mem G a
    have hbI : b ∉ I := fun hb => hmis.1 a haI b hb hab
    have htr := (hfit I hmis).2 b hbI
    rw [eval_iff, hov] at htr
    rcases htr with ⟨_, hm, _⟩ | ⟨j, hj, _⟩
    · simp at hm
    · rw [h1 j] at hj; exact absurd hj h0out

-- General theorem: for ANY n, C.size = 2 => HasBicliqueCover G 2!
private lemma mis_le_3_imp_bc_le_2 {n : ℕ} (G : SimpleGraph (Fin n)) (I0 I1 I2 : Finset (Fin n))
    (h0 : IsMIS G I0) (h1 : IsMIS G I1) (h2 : IsMIS G I2)
    (hall : ∀ I : Finset (Fin n), IsMIS G I → I = I0 ∨ I = I1 ∨ I = I2) :
    HasBicliqueCover G 2 := by
  classical
  let S : Fin n → Finset (Fin 3) := fun v =>
    (if v ∈ I0 then {0} else ∅) ∪ (if v ∈ I1 then {1} else ∅) ∪ (if v ∈ I2 then {2} else ∅)
  have hmemS : ∀ (v : Fin n) (k : Fin 3), k ∈ S v ↔
      (k = 0 ∧ v ∈ I0) ∨ (k = 1 ∧ v ∈ I1) ∨ (k = 2 ∧ v ∈ I2) := by
    intro v k
    simp only [S, Finset.mem_union]
    fin_cases k <;> by_cases hv0 : v ∈ I0 <;> by_cases hv1 : v ∈ I1 <;> by_cases hv2 : v ∈ I2 <;> simp [hv0, hv1, hv2]
  have hadj_iff : ∀ u v : Fin n, G.Adj u v ↔ Disjoint (S u) (S v) := by
    intro u v
    constructor
    · intro huv
      rw [Finset.disjoint_left]
      intro k hku hkv
      rw [hmemS] at hku hkv
      fin_cases k
      · rcases hku with ⟨_, hu0⟩ | ⟨h, _⟩ | ⟨h, _⟩
        · rcases hkv with ⟨_, hv0⟩ | ⟨h, _⟩ | ⟨h, _⟩
          · exact h0.1 u hu0 v hv0 huv
          · exact absurd h (by decide)
          · exact absurd h (by decide)
        · exact absurd h (by decide)
        · exact absurd h (by decide)
      · rcases hku with ⟨h, _⟩ | ⟨_, hu1⟩ | ⟨h, _⟩
        · exact absurd h (by decide)
        · rcases hkv with ⟨h, _⟩ | ⟨_, hv1⟩ | ⟨h, _⟩
          · exact absurd h (by decide)
          · exact h1.1 u hu1 v hv1 huv
          · exact absurd h (by decide)
        · exact absurd h (by decide)
      · rcases hku with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, hu2⟩
        · exact absurd h (by decide)
        · exact absurd h (by decide)
        · rcases hkv with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, hv2⟩
          · exact absurd h (by decide)
          · exact absurd h (by decide)
          · exact h2.1 u hu2 v hv2 huv
    · intro hdisj
      by_contra hna
      obtain ⟨I, huI, hvI, hmis⟩ := exists_mis_pair G hna
      rcases hall I hmis with rfl | rfl | rfl
      · exact Finset.disjoint_left.mp hdisj ((hmemS u 0).mpr (Or.inl ⟨rfl, huI⟩)) ((hmemS v 0).mpr (Or.inl ⟨rfl, hvI⟩))
      · exact Finset.disjoint_left.mp hdisj ((hmemS u 1).mpr (Or.inr (Or.inl ⟨rfl, huI⟩))) ((hmemS v 1).mpr (Or.inr (Or.inl ⟨rfl, hvI⟩)))
      · exact Finset.disjoint_left.mp hdisj ((hmemS u 2).mpr (Or.inr (Or.inr ⟨rfl, huI⟩))) ((hmemS v 2).mpr (Or.inr (Or.inr ⟨rfl, hvI⟩)))
  have hS_ne : ∀ v : Fin n, (S v).Nonempty := by
    intro v
    obtain ⟨I, hvI, hmis⟩ := exists_mis_mem G v
    rcases hall I hmis with rfl | rfl | rfl
    · exact ⟨0, (hmemS v 0).mpr (Or.inl ⟨rfl, hvI⟩)⟩
    · exact ⟨1, (hmemS v 1).mpr (Or.inr (Or.inl ⟨rfl, hvI⟩))⟩
    · exact ⟨2, (hmemS v 2).mpr (Or.inr (Or.inr ⟨rfl, hvI⟩))⟩
  -- At least one of the 3 pairs {1,2}, {0,2}, {0,1} is not equal to S v for any v!
  have hmiss : (∀ v : Fin n, S v ≠ {1, 2}) ∨ (∀ v : Fin n, S v ≠ {0, 2}) ∨ (∀ v : Fin n, S v ≠ {0, 1}) := by
    by_contra h
    push_neg at h
    obtain ⟨⟨v0, hv0⟩, ⟨v1, hv1⟩, ⟨v2, hv2⟩⟩ := h
    have hind : ∀ x ∈ ({v0, v1, v2} : Finset (Fin n)), ∀ y ∈ ({v0, v1, v2} : Finset (Fin n)), ¬ G.Adj x y := by
      intro x hx y hy hadj
      have hd := (hadj_iff x y).mp hadj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
      · exact Finset.disjoint_left.mp hd (by rw [hv0]; simp : (1 : Fin 3) ∈ _) (by rw [hv0]; simp)
      · exact Finset.disjoint_left.mp hd (by rw [hv0]; simp : (2 : Fin 3) ∈ _) (by rw [hv1]; simp)
      · exact Finset.disjoint_left.mp hd (by rw [hv0]; simp : (1 : Fin 3) ∈ _) (by rw [hv2]; simp)
      · exact Finset.disjoint_left.mp hd (by rw [hv1]; simp : (2 : Fin 3) ∈ _) (by rw [hv0]; simp)
      · exact Finset.disjoint_left.mp hd (by rw [hv1]; simp : (0 : Fin 3) ∈ _) (by rw [hv1]; simp)
      · exact Finset.disjoint_left.mp hd (by rw [hv1]; simp : (0 : Fin 3) ∈ _) (by rw [hv2]; simp)
      · exact Finset.disjoint_left.mp hd (by rw [hv2]; simp : (1 : Fin 3) ∈ _) (by rw [hv0]; simp)
      · exact Finset.disjoint_left.mp hd (by rw [hv2]; simp : (0 : Fin 3) ∈ _) (by rw [hv1]; simp)
      · exact Finset.disjoint_left.mp hd (by rw [hv2]; simp : (0 : Fin 3) ∈ _) (by rw [hv2]; simp)
    obtain ⟨I, hsub, hmis⟩ := exists_mis_supset G {v0, v1, v2} hind
    have hv0I : v0 ∈ I := hsub (by simp)
    have hv1I : v1 ∈ I := hsub (by simp)
    have hv2I : v2 ∈ I := hsub (by simp)
    rcases hall I hmis with rfl | rfl | rfl
    · have : (0 : Fin 3) ∈ S v0 := (hmemS v0 0).mpr (Or.inl ⟨rfl, hv0I⟩)
      rw [hv0] at this; exact absurd this (by decide)
    · have : (1 : Fin 3) ∈ S v1 := (hmemS v1 1).mpr (Or.inr (Or.inl ⟨rfl, hv1I⟩))
      rw [hv1] at this; exact absurd this (by decide)
    · have : (2 : Fin 3) ∈ S v2 := (hmemS v2 2).mpr (Or.inr (Or.inr ⟨rfl, hv2I⟩))
      rw [hv2] at this; exact absurd this (by decide)
  have mk_cov : ∀ a b : Fin 3, a ≠ b → (∀ v : Fin n, S v ≠ {a, b}) → HasBicliqueCover G 2 := by
    intro a b hab hno
    refine ⟨![Finset.univ.filter (fun v => S v = {a}), Finset.univ.filter (fun v => S v = {b})],
            ![Finset.univ.filter (fun v => a ∉ S v), Finset.univ.filter (fun v => b ∉ S v)], ?_, ?_⟩
    · intro i u hu v hv
      rw [hadj_iff]
      fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
        rw [hu]; exact Finset.disjoint_singleton_left.mpr hv
      · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero, Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
        rw [hu]; exact Finset.disjoint_singleton_left.mpr hv
    · intro u v huv
      have hdisj := (hadj_iff u v).mp huv
      have hu_ne := hS_ne u
      have hv_ne := hS_ne v
      by_cases hua : S u = {a}
      · exact ⟨0, Or.inl ⟨by simp [hua], by simp [Finset.disjoint_singleton_left.mp (hua ▸ hdisj)]⟩⟩
      · by_cases hva : S v = {a}
        · exact ⟨0, Or.inr ⟨by simp [hva], by simp [Finset.disjoint_singleton_right.mp (hva ▸ hdisj)]⟩⟩
        · by_cases hub : S u = {b}
          · exact ⟨1, Or.inl ⟨by simp [hub], by simp [Finset.disjoint_singleton_left.mp (hub ▸ hdisj)]⟩⟩
          · by_cases hvb : S v = {b}
            · exact ⟨1, Or.inr ⟨by simp [hvb], by simp [Finset.disjoint_singleton_right.mp (hvb ▸ hdisj)]⟩⟩
            · -- Since S u and S v are disjoint nonempty subsets of Fin 3, neither is {a}, {b}, or {a, b}: impossible!
              exfalso
              have hfin : ∀ (A B : Finset (Fin 3)) (a b : Fin 3), a ≠ b →
                  A.Nonempty → B.Nonempty → Disjoint A B →
                  A ≠ {a} → B ≠ {a} → A ≠ {b} → B ≠ {b} → A ≠ {a, b} → B ≠ {a, b} → False := by
                decide
              exact hfin (S u) (S v) a b hab hu_ne hv_ne hdisj hua hva hub hvb (hno u) (hno v)
  rcases hmiss with h | h | h
  · exact mk_cov 1 2 (by decide) h
  · exact mk_cov 0 2 (by decide) h
  · exact mk_cov 0 1 (by decide) h

private lemma size_eq_2 {n : ℕ} {G : SimpleGraph (Fin n)} {C : AndCountCircuit n}
    (hC : C.WellFormed) (hfit : Fits G C) (hsz : C.size = 2) : HasBicliqueCover G 2 := by
  classical
  let allMIS : Finset (Finset (Fin n)) := Finset.univ.filter (fun I => IsMIS G I)
  have hle4 : allMIS.card ≤ 4 := by
    have hb := familyBound hfit allMIS (fun I hI => (Finset.mem_filter.mp hI).2)
    rw [hsz] at hb
    exact hb
  by_cases hle3 : allMIS.card ≤ 3
  · have hne0 : allMIS.Nonempty := by
      obtain ⟨I, _, hmis⟩ := exists_mis_supset G ∅ (by simp)
      exact ⟨I, Finset.mem_filter.mpr ⟨Finset.mem_univ I, hmis⟩⟩
    obtain ⟨I0, hI0m⟩ := hne0
    have hI0 : IsMIS G I0 := (Finset.mem_filter.mp hI0m).2
    by_cases h1 : (allMIS.erase I0).Nonempty
    · obtain ⟨I1, hI1m⟩ := h1
      have hI1 : IsMIS G I1 := (Finset.mem_filter.mp (Finset.mem_erase.mp hI1m).2).2
      by_cases h2 : ((allMIS.erase I0).erase I1).Nonempty
      · obtain ⟨I2, hI2m⟩ := h2
        have hI2 : IsMIS G I2 :=
          (Finset.mem_filter.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hI2m).2).2).2
        apply mis_le_3_imp_bc_le_2 G I0 I1 I2 hI0 hI1 hI2
        intro I hI
        by_contra hnot
        push_neg at hnot
        have hIin : I ∈ ((allMIS.erase I0).erase I1).erase I2 := by
          simp only [Finset.mem_erase, allMIS, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hnot.2.2, hnot.2.1, hnot.1, hI⟩
        have hc1 : (allMIS.erase I0).card + 1 = allMIS.card := Finset.card_erase_add_one hI0m
        have hc2 : ((allMIS.erase I0).erase I1).card + 1 = (allMIS.erase I0).card := Finset.card_erase_add_one hI1m
        have hc3 : (((allMIS.erase I0).erase I1).erase I2).card + 1 = ((allMIS.erase I0).erase I1).card :=
          Finset.card_erase_add_one hI2m
        have hpos : 1 ≤ (((allMIS.erase I0).erase I1).erase I2).card := Finset.card_pos.mpr ⟨I, hIin⟩
        omega
      · rw [Finset.not_nonempty_iff_eq_empty] at h2
        apply mis_le_3_imp_bc_le_2 G I0 I1 I1 hI0 hI1 hI1
        intro I hI
        by_contra hnot; push_neg at hnot
        have : I ∈ (allMIS.erase I0).erase I1 := by
          simp only [Finset.mem_erase, allMIS, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hnot.2.1, hnot.1, hI⟩
        rw [h2] at this; exact Finset.notMem_empty I this
    · rw [Finset.not_nonempty_iff_eq_empty] at h1
      apply mis_le_3_imp_bc_le_2 G I0 I0 I0 hI0 hI0 hI0
      intro I hI
      by_contra hnot; push_neg at hnot
      have : I ∈ allMIS.erase I0 := by
        simp only [Finset.mem_erase, allMIS, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hnot.1, hI⟩
      rw [h1] at this; exact Finset.notMem_empty I this
  · -- allMIS.card = 4!
    have hcard4 : allMIS.card = 4 := by omega
    let e : Fin 4 ≃ allMIS := (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, hcard4])).symm
    let M : Fin 4 → Finset (Fin n) := fun k => (e k).1
    have hM_mis : ∀ k : Fin 4, IsMIS G (M k) := fun k => (Finset.mem_filter.mp (e k).2).2
    have hM_inj : Function.Injective M := fun a b hab => e.injective (Subtype.ext hab)
    have hM_all : ∀ I : Finset (Fin n), IsMIS G I → ∃ k : Fin 4, I = M k := by
      intro I hI
      have hmem : I ∈ allMIS := Finset.mem_filter.mpr ⟨Finset.mem_univ I, hI⟩
      exact ⟨e.symm ⟨I, hmem⟩, by simp [M]⟩
    let S : Fin n → Finset (Fin 4) := fun v => Finset.univ.filter (fun k : Fin 4 => v ∈ M k)
    have hmemS : ∀ (v : Fin n) (k : Fin 4), k ∈ S v ↔ v ∈ M k := by
      intro v k; simp [S]
    have hadj_iff : ∀ u v : Fin n, G.Adj u v ↔ Disjoint (S u) (S v) := by
      intro u v
      constructor
      · intro huv
        rw [Finset.disjoint_left]
        intro k hku hkv
        exact (hM_mis k).1 u ((hmemS u k).mp hku) v ((hmemS v k).mp hkv) huv
      · intro hdisj
        by_contra hna
        obtain ⟨I, huI, hvI, hmis⟩ := exists_mis_pair G hna
        obtain ⟨k, rfl⟩ := hM_all I hmis
        exact Finset.disjoint_left.mp hdisj ((hmemS u k).mpr huI) ((hmemS v k).mpr hvI)
    have hS_ne : ∀ v : Fin n, (S v).Nonempty := by
      intro v
      obtain ⟨I, hvI, hmis⟩ := exists_mis_mem G v
      obtain ⟨k, rfl⟩ := hM_all I hmis
      exact ⟨k, (hmemS v k).mpr hvI⟩
    -- No vertex can have (S v).card = 3 (by proj_vertex_kill!)
    have hno3 : ∀ v : Fin n, (S v).card ≠ 3 := by
      intro v h3
      have hnot4 : S v ≠ Finset.univ := by intro h; rw [h] at h3; simp at h3
      obtain ⟨k0, hk0⟩ : ∃ k0 : Fin 4, k0 ∉ S v := by
        by_contra h; push_neg at h; apply hnot4; ext k; simp [h k]
      have hni : ∃ I, IsMIS G I ∧ v ∉ I := ⟨M k0, hM_mis k0, fun hm => hk0 ((hmemS v k0).mpr hm)⟩
      let T := (S v).image M
      have hTcard : T.card = 3 := by
        rw [Finset.card_image_of_injective _ hM_inj, h3]
      have hT : ∀ I ∈ T, IsMIS G I ∧ v ∈ I := by
        intro I hI
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hI
        exact ⟨hM_mis k, (hmemS v k).mp hk⟩
      exact proj_vertex_kill hfit v hni T hT (by rw [hTcard, hsz]; decide)
    -- No triangle of pairs: for any distinct i j k : Fin 4, cannot have vertices with {i,j}, {i,k}, {j,k}
    have hno_tri : ∀ a b c : Fin 4, a ≠ b → a ≠ c → b ≠ c →
        ¬ (∃ u v w : Fin n, S u = {a, b} ∧ S v = {a, c} ∧ S w = {b, c}) := by
      rintro a b c hab hac hbc ⟨u, v, w, hu, hv, hw⟩
      have hind : ∀ x ∈ ({u, v, w} : Finset (Fin n)), ∀ y ∈ ({u, v, w} : Finset (Fin n)), ¬ G.Adj x y := by
        intro x hx y hy hadj
        have hd := (hadj_iff x y).mp hadj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
        rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
        · exact Finset.disjoint_left.mp hd (by rw [hu]; simp : a ∈ _) (by rw [hu]; simp)
        · exact Finset.disjoint_left.mp hd (by rw [hu]; simp : a ∈ _) (by rw [hv]; simp)
        · exact Finset.disjoint_left.mp hd (by rw [hu]; simp : b ∈ _) (by rw [hw]; simp)
        · exact Finset.disjoint_left.mp hd (by rw [hv]; simp : a ∈ _) (by rw [hu]; simp)
        · exact Finset.disjoint_left.mp hd (by rw [hv]; simp : a ∈ _) (by rw [hv]; simp)
        · exact Finset.disjoint_left.mp hd (by rw [hv]; simp : c ∈ _) (by rw [hw]; simp)
        · exact Finset.disjoint_left.mp hd (by rw [hw]; simp : b ∈ _) (by rw [hu]; simp)
        · exact Finset.disjoint_left.mp hd (by rw [hw]; simp : c ∈ _) (by rw [hv]; simp)
        · exact Finset.disjoint_left.mp hd (by rw [hw]; simp : b ∈ _) (by rw [hw]; simp)
      obtain ⟨I, hsub, hmis⟩ := exists_mis_supset G {u, v, w} hind
      obtain ⟨k, rfl⟩ := hM_all I hmis
      have hku : k ∈ S u := (hmemS u k).mpr (hsub (by simp))
      have hkv : k ∈ S v := (hmemS v k).mpr (hsub (by simp))
      have hkw : k ∈ S w := (hmemS w k).mpr (hsub (by simp))
      rw [hu] at hku; rw [hv] at hkv; rw [hw] at hkw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hku hkv hkw
      rcases hku with rfl | rfl
      · rcases hkw with h1 | h2
        · exact hab h1
        · exact hac h2
      · rcases hkv with h1 | h2
        · exact hab h1.symm
        · exact hbc h2
    -- No star of 3 pairs: for any permutation (a,b,c,d) of Fin 4, cannot have {a,d}, {b,d}, {c,d}
    have hno_star : ∀ a b c d : Fin 4,
        a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
        ¬ (∃ u v w : Fin n, S u = {a, d} ∧ S v = {b, d} ∧ S w = {c, d}) := by
      rintro a b c d hab hac had hbc hbd hcd ⟨u, v, w, hu, hv, hw⟩
      exact cosun_kill hC hfit hsz (M a) (M b) (M c) (M d)
        (hM_mis a) (hM_mis b) (hM_mis c) (hM_mis d)
        (fun h => hab (hM_inj h)) (fun h => hac (hM_inj h)) (fun h => had (hM_inj h))
        (fun h => hbc (hM_inj h)) (fun h => hbd (hM_inj h)) (fun h => hcd (hM_inj h))
        u v w
        ⟨(hmemS u a).mp (by rw [hu]; simp), (hmemS u d).mp (by rw [hu]; simp),
          fun hm => by have := (hmemS u b).mpr hm; rw [hu] at this; simp at this; rcases this with h | h; exact hab h.symm; exact hbd h⟩
        ⟨(hmemS v b).mp (by rw [hv]; simp), (hmemS v d).mp (by rw [hv]; simp),
          fun hm => by have := (hmemS v c).mpr hm; rw [hv] at this; simp at this; rcases this with h | h; exact hbc h.symm; exact hcd h⟩
        ⟨(hmemS w c).mp (by rw [hw]; simp), (hmemS w d).mp (by rw [hw]; simp),
          fun hm => by have := (hmemS w a).mpr hm; rw [hw] at this; simp at this; rcases this with h | h; exact hac h; exact had h⟩
    -- Let P be the set of inhabited pairs (2-element subsets of Fin 4)
    let P : Finset (Finset (Fin 4)) := Finset.univ.filter (fun A : Finset (Fin 4) => A.card = 2 ∧ ∃ v : Fin n, S v = A)
    have hP_c4 : ∃ (p0 p1 p2 p3 : Fin 4),
        p0 ≠ p1 ∧ p0 ≠ p2 ∧ p0 ≠ p3 ∧ p1 ≠ p2 ∧ p1 ≠ p3 ∧ p2 ≠ p3 ∧
        ∀ A ∈ P, A ≠ {p0, p2} ∧ A ≠ {p1, p3} := by
      have hP_notri : ∀ a b c : Fin 4, a ≠ b → a ≠ c → b ≠ c →
          ¬ ({a, b} ∈ P ∧ {a, c} ∈ P ∧ {b, c} ∈ P) := by
        rintro a b c hab hac hbc ⟨h1, h2, h3⟩
        obtain ⟨u, hu⟩ := (Finset.mem_filter.mp h1).2.2
        obtain ⟨v, hv⟩ := (Finset.mem_filter.mp h2).2.2
        obtain ⟨w, hw⟩ := (Finset.mem_filter.mp h3).2.2
        exact hno_tri a b c hab hac hbc ⟨u, v, w, hu, hv, hw⟩
      have hP_nostar : ∀ a b c d : Fin 4,
          a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
          ¬ ({a, d} ∈ P ∧ {b, d} ∈ P ∧ {c, d} ∈ P) := by
        rintro a b c d hab hac had hbc hbd hcd ⟨h1, h2, h3⟩
        obtain ⟨u, hu⟩ := (Finset.mem_filter.mp h1).2.2
        obtain ⟨v, hv⟩ := (Finset.mem_filter.mp h2).2.2
        obtain ⟨w, hw⟩ := (Finset.mem_filter.mp h3).2.2
        exact hno_star a b c d hab hac had hbc hbd hcd ⟨u, v, w, hu, hv, hw⟩
      have hP_card2 : ∀ A ∈ P, A.card = 2 := fun A hA => (Finset.mem_filter.mp hA).2.1
      -- Purely finite fact about graphs on Fin 4 (only 2^6 = 64 edge subsets!):
      let hasE : Fin 4 → Fin 4 → Bool := fun a b => decide ({a, b} ∈ P)
      have hfin : ∀ (e01 e02 e03 e12 e13 e23 : Bool),
          ¬ (e01 = true ∧ e02 = true ∧ e12 = true) →
          ¬ (e01 = true ∧ e03 = true ∧ e13 = true) →
          ¬ (e02 = true ∧ e03 = true ∧ e23 = true) →
          ¬ (e12 = true ∧ e13 = true ∧ e23 = true) →
          ¬ (e01 = true ∧ e02 = true ∧ e03 = true) →
          ¬ (e01 = true ∧ e12 = true ∧ e13 = true) →
          ¬ (e02 = true ∧ e12 = true ∧ e23 = true) →
          ¬ (e03 = true ∧ e13 = true ∧ e23 = true) →
          (e02 = false ∧ e13 = false) ∨ (e01 = false ∧ e23 = false) ∨ (e03 = false ∧ e12 = false) := by
        intro e01 e02 e03 e12 e13 e23
        cases e01 <;> cases e02 <;> cases e03 <;> cases e12 <;> cases e13 <;> cases e23 <;> simp
      have hmemP : ∀ a b : Fin 4, hasE a b = true ↔ {a, b} ∈ P := fun a b => by simp [hasE]
      have htri : ∀ a b c : Fin 4, a ≠ b → a ≠ c → b ≠ c →
          ¬ (hasE a b = true ∧ hasE a c = true ∧ hasE b c = true) := by
        intro a b c hab hac hbc ⟨h1, h2, h3⟩
        exact hP_notri a b c hab hac hbc ⟨(hmemP a b).mp h1, (hmemP a c).mp h2, (hmemP b c).mp h3⟩
      have hstar : ∀ a b c d : Fin 4, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
          ¬ (hasE a d = true ∧ hasE b d = true ∧ hasE c d = true) := by
        intro a b c d hab hac had hbc hbd hcd ⟨h1, h2, h3⟩
        exact hP_nostar a b c d hab hac had hbc hbd hcd ⟨(hmemP a d).mp h1, (hmemP b d).mp h2, (hmemP c d).mp h3⟩
      have hsym : ∀ a b : Fin 4, hasE a b = hasE b a := fun a b => by
        simp only [hasE, Finset.pair_comm]
      have hdisj3 := hfin (hasE 0 1) (hasE 0 2) (hasE 0 3) (hasE 1 2) (hasE 1 3) (hasE 2 3)
        (htri 0 1 2 (by decide) (by decide) (by decide))
        (htri 0 1 3 (by decide) (by decide) (by decide))
        (htri 0 2 3 (by decide) (by decide) (by decide))
        (htri 1 2 3 (by decide) (by decide) (by decide))
        (by rw [hsym 0 1, hsym 0 2, hsym 0 3]; exact hstar 1 2 3 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
        (by rw [hsym 1 2, hsym 1 3]; exact hstar 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
        (by rw [hsym 2 3]; exact hstar 0 1 3 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
        (hstar 0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      have notInP : ∀ a b : Fin 4, hasE a b = false → ∀ A ∈ P, A ≠ {a, b} := by
        intro a b hf A hA heq
        rw [heq] at hA
        have ht := (hmemP a b).mpr hA
        rw [hf] at ht; exact Bool.noConfusion ht
      rcases hdisj3 with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨0, 1, 2, 3, by decide, by decide, by decide, by decide, by decide, by decide,
          fun A hA => ⟨notInP 0 2 h1 A hA, notInP 1 3 h2 A hA⟩⟩
      · exact ⟨0, 2, 1, 3, by decide, by decide, by decide, by decide, by decide, by decide,
          fun A hA => ⟨notInP 0 1 h1 A hA, notInP 2 3 h2 A hA⟩⟩
      · exact ⟨0, 1, 3, 2, by decide, by decide, by decide, by decide, by decide, by decide,
          fun A hA => ⟨notInP 0 3 h1 A hA, notInP 1 2 h2 A hA⟩⟩
    obtain ⟨p0, p1, p2, p3, h01, h02, h03, h12, h13, h23, hnoDiag⟩ := hP_c4
    -- Construct the 2 bicliques!
    refine ⟨![Finset.univ.filter (fun v => S v ⊆ {p0, p1}), Finset.univ.filter (fun v => S v ⊆ {p1, p2})],
            ![Finset.univ.filter (fun v => S v ⊆ {p2, p3}), Finset.univ.filter (fun v => S v ⊆ {p3, p0})], ?_, ?_⟩
    · intro i u hu v hv
      rw [hadj_iff]
      fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
        exact Disjoint.mono hu hv (by
          rw [Finset.disjoint_left]; intro k hk1 hk2
          simp only [Finset.mem_insert, Finset.mem_singleton] at hk1 hk2
          rcases hk1 with rfl | rfl <;> rcases hk2 with h1 | h2
          · exact h02 h1
          · exact h03 h2
          · exact h12 h1
          · exact h13 h2)
      · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero, Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
        exact Disjoint.mono hu hv (by
          rw [Finset.disjoint_left]; intro k hk1 hk2
          simp only [Finset.mem_insert, Finset.mem_singleton] at hk1 hk2
          rcases hk1 with rfl | rfl <;> rcases hk2 with h1 | h2
          · exact h13 h1
          · exact h01 h2.symm
          · exact h23 h1
          · exact h02 h2.symm)
    · intro u v huv
      have hdisj := (hadj_iff u v).mp huv
      have hu_ne := hS_ne u
      have hv_ne := hS_ne v
      have hu_le2 : (S u).card ≤ 2 := by
        have h4 : (S u).card ≤ 4 := by simpa using Finset.card_le_univ (S u)
        have h3 := hno3 u
        have hnot4 : (S u).card ≠ 4 := by
          intro h4'
          have : S u = Finset.univ := Finset.eq_univ_of_card (S u) (by simpa using h4')
          obtain ⟨k, hk⟩ := hv_ne
          exact Finset.disjoint_left.mp hdisj (by rw [this]; exact Finset.mem_univ k) hk
        omega
      have hv_le2 : (S v).card ≤ 2 := by
        have h4 : (S v).card ≤ 4 := by simpa using Finset.card_le_univ (S v)
        have h3 := hno3 v
        have hnot4 : (S v).card ≠ 4 := by
          intro h4'
          have : S v = Finset.univ := Finset.eq_univ_of_card (S v) (by simpa using h4')
          obtain ⟨k, hk⟩ := hu_ne
          exact Finset.disjoint_left.mp hdisj hk (by rw [this]; exact Finset.mem_univ k)
        omega
      have hu_nd : S u ≠ {p0, p2} ∧ S u ≠ {p1, p3} := by
        by_cases h2 : (S u).card = 2
        · exact hnoDiag (S u) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2, u, rfl⟩)
        · constructor <;> intro h <;> rw [h] at h2
          · exact h2 (Finset.card_pair h02)
          · exact h2 (Finset.card_pair h13)
      have hv_nd : S v ≠ {p0, p2} ∧ S v ≠ {p1, p3} := by
        by_cases h2 : (S v).card = 2
        · exact hnoDiag (S v) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2, v, rfl⟩)
        · constructor <;> intro h <;> rw [h] at h2
          · exact h2 (Finset.card_pair h02)
          · exact h2 (Finset.card_pair h13)
      have hcov_all : ∀ k : Fin 4, k = p0 ∨ k = p1 ∨ k = p2 ∨ k = p3 := by
        intro k
        have hset : ({p0, p1, p2, p3} : Finset (Fin 4)) = Finset.univ := by
          apply Finset.eq_univ_of_card
          simp [Finset.card_insert_of_notMem, h01, h02, h03, h12, h13, h23]
        have hk : k ∈ ({p0, p1, p2, p3} : Finset (Fin 4)) := by rw [hset]; exact Finset.mem_univ k
        simpa [Finset.mem_insert, Finset.mem_singleton] using hk
      have hcls : ∀ (A : Finset (Fin 4)), A.card ≤ 2 → A ≠ {p0, p2} → A ≠ {p1, p3} →
          A ⊆ {p0, p1} ∨ A ⊆ {p1, p2} ∨ A ⊆ {p2, p3} ∨ A ⊆ {p3, p0} := by
        intro A hA hA02 hA13
        by_cases h0 : p0 ∈ A
        · by_cases h2 : p2 ∈ A
          · exfalso; apply hA02; apply (Finset.eq_of_subset_of_card_le
              (by intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx
                  · exact h0
                  · rw [Finset.mem_singleton.mp hx]; exact h2)
              (by rw [Finset.card_pair h02]; exact hA)).symm
          · by_cases h1 : p1 ∈ A
            · left; intro x hx
              by_cases hx0 : x = p0
              · simp [hx0]
              · by_cases hx1 : x = p1
                · simp [hx1]
                · exfalso
                  have hsub : ({p0, p1, x} : Finset (Fin 4)) ⊆ A := by
                    intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
                    rcases hy with rfl | rfl | rfl <;> assumption
                  have h3 := Finset.card_le_card hsub
                  rw [Finset.card_insert_of_notMem (by simp [h01, Ne.symm hx0]),
                      Finset.card_pair (Ne.symm hx1)] at h3
                  omega
            · right; right; right; intro x hx
              rcases hcov_all x with rfl | rfl | rfl | rfl
              · simp
              · exact absurd hx h1
              · exact absurd hx h2
              · simp
        · by_cases h2 : p2 ∈ A
          · by_cases h1 : p1 ∈ A
            · right; left; intro x hx
              by_cases hx1 : x = p1
              · simp [hx1]
              · by_cases hx2 : x = p2
                · simp [hx2]
                · exfalso
                  have hsub : ({p1, p2, x} : Finset (Fin 4)) ⊆ A := by
                    intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
                    rcases hy with rfl | rfl | rfl <;> assumption
                  have h3 := Finset.card_le_card hsub
                  rw [Finset.card_insert_of_notMem (by simp [h12, Ne.symm hx1]),
                      Finset.card_pair (Ne.symm hx2)] at h3
                  omega
            · right; right; left; intro x hx
              rcases hcov_all x with rfl | rfl | rfl | rfl
              · exact absurd hx h0
              · exact absurd hx h1
              · simp
              · simp
          · by_cases h1 : p1 ∈ A
            · by_cases h3 : p3 ∈ A
              · exfalso; apply hA13; apply (Finset.eq_of_subset_of_card_le
                  (by intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx
                      · exact h1
                      · rw [Finset.mem_singleton.mp hx]; exact h3)
                  (by rw [Finset.card_pair h13]; exact hA)).symm
              · left; intro x hx
                rcases hcov_all x with rfl | rfl | rfl | rfl
                · exact absurd hx h0
                · simp
                · exact absurd hx h2
                · exact absurd hx h3
            · right; right; left; intro x hx
              rcases hcov_all x with rfl | rfl | rfl | rfl
              · exact absurd hx h0
              · exact absurd hx h1
              · exact absurd hx h2
              · simp
      have hdisj_sub : ∀ (A B : Finset (Fin 4)), A.Nonempty → B.Nonempty → Disjoint A B →
          (A ⊆ {p0, p1} → B ⊆ {p0, p1} → (A ⊆ {p3, p0} ∧ B ⊆ {p1, p2}) ∨ (B ⊆ {p3, p0} ∧ A ⊆ {p1, p2})) ∧
          (A ⊆ {p1, p2} → B ⊆ {p1, p2} → (A ⊆ {p0, p1} ∧ B ⊆ {p2, p3}) ∨ (B ⊆ {p0, p1} ∧ A ⊆ {p2, p3})) ∧
          (A ⊆ {p2, p3} → B ⊆ {p2, p3} → (A ⊆ {p1, p2} ∧ B ⊆ {p3, p0}) ∨ (B ⊆ {p1, p2} ∧ A ⊆ {p3, p0})) ∧
          (A ⊆ {p3, p0} → B ⊆ {p3, p0} → (A ⊆ {p2, p3} ∧ B ⊆ {p0, p1}) ∨ (B ⊆ {p2, p3} ∧ A ⊆ {p0, p1})) := by
        have pair_split : ∀ (q0 q1 a b : Fin 4) (A B : Finset (Fin 4)),
            A.Nonempty → B.Nonempty → Disjoint A B → A ⊆ {q0, q1} → B ⊆ {q0, q1} →
            (A ⊆ {a, q0} ∧ B ⊆ {q1, b}) ∨ (B ⊆ {a, q0} ∧ A ⊆ {q1, b}) := by
          intro q0 q1 a b A B hAne hBne hd hA hB
          by_cases h0 : q0 ∈ A
          · have h0nB : q0 ∉ B := Finset.disjoint_left.mp hd h0
            have h1B : q1 ∈ B := by
              obtain ⟨y, hy⟩ := hBne
              rcases Finset.mem_insert.mp (hB hy) with rfl | hy'
              · exact absurd hy h0nB
              · rwa [Finset.mem_singleton.mp hy'] at hy
            have h1nA : q1 ∉ A := Finset.disjoint_right.mp hd h1B
            left; refine ⟨fun x hx => ?_, fun x hx => ?_⟩
            · rcases Finset.mem_insert.mp (hA hx) with rfl | hx'
              · simp
              · rw [Finset.mem_singleton.mp hx'] at hx; exact absurd hx h1nA
            · rcases Finset.mem_insert.mp (hB hx) with rfl | hx'
              · exact absurd hx h0nB
              · rw [Finset.mem_singleton.mp hx']; simp
          · have h1A : q1 ∈ A := by
              obtain ⟨x, hx⟩ := hAne
              rcases Finset.mem_insert.mp (hA hx) with rfl | hx'
              · exact absurd hx h0
              · rwa [Finset.mem_singleton.mp hx'] at hx
            have h1nB : q1 ∉ B := Finset.disjoint_left.mp hd h1A
            right; refine ⟨fun x hx => ?_, fun x hx => ?_⟩
            · rcases Finset.mem_insert.mp (hB hx) with rfl | hx'
              · simp
              · rw [Finset.mem_singleton.mp hx'] at hx; exact absurd hx h1nB
            · rcases Finset.mem_insert.mp (hA hx) with rfl | hx'
              · exact absurd hx h0
              · rw [Finset.mem_singleton.mp hx']; simp
        intro A B hAne hBne hd
        exact ⟨pair_split p0 p1 p3 p2 A B hAne hBne hd,
               pair_split p1 p2 p0 p3 A B hAne hBne hd,
               pair_split p2 p3 p1 p0 A B hAne hBne hd,
               pair_split p3 p0 p2 p1 A B hAne hBne hd⟩
      have hstep := hdisj_sub (S u) (S v) hu_ne hv_ne hdisj
      have hadj_pair : ∀ (A B : Finset (Fin 4)), Disjoint A B →
          (A ⊆ {p0, p1} → B ⊆ {p1, p2} → (A ⊆ {p3, p0} ∧ B ⊆ {p1, p2}) ∨ (A ⊆ {p0, p1} ∧ B ⊆ {p2, p3})) ∧
          (A ⊆ {p1, p2} → B ⊆ {p2, p3} → (A ⊆ {p0, p1} ∧ B ⊆ {p2, p3}) ∨ (A ⊆ {p1, p2} ∧ B ⊆ {p3, p0})) ∧
          (A ⊆ {p2, p3} → B ⊆ {p3, p0} → (A ⊆ {p1, p2} ∧ B ⊆ {p3, p0}) ∨ (A ⊆ {p2, p3} ∧ B ⊆ {p0, p1})) ∧
          (A ⊆ {p3, p0} → B ⊆ {p0, p1} → (A ⊆ {p2, p3} ∧ B ⊆ {p0, p1}) ∨ (A ⊆ {p3, p0} ∧ B ⊆ {p1, p2})) := by
        intro A B hd
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro hA hB
          by_cases h1A : p1 ∈ A
          · right; refine ⟨hA, fun x hx => ?_⟩
            rcases Finset.mem_insert.mp (hB hx) with rfl | hx'
            · exact absurd hx (Finset.disjoint_left.mp hd h1A)
            · rw [Finset.mem_singleton.mp hx']; simp
          · left; refine ⟨fun x hx => ?_, hB⟩
            rcases Finset.mem_insert.mp (hA hx) with rfl | hx'
            · simp
            · rw [Finset.mem_singleton.mp hx'] at hx; exact absurd hx h1A
        · intro hA hB
          by_cases h2A : p2 ∈ A
          · right; refine ⟨hA, fun x hx => ?_⟩
            rcases Finset.mem_insert.mp (hB hx) with rfl | hx'
            · exact absurd hx (Finset.disjoint_left.mp hd h2A)
            · rw [Finset.mem_singleton.mp hx']; simp
          · left; refine ⟨fun x hx => ?_, hB⟩
            rcases Finset.mem_insert.mp (hA hx) with rfl | hx'
            · simp
            · rw [Finset.mem_singleton.mp hx'] at hx; exact absurd hx h2A
        · intro hA hB
          by_cases h3A : p3 ∈ A
          · right; refine ⟨hA, fun x hx => ?_⟩
            rcases Finset.mem_insert.mp (hB hx) with rfl | hx'
            · exact absurd hx (Finset.disjoint_left.mp hd h3A)
            · rw [Finset.mem_singleton.mp hx']; simp
          · left; refine ⟨fun x hx => ?_, hB⟩
            rcases Finset.mem_insert.mp (hA hx) with rfl | hx'
            · simp
            · rw [Finset.mem_singleton.mp hx'] at hx; exact absurd hx h3A
        · intro hA hB
          by_cases h0A : p0 ∈ A
          · right; refine ⟨hA, fun x hx => ?_⟩
            rcases Finset.mem_insert.mp (hB hx) with rfl | hx'
            · exact absurd hx (Finset.disjoint_left.mp hd h0A)
            · rw [Finset.mem_singleton.mp hx']; simp
          · left; refine ⟨fun x hx => ?_, hB⟩
            rcases Finset.mem_insert.mp (hA hx) with rfl | hx'
            · simp
            · rw [Finset.mem_singleton.mp hx'] at hx; exact absurd hx h0A
      have hp1 := hadj_pair (S u) (S v) hdisj
      have hp2 := hadj_pair (S v) (S u) hdisj.symm
      have mk0L : S u ⊆ {p0, p1} → S v ⊆ {p2, p3} →
          ∃ i : Fin 2,
            (u ∈ (![Finset.univ.filter (fun w => S w ⊆ {p0, p1}), Finset.univ.filter (fun w => S w ⊆ {p1, p2})] : Fin 2 → Finset (Fin n)) i ∧
             v ∈ (![Finset.univ.filter (fun w => S w ⊆ {p2, p3}), Finset.univ.filter (fun w => S w ⊆ {p3, p0})] : Fin 2 → Finset (Fin n)) i) ∨
            (v ∈ (![Finset.univ.filter (fun w => S w ⊆ {p0, p1}), Finset.univ.filter (fun w => S w ⊆ {p1, p2})] : Fin 2 → Finset (Fin n)) i ∧
             u ∈ (![Finset.univ.filter (fun w => S w ⊆ {p2, p3}), Finset.univ.filter (fun w => S w ⊆ {p3, p0})] : Fin 2 → Finset (Fin n)) i) :=
        fun h1 h2 => ⟨0, Or.inl ⟨by simp [h1], by simp [h2]⟩⟩
      have mk0R : S v ⊆ {p0, p1} → S u ⊆ {p2, p3} →
          ∃ i : Fin 2,
            (u ∈ (![Finset.univ.filter (fun w => S w ⊆ {p0, p1}), Finset.univ.filter (fun w => S w ⊆ {p1, p2})] : Fin 2 → Finset (Fin n)) i ∧
             v ∈ (![Finset.univ.filter (fun w => S w ⊆ {p2, p3}), Finset.univ.filter (fun w => S w ⊆ {p3, p0})] : Fin 2 → Finset (Fin n)) i) ∨
            (v ∈ (![Finset.univ.filter (fun w => S w ⊆ {p0, p1}), Finset.univ.filter (fun w => S w ⊆ {p1, p2})] : Fin 2 → Finset (Fin n)) i ∧
             u ∈ (![Finset.univ.filter (fun w => S w ⊆ {p2, p3}), Finset.univ.filter (fun w => S w ⊆ {p3, p0})] : Fin 2 → Finset (Fin n)) i) :=
        fun h1 h2 => ⟨0, Or.inr ⟨by simp [h1], by simp [h2]⟩⟩
      have mk1L : S u ⊆ {p1, p2} → S v ⊆ {p3, p0} →
          ∃ i : Fin 2,
            (u ∈ (![Finset.univ.filter (fun w => S w ⊆ {p0, p1}), Finset.univ.filter (fun w => S w ⊆ {p1, p2})] : Fin 2 → Finset (Fin n)) i ∧
             v ∈ (![Finset.univ.filter (fun w => S w ⊆ {p2, p3}), Finset.univ.filter (fun w => S w ⊆ {p3, p0})] : Fin 2 → Finset (Fin n)) i) ∨
            (v ∈ (![Finset.univ.filter (fun w => S w ⊆ {p0, p1}), Finset.univ.filter (fun w => S w ⊆ {p1, p2})] : Fin 2 → Finset (Fin n)) i ∧
             u ∈ (![Finset.univ.filter (fun w => S w ⊆ {p2, p3}), Finset.univ.filter (fun w => S w ⊆ {p3, p0})] : Fin 2 → Finset (Fin n)) i) :=
        fun h1 h2 => ⟨1, Or.inl ⟨by simp [h1], by simp [h2]⟩⟩
      have mk1R : S v ⊆ {p1, p2} → S u ⊆ {p3, p0} →
          ∃ i : Fin 2,
            (u ∈ (![Finset.univ.filter (fun w => S w ⊆ {p0, p1}), Finset.univ.filter (fun w => S w ⊆ {p1, p2})] : Fin 2 → Finset (Fin n)) i ∧
             v ∈ (![Finset.univ.filter (fun w => S w ⊆ {p2, p3}), Finset.univ.filter (fun w => S w ⊆ {p3, p0})] : Fin 2 → Finset (Fin n)) i) ∨
            (v ∈ (![Finset.univ.filter (fun w => S w ⊆ {p0, p1}), Finset.univ.filter (fun w => S w ⊆ {p1, p2})] : Fin 2 → Finset (Fin n)) i ∧
             u ∈ (![Finset.univ.filter (fun w => S w ⊆ {p2, p3}), Finset.univ.filter (fun w => S w ⊆ {p3, p0})] : Fin 2 → Finset (Fin n)) i) :=
        fun h1 h2 => ⟨1, Or.inr ⟨by simp [h1], by simp [h2]⟩⟩
      rcases hcls (S u) hu_le2 hu_nd.1 hu_nd.2 with hu01 | hu12 | hu23 | hu30 <;>
      rcases hcls (S v) hv_le2 hv_nd.1 hv_nd.2 with hv01 | hv12 | hv23 | hv30
      · rcases hstep.1 hu01 hv01 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact mk1R h2 h1
        · exact mk1L h2 h1
      · rcases hp1.1 hu01 hv12 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact mk1R h2 h1
        · exact mk0L h1 h2
      · exact mk0L hu01 hv23
      · rcases hp2.2.2.2 hv30 hu01 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact mk0L h2 h1
        · exact mk1L h2 h1
      · rcases hp2.1 hv01 hu12 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact mk1L h2 h1
        · exact mk0R h1 h2
      · rcases hstep.2.1 hu12 hv12 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact mk0L h1 h2
        · exact mk0R h1 h2
      · rcases hp1.2.1 hu12 hv23 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact mk0L h1 h2
        · exact mk1L h1 h2
      · exact mk1L hu12 hv30
      · exact mk0R hv01 hu23
      · rcases hp2.2.1 hv12 hu23 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact mk0R h1 h2
        · exact mk1R h1 h2
      · rcases hstep.2.2.1 hu23 hv23 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact mk1L h1 h2
        · exact mk1R h1 h2
      · rcases hp1.2.2.1 hu23 hv30 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact mk1L h1 h2
        · exact mk0R h2 h1
      · rcases hp1.2.2.2 hu30 hv01 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact mk0R h2 h1
        · exact mk1R h2 h1
      · exact mk1R hv12 hu30
      · rcases hp2.2.2.1 hv23 hu30 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact mk1R h1 h2
        · exact mk0L h2 h1
      · rcases hstep.2.2.2 hu30 hv30 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact mk0R h2 h1
        · exact mk0L h2 h1

end Size0124

section Size3Fin6

-- Helper: a 3-biclique cover of K_6 (or any 6-vertex graph with no H-edges)
private lemma bc3_complete (G : SimpleGraph (Fin 6)) (hK : ∀ a b : Fin 6, a ≠ b → G.Adj a b) :
    HasBicliqueCover G 3 := by
  refine ⟨![{0, 1, 2}, {0, 3}, {1, 4}], ![{3, 4, 5}, {1, 2, 4, 5}, {2, 5}], ?_, ?_⟩
  · intro i a ha b hb
    apply hK a b
    intro hab; subst hab
    fin_cases i <;> simp at ha hb <;> omega
  · intro a b hab
    have hne : a ≠ b := G.ne_of_adj hab
    fin_cases a <;> fin_cases b <;> simp_all <;> decide

-- Helper: extract 4 distinct elements from a Finset of card 4
private lemma card_eq_four {α : Type*} [DecidableEq α] {s : Finset α} (h : s.card = 4) :
    ∃ a b c d : α, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧ s = {a, b, c, d} := by
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < s.card)
  have h3 : (s.erase a).card = 3 := by rw [Finset.card_erase_of_mem ha, h]
  obtain ⟨b, c, d, hbc, hbd, hcd, heq⟩ := Finset.card_eq_three.mp h3
  have hab : a ≠ b := fun he => (Finset.notMem_erase a s) (by rw [heq]; simp [he])
  have hac : a ≠ c := fun he => (Finset.notMem_erase a s) (by rw [heq]; simp [he])
  have had : a ≠ d := fun he => (Finset.notMem_erase a s) (by rw [heq]; simp [he])
  refine ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, ?_⟩
  rw [← Finset.insert_erase ha, heq]

-- Helper: extract 5 distinct elements from a Finset of card 5
private lemma card_eq_five {α : Type*} [DecidableEq α] {s : Finset α} (h : s.card = 5) :
    ∃ a b c d e : α,
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧ b ≠ c ∧ b ≠ d ∧ b ≠ e ∧ c ≠ d ∧ c ≠ e ∧ d ≠ e ∧
      s = {a, b, c, d, e} := by
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < s.card)
  have h4 : (s.erase a).card = 4 := by rw [Finset.card_erase_of_mem ha, h]
  obtain ⟨b, c, d, e, hbc, hbd, hbe, hcd, hce, hde, heq⟩ := card_eq_four h4
  have hab : a ≠ b := fun he => (Finset.notMem_erase a s) (by rw [heq]; simp [he])
  have hac : a ≠ c := fun he => (Finset.notMem_erase a s) (by rw [heq]; simp [he])
  have had : a ≠ d := fun he => (Finset.notMem_erase a s) (by rw [heq]; simp [he])
  have hae : a ≠ e := fun he => (Finset.notMem_erase a s) (by rw [heq]; simp [he])
  refine ⟨a, b, c, d, e, hab, hac, had, hae, hbc, hbd, hbe, hcd, hce, hde, ?_⟩
  rw [← Finset.insert_erase ha, heq]

-- Helper: star complement H (every H-edge touches v) => bc(G) <= 3!
private lemma bc3_star_comp (G : SimpleGraph (Fin 6)) (v : Fin 6)
    (hK5 : ∀ x y : Fin 6, x ≠ v → y ≠ v → x ≠ y → G.Adj x y) :
    HasBicliqueCover G 3 := by
  classical
  let M : Finset (Fin 6) := Finset.univ.filter (fun u => G.Adj v u)
  let N : Finset (Fin 6) := (Finset.univ.erase v) \ M
  have hvM : v ∉ M := by simp [M]
  have hvN : v ∉ N := by simp [N]
  have hMsub : M ⊆ Finset.univ.erase v := by
    intro u hu; exact Finset.mem_erase.mpr ⟨(G.ne_of_adj (Finset.mem_filter.mp hu).2).symm, Finset.mem_univ u⟩
  have hMNcard : M.card + N.card = 5 := by
    have h1 := Finset.card_sdiff_add_card_eq_card hMsub
    have h2 : (Finset.univ.erase v).card = 5 := by simp
    rw [h2] at h1
    change N.card + M.card = 5 at h1
    omega
  have hM_adj : ∀ u ∈ M, G.Adj v u := fun u hu => (Finset.mem_filter.mp hu).2
  have hN_nadj : ∀ u ∈ N, ¬ G.Adj v u := by
    intro u hu; have := (Finset.mem_sdiff.mp hu).2; simp only [M, Finset.mem_filter, Finset.mem_univ, true_and] at this; exact this
  have hpart : ∀ u : Fin 6, u = v ∨ u ∈ M ∨ u ∈ N := by
    intro u
    by_cases huv : u = v
    · exact Or.inl huv
    · by_cases huM : u ∈ M
      · exact Or.inr (Or.inl huM)
      · exact Or.inr (Or.inr (Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨huv, Finset.mem_univ u⟩, huM⟩))
  have hMle5 : M.card ≤ 5 := by omega
  interval_cases hMc : M.card
  · -- M = empty: v isolated, N has 5 vertices forming K_5
    have hN5 : N.card = 5 := by omega
    obtain ⟨n1, n2, n3, n4, n5, h12, h13, h14, h15, h23, h24, h25, h34, h35, h45, hNeq⟩ := card_eq_five hN5
    have hn_nev : ∀ x ∈ N, x ≠ v := fun x hx => (Finset.mem_erase.mp (Finset.mem_sdiff.mp hx).1).1
    have hmemN : n1 ∈ N ∧ n2 ∈ N ∧ n3 ∈ N ∧ n4 ∈ N ∧ n5 ∈ N := by rw [hNeq]; simp
    have hK : ∀ a b : Fin 6, a ∈ ({n1, n2, n3, n4, n5} : Finset (Fin 6)) →
        b ∈ ({n1, n2, n3, n4, n5} : Finset (Fin 6)) → a ≠ b → G.Adj a b := fun a b ha hb hab =>
      hK5 a b (hn_nev a (hNeq.symm ▸ ha)) (hn_nev b (hNeq.symm ▸ hb)) hab
    refine ⟨![{n1, n2}, {n1, n3}, {n3, n4}], ![{n3, n4, n5}, {n2, n4, n5}, {n5}], ?_, ?_⟩
    · intro i a ha b hb
      fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Finset.mem_insert,
        Finset.mem_singleton] at ha hb
      · rcases ha with rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
          exact hK _ _ (by simp) (by simp) (by assumption)
      · rcases ha with rfl | rfl <;> rcases hb with rfl | rfl | rfl
        · exact hK _ _ (by simp) (by simp) h12
        · exact hK _ _ (by simp) (by simp) h14
        · exact hK _ _ (by simp) (by simp) h15
        · exact hK _ _ (by simp) (by simp) h23.symm
        · exact hK _ _ (by simp) (by simp) h34
        · exact hK _ _ (by simp) (by simp) h35
      · subst hb
        rcases ha with rfl | rfl
        · exact hK _ _ (by simp) (by simp) h35
        · exact hK _ _ (by simp) (by simp) h45
    · intro a b hab
      have hM0 : M = ∅ := Finset.card_eq_zero.mp hMc
      have hav : a ≠ v := by
        intro h; subst h
        have : b ∈ M := Finset.mem_filter.mpr ⟨Finset.mem_univ b, hab⟩
        rw [hM0] at this; exact Finset.notMem_empty b this
      have hbv : b ≠ v := by
        intro h; subst h
        have : a ∈ M := Finset.mem_filter.mpr ⟨Finset.mem_univ a, (G.adj_comm _ _).mp hab⟩
        rw [hM0] at this; exact Finset.notMem_empty a this
      have haN : a ∈ N := by rcases hpart a with h | h | h; exact absurd h hav; rw [hM0] at h; exact absurd h (Finset.notMem_empty _); exact h
      have hbN : b ∈ N := by rcases hpart b with h | h | h; exact absurd h hbv; rw [hM0] at h; exact absurd h (Finset.notMem_empty _); exact h
      rw [hNeq] at haN hbN
      have hne : a ≠ b := G.ne_of_adj hab
      simp only [Finset.mem_insert, Finset.mem_singleton] at haN hbN
      rcases haN with rfl | rfl | rfl | rfl | rfl <;> rcases hbN with rfl | rfl | rfl | rfl | rfl
      · exact absurd rfl hne
      · exact ⟨1, Or.inl ⟨by simp, by simp⟩⟩
      · exact ⟨0, Or.inl ⟨by simp, by simp⟩⟩
      · exact ⟨0, Or.inl ⟨by simp, by simp⟩⟩
      · exact ⟨0, Or.inl ⟨by simp, by simp⟩⟩
      · exact ⟨1, Or.inr ⟨by simp, by simp⟩⟩
      · exact absurd rfl hne
      · exact ⟨0, Or.inl ⟨by simp, by simp⟩⟩
      · exact ⟨0, Or.inl ⟨by simp, by simp⟩⟩
      · exact ⟨0, Or.inl ⟨by simp, by simp⟩⟩
      · exact ⟨0, Or.inr ⟨by simp, by simp⟩⟩
      · exact ⟨0, Or.inr ⟨by simp, by simp⟩⟩
      · exact absurd rfl hne
      · exact ⟨1, Or.inl ⟨by simp, by simp⟩⟩
      · exact ⟨2, Or.inl ⟨by simp, by simp⟩⟩
      · exact ⟨0, Or.inr ⟨by simp, by simp⟩⟩
      · exact ⟨0, Or.inr ⟨by simp, by simp⟩⟩
      · exact ⟨1, Or.inr ⟨by simp, by simp⟩⟩
      · exact absurd rfl hne
      · exact ⟨2, Or.inl ⟨by simp, by simp⟩⟩
      · exact ⟨0, Or.inr ⟨by simp, by simp⟩⟩
      · exact ⟨0, Or.inr ⟨by simp, by simp⟩⟩
      · exact ⟨2, Or.inr ⟨by simp, by simp⟩⟩
      · exact ⟨2, Or.inr ⟨by simp, by simp⟩⟩
      · exact absurd rfl hne
  · -- M.card = 1, N.card = 4
    obtain ⟨m, hMeq⟩ := Finset.card_eq_one.mp hMc
    have hN4 : N.card = 4 := by omega
    obtain ⟨n1, n2, n3, n4, h12, h13, h14, h23, h24, h34, hNeq⟩ := card_eq_four hN4
    have hm_adj : G.Adj v m := hM_adj m (by rw [hMeq]; simp)
    have hm_nev : m ≠ v := (G.ne_of_adj hm_adj).symm
    have hn_nev : ∀ x ∈ N, x ≠ v := fun x hx => (Finset.mem_erase.mp (Finset.mem_sdiff.mp hx).1).1
    have hn_nem : ∀ x ∈ N, x ≠ m := fun x hx hxm => (Finset.mem_sdiff.mp hx).2 (by rw [hMeq, hxm]; simp)
    refine ⟨![insert v N, {n1, n2}, {n1, n3}], ![{m}, {n3, n4}, {n2, n4}], ?_, ?_⟩
    · intro i a ha b hb
      fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Finset.mem_insert,
        Finset.mem_singleton] at ha hb
      · subst hb
        rcases ha with rfl | haN
        · exact hm_adj
        · exact hK5 a _ (hn_nev a haN) hm_nev (hn_nem a haN)
      · rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact hK5 _ _ (hn_nev _ (by rw [hNeq]; simp)) (hn_nev _ (by rw [hNeq]; simp)) h13
        · exact hK5 _ _ (hn_nev _ (by rw [hNeq]; simp)) (hn_nev _ (by rw [hNeq]; simp)) h14
        · exact hK5 _ _ (hn_nev _ (by rw [hNeq]; simp)) (hn_nev _ (by rw [hNeq]; simp)) h23
        · exact hK5 _ _ (hn_nev _ (by rw [hNeq]; simp)) (hn_nev _ (by rw [hNeq]; simp)) h24
      · rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact hK5 _ _ (hn_nev _ (by rw [hNeq]; simp)) (hn_nev _ (by rw [hNeq]; simp)) h12
        · exact hK5 _ _ (hn_nev _ (by rw [hNeq]; simp)) (hn_nev _ (by rw [hNeq]; simp)) h14
        · exact hK5 _ _ (hn_nev _ (by rw [hNeq]; simp)) (hn_nev _ (by rw [hNeq]; simp)) h23.symm
        · exact hK5 _ _ (hn_nev _ (by rw [hNeq]; simp)) (hn_nev _ (by rw [hNeq]; simp)) h34
    · intro a b hab
      have hne := G.ne_of_adj hab
      rcases hpart a with rfl | haM | haN <;> rcases hpart b with rfl | hbM | hbN
      · exact absurd rfl hne
      · rw [hMeq, Finset.mem_singleton] at hbM; subst hbM; exact ⟨0, Or.inl ⟨by simp, by simp⟩⟩
      · exact absurd hab (hN_nadj b hbN)
      · rw [hMeq, Finset.mem_singleton] at haM; subst haM; exact ⟨0, Or.inr ⟨by simp, by simp⟩⟩
      · rw [hMeq, Finset.mem_singleton] at haM hbM; exact absurd (haM.trans hbM.symm) hne
      · rw [hMeq, Finset.mem_singleton] at haM; subst haM; exact ⟨0, Or.inr ⟨by simp [hbN], by simp⟩⟩
      · exact absurd ((G.adj_comm _ _).mp hab) (hN_nadj a haN)
      · rw [hMeq, Finset.mem_singleton] at hbM; subst hbM; exact ⟨0, Or.inl ⟨by simp [haN], by simp⟩⟩
      · rw [hNeq] at haN hbN; simp only [Finset.mem_insert, Finset.mem_singleton] at haN hbN
        rcases haN with rfl | rfl | rfl | rfl <;> rcases hbN with rfl | rfl | rfl | rfl
        · exact absurd rfl hne
        · exact ⟨2, Or.inl ⟨by simp, by simp⟩⟩
        · exact ⟨1, Or.inl ⟨by simp, by simp⟩⟩
        · exact ⟨1, Or.inl ⟨by simp, by simp⟩⟩
        · exact ⟨2, Or.inr ⟨by simp, by simp⟩⟩
        · exact absurd rfl hne
        · exact ⟨1, Or.inl ⟨by simp, by simp⟩⟩
        · exact ⟨1, Or.inl ⟨by simp, by simp⟩⟩
        · exact ⟨1, Or.inr ⟨by simp, by simp⟩⟩
        · exact ⟨1, Or.inr ⟨by simp, by simp⟩⟩
        · exact absurd rfl hne
        · exact ⟨2, Or.inl ⟨by simp, by simp⟩⟩
        · exact ⟨1, Or.inr ⟨by simp, by simp⟩⟩
        · exact ⟨1, Or.inr ⟨by simp, by simp⟩⟩
        · exact ⟨2, Or.inr ⟨by simp, by simp⟩⟩
        · exact absurd rfl hne
  · -- M.card = 2, N.card = 3
    obtain ⟨m1, m2, hm12, hMeq⟩ := Finset.card_eq_two.mp hMc
    have hN3 : N.card = 3 := by omega
    obtain ⟨n1, n2, n3, h12, h13, h23, hNeq⟩ := Finset.card_eq_three.mp hN3
    have hm1v : m1 ≠ v := (G.ne_of_adj (hM_adj m1 (by rw [hMeq]; simp))).symm
    have hm2v : m2 ≠ v := (G.ne_of_adj (hM_adj m2 (by rw [hMeq]; simp))).symm
    have hn_nev : ∀ x ∈ N, x ≠ v := fun x hx => (Finset.mem_erase.mp (Finset.mem_sdiff.mp hx).1).1
    have hdisjMN : ∀ x ∈ N, ∀ y ∈ M, x ≠ y := fun x hx y hy hxy => (Finset.mem_sdiff.mp hx).2 (hxy ▸ hy)
    have hn1N : n1 ∈ N := by rw [hNeq]; simp
    have hn2N : n2 ∈ N := by rw [hNeq]; simp
    have hn3N : n3 ∈ N := by rw [hNeq]; simp
    have hm1M : m1 ∈ M := by rw [hMeq]; simp
    have hm2M : m2 ∈ M := by rw [hMeq]; simp
    refine ⟨![insert v N, {m1, n1}, {n1, n2}], ![M, {m2, n2}, {n3}], ?_, ?_⟩
    · intro i a ha b hb
      fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Finset.mem_insert,
        Finset.mem_singleton] at ha hb
      · rcases ha with rfl | haN
        · exact hM_adj b hb
        · exact hK5 a b (hn_nev a haN) (G.ne_of_adj (hM_adj b hb)).symm (hdisjMN a haN b hb)
      · rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact hK5 _ _ hm1v hm2v hm12
        · exact hK5 _ _ hm1v (hn_nev _ hn2N) (hdisjMN _ hn2N _ hm1M).symm
        · exact hK5 _ _ (hn_nev _ hn1N) hm2v (hdisjMN _ hn1N _ hm2M)
        · exact hK5 _ _ (hn_nev _ hn1N) (hn_nev _ hn2N) h12
      · subst hb
        rcases ha with rfl | rfl
        · exact hK5 _ _ (hn_nev _ hn1N) (hn_nev _ hn3N) h13
        · exact hK5 _ _ (hn_nev _ hn2N) (hn_nev _ hn3N) h23
    · intro a b hab
      have hne := G.ne_of_adj hab
      rcases hpart a with rfl | haM | haN <;> rcases hpart b with rfl | hbM | hbN
      · exact absurd rfl hne
      · exact ⟨0, Or.inl ⟨by simp, hbM⟩⟩
      · exact absurd hab (hN_nadj b hbN)
      · exact ⟨0, Or.inr ⟨by simp, haM⟩⟩
      · rw [hMeq] at haM hbM; simp only [Finset.mem_insert, Finset.mem_singleton] at haM hbM
        rcases haM with rfl | rfl <;> rcases hbM with rfl | rfl
        · exact absurd rfl hne
        · exact ⟨1, Or.inl ⟨by simp, by simp⟩⟩
        · exact ⟨1, Or.inr ⟨by simp, by simp⟩⟩
        · exact absurd rfl hne
      · exact ⟨0, Or.inr ⟨by simp [hbN], haM⟩⟩
      · exact absurd ((G.adj_comm _ _).mp hab) (hN_nadj a haN)
      · exact ⟨0, Or.inl ⟨by simp [haN], hbM⟩⟩
      · rw [hNeq] at haN hbN; simp only [Finset.mem_insert, Finset.mem_singleton] at haN hbN
        rcases haN with rfl | rfl | rfl <;> rcases hbN with rfl | rfl | rfl
        · exact absurd rfl hne
        · exact ⟨1, Or.inl ⟨by simp, by simp⟩⟩
        · exact ⟨2, Or.inl ⟨by simp, by simp⟩⟩
        · exact ⟨1, Or.inr ⟨by simp, by simp⟩⟩
        · exact absurd rfl hne
        · exact ⟨2, Or.inl ⟨by simp, by simp⟩⟩
        · exact ⟨2, Or.inr ⟨by simp, by simp⟩⟩
        · exact ⟨2, Or.inr ⟨by simp, by simp⟩⟩
        · exact absurd rfl hne
  · -- M.card = 3, N.card = 2
    obtain ⟨m1, m2, m3, hm12, hm13, hm23, hMeq⟩ := Finset.card_eq_three.mp hMc
    have hN2 : N.card = 2 := by omega
    obtain ⟨n1, n2, hn12, hNeq⟩ := Finset.card_eq_two.mp hN2
    have hm1M : m1 ∈ M := by rw [hMeq]; simp
    have hm2M : m2 ∈ M := by rw [hMeq]; simp
    have hm3M : m3 ∈ M := by rw [hMeq]; simp
    have hn1N : n1 ∈ N := by rw [hNeq]; simp
    have hn2N : n2 ∈ N := by rw [hNeq]; simp
    have hm_nev : ∀ y ∈ M, y ≠ v := fun y hy => (G.ne_of_adj (hM_adj y hy)).symm
    have hn_nev : ∀ x ∈ N, x ≠ v := fun x hx => (Finset.mem_erase.mp (Finset.mem_sdiff.mp hx).1).1
    have hdisjMN : ∀ x ∈ N, ∀ y ∈ M, x ≠ y := fun x hx y hy hxy => (Finset.mem_sdiff.mp hx).2 (hxy ▸ hy)
    refine ⟨![insert v N, {n1, m1}, {m1, m2}], ![M, {n2, m2}, {m3}], ?_, ?_⟩
    · intro i a ha b hb
      fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Finset.mem_insert,
        Finset.mem_singleton] at ha hb
      · rcases ha with rfl | haN
        · exact hM_adj b hb
        · exact hK5 a b (hn_nev a haN) (hm_nev b hb) (hdisjMN a haN b hb)
      · rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact hK5 _ _ (hn_nev _ hn1N) (hn_nev _ hn2N) hn12
        · exact hK5 _ _ (hn_nev _ hn1N) (hm_nev _ hm2M) (hdisjMN _ hn1N _ hm2M)
        · exact hK5 _ _ (hm_nev _ hm1M) (hn_nev _ hn2N) (hdisjMN _ hn2N _ hm1M).symm
        · exact hK5 _ _ (hm_nev _ hm1M) (hm_nev _ hm2M) hm12
      · subst hb
        rcases ha with rfl | rfl
        · exact hK5 _ _ (hm_nev _ hm1M) (hm_nev _ hm3M) hm13
        · exact hK5 _ _ (hm_nev _ hm2M) (hm_nev _ hm3M) hm23
    · intro a b hab
      have hne := G.ne_of_adj hab
      rcases hpart a with rfl | haM | haN <;> rcases hpart b with rfl | hbM | hbN
      · exact absurd rfl hne
      · exact ⟨0, Or.inl ⟨by simp, hbM⟩⟩
      · exact absurd hab (hN_nadj b hbN)
      · exact ⟨0, Or.inr ⟨by simp, haM⟩⟩
      · rw [hMeq] at haM hbM; simp only [Finset.mem_insert, Finset.mem_singleton] at haM hbM
        rcases haM with rfl | rfl | rfl <;> rcases hbM with rfl | rfl | rfl
        · exact absurd rfl hne
        · exact ⟨1, Or.inl ⟨by simp, by simp⟩⟩
        · exact ⟨2, Or.inl ⟨by simp, by simp⟩⟩
        · exact ⟨1, Or.inr ⟨by simp, by simp⟩⟩
        · exact absurd rfl hne
        · exact ⟨2, Or.inl ⟨by simp, by simp⟩⟩
        · exact ⟨2, Or.inr ⟨by simp, by simp⟩⟩
        · exact ⟨2, Or.inr ⟨by simp, by simp⟩⟩
        · exact absurd rfl hne
      · exact ⟨0, Or.inr ⟨by simp [hbN], haM⟩⟩
      · exact absurd ((G.adj_comm _ _).mp hab) (hN_nadj a haN)
      · exact ⟨0, Or.inl ⟨by simp [haN], hbM⟩⟩
      · rw [hNeq] at haN hbN; simp only [Finset.mem_insert, Finset.mem_singleton] at haN hbN
        rcases haN with rfl | rfl <;> rcases hbN with rfl | rfl
        · exact absurd rfl hne
        · exact ⟨1, Or.inl ⟨by simp, by simp⟩⟩
        · exact ⟨1, Or.inr ⟨by simp, by simp⟩⟩
        · exact absurd rfl hne
  · -- M.card = 4, N.card = 1
    obtain ⟨m1, m2, m3, m4, h12, h13, h14, h23, h24, h34, hMeq⟩ := card_eq_four hMc
    have hN1 : N.card = 1 := by omega
    obtain ⟨n1, hNeq⟩ := Finset.card_eq_one.mp hN1
    have hm_nev : ∀ y ∈ M, y ≠ v := fun y hy => (G.ne_of_adj (hM_adj y hy)).symm
    have hn1N : n1 ∈ N := by rw [hNeq]; simp
    have hn1_nev : n1 ≠ v := (Finset.mem_erase.mp (Finset.mem_sdiff.mp hn1N).1).1
    have hdisjMN : ∀ y ∈ M, n1 ≠ y := fun y hy hxy => (Finset.mem_sdiff.mp hn1N).2 (hxy ▸ hy)
    have hm1M : m1 ∈ M := by rw [hMeq]; simp
    have hm2M : m2 ∈ M := by rw [hMeq]; simp
    have hm3M : m3 ∈ M := by rw [hMeq]; simp
    have hm4M : m4 ∈ M := by rw [hMeq]; simp
    refine ⟨![{v, n1}, {m1, m2}, {m1, m3}], ![M, {m3, m4}, {m2, m4}], ?_, ?_⟩
    · intro i a ha b hb
      fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Finset.mem_insert,
        Finset.mem_singleton] at ha hb
      · rcases ha with rfl | rfl
        · exact hM_adj b hb
        · exact hK5 _ b hn1_nev (hm_nev b hb) (hdisjMN b hb)
      · rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact hK5 _ _ (hm_nev _ hm1M) (hm_nev _ hm3M) h13
        · exact hK5 _ _ (hm_nev _ hm1M) (hm_nev _ hm4M) h14
        · exact hK5 _ _ (hm_nev _ hm2M) (hm_nev _ hm3M) h23
        · exact hK5 _ _ (hm_nev _ hm2M) (hm_nev _ hm4M) h24
      · rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact hK5 _ _ (hm_nev _ hm1M) (hm_nev _ hm2M) h12
        · exact hK5 _ _ (hm_nev _ hm1M) (hm_nev _ hm4M) h14
        · exact hK5 _ _ (hm_nev _ hm3M) (hm_nev _ hm2M) h23.symm
        · exact hK5 _ _ (hm_nev _ hm3M) (hm_nev _ hm4M) h34
    · intro a b hab
      have hne := G.ne_of_adj hab
      rcases hpart a with rfl | haM | haN <;> rcases hpart b with rfl | hbM | hbN
      · exact absurd rfl hne
      · exact ⟨0, Or.inl ⟨by simp, hbM⟩⟩
      · exact absurd hab (hN_nadj b hbN)
      · exact ⟨0, Or.inr ⟨by simp, haM⟩⟩
      · rw [hMeq] at haM hbM; simp only [Finset.mem_insert, Finset.mem_singleton] at haM hbM
        rcases haM with rfl | rfl | rfl | rfl <;> rcases hbM with rfl | rfl | rfl | rfl
        · exact absurd rfl hne
        · exact ⟨2, Or.inl ⟨by simp, by simp⟩⟩
        · exact ⟨1, Or.inl ⟨by simp, by simp⟩⟩
        · exact ⟨1, Or.inl ⟨by simp, by simp⟩⟩
        · exact ⟨2, Or.inr ⟨by simp, by simp⟩⟩
        · exact absurd rfl hne
        · exact ⟨1, Or.inl ⟨by simp, by simp⟩⟩
        · exact ⟨1, Or.inl ⟨by simp, by simp⟩⟩
        · exact ⟨1, Or.inr ⟨by simp, by simp⟩⟩
        · exact ⟨1, Or.inr ⟨by simp, by simp⟩⟩
        · exact absurd rfl hne
        · exact ⟨2, Or.inl ⟨by simp, by simp⟩⟩
        · exact ⟨1, Or.inr ⟨by simp, by simp⟩⟩
        · exact ⟨1, Or.inr ⟨by simp, by simp⟩⟩
        · exact ⟨2, Or.inr ⟨by simp, by simp⟩⟩
        · exact absurd rfl hne
      · rw [hNeq, Finset.mem_singleton] at hbN; subst hbN; exact ⟨0, Or.inr ⟨by simp, haM⟩⟩
      · exact absurd ((G.adj_comm _ _).mp hab) (hN_nadj a haN)
      · rw [hNeq, Finset.mem_singleton] at haN; subst haN; exact ⟨0, Or.inl ⟨by simp, hbM⟩⟩
      · rw [hNeq, Finset.mem_singleton] at haN hbN; exact absurd (haN.trans hbN.symm) hne
  · -- M.card = 5 => G = K_6
    apply bc3_complete G
    intro a b hab
    by_cases hav : a = v
    · subst hav
      have hMeq : M = Finset.univ.erase a := Finset.eq_of_subset_of_card_le hMsub (by simp [hMc])
      exact hM_adj b (by rw [hMeq]; exact Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩)
    · by_cases hbv : b = v
      · subst hbv
        have hMeq : M = Finset.univ.erase b := Finset.eq_of_subset_of_card_le hMsub (by simp [hMc])
        exact (G.adj_comm b a).mp (hM_adj a (by rw [hMeq]; exact Finset.mem_erase.mpr ⟨hab, Finset.mem_univ a⟩))
      · exact hK5 a b hav hbv hab

private lemma bc3_h_atmost_one_deg3 (G : SimpleGraph (Fin 6))
    (hTF : ∀ a b c : Fin 6, (a ≠ b ∧ ¬ G.Adj a b) → (b ≠ c ∧ ¬ G.Adj b c) → ¬ (a ≠ c ∧ ¬ G.Adj a c))
    (v : Fin 6)
    (hno_third : ∀ u x y z : Fin 6, u ≠ v → x ≠ y → (u ≠ x ∧ ¬ G.Adj u x) → (u ≠ y ∧ ¬ G.Adj u y) → z ≠ x → z ≠ y → ¬ (u ≠ z ∧ ¬ G.Adj u z)) :
    HasBicliqueCover G 3 := by
  classical
  let HAdj : Fin 6 → Fin 6 → Prop := fun a b => a ≠ b ∧ ¬ G.Adj a b
  have hHsym : ∀ a b, HAdj a b → HAdj b a := fun a b ⟨hne, hna⟩ => ⟨hne.symm, fun h => hna ((G.adj_comm a b).mpr h)⟩
  by_cases hstar : ∀ x y : Fin 6, x ≠ v → y ≠ v → x ≠ y → G.Adj x y
  · exact bc3_star_comp G v hstar
  · push_neg at hstar
    by_cases hP5 : ∃ u0 u1 u2 u3 u4 : Fin 6,
        u0 ≠ v ∧ u1 ≠ v ∧ u2 ≠ v ∧ u3 ≠ v ∧ u4 ≠ v ∧
        u0 ≠ u1 ∧ u0 ≠ u2 ∧ u0 ≠ u3 ∧ u0 ≠ u4 ∧ u1 ≠ u2 ∧ u1 ≠ u3 ∧ u1 ≠ u4 ∧
        u2 ≠ u3 ∧ u2 ≠ u4 ∧ u3 ≠ u4 ∧
        HAdj u0 u1 ∧ HAdj u1 u2 ∧ HAdj u2 u3 ∧ HAdj u3 u4
    · obtain ⟨u0, u1, u2, u3, u4, hv0, hv1, hv2, hv3, hv4,
              h01, h02, h03, h04, h12, h13, h14, h23, h24, h34, e01, e12, e23, e34⟩ := hP5
      have hpart6 : ∀ x : Fin 6, x = v ∨ x = u0 ∨ x = u1 ∨ x = u2 ∨ x = u3 ∨ x = u4 := by
        intro x
        have huniv : ({v, u0, u1, u2, u3, u4} : Finset (Fin 6)) = Finset.univ := by
          apply Finset.eq_univ_of_card
          simp [Finset.card_insert_of_notMem, hv0.symm, hv1.symm, hv2.symm, hv3.symm, hv4.symm,
            h01, h02, h03, h04, h12, h13, h14, h23, h24, h34]
        have hx : x ∈ ({v, u0, u1, u2, u3, u4} : Finset (Fin 6)) := by rw [huniv]; exact Finset.mem_univ x
        simpa [Finset.mem_insert, Finset.mem_singleton] using hx
      have hG02 : G.Adj u0 u2 := by by_contra h; exact hTF u0 u1 u2 e01 e12 ⟨h02, h⟩
      have hG13 : G.Adj u1 u3 := by by_contra h; exact hTF u1 u2 u3 e12 e23 ⟨h13, h⟩
      have hG24 : G.Adj u2 u4 := by by_contra h; exact hTF u2 u3 u4 e23 e34 ⟨h24, h⟩
      have hG03 : G.Adj u0 u3 := by
        by_contra h; exact hno_third u3 u2 u4 u0 hv3 h24 (hHsym _ _ e23) e34 h02 h04 (hHsym _ _ ⟨h03, h⟩)
      have hG14 : G.Adj u1 u4 := by
        by_contra h; exact hno_third u1 u0 u2 u4 hv1 h02 (hHsym _ _ e01) e12 h04.symm h24.symm ⟨h14, h⟩
      by_cases hC5 : HAdj u4 u0
      · have hv_all : G.Adj v u0 ∧ G.Adj v u1 ∧ G.Adj v u2 ∧ G.Adj v u3 ∧ G.Adj v u4 := by
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · by_contra h; exact hno_third u0 u1 u4 v hv0 h14 e01 (hHsym _ _ hC5) hv1.symm hv4.symm (hHsym _ _ ⟨hv0.symm, h⟩)
          · by_contra h; exact hno_third u1 u0 u2 v hv1 h02 (hHsym _ _ e01) e12 hv0.symm hv2.symm (hHsym _ _ ⟨hv1.symm, h⟩)
          · by_contra h; exact hno_third u2 u1 u3 v hv2 h13 (hHsym _ _ e12) e23 hv1.symm hv3.symm (hHsym _ _ ⟨hv2.symm, h⟩)
          · by_contra h; exact hno_third u3 u2 u4 v hv3 h24 (hHsym _ _ e23) e34 hv2.symm hv4.symm (hHsym _ _ ⟨hv3.symm, h⟩)
          · by_contra h; exact hno_third u4 u3 u0 v hv4 h03.symm (hHsym _ _ e34) hC5 hv3.symm hv0.symm (hHsym _ _ ⟨hv4.symm, h⟩)
        refine ⟨![{u0, u1}, {u2, u3}, {u1, u2, v}], ![{u3, v}, {u0, v}, {u4}], ?_, ?_⟩
        · intro i x hx y hy
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
            Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Finset.mem_insert,
            Finset.mem_singleton] at hx hy
          · rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
            · exact hG03
            · exact (G.adj_comm _ _).mp hv_all.1
            · exact hG13
            · exact (G.adj_comm _ _).mp hv_all.2.1
          · rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
            · exact (G.adj_comm _ _).mp hG02
            · exact (G.adj_comm _ _).mp hv_all.2.2.1
            · exact (G.adj_comm _ _).mp hG03
            · exact (G.adj_comm _ _).mp hv_all.2.2.2.1
          · subst hy
            rcases hx with rfl | rfl | rfl
            · exact hG14
            · exact hG24
            · exact hv_all.2.2.2.2
        · intro x y hxy
          have hne := G.ne_of_adj hxy
          rcases hpart6 x with rfl | rfl | rfl | rfl | rfl | rfl <;>
          rcases hpart6 y with rfl | rfl | rfl | rfl | rfl | rfl
          · exact absurd rfl hne
          · exact ⟨0, Or.inr ⟨by simp, by simp⟩⟩
          · exact ⟨0, Or.inr ⟨by simp, by simp⟩⟩
          · exact ⟨1, Or.inr ⟨by simp, by simp⟩⟩
          · exact ⟨1, Or.inr ⟨by simp, by simp⟩⟩
          · exact ⟨2, Or.inl ⟨by simp, by simp⟩⟩
          · exact ⟨0, Or.inl ⟨by simp, by simp⟩⟩
          · exact absurd rfl hne
          · exact absurd hxy e01.2
          · exact ⟨1, Or.inr ⟨by simp, by simp⟩⟩
          · exact ⟨0, Or.inl ⟨by simp, by simp⟩⟩
          · exact absurd hxy (hHsym _ _ hC5).2
          · exact ⟨0, Or.inl ⟨by simp, by simp⟩⟩
          · exact absurd hxy (hHsym _ _ e01).2
          · exact absurd rfl hne
          · exact absurd hxy e12.2
          · exact ⟨0, Or.inl ⟨by simp, by simp⟩⟩
          · exact ⟨2, Or.inl ⟨by simp, by simp⟩⟩
          · exact ⟨1, Or.inl ⟨by simp, by simp⟩⟩
          · exact ⟨1, Or.inl ⟨by simp, by simp⟩⟩
          · exact absurd hxy (hHsym _ _ e12).2
          · exact absurd rfl hne
          · exact absurd hxy e23.2
          · exact ⟨2, Or.inl ⟨by simp, by simp⟩⟩
          · exact ⟨1, Or.inl ⟨by simp, by simp⟩⟩
          · exact ⟨0, Or.inr ⟨by simp, by simp⟩⟩
          · exact ⟨0, Or.inr ⟨by simp, by simp⟩⟩
          · exact absurd hxy (hHsym _ _ e23).2
          · exact absurd rfl hne
          · exact absurd hxy e34.2
          · exact ⟨2, Or.inr ⟨by simp, by simp⟩⟩
          · exact absurd hxy hC5.2
          · exact ⟨2, Or.inr ⟨by simp, by simp⟩⟩
          · exact ⟨2, Or.inr ⟨by simp, by simp⟩⟩
          · exact absurd hxy (hHsym _ _ e34).2
          · exact absurd rfl hne
      · have hG04 : G.Adj u0 u4 := by by_contra h; exact hC5 ⟨h04.symm, fun h' => h ((G.adj_comm _ _).mpr h')⟩
        apply bc_add_vertex G v 2
        refine ⟨![{u0, u1}, {u0, u4}], ![{u3, u4}, {u2}], ?_, ?_⟩
        · intro i x hx y hy
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue,
            Matrix.cons_val_zero, Matrix.cons_val_one, Finset.mem_insert,
            Finset.mem_singleton] at hx hy
          · rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
            · exact hG03
            · exact hG04
            · exact hG13
            · exact hG14
          · subst hy
            rcases hx with rfl | rfl
            · exact hG02
            · exact (G.adj_comm _ _).mp hG24
        · intro x y hxv hyv hxy
          have hne := G.ne_of_adj hxy
          rcases hpart6 x with rfl | rfl | rfl | rfl | rfl | rfl
          · exact absurd rfl hxv
          · rcases hpart6 y with rfl | rfl | rfl | rfl | rfl | rfl
            · exact absurd rfl hyv
            · exact absurd rfl hne
            · exact absurd hxy e01.2
            · exact ⟨1, Or.inl ⟨by simp, by simp⟩⟩
            · exact ⟨0, Or.inl ⟨by simp, by simp⟩⟩
            · exact ⟨0, Or.inl ⟨by simp, by simp⟩⟩
          · rcases hpart6 y with rfl | rfl | rfl | rfl | rfl | rfl
            · exact absurd rfl hyv
            · exact absurd hxy (hHsym _ _ e01).2
            · exact absurd rfl hne
            · exact absurd hxy e12.2
            · exact ⟨0, Or.inl ⟨by simp, by simp⟩⟩
            · exact ⟨0, Or.inl ⟨by simp, by simp⟩⟩
          · rcases hpart6 y with rfl | rfl | rfl | rfl | rfl | rfl
            · exact absurd rfl hyv
            · exact ⟨1, Or.inr ⟨by simp, by simp⟩⟩
            · exact absurd hxy (hHsym _ _ e12).2
            · exact absurd rfl hne
            · exact absurd hxy e23.2
            · exact ⟨1, Or.inr ⟨by simp, by simp⟩⟩
          · rcases hpart6 y with rfl | rfl | rfl | rfl | rfl | rfl
            · exact absurd rfl hyv
            · exact ⟨0, Or.inr ⟨by simp, by simp⟩⟩
            · exact ⟨0, Or.inr ⟨by simp, by simp⟩⟩
            · exact absurd hxy (hHsym _ _ e23).2
            · exact absurd rfl hne
            · exact absurd hxy e34.2
          · rcases hpart6 y with rfl | rfl | rfl | rfl | rfl | rfl
            · exact absurd rfl hyv
            · exact ⟨0, Or.inr ⟨by simp, by simp⟩⟩
            · exact ⟨0, Or.inr ⟨by simp, by simp⟩⟩
            · exact ⟨1, Or.inl ⟨by simp, by simp⟩⟩
            · exact absurd hxy (hHsym _ _ e34).2
            · exact absurd rfl hne
    · by_cases hP4 : ∃ u0 u1 u2 u3 : Fin 6,
          u0 ≠ v ∧ u1 ≠ v ∧ u2 ≠ v ∧ u3 ≠ v ∧
          u0 ≠ u1 ∧ u0 ≠ u2 ∧ u0 ≠ u3 ∧ u1 ≠ u2 ∧ u1 ≠ u3 ∧ u2 ≠ u3 ∧
          HAdj u0 u1 ∧ HAdj u1 u2 ∧ HAdj u2 u3
      · obtain ⟨u0, u1, u2, u3, hv0, hv1, hv2, hv3, h01, h02, h03, h12, h13, h23, e01, e12, e23⟩ := hP4
        have hrem : (Finset.univ \ ({v, u0, u1, u2, u3} : Finset (Fin 6))).card = 1 := by
          rw [Finset.card_sdiff]; simp [Finset.card_insert_of_notMem, hv0.symm, hv1.symm, hv2.symm, hv3.symm,
            h01, h02, h03, h12, h13, h23]
        obtain ⟨u4, hu4eq⟩ := Finset.card_eq_one.mp hrem
        have hu4mem : u4 ∈ Finset.univ \ ({v, u0, u1, u2, u3} : Finset (Fin 6)) := by rw [hu4eq]; simp
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton, not_or] at hu4mem
        obtain ⟨hv4, h04, h14, h24, h34⟩ : u4 ≠ v ∧ u4 ≠ u0 ∧ u4 ≠ u1 ∧ u4 ≠ u2 ∧ u4 ≠ u3 := hu4mem
        have hpart6 : ∀ x : Fin 6, x = v ∨ x = u0 ∨ x = u1 ∨ x = u2 ∨ x = u3 ∨ x = u4 := by
          intro x
          by_cases hx : x ∈ ({v, u0, u1, u2, u3} : Finset (Fin 6))
          · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp
          · have : x ∈ ({u4} : Finset (Fin 6)) := by rw [← hu4eq]; exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hx⟩
            rw [Finset.mem_singleton.mp this]; simp
        have hG02 : G.Adj u0 u2 := by by_contra h; exact hTF u0 u1 u2 e01 e12 ⟨h02, h⟩
        have hG13 : G.Adj u1 u3 := by by_contra h; exact hTF u1 u2 u3 e12 e23 ⟨h13, h⟩
        have hG04 : G.Adj u0 u4 := by
          by_contra h; apply hP5
          exact ⟨u4, u0, u1, u2, u3, hv4, hv0, hv1, hv2, hv3, h04, h14, h24, h34,
            h01, h02, h03, h12, h13, h23, ⟨h04, fun h' => h ((G.adj_comm _ _).mpr h')⟩, e01, e12, e23⟩
        have hG34 : G.Adj u3 u4 := by
          by_contra h; apply hP5
          exact ⟨u0, u1, u2, u3, u4, hv0, hv1, hv2, hv3, hv4, h01, h02, h03, h04.symm,
            h12, h13, h14.symm, h23, h24.symm, h34.symm, e01, e12, e23, ⟨h34.symm, h⟩⟩
        have hG14 : G.Adj u1 u4 := by
          by_contra h; exact hno_third u1 u0 u2 u4 hv1 h02 (hHsym _ _ e01) e12 h04 h24 ⟨h14.symm, h⟩
        have hG24 : G.Adj u2 u4 := by
          by_contra h; exact hno_third u2 u1 u3 u4 hv2 h13 (hHsym _ _ e12) e23 h14 h34 ⟨h24.symm, h⟩
        by_cases hC4 : HAdj u3 u0
        · have hGv1 : G.Adj v u1 := by by_contra h; exact hno_third u1 u0 u2 v hv1 h02 (hHsym _ _ e01) e12 hv0.symm hv2.symm (hHsym _ _ ⟨hv1.symm, h⟩)
          have hGv2 : G.Adj v u2 := by by_contra h; exact hno_third u2 u1 u3 v hv2 h13 (hHsym _ _ e12) e23 hv1.symm hv3.symm (hHsym _ _ ⟨hv2.symm, h⟩)
          have hGv3 : G.Adj v u3 := by by_contra h; exact hno_third u3 u2 u0 v hv3 h02.symm (hHsym _ _ e23) hC4 hv2.symm hv0.symm (hHsym _ _ ⟨hv3.symm, h⟩)
          apply bc_add_vertex G u0 2
          let X2 : Finset (Fin 6) := insert u1 (if G.Adj v u4 then {v} else ∅)
          let Y2 : Finset (Fin 6) := insert u3 (if G.Adj v u4 then {u4} else ∅)
          refine ⟨![{u1, u2, u3}, X2], ![{v, u4}, Y2], ?_, ?_⟩
          · intro i x hx y hy
            fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue,
              Matrix.cons_val_zero, Matrix.cons_val_one, Finset.mem_insert,
              Finset.mem_singleton] at hx hy
            · rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl
              · exact (G.adj_comm _ _).mp hGv1
              · exact hG14
              · exact (G.adj_comm _ _).mp hGv2
              · exact hG24
              · exact (G.adj_comm _ _).mp hGv3
              · exact hG34
            · rcases Finset.mem_insert.mp hx with rfl | hx'
              · rcases Finset.mem_insert.mp hy with rfl | hy'
                · exact hG13
                · split_ifs at hy' with hv4g
                  · rw [Finset.mem_singleton.mp hy']; exact hG14
                  · exact absurd hy' (Finset.notMem_empty _)
              · split_ifs at hx' with hv4g
                · rw [Finset.mem_singleton.mp hx']
                  rcases Finset.mem_insert.mp hy with rfl | hy'
                  · exact hGv3
                  · rw [if_pos hv4g] at hy'; rw [Finset.mem_singleton.mp hy']; exact hv4g
                · exact absurd hx' (Finset.notMem_empty _)
          · intro x y hxu0 hyu0 hxy
            have hne := G.ne_of_adj hxy
            rcases hpart6 x with rfl | rfl | rfl | rfl | rfl | rfl
            · rcases hpart6 y with rfl | rfl | rfl | rfl | rfl | rfl
              · exact absurd rfl hne
              · exact absurd rfl hyu0
              · exact ⟨0, Or.inr ⟨by simp, by simp⟩⟩
              · exact ⟨0, Or.inr ⟨by simp, by simp⟩⟩
              · exact ⟨0, Or.inr ⟨by simp, by simp⟩⟩
              · exact ⟨1, Or.inl ⟨Finset.mem_insert_of_mem (by simp [hxy]), Finset.mem_insert_of_mem (by simp [hxy])⟩⟩
            · exact absurd rfl hxu0
            · rcases hpart6 y with rfl | rfl | rfl | rfl | rfl | rfl
              · exact ⟨0, Or.inl ⟨by simp, by simp⟩⟩
              · exact absurd rfl hyu0
              · exact absurd rfl hne
              · exact absurd hxy e12.2
              · exact ⟨1, Or.inl ⟨Finset.mem_insert_self _ _, Finset.mem_insert_self _ _⟩⟩
              · exact ⟨0, Or.inl ⟨by simp, by simp⟩⟩
            · rcases hpart6 y with rfl | rfl | rfl | rfl | rfl | rfl
              · exact ⟨0, Or.inl ⟨by simp, by simp⟩⟩
              · exact absurd rfl hyu0
              · exact absurd hxy (hHsym _ _ e12).2
              · exact absurd rfl hne
              · exact absurd hxy e23.2
              · exact ⟨0, Or.inl ⟨by simp, by simp⟩⟩
            · rcases hpart6 y with rfl | rfl | rfl | rfl | rfl | rfl
              · exact ⟨0, Or.inl ⟨by simp, by simp⟩⟩
              · exact absurd rfl hyu0
              · exact ⟨1, Or.inr ⟨Finset.mem_insert_self _ _, Finset.mem_insert_self _ _⟩⟩
              · exact absurd hxy (hHsym _ _ e23).2
              · exact absurd rfl hne
              · exact ⟨0, Or.inl ⟨by simp, by simp⟩⟩
            · rcases hpart6 y with rfl | rfl | rfl | rfl | rfl | rfl
              · exact ⟨1, Or.inr ⟨Finset.mem_insert_of_mem (by simp [(G.adj_comm _ _).mp hxy]), Finset.mem_insert_of_mem (by simp [(G.adj_comm _ _).mp hxy])⟩⟩
              · exact absurd rfl hyu0
              · exact ⟨0, Or.inr ⟨by simp, by simp⟩⟩
              · exact ⟨0, Or.inr ⟨by simp, by simp⟩⟩
              · exact ⟨0, Or.inr ⟨by simp, by simp⟩⟩
              · exact absurd rfl hne
        · have hG03 : G.Adj u0 u3 := by by_contra h; exact hC4 ⟨h03.symm, fun h' => h ((G.adj_comm _ _).mpr h')⟩
          apply bc_add_vertex G v 2
          refine ⟨![{u0, u1}, {u0, u4}], ![{u3, u4}, {u2, u3}], ?_, ?_⟩
          · intro i x hx y hy
            fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue,
              Matrix.cons_val_zero, Matrix.cons_val_one, Finset.mem_insert,
              Finset.mem_singleton] at hx hy
            · rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
              · exact hG03
              · exact hG04
              · exact hG13
              · exact hG14
            · rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
              · exact hG02
              · exact hG03
              · exact (G.adj_comm _ _).mp hG24
              · exact (G.adj_comm _ _).mp hG34
          · intro x y hxv hyv hxy
            have hne := G.ne_of_adj hxy
            rcases hpart6 x with rfl | rfl | rfl | rfl | rfl | rfl
            · exact absurd rfl hxv
            · rcases hpart6 y with rfl | rfl | rfl | rfl | rfl | rfl
              · exact absurd rfl hyv
              · exact absurd rfl hne
              · exact absurd hxy e01.2
              · exact ⟨1, Or.inl ⟨by simp, by simp⟩⟩
              · exact ⟨0, Or.inl ⟨by simp, by simp⟩⟩
              · exact ⟨0, Or.inl ⟨by simp, by simp⟩⟩
            · rcases hpart6 y with rfl | rfl | rfl | rfl | rfl | rfl
              · exact absurd rfl hyv
              · exact absurd hxy (hHsym _ _ e01).2
              · exact absurd rfl hne
              · exact absurd hxy e12.2
              · exact ⟨0, Or.inl ⟨by simp, by simp⟩⟩
              · exact ⟨0, Or.inl ⟨by simp, by simp⟩⟩
            · rcases hpart6 y with rfl | rfl | rfl | rfl | rfl | rfl
              · exact absurd rfl hyv
              · exact ⟨1, Or.inr ⟨by simp, by simp⟩⟩
              · exact absurd hxy (hHsym _ _ e12).2
              · exact absurd rfl hne
              · exact absurd hxy e23.2
              · exact ⟨1, Or.inr ⟨by simp, by simp⟩⟩
            · rcases hpart6 y with rfl | rfl | rfl | rfl | rfl | rfl
              · exact absurd rfl hyv
              · exact ⟨0, Or.inr ⟨by simp, by simp⟩⟩
              · exact ⟨0, Or.inr ⟨by simp, by simp⟩⟩
              · exact absurd hxy (hHsym _ _ e23).2
              · exact absurd rfl hne
              · exact ⟨1, Or.inr ⟨by simp, by simp⟩⟩
            · rcases hpart6 y with rfl | rfl | rfl | rfl | rfl | rfl
              · exact absurd rfl hyv
              · exact ⟨0, Or.inr ⟨by simp, by simp⟩⟩
              · exact ⟨0, Or.inr ⟨by simp, by simp⟩⟩
              · exact ⟨1, Or.inl ⟨by simp, by simp⟩⟩
              · exact ⟨1, Or.inl ⟨by simp, by simp⟩⟩
              · exact absurd rfl hne
      · by_cases hP3 : ∃ u0 u1 u2 : Fin 6,
            u0 ≠ v ∧ u1 ≠ v ∧ u2 ≠ v ∧ u0 ≠ u1 ∧ u0 ≠ u2 ∧ u1 ≠ u2 ∧
            HAdj u0 u1 ∧ HAdj u1 u2
        · obtain ⟨u0, u1, u2, hv0, hv1, hv2, h01, h02, h12, e01, e12⟩ := hP3
          have hrem : (Finset.univ \ ({v, u0, u1, u2} : Finset (Fin 6))).card = 2 := by
            rw [Finset.card_sdiff]; simp [Finset.card_insert_of_notMem, hv0.symm, hv1.symm, hv2.symm, h01, h02, h12]
          obtain ⟨u3, u4, h34, hreq⟩ := Finset.card_eq_two.mp hrem
          have hu3mem : u3 ∈ Finset.univ \ ({v, u0, u1, u2} : Finset (Fin 6)) := by rw [hreq]; simp
          have hu4mem : u4 ∈ Finset.univ \ ({v, u0, u1, u2} : Finset (Fin 6)) := by rw [hreq]; simp
          simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
            Finset.mem_singleton, not_or] at hu3mem hu4mem
          obtain ⟨hv3, h03, h13, h23⟩ : u3 ≠ v ∧ u3 ≠ u0 ∧ u3 ≠ u1 ∧ u3 ≠ u2 := hu3mem
          obtain ⟨hv4, h04, h14, h24⟩ : u4 ≠ v ∧ u4 ≠ u0 ∧ u4 ≠ u1 ∧ u4 ≠ u2 := hu4mem
          have hpart6 : ∀ x : Fin 6, x = v ∨ x = u0 ∨ x = u1 ∨ x = u2 ∨ x = u3 ∨ x = u4 := by
            intro x
            by_cases hx : x ∈ ({v, u0, u1, u2} : Finset (Fin 6))
            · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              rcases hx with rfl | rfl | rfl | rfl <;> simp
            · have : x ∈ ({u3, u4} : Finset (Fin 6)) := by rw [← hreq]; exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hx⟩
              simp only [Finset.mem_insert, Finset.mem_singleton] at this
              rcases this with rfl | rfl <;> simp
          have hG02 : G.Adj u0 u2 := by by_contra h; exact hTF u0 u1 u2 e01 e12 ⟨h02, h⟩
          have hG03 : G.Adj u0 u3 := by
            by_contra h; apply hP4
            exact ⟨u3, u0, u1, u2, hv3, hv0, hv1, hv2, h03, h13, h23, h01, h02, h12,
              ⟨h03, fun h' => h ((G.adj_comm _ _).mpr h')⟩, e01, e12⟩
          have hG04 : G.Adj u0 u4 := by
            by_contra h; apply hP4
            exact ⟨u4, u0, u1, u2, hv4, hv0, hv1, hv2, h04, h14, h24, h01, h02, h12,
              ⟨h04, fun h' => h ((G.adj_comm _ _).mpr h')⟩, e01, e12⟩
          have hG23 : G.Adj u2 u3 := by
            by_contra h; apply hP4
            exact ⟨u0, u1, u2, u3, hv0, hv1, hv2, hv3, h01, h02, h03.symm, h12, h13.symm, h23.symm,
              e01, e12, ⟨h23.symm, h⟩⟩
          have hG24 : G.Adj u2 u4 := by
            by_contra h; apply hP4
            exact ⟨u0, u1, u2, u4, hv0, hv1, hv2, hv4, h01, h02, h04.symm, h12, h14.symm, h24.symm,
              e01, e12, ⟨h24.symm, h⟩⟩
          have hG13 : G.Adj u1 u3 := by
            by_contra h; exact hno_third u1 u0 u2 u3 hv1 h02 (hHsym _ _ e01) e12 h03 h23 ⟨h13.symm, h⟩
          have hG14 : G.Adj u1 u4 := by
            by_contra h; exact hno_third u1 u0 u2 u4 hv1 h02 (hHsym _ _ e01) e12 h04 h24 ⟨h14.symm, h⟩
          apply bc_add_vertex G v 2
          let X2 : Finset (Fin 6) := insert u0 (if G.Adj u3 u4 then {u3} else ∅)
          let Y2 : Finset (Fin 6) := insert u2 (if G.Adj u3 u4 then {u4} else ∅)
          refine ⟨![{u0, u1, u2}, X2], ![{u3, u4}, Y2], ?_, ?_⟩
          · intro i x hx y hy
            fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue,
              Matrix.cons_val_zero, Matrix.cons_val_one, Finset.mem_insert,
              Finset.mem_singleton] at hx hy
            · rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl
              · exact hG03
              · exact hG04
              · exact hG13
              · exact hG14
              · exact hG23
              · exact hG24
            · rcases Finset.mem_insert.mp hx with rfl | hx'
              · rcases Finset.mem_insert.mp hy with rfl | hy'
                · exact hG02
                · split_ifs at hy' with h34g
                  · rw [Finset.mem_singleton.mp hy']; exact hG04
                  · exact absurd hy' (Finset.notMem_empty _)
              · split_ifs at hx' with h34g
                · rw [Finset.mem_singleton.mp hx']
                  rcases Finset.mem_insert.mp hy with rfl | hy'
                  · exact (G.adj_comm _ _).mp hG23
                  · rw [if_pos h34g] at hy'; rw [Finset.mem_singleton.mp hy']; exact h34g
                · exact absurd hx' (Finset.notMem_empty _)
          · intro x y hxv hyv hxy
            have hne := G.ne_of_adj hxy
            rcases hpart6 x with rfl | rfl | rfl | rfl | rfl | rfl
            · exact absurd rfl hxv
            · rcases hpart6 y with rfl | rfl | rfl | rfl | rfl | rfl
              · exact absurd rfl hyv
              · exact absurd rfl hne
              · exact absurd hxy e01.2
              · exact ⟨1, Or.inl ⟨Finset.mem_insert_self _ _, Finset.mem_insert_self _ _⟩⟩
              · exact ⟨0, Or.inl ⟨by simp, by simp⟩⟩
              · exact ⟨0, Or.inl ⟨by simp, by simp⟩⟩
            · rcases hpart6 y with rfl | rfl | rfl | rfl | rfl | rfl
              · exact absurd rfl hyv
              · exact absurd hxy (hHsym _ _ e01).2
              · exact absurd rfl hne
              · exact absurd hxy e12.2
              · exact ⟨0, Or.inl ⟨by simp, by simp⟩⟩
              · exact ⟨0, Or.inl ⟨by simp, by simp⟩⟩
            · rcases hpart6 y with rfl | rfl | rfl | rfl | rfl | rfl
              · exact absurd rfl hyv
              · exact ⟨1, Or.inr ⟨Finset.mem_insert_self _ _, Finset.mem_insert_self _ _⟩⟩
              · exact absurd hxy (hHsym _ _ e12).2
              · exact absurd rfl hne
              · exact ⟨0, Or.inl ⟨by simp, by simp⟩⟩
              · exact ⟨0, Or.inl ⟨by simp, by simp⟩⟩
            · rcases hpart6 y with rfl | rfl | rfl | rfl | rfl | rfl
              · exact absurd rfl hyv
              · exact ⟨0, Or.inr ⟨by simp, by simp⟩⟩
              · exact ⟨0, Or.inr ⟨by simp, by simp⟩⟩
              · exact ⟨0, Or.inr ⟨by simp, by simp⟩⟩
              · exact absurd rfl hne
              · exact ⟨1, Or.inl ⟨Finset.mem_insert_of_mem (by simp [hxy]), Finset.mem_insert_of_mem (by simp [hxy])⟩⟩
            · rcases hpart6 y with rfl | rfl | rfl | rfl | rfl | rfl
              · exact absurd rfl hyv
              · exact ⟨0, Or.inr ⟨by simp, by simp⟩⟩
              · exact ⟨0, Or.inr ⟨by simp, by simp⟩⟩
              · exact ⟨0, Or.inr ⟨by simp, by simp⟩⟩
              · exact ⟨1, Or.inr ⟨Finset.mem_insert_of_mem (by simp [(G.adj_comm _ _).mp hxy]), Finset.mem_insert_of_mem (by simp [(G.adj_comm _ _).mp hxy])⟩⟩
              · exact absurd rfl hne
        · obtain ⟨u0, u1, hv0, hv1, h01, hna01⟩ := hstar
          have e01 : HAdj u0 u1 := ⟨h01, hna01⟩
          have hrem : (Finset.univ \ ({v, u0, u1} : Finset (Fin 6))).card = 3 := by
            rw [Finset.card_sdiff]; simp [Finset.card_insert_of_notMem, hv0.symm, hv1.symm, h01]
          obtain ⟨u2, u3, u4, h23, h24, h34, hreq⟩ := Finset.card_eq_three.mp hrem
          have hu2mem : u2 ∈ Finset.univ \ ({v, u0, u1} : Finset (Fin 6)) := by rw [hreq]; simp
          have hu3mem : u3 ∈ Finset.univ \ ({v, u0, u1} : Finset (Fin 6)) := by rw [hreq]; simp
          have hu4mem : u4 ∈ Finset.univ \ ({v, u0, u1} : Finset (Fin 6)) := by rw [hreq]; simp
          simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
            Finset.mem_singleton, not_or] at hu2mem hu3mem hu4mem
          obtain ⟨hv2, h02, h12⟩ := hu2mem
          obtain ⟨hv3, h03, h13⟩ := hu3mem
          obtain ⟨hv4, h04, h14⟩ := hu4mem
          have hpart6 : ∀ x : Fin 6, x = v ∨ x = u0 ∨ x = u1 ∨ x = u2 ∨ x = u3 ∨ x = u4 := by
            intro x
            by_cases hx : x ∈ ({v, u0, u1} : Finset (Fin 6))
            · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              rcases hx with rfl | rfl | rfl <;> simp
            · have : x ∈ ({u2, u3, u4} : Finset (Fin 6)) := by rw [← hreq]; exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hx⟩
              simp only [Finset.mem_insert, Finset.mem_singleton] at this
              rcases this with rfl | rfl | rfl <;> simp
          have hG0R : ∀ z ∈ ({u2, u3, u4} : Finset (Fin 6)), G.Adj u0 z := by
            intro z hz; by_contra hna
            have hz' : z ≠ v ∧ z ≠ u0 ∧ z ≠ u1 := by
              simp only [Finset.mem_insert, Finset.mem_singleton] at hz
              rcases hz with rfl | rfl | rfl <;> exact ⟨‹_›, ‹_›, ‹_›⟩
            exact hP3 ⟨z, u0, u1, hz'.1, hv0, hv1, hz'.2.1, hz'.2.2, h01,
              ⟨hz'.2.1, fun h => hna ((G.adj_comm _ _).mpr h)⟩, e01⟩
          have hG1R : ∀ z ∈ ({u2, u3, u4} : Finset (Fin 6)), G.Adj u1 z := by
            intro z hz; by_contra hna
            have hz' : z ≠ v ∧ z ≠ u0 ∧ z ≠ u1 := by
              simp only [Finset.mem_insert, Finset.mem_singleton] at hz
              rcases hz with rfl | rfl | rfl <;> exact ⟨‹_›, ‹_›, ‹_›⟩
            exact hP3 ⟨u0, u1, z, hv0, hv1, hz'.1, h01, hz'.2.1.symm, hz'.2.2.symm,
              e01, ⟨hz'.2.2.symm, hna⟩⟩
          have h2K2 : ∀ a b c : Fin 6,
              a ≠ v → b ≠ v → c ≠ v → a ≠ b → a ≠ c → b ≠ c →
              ({u2, u3, u4} : Finset (Fin 6)) = {a, b, c} → HAdj a b → HasBicliqueCover G 3 := by
            intro a b c hva hvb hvc hab hac hbc hset eab
            have hGac : G.Adj a c := by
              by_contra h; exact hP3 ⟨b, a, c, hvb, hva, hvc, hab.symm, hbc, hac, hHsym _ _ eab, ⟨hac, h⟩⟩
            have hGbc : G.Adj b c := by
              by_contra h; exact hP3 ⟨a, b, c, hva, hvb, hvc, hab, hac, hbc, eab, ⟨hbc, h⟩⟩
            apply bc_add_vertex G v 2
            refine ⟨![{u0, u1}, {a, b}], ![{a, b, c}, {c}], ?_, ?_⟩
            · intro i x hx y hy
              fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue,
                Matrix.cons_val_zero, Matrix.cons_val_one, Finset.mem_insert,
                Finset.mem_singleton] at hx hy
              · have hyR : y ∈ ({u2, u3, u4} : Finset (Fin 6)) := by rw [hset]; simpa using hy
                rcases hx with rfl | rfl
                · exact hG0R y hyR
                · exact hG1R y hyR
              · subst hy
                rcases hx with rfl | rfl
                · exact hGac
                · exact hGbc
            · intro x y hxv hyv hxy
              have hne := G.ne_of_adj hxy
              have hpx : x = u0 ∨ x = u1 ∨ x = a ∨ x = b ∨ x = c := by
                rcases hpart6 x with rfl | rfl | rfl | rfl | rfl | rfl
                · exact absurd rfl hxv
                · exact Or.inl rfl
                · exact Or.inr (Or.inl rfl)
                all_goals
                  have : x ∈ ({a, b, c} : Finset (Fin 6)) := by rw [← hset]; simp
                  simp only [Finset.mem_insert, Finset.mem_singleton] at this
                  rcases this with h | h | h <;> simp [h]
              have hpy : y = u0 ∨ y = u1 ∨ y = a ∨ y = b ∨ y = c := by
                rcases hpart6 y with rfl | rfl | rfl | rfl | rfl | rfl
                · exact absurd rfl hyv
                · exact Or.inl rfl
                · exact Or.inr (Or.inl rfl)
                all_goals
                  have : y ∈ ({a, b, c} : Finset (Fin 6)) := by rw [← hset]; simp
                  simp only [Finset.mem_insert, Finset.mem_singleton] at this
                  rcases this with h | h | h <;> simp [h]
              rcases hpx with rfl | rfl | rfl | rfl | rfl <;>
              rcases hpy with rfl | rfl | rfl | rfl | rfl
              · exact absurd rfl hne
              · exact absurd hxy e01.2
              · exact ⟨0, Or.inl ⟨by simp, by simp⟩⟩
              · exact ⟨0, Or.inl ⟨by simp, by simp⟩⟩
              · exact ⟨0, Or.inl ⟨by simp, by simp⟩⟩
              · exact absurd hxy (hHsym _ _ e01).2
              · exact absurd rfl hne
              · exact ⟨0, Or.inl ⟨by simp, by simp⟩⟩
              · exact ⟨0, Or.inl ⟨by simp, by simp⟩⟩
              · exact ⟨0, Or.inl ⟨by simp, by simp⟩⟩
              · exact ⟨0, Or.inr ⟨by simp, by simp⟩⟩
              · exact ⟨0, Or.inr ⟨by simp, by simp⟩⟩
              · exact absurd rfl hne
              · exact absurd hxy eab.2
              · exact ⟨1, Or.inl ⟨by simp, by simp⟩⟩
              · exact ⟨0, Or.inr ⟨by simp, by simp⟩⟩
              · exact ⟨0, Or.inr ⟨by simp, by simp⟩⟩
              · exact absurd hxy (hHsym _ _ eab).2
              · exact absurd rfl hne
              · exact ⟨1, Or.inl ⟨by simp, by simp⟩⟩
              · exact ⟨0, Or.inr ⟨by simp, by simp⟩⟩
              · exact ⟨0, Or.inr ⟨by simp, by simp⟩⟩
              · exact ⟨1, Or.inr ⟨by simp, by simp⟩⟩
              · exact ⟨1, Or.inr ⟨by simp, by simp⟩⟩
              · exact absurd rfl hne
          by_cases h23H : HAdj u2 u3
          · exact h2K2 u2 u3 u4 hv2 hv3 hv4 h23 h24 h34 rfl h23H
          · by_cases h24H : HAdj u2 u4
            · exact h2K2 u2 u4 u3 hv2 hv4 hv3 h24 h23 h34.symm (by ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; exact ⟨fun h => by rcases h with rfl | rfl | rfl <;> simp, fun h => by rcases h with rfl | rfl | rfl <;> simp⟩) h24H
            · by_cases h34H : HAdj u3 u4
              · exact h2K2 u3 u4 u2 hv3 hv4 hv2 h34 h23.symm h24.symm (by ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; exact ⟨fun h => by rcases h with rfl | rfl | rfl <;> simp, fun h => by rcases h with rfl | rfl | rfl <;> simp⟩) h34H
              · have hG23 : G.Adj u2 u3 := by by_contra h; exact h23H ⟨h23, h⟩
                have hG24 : G.Adj u2 u4 := by by_contra h; exact h24H ⟨h24, h⟩
                have hG34 : G.Adj u3 u4 := by by_contra h; exact h34H ⟨h34, h⟩
                apply bc_add_vertex G v 2
                refine ⟨![{u0, u1, u2}, {u0, u1, u3}], ![{u3, u4}, {u2, u4}], ?_, ?_⟩
                · intro i x hx y hy
                  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue,
                    Matrix.cons_val_zero, Matrix.cons_val_one, Finset.mem_insert,
                    Finset.mem_singleton] at hx hy
                  · rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl
                    · exact hG0R _ (by simp)
                    · exact hG0R _ (by simp)
                    · exact hG1R _ (by simp)
                    · exact hG1R _ (by simp)
                    · exact hG23
                    · exact hG24
                  · rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl
                    · exact hG0R _ (by simp)
                    · exact hG0R _ (by simp)
                    · exact hG1R _ (by simp)
                    · exact hG1R _ (by simp)
                    · exact (G.adj_comm _ _).mp hG23
                    · exact hG34
                · intro x y hxv hyv hxy
                  have hne := G.ne_of_adj hxy
                  rcases hpart6 x with rfl | rfl | rfl | rfl | rfl | rfl
                  · exact absurd rfl hxv
                  · rcases hpart6 y with rfl | rfl | rfl | rfl | rfl | rfl
                    · exact absurd rfl hyv
                    · exact absurd rfl hne
                    · exact absurd hxy e01.2
                    · exact ⟨1, Or.inl ⟨by simp, by simp⟩⟩
                    · exact ⟨0, Or.inl ⟨by simp, by simp⟩⟩
                    · exact ⟨0, Or.inl ⟨by simp, by simp⟩⟩
                  · rcases hpart6 y with rfl | rfl | rfl | rfl | rfl | rfl
                    · exact absurd rfl hyv
                    · exact absurd hxy (hHsym _ _ e01).2
                    · exact absurd rfl hne
                    · exact ⟨1, Or.inl ⟨by simp, by simp⟩⟩
                    · exact ⟨0, Or.inl ⟨by simp, by simp⟩⟩
                    · exact ⟨0, Or.inl ⟨by simp, by simp⟩⟩
                  · rcases hpart6 y with rfl | rfl | rfl | rfl | rfl | rfl
                    · exact absurd rfl hyv
                    · exact ⟨1, Or.inr ⟨by simp, by simp⟩⟩
                    · exact ⟨1, Or.inr ⟨by simp, by simp⟩⟩
                    · exact absurd rfl hne
                    · exact ⟨0, Or.inl ⟨by simp, by simp⟩⟩
                    · exact ⟨0, Or.inl ⟨by simp, by simp⟩⟩
                  · rcases hpart6 y with rfl | rfl | rfl | rfl | rfl | rfl
                    · exact absurd rfl hyv
                    · exact ⟨0, Or.inr ⟨by simp, by simp⟩⟩
                    · exact ⟨0, Or.inr ⟨by simp, by simp⟩⟩
                    · exact ⟨0, Or.inr ⟨by simp, by simp⟩⟩
                    · exact absurd rfl hne
                    · exact ⟨1, Or.inl ⟨by simp, by simp⟩⟩
                  · rcases hpart6 y with rfl | rfl | rfl | rfl | rfl | rfl
                    · exact absurd rfl hyv
                    · exact ⟨0, Or.inr ⟨by simp, by simp⟩⟩
                    · exact ⟨0, Or.inr ⟨by simp, by simp⟩⟩
                    · exact ⟨0, Or.inr ⟨by simp, by simp⟩⟩
                    · exact ⟨1, Or.inr ⟨by simp, by simp⟩⟩
                    · exact absurd rfl hne

private lemma size_eq_3_fin6 (G : SimpleGraph (Fin 6)) (C : AndCountCircuit 6)
    (hfit : Fits G C) (hsz : C.size = 3) : HasBicliqueCover G 3 := by
  classical
  by_cases hα3 : ∃ S : Finset (Fin 6), S.card = 3 ∧ ∀ a ∈ S, ∀ b ∈ S, ¬ G.Adj a b
  · obtain ⟨S, hSc, hSind⟩ := hα3
    let T := Finset.univ \ S
    have hTc : T.card = 3 := by rw [Finset.card_sdiff]; simp [hSc]
    have hvc : ∀ a b : Fin 6, G.Adj a b → a ∈ T ∨ b ∈ T := by
      intro a b hab
      by_contra hboth
      push_neg at hboth
      have haS : a ∈ S := by
        have := hboth.1; simp only [T, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not] at this; exact this
      have hbS : b ∈ S := by
        have := hboth.2; simp only [T, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not] at this; exact this
      exact hSind a haS b hbS hab
    rw [← hTc]
    exact bc_of_vc G T hvc
  · -- alpha(G) <= 2, so H = G^c is triangle-free!
    let HAdj : Fin 6 → Fin 6 → Prop := fun a b => a ≠ b ∧ ¬ G.Adj a b
    have hHsym : ∀ a b, HAdj a b → HAdj b a := fun a b ⟨hne, hna⟩ =>
      ⟨hne.symm, fun h => hna ((G.adj_comm a b).mpr h)⟩
    have hTF : ∀ a b c : Fin 6, HAdj a b → HAdj b c → ¬ HAdj a c := by
      intro a b c hab hbc hac
      apply hα3
      refine ⟨{a, b, c}, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem (by simp [hab.1, hac.1]), Finset.card_pair hbc.1]
      · intro x hx y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
        rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
        · exact fun h => G.ne_of_adj h rfl
        · exact hab.2
        · exact hac.2
        · exact (hHsym _ _ hab).2
        · exact fun h => G.ne_of_adj h rfl
        · exact hbc.2
        · exact (hHsym _ _ hac).2
        · exact (hHsym _ _ hbc).2
        · exact fun h => G.ne_of_adj h rfl
    have hH_mis : ∀ a b : Fin 6, HAdj a b → IsMIS G {a, b} := by
      intro a b hab
      refine ⟨?_, ?_⟩
      · intro x hx y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
        · exact fun h => G.ne_of_adj h rfl
        · exact hab.2
        · exact (hHsym _ _ hab).2
        · exact fun h => G.ne_of_adj h rfl
      · intro u hu
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hu
        by_contra hno
        push_neg at hno
        have hua : ¬ G.Adj u a := hno a (by simp)
        have hub : ¬ G.Adj u b := hno b (by simp)
        exact hTF u a b ⟨hu.1, hua⟩ hab ⟨hu.2, hub⟩
    have hH_iso_mis : ∀ a : Fin 6, (∀ b : Fin 6, ¬ HAdj a b) → IsMIS G {a} := by
      intro a hiso
      refine ⟨fun x hx y hy => by rw [Finset.mem_singleton.mp hx, Finset.mem_singleton.mp hy]; exact fun h => G.ne_of_adj h rfl, ?_⟩
      intro u hu
      rw [Finset.mem_singleton] at hu
      refine ⟨a, by simp, ?_⟩
      by_contra hna
      exact hiso u ⟨fun h => hu h.symm, fun h => hna ((G.adj_comm u a).mpr h)⟩
    let degH : Fin 6 → ℕ := fun v => (Finset.univ.filter (fun u : Fin 6 => HAdj v u)).card
    have hdegH_mis : ∀ a : Fin 6, ∃ Sa : Finset (Finset (Fin 6)),
        (∀ I ∈ Sa, IsMIS G I ∧ a ∈ I) ∧ Sa.card = degH a := by
      intro a
      let N := Finset.univ.filter (fun u : Fin 6 => HAdj a u)
      refine ⟨N.image (fun u => {a, u}), ?_, ?_⟩
      · intro I hI
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hI
        exact ⟨hH_mis a u (Finset.mem_filter.mp hu).2, by simp⟩
      · apply Finset.card_image_of_injOn
        intro u hu v hv heq
        dsimp only at heq
        have hau : a ≠ u := (Finset.mem_filter.mp hu).2.1
        have hav : a ≠ v := (Finset.mem_filter.mp hv).2.1
        have hvmem : v ∈ ({a, u} : Finset (Fin 6)) := by rw [heq]; simp
        rcases Finset.mem_insert.mp hvmem with h1 | h2
        · exact absurd h1.symm hav
        · exact (Finset.mem_singleton.mp h2).symm
    let D3 : Finset (Fin 6) := Finset.univ.filter (fun v : Fin 6 => 3 ≤ degH v)
    by_cases hD3_ncl : ∃ a ∈ D3, ∃ b ∈ D3, a ≠ b ∧ ¬ HAdj a b
    · -- Case 1: two non-H-adjacent (i.e. G-adjacent) vertices a, b of deg_H >= 3!
      obtain ⟨a, haD, b, hbD, hab_ne, hab_nH⟩ := hD3_ncl
      have hab : G.Adj a b := by by_contra hna; exact hab_nH ⟨hab_ne, hna⟩
      have hnoI0 : ∀ I0 : Finset (Fin 6), IsMIS G I0 → a ∈ I0 ∨ b ∈ I0 := by
        intro I0 hI0
        by_contra hnot; push_neg at hnot
        obtain ⟨Sa, hSa, hSac⟩ := hdegH_mis a
        obtain ⟨Sb, hSb, hSbc⟩ := hdegH_mis b
        have h4 := two_deg3_kill hfit a b hab I0 hI0 hnot.1 hnot.2 Sa Sb hSa hSb
          (by rw [hSac]; exact (Finset.mem_filter.mp haD).2)
          (by rw [hSbc]; exact (Finset.mem_filter.mp hbD).2)
        omega
      let W : Finset (Fin 6) := Finset.univ \ {a, b}
      have hW4 : W.card = 4 := by rw [Finset.card_sdiff]; simp [Finset.card_pair hab_ne]
      have hW_K4 : ∀ x ∈ W, ∀ y ∈ W, x ≠ y → G.Adj x y := by
        intro x hx y hy hxy
        by_contra hna
        have hxab : x ≠ a ∧ x ≠ b := by simp only [W, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton, not_or] at hx; exact hx
        have hyab : y ≠ a ∧ y ≠ b := by simp only [W, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton, not_or] at hy; exact hy
        rcases hnoI0 {x, y} (hH_mis x y ⟨hxy, hna⟩) with h1 | h2
        · simp only [Finset.mem_insert, Finset.mem_singleton] at h1
          rcases h1 with rfl | rfl; exact hxab.1 rfl; exact hyab.1 rfl
        · simp only [Finset.mem_insert, Finset.mem_singleton] at h2
          rcases h2 with rfl | rfl; exact hxab.2 rfl; exact hyab.2 rfl
      have hW_hit : ∀ x ∈ W, HAdj a x ∨ HAdj b x := by
        intro x hx
        by_contra hno; push_neg at hno
        have hxab : x ≠ a ∧ x ≠ b := by simp only [W, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton, not_or] at hx; exact hx
        have hiso : ∀ y : Fin 6, ¬ HAdj x y := by
          intro y hxy
          by_cases hya : y = a
          · rw [hya] at hxy; exact hno.1 (hHsym _ _ hxy)
          · by_cases hyb : y = b
            · rw [hyb] at hxy; exact hno.2 (hHsym _ _ hxy)
            · have hyW : y ∈ W := Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, by simp [hya, hyb]⟩
              exact hxy.2 (hW_K4 x hx y hyW hxy.1)
        rcases hnoI0 {x} (hH_iso_mis x hiso) with h1 | h2
        · rw [Finset.mem_singleton] at h1; exact hxab.1 h1.symm
        · rw [Finset.mem_singleton] at h2; exact hxab.2 h2.symm
      -- Every vertex in W is G-adjacent to at most one of a, b, and each of a, b has at most 1 G-neighbor in W!
      let Na := W.filter (fun x => G.Adj a x)
      let Nb := W.filter (fun x => G.Adj b x)
      have hNa_le1 : Na.card ≤ 1 := by
        have hHa : Finset.univ.filter (fun u => HAdj a u) = W \ Na := by
          ext u
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, W, Na,
            Finset.mem_insert, Finset.mem_singleton, not_or, not_and]
          constructor
          · rintro ⟨hau, hna⟩
            have hbu : u ≠ b := fun h => hab_nH (h ▸ ⟨hau, hna⟩)
            exact ⟨⟨hau.symm, hbu⟩, fun _ => hna⟩
          · rintro ⟨⟨hua, hub⟩, hna⟩
            exact ⟨fun h => hua h.symm, fun h => hna ⟨hua, hub⟩ h⟩
        have hda : 3 ≤ degH a := (Finset.mem_filter.mp haD).2
        have hsub : Na ⊆ W := Finset.filter_subset _ _
        have hsum := Finset.card_sdiff_add_card_eq_card hsub
        have : (W \ Na).card = degH a := by rw [← hHa]
        omega
      have hNb_le1 : Nb.card ≤ 1 := by
        have hHb : Finset.univ.filter (fun u => HAdj b u) = W \ Nb := by
          ext u
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, W, Nb,
            Finset.mem_insert, Finset.mem_singleton, not_or, not_and]
          constructor
          · rintro ⟨hbu, hna⟩
            have hau : u ≠ a := fun h => hab_nH (hHsym _ _ (h ▸ ⟨hbu, hna⟩))
            exact ⟨⟨hau, hbu.symm⟩, fun _ => hna⟩
          · rintro ⟨⟨hua, hub⟩, hna⟩
            exact ⟨fun h => hub h.symm, fun h => hna ⟨hua, hub⟩ h⟩
        have hdb : 3 ≤ degH b := (Finset.mem_filter.mp hbD).2
        have hsub : Nb ⊆ W := Finset.filter_subset _ _
        have hsum := Finset.card_sdiff_add_card_eq_card hsub
        have : (W \ Nb).card = degH b := by rw [← hHb]
        omega
      have hdisjNab : Disjoint Na Nb := by
        rw [Finset.disjoint_left]
        intro x hxa hxb
        have hxW := (Finset.mem_filter.mp hxa).1
        rcases hW_hit x hxW with h1 | h2
        · exact h1.2 (Finset.mem_filter.mp hxa).2
        · exact h2.2 (Finset.mem_filter.mp hxb).2
      -- Pick w1, w2, w3, w4 in W such that Na <= {w1} and Nb <= {w2}
      have hex_w12 : ∃ w1 ∈ W, ∃ w2 ∈ W, w1 ≠ w2 ∧ Na ⊆ {w1} ∧ Nb ⊆ {w2} := by
        have hNa_pick : ∃ w1 ∈ W, Na ⊆ {w1} ∧ w1 ∉ Nb := by
          by_cases hne : Na.Nonempty
          · obtain ⟨w1, hw1⟩ := hne
            have h1c : Na.card = 1 := le_antisymm hNa_le1 (Finset.card_pos.mpr ⟨w1, hw1⟩)
            have h1eq : Na = {w1} := (Finset.card_eq_one.mp h1c).elim
              fun y hy => by rw [hy] at hw1 ⊢; rw [Finset.mem_singleton.mp hw1]
            exact ⟨w1, (Finset.mem_filter.mp hw1).1, by rw [h1eq], Finset.disjoint_left.mp hdisjNab hw1⟩
          · rw [Finset.not_nonempty_iff_eq_empty] at hne
            have hWnb : (W \ Nb).Nonempty := by
              apply Finset.card_pos.mp
              have := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset (fun x => G.Adj b x) W)
              change (W \ Nb).card + Nb.card = W.card at this
              omega
            obtain ⟨w1, hw1⟩ := hWnb
            exact ⟨w1, (Finset.mem_sdiff.mp hw1).1, by rw [hne]; simp, (Finset.mem_sdiff.mp hw1).2⟩
        obtain ⟨w1, hw1W, hNa1, hw1nNb⟩ := hNa_pick
        by_cases hne : Nb.Nonempty
        · obtain ⟨w2, hw2⟩ := hne
          have h2c : Nb.card = 1 := le_antisymm hNb_le1 (Finset.card_pos.mpr ⟨w2, hw2⟩)
          have h2eq : Nb = {w2} := (Finset.card_eq_one.mp h2c).elim
            fun y hy => by rw [hy] at hw2 ⊢; rw [Finset.mem_singleton.mp hw2]
          exact ⟨w1, hw1W, w2, (Finset.mem_filter.mp hw2).1, fun he => hw1nNb (he ▸ hw2), hNa1, by rw [h2eq]⟩
        · rw [Finset.not_nonempty_iff_eq_empty] at hne
          have hW1 : (W.erase w1).Nonempty := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hw1W, hW4]; omega)
          obtain ⟨w2, hw2⟩ := hW1
          exact ⟨w1, hw1W, w2, (Finset.mem_erase.mp hw2).2, (Finset.mem_erase.mp hw2).1.symm, hNa1, by rw [hne]; simp⟩
      obtain ⟨w1, hw1W, w2, hw2W, hw12, hNa1, hNb2⟩ := hex_w12
      have hWrem : ((W.erase w1).erase w2).card = 2 := by
        rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hw12.symm, hw2W⟩),
            Finset.card_erase_of_mem hw1W, hW4]
      obtain ⟨w3, w4, hw34, hWeq⟩ := Finset.card_eq_two.mp hWrem
      have hw3W : w3 ∈ W := (Finset.mem_erase.mp (Finset.mem_erase.mp (by rw [hWeq]; simp : w3 ∈ _)).2).2
      have hw4W : w4 ∈ W := (Finset.mem_erase.mp (Finset.mem_erase.mp (by rw [hWeq]; simp : w4 ∈ _)).2).2
      have hw13 : w1 ≠ w3 := (Finset.mem_erase.mp (Finset.mem_erase.mp (by rw [hWeq]; simp : w3 ∈ _)).2).1.symm
      have hw14 : w1 ≠ w4 := (Finset.mem_erase.mp (Finset.mem_erase.mp (by rw [hWeq]; simp : w4 ∈ _)).2).1.symm
      have hw23 : w2 ≠ w3 := (Finset.mem_erase.mp (by rw [hWeq]; simp : w3 ∈ _)).1.symm
      have hw24 : w2 ≠ w4 := (Finset.mem_erase.mp (by rw [hWeq]; simp : w4 ∈ _)).1.symm
      have hW_all : ∀ x ∈ W, x = w1 ∨ x = w2 ∨ x = w3 ∨ x = w4 := by
        intro x hx
        by_cases h1 : x = w1
        · exact Or.inl h1
        · by_cases h2 : x = w2
          · exact Or.inr (Or.inl h2)
          · have : x ∈ ({w3, w4} : Finset (Fin 6)) := by
              rw [← hWeq]; exact Finset.mem_erase.mpr ⟨h2, Finset.mem_erase.mpr ⟨h1, hx⟩⟩
            rcases Finset.mem_insert.mp this with rfl | h4
            · exact Or.inr (Or.inr (Or.inl rfl))
            · exact Or.inr (Or.inr (Or.inr (Finset.mem_singleton.mp h4)))
      have hpart6 : ∀ z : Fin 6, z = a ∨ z = b ∨ z ∈ W := fun z => by
        by_cases h1 : z = a
        · exact Or.inl h1
        · by_cases h2 : z = b
          · exact Or.inr (Or.inl h2)
          · exact Or.inr (Or.inr (Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, by simp [h1, h2]⟩))
      by_cases hboth : G.Adj a w1 ∧ G.Adj b w2
      · obtain ⟨haw1, hbw2⟩ := hboth
        refine ⟨![{w1, w2}, {a, w2}, {w3}], ![{w3, w4}, {b, w1}, {w4}], ?_, ?_⟩
        · intro i x hx y hy
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
            Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Finset.mem_insert,
            Finset.mem_singleton] at hx hy
          · rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
            · exact hW_K4 _ hw1W _ hw3W hw13
            · exact hW_K4 _ hw1W _ hw4W hw14
            · exact hW_K4 _ hw2W _ hw3W hw23
            · exact hW_K4 _ hw2W _ hw4W hw24
          · rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
            · exact hab
            · exact haw1
            · exact (G.adj_comm _ _).mp hbw2
            · exact hW_K4 _ hw2W _ hw1W hw12.symm
          · rw [hx, hy]; exact hW_K4 _ hw3W _ hw4W hw34
        · intro x y hxy
          have hne := G.ne_of_adj hxy
          rcases hpart6 x with rfl | rfl | hxW <;> rcases hpart6 y with rfl | rfl | hyW
          · exact absurd rfl hne
          · exact ⟨1, Or.inl ⟨by simp, by simp⟩⟩
          · have hy1 : y = w1 := Finset.mem_singleton.mp (hNa1 (Finset.mem_filter.mpr ⟨hyW, hxy⟩))
            subst hy1; exact ⟨1, Or.inl ⟨by simp, by simp⟩⟩
          · exact ⟨1, Or.inr ⟨by simp, by simp⟩⟩
          · exact absurd rfl hne
          · have hy2 : y = w2 := Finset.mem_singleton.mp (hNb2 (Finset.mem_filter.mpr ⟨hyW, hxy⟩))
            subst hy2; exact ⟨1, Or.inr ⟨by simp, by simp⟩⟩
          · have hx1 : x = w1 := Finset.mem_singleton.mp (hNa1 (Finset.mem_filter.mpr ⟨hxW, (G.adj_comm _ _).mpr hxy⟩))
            subst hx1; exact ⟨1, Or.inr ⟨by simp, by simp⟩⟩
          · have hx2 : x = w2 := Finset.mem_singleton.mp (hNb2 (Finset.mem_filter.mpr ⟨hxW, (G.adj_comm _ _).mpr hxy⟩))
            subst hx2; exact ⟨1, Or.inl ⟨by simp, by simp⟩⟩
          · rcases hW_all x hxW with rfl | rfl | rfl | rfl <;> rcases hW_all y hyW with rfl | rfl | rfl | rfl
            · exact absurd rfl hne
            · exact ⟨1, Or.inr ⟨by simp, by simp⟩⟩
            · exact ⟨0, Or.inl ⟨by simp, by simp⟩⟩
            · exact ⟨0, Or.inl ⟨by simp, by simp⟩⟩
            · exact ⟨1, Or.inl ⟨by simp, by simp⟩⟩
            · exact absurd rfl hne
            · exact ⟨0, Or.inl ⟨by simp, by simp⟩⟩
            · exact ⟨0, Or.inl ⟨by simp, by simp⟩⟩
            · exact ⟨0, Or.inr ⟨by simp, by simp⟩⟩
            · exact ⟨0, Or.inr ⟨by simp, by simp⟩⟩
            · exact absurd rfl hne
            · exact ⟨2, Or.inl ⟨by simp, by simp⟩⟩
            · exact ⟨0, Or.inr ⟨by simp, by simp⟩⟩
            · exact ⟨0, Or.inr ⟨by simp, by simp⟩⟩
            · exact ⟨2, Or.inr ⟨by simp, by simp⟩⟩
            · exact absurd rfl hne
      · by_cases haw1 : G.Adj a w1
        · have hnbw2 : ¬ G.Adj b w2 := fun h => hboth ⟨haw1, h⟩
          have hNb_empty : ∀ z ∈ W, ¬ G.Adj b z := fun z hz hbz =>
            hnbw2 (Finset.mem_singleton.mp (hNb2 (Finset.mem_filter.mpr ⟨hz, hbz⟩)) ▸ hbz)
          refine ⟨![{w1, w2}, {w1, w3}, {a}], ![{w3, w4}, {w2, w4}, {b, w1}], ?_, ?_⟩
          · intro i x hx y hy
            fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
              Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Finset.mem_insert,
              Finset.mem_singleton] at hx hy
            · rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
              · exact hW_K4 _ hw1W _ hw3W hw13
              · exact hW_K4 _ hw1W _ hw4W hw14
              · exact hW_K4 _ hw2W _ hw3W hw23
              · exact hW_K4 _ hw2W _ hw4W hw24
            · rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
              · exact hW_K4 _ hw1W _ hw2W hw12
              · exact hW_K4 _ hw1W _ hw4W hw14
              · exact hW_K4 _ hw3W _ hw2W hw23.symm
              · exact hW_K4 _ hw3W _ hw4W hw34
            · rw [hx]; rcases hy with rfl | rfl
              · exact hab
              · exact haw1
          · intro x y hxy
            have hne := G.ne_of_adj hxy
            rcases hpart6 x with rfl | rfl | hxW <;> rcases hpart6 y with rfl | rfl | hyW
            · exact absurd rfl hne
            · exact ⟨2, Or.inl ⟨by simp, by simp⟩⟩
            · have hy1 : y = w1 := Finset.mem_singleton.mp (hNa1 (Finset.mem_filter.mpr ⟨hyW, hxy⟩))
              subst hy1; exact ⟨2, Or.inl ⟨by simp, by simp⟩⟩
            · exact ⟨2, Or.inr ⟨by simp, by simp⟩⟩
            · exact absurd rfl hne
            · exact absurd hxy (hNb_empty y hyW)
            · have hx1 : x = w1 := Finset.mem_singleton.mp (hNa1 (Finset.mem_filter.mpr ⟨hxW, (G.adj_comm _ _).mpr hxy⟩))
              subst hx1; exact ⟨2, Or.inr ⟨by simp, by simp⟩⟩
            · exact absurd ((G.adj_comm _ _).mpr hxy) (hNb_empty x hxW)
            · rcases hW_all x hxW with rfl | rfl | rfl | rfl <;> rcases hW_all y hyW with rfl | rfl | rfl | rfl
              · exact absurd rfl hne
              · exact ⟨1, Or.inl ⟨by simp, by simp⟩⟩
              · exact ⟨0, Or.inl ⟨by simp, by simp⟩⟩
              · exact ⟨0, Or.inl ⟨by simp, by simp⟩⟩
              · exact ⟨1, Or.inr ⟨by simp, by simp⟩⟩
              · exact absurd rfl hne
              · exact ⟨0, Or.inl ⟨by simp, by simp⟩⟩
              · exact ⟨0, Or.inl ⟨by simp, by simp⟩⟩
              · exact ⟨0, Or.inr ⟨by simp, by simp⟩⟩
              · exact ⟨0, Or.inr ⟨by simp, by simp⟩⟩
              · exact absurd rfl hne
              · exact ⟨1, Or.inl ⟨by simp, by simp⟩⟩
              · exact ⟨0, Or.inr ⟨by simp, by simp⟩⟩
              · exact ⟨0, Or.inr ⟨by simp, by simp⟩⟩
              · exact ⟨1, Or.inr ⟨by simp, by simp⟩⟩
              · exact absurd rfl hne
        · have hNa_empty : ∀ z ∈ W, ¬ G.Adj a z := fun z hz haz =>
            haw1 (Finset.mem_singleton.mp (hNa1 (Finset.mem_filter.mpr ⟨hz, haz⟩)) ▸ haz)
          let Y2 : Finset (Fin 6) := insert a (if G.Adj b w2 then {w2} else ∅)
          refine ⟨![{w1, w2}, {w1, w3}, {b}], ![{w3, w4}, {w2, w4}, Y2], ?_, ?_⟩
          · intro i x hx y hy
            fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
              Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Finset.mem_insert,
              Finset.mem_singleton] at hx hy
            · rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
              · exact hW_K4 _ hw1W _ hw3W hw13
              · exact hW_K4 _ hw1W _ hw4W hw14
              · exact hW_K4 _ hw2W _ hw3W hw23
              · exact hW_K4 _ hw2W _ hw4W hw24
            · rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
              · exact hW_K4 _ hw1W _ hw2W hw12
              · exact hW_K4 _ hw1W _ hw4W hw14
              · exact hW_K4 _ hw3W _ hw2W hw23.symm
              · exact hW_K4 _ hw3W _ hw4W hw34
            · rw [hx]
              rcases Finset.mem_insert.mp hy with rfl | hy'
              · exact (G.adj_comm _ _).mp hab
              · split_ifs at hy' with h2
                · rw [Finset.mem_singleton.mp hy']; exact h2
                · exact absurd hy' (Finset.notMem_empty _)
          · intro x y hxy
            have hne := G.ne_of_adj hxy
            rcases hpart6 x with rfl | rfl | hxW <;> rcases hpart6 y with rfl | rfl | hyW
            · exact absurd rfl hne
            · exact ⟨2, Or.inr ⟨by simp, Finset.mem_insert_self _ _⟩⟩
            · exact absurd hxy (hNa_empty y hyW)
            · exact ⟨2, Or.inl ⟨by simp, Finset.mem_insert_self _ _⟩⟩
            · exact absurd rfl hne
            · have hy2 : y = w2 := Finset.mem_singleton.mp (hNb2 (Finset.mem_filter.mpr ⟨hyW, hxy⟩))
              subst hy2
              exact ⟨2, Or.inl ⟨by simp, Finset.mem_insert_of_mem (by simp [hxy])⟩⟩
            · exact absurd ((G.adj_comm _ _).mpr hxy) (hNa_empty x hxW)
            · have hx2 : x = w2 := Finset.mem_singleton.mp (hNb2 (Finset.mem_filter.mpr ⟨hxW, (G.adj_comm _ _).mpr hxy⟩))
              subst hx2
              exact ⟨2, Or.inr ⟨by simp, Finset.mem_insert_of_mem (by simp [(G.adj_comm _ _).mpr hxy])⟩⟩
            · rcases hW_all x hxW with rfl | rfl | rfl | rfl <;> rcases hW_all y hyW with rfl | rfl | rfl | rfl
              · exact absurd rfl hne
              · exact ⟨1, Or.inl ⟨by simp, by simp⟩⟩
              · exact ⟨0, Or.inl ⟨by simp, by simp⟩⟩
              · exact ⟨0, Or.inl ⟨by simp, by simp⟩⟩
              · exact ⟨1, Or.inr ⟨by simp, by simp⟩⟩
              · exact absurd rfl hne
              · exact ⟨0, Or.inl ⟨by simp, by simp⟩⟩
              · exact ⟨0, Or.inl ⟨by simp, by simp⟩⟩
              · exact ⟨0, Or.inr ⟨by simp, by simp⟩⟩
              · exact ⟨0, Or.inr ⟨by simp, by simp⟩⟩
              · exact absurd rfl hne
              · exact ⟨1, Or.inl ⟨by simp, by simp⟩⟩
              · exact ⟨0, Or.inr ⟨by simp, by simp⟩⟩
              · exact ⟨0, Or.inr ⟨by simp, by simp⟩⟩
              · exact ⟨1, Or.inr ⟨by simp, by simp⟩⟩
              · exact absurd rfl hne
    · -- Case 2: D3 is a clique in H => D3.card <= 2!
      push_neg at hD3_ncl
      have hD3_le2 : D3.card ≤ 2 := by
        by_contra hgt
        obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < D3.card)
        obtain ⟨b, hb⟩ := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem ha]; omega : 0 < (D3.erase a).card)
        obtain ⟨c, hc⟩ := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hb, Finset.card_erase_of_mem ha]; omega : 0 < ((D3.erase a).erase b).card)
        have hbD := (Finset.mem_erase.mp hb).2
        have hab : a ≠ b := (Finset.mem_erase.mp hb).1.symm
        have hcD := (Finset.mem_erase.mp (Finset.mem_erase.mp hc).2).2
        have hac : a ≠ c := (Finset.mem_erase.mp (Finset.mem_erase.mp hc).2).1.symm
        have hbc : b ≠ c := (Finset.mem_erase.mp hc).1.symm
        exact hTF a b c (hD3_ncl a ha b hbD hab) (hD3_ncl b hbD c hcD hbc) (hD3_ncl a ha c hcD hac)
      by_cases hD3_2 : D3.card = 2
      · -- Case 2a: D3 = {a, b} with HAdj a b!
        obtain ⟨a, b, hab_ne, hD3eq⟩ := Finset.card_eq_two.mp hD3_2
        have haD : a ∈ D3 := by rw [hD3eq]; simp
        have hbD : b ∈ D3 := by rw [hD3eq]; simp
        have habH : HAdj a b := hD3_ncl a haD b hbD hab_ne
        let A := (Finset.univ.filter (fun u : Fin 6 => HAdj a u)).erase b
        let B := (Finset.univ.filter (fun u : Fin 6 => HAdj b u)).erase a
        have hdisjAB : Disjoint A B := by
          rw [Finset.disjoint_left]
          intro x hxA hxB
          exact hTF a b x habH (Finset.mem_filter.mp (Finset.mem_erase.mp hxB).2).2
            (Finset.mem_filter.mp (Finset.mem_erase.mp hxA).2).2
        have ha_nA : a ∉ A := fun h => (Finset.mem_filter.mp (Finset.mem_erase.mp h).2).2.1 rfl
        have hb_nA : b ∉ A := Finset.notMem_erase b _
        have ha_nB : a ∉ B := Finset.notMem_erase a _
        have hb_nB : b ∉ B := fun h => (Finset.mem_filter.mp (Finset.mem_erase.mp h).2).2.1 rfl
        have hA_ge2 : 2 ≤ A.card := by
          have hbNa : b ∈ Finset.univ.filter (fun u : Fin 6 => HAdj a u) := Finset.mem_filter.mpr ⟨Finset.mem_univ b, habH⟩
          have := Finset.card_erase_add_one hbNa
          have hda : 3 ≤ degH a := (Finset.mem_filter.mp haD).2
          change A.card + 1 = degH a at this
          omega
        have hB_ge2 : 2 ≤ B.card := by
          have haNb : a ∈ Finset.univ.filter (fun u : Fin 6 => HAdj b u) := Finset.mem_filter.mpr ⟨Finset.mem_univ a, hHsym _ _ habH⟩
          have := Finset.card_erase_add_one haNb
          have hdb : 3 ≤ degH b := (Finset.mem_filter.mp hbD).2
          change B.card + 1 = degH b at this
          omega
        have hAB_le4 : A.card + B.card ≤ 4 := by
          have hsub : A ∪ B ⊆ Finset.univ \ {a, b} := by
            intro x hx
            refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, ?_⟩
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            rcases Finset.mem_union.mp hx with h | h
            · exact ⟨fun he => ha_nA (he ▸ h), fun he => hb_nA (he ▸ h)⟩
            · exact ⟨fun he => ha_nB (he ▸ h), fun he => hb_nB (he ▸ h)⟩
          have h1 := Finset.card_le_card hsub
          rw [Finset.card_union_of_disjoint hdisjAB, Finset.card_sdiff] at h1
          simp [Finset.card_pair hab_ne] at h1
          exact h1
        have hA2 : A.card = 2 := by omega
        have hB2 : B.card = 2 := by omega
        obtain ⟨a1, a2, ha12, hAeq⟩ := Finset.card_eq_two.mp hA2
        obtain ⟨b1, b2, hb12, hBeq⟩ := Finset.card_eq_two.mp hB2
        have hpart6 : ∀ x : Fin 6, x = a ∨ x = b ∨ x = a1 ∨ x = a2 ∨ x = b1 ∨ x = b2 := by
          intro x
          have huniv : ({a, b} ∪ (A ∪ B) : Finset (Fin 6)) = Finset.univ := by
            apply Finset.eq_univ_of_card
            have hd1 : Disjoint ({a, b} : Finset (Fin 6)) (A ∪ B) := by
              rw [Finset.disjoint_left]; intro z hz hz2
              simp only [Finset.mem_insert, Finset.mem_singleton] at hz
              rcases Finset.mem_union.mp hz2 with h | h <;> rcases hz with rfl | rfl
              · exact ha_nA h
              · exact hb_nA h
              · exact ha_nB h
              · exact hb_nB h
            rw [Finset.card_union_of_disjoint hd1, Finset.card_union_of_disjoint hdisjAB,
                Finset.card_pair hab_ne, hA2, hB2]
            decide
          have hx : x ∈ ({a, b} ∪ (A ∪ B) : Finset (Fin 6)) := by rw [huniv]; exact Finset.mem_univ x
          rw [hAeq, hBeq] at hx
          simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hx
          tauto
        have ha1A : a1 ∈ A := by rw [hAeq]; simp
        have ha2A : a2 ∈ A := by rw [hAeq]; simp
        have hb1B : b1 ∈ B := by rw [hBeq]; simp
        have hb2B : b2 ∈ B := by rw [hBeq]; simp
        have hH_a : ∀ x ∈ A, HAdj a x := fun x hx => (Finset.mem_filter.mp (Finset.mem_erase.mp hx).2).2
        have hH_b : ∀ y ∈ B, HAdj b y := fun y hy => (Finset.mem_filter.mp (Finset.mem_erase.mp hy).2).2
        -- A is a G-edge, B is a G-edge, a-B are G-edges, b-A are G-edges!
        have hGa12 : G.Adj a1 a2 := by by_contra hna; exact hTF a a1 a2 (hH_a a1 ha1A) ⟨ha12, hna⟩ (hH_a a2 ha2A)
        have hGb12 : G.Adj b1 b2 := by by_contra hna; exact hTF b b1 b2 (hH_b b1 hb1B) ⟨hb12, hna⟩ (hH_b b2 hb2B)
        have hGaB : ∀ y ∈ B, G.Adj a y := fun y hy => by
          by_contra hna
          exact hTF a b y habH (hH_b y hy) ⟨fun he => ha_nB (he ▸ hy), hna⟩
        have hGbA : ∀ x ∈ A, G.Adj b x := fun x hx => by
          by_contra hna
          exact hTF b a x (hHsym _ _ habH) (hH_a x hx) ⟨fun he => hb_nA (he ▸ hx), hna⟩
        -- Each x in A has deg_H x <= 2 (since x not in D3), already has H-edge to a, so at most 1 H-edge to B!
        have hdeg_le2_A : ∀ x ∈ A, degH x ≤ 2 := fun x hx => by
          by_contra hge
          have hxD : x ∈ D3 := Finset.mem_filter.mpr ⟨Finset.mem_univ x, by omega⟩
          rw [hD3eq] at hxD; rcases Finset.mem_insert.mp hxD with rfl | h2
          · exact ha_nA hx
          · rw [Finset.mem_singleton.mp h2] at hx; exact hb_nA hx
        have hdeg_le2_B : ∀ y ∈ B, degH y ≤ 2 := fun y hy => by
          by_contra hge
          have hyD : y ∈ D3 := Finset.mem_filter.mpr ⟨Finset.mem_univ y, by omega⟩
          rw [hD3eq] at hyD; rcases Finset.mem_insert.mp hyD with rfl | h2
          · exact ha_nB hy
          · rw [Finset.mem_singleton.mp h2] at hy; exact hb_nB hy
        have hA_atmost1 : ∀ x ∈ A, G.Adj x b1 ∨ G.Adj x b2 := by
          intro x hx
          by_contra hno; push_neg at hno
          have hsub : ({a, b1, b2} : Finset (Fin 6)) ⊆ Finset.univ.filter (fun u => HAdj x u) := by
            intro u hu; simp only [Finset.mem_insert, Finset.mem_singleton] at hu
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ u, ?_⟩
            rcases hu with rfl | rfl | rfl
            · exact hHsym _ _ (hH_a x hx)
            · exact ⟨fun he => Finset.disjoint_left.mp hdisjAB hx (he ▸ hb1B), hno.1⟩
            · exact ⟨fun he => Finset.disjoint_left.mp hdisjAB hx (he ▸ hb2B), hno.2⟩
          have hc := Finset.card_le_card hsub
          have ha_n1 : a ≠ b1 := fun he => ha_nB (he ▸ hb1B)
          have ha_n2 : a ≠ b2 := fun he => ha_nB (he ▸ hb2B)
          rw [Finset.card_insert_of_notMem (by simp [ha_n1, ha_n2]),
              Finset.card_pair hb12] at hc
          have := hdeg_le2_A x hx; change _ ≤ degH x at hc; omega
        have hB_atmost1 : ∀ y ∈ B, G.Adj a1 y ∨ G.Adj a2 y := by
          intro y hy
          by_contra hno; push_neg at hno
          have hsub : ({b, a1, a2} : Finset (Fin 6)) ⊆ Finset.univ.filter (fun u => HAdj y u) := by
            intro u hu; simp only [Finset.mem_insert, Finset.mem_singleton] at hu
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ u, ?_⟩
            rcases hu with rfl | rfl | rfl
            · exact hHsym _ _ (hH_b y hy)
            · exact ⟨fun he => Finset.disjoint_right.mp hdisjAB hy (he ▸ ha1A), fun h => hno.1 ((G.adj_comm _ _).mpr h)⟩
            · exact ⟨fun he => Finset.disjoint_right.mp hdisjAB hy (he ▸ ha2A), fun h => hno.2 ((G.adj_comm _ _).mpr h)⟩
          have hc := Finset.card_le_card hsub
          have hb_n1 : b ≠ a1 := fun he => hb_nA (he ▸ ha1A)
          have hb_n2 : b ≠ a2 := fun he => hb_nA (he ▸ ha2A)
          rw [Finset.card_insert_of_notMem (by simp [hb_n1, hb_n2]),
              Finset.card_pair ha12] at hc
          have := hdeg_le2_B y hy; change _ ≤ degH y at hc; omega
        -- Pick ordering (q1, q2) of {b1, b2} such that G.Adj a1 q2 and G.Adj a2 q1!
        have hex_q : ∃ q1 q2 : Fin 6, q1 ∈ B ∧ q2 ∈ B ∧ q1 ≠ q2 ∧ (∀ y ∈ B, y = q1 ∨ y = q2) ∧
            G.Adj a1 q2 ∧ G.Adj a2 q1 := by
          by_cases h1 : G.Adj a1 b2 ∧ G.Adj a2 b1
          · exact ⟨b1, b2, hb1B, hb2B, hb12, fun y hy => by rw [hBeq] at hy; simpa using hy, h1.1, h1.2⟩
          · refine ⟨b2, b1, hb2B, hb1B, hb12.symm, fun y hy => by rw [hBeq] at hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy; tauto, ?_, ?_⟩
            · by_cases h12' : G.Adj a1 b2
              · have h21' : ¬ G.Adj a2 b1 := fun h => h1 ⟨h12', h⟩
                exact (hB_atmost1 b1 hb1B).resolve_right h21'
              · exact (hA_atmost1 a1 ha1A).resolve_right h12'
            · by_cases h12' : G.Adj a1 b2
              · have h21' : ¬ G.Adj a2 b1 := fun h => h1 ⟨h12', h⟩
                exact (hA_atmost1 a2 ha2A).resolve_left h21'
              · exact (hB_atmost1 b2 hb2B).resolve_left h12'
        obtain ⟨q1, q2, hq1B, hq2B, hq12, hBq, hGa1q2, hGa2q1⟩ := hex_q
        have hGq12 : G.Adj q1 q2 := by
          by_contra hna; exact hTF b q1 q2 (hH_b q1 hq1B) ⟨hq12, hna⟩ (hH_b q2 hq2B)
        let X2 : Finset (Fin 6) := insert a (if G.Adj a1 q1 then {a1} else ∅)
        let X3 : Finset (Fin 6) := insert b (if G.Adj a2 q2 then {q2} else ∅)
        refine ⟨![{a1, q1}, X2, X3], ![{a2, q2}, {q1, q2}, {a1, a2}], ?_, ?_⟩
        · intro i x hx y hy
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
            Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Finset.mem_insert,
            Finset.mem_singleton] at hx hy
          · rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
            · exact hGa12
            · exact hGa1q2
            · exact (G.adj_comm _ _).mp hGa2q1
            · exact hGq12
          · rcases Finset.mem_insert.mp hx with rfl | hx'
            · rcases hy with rfl | rfl
              · exact hGaB _ hq1B
              · exact hGaB _ hq2B
            · split_ifs at hx' with h11
              · rw [Finset.mem_singleton.mp hx']
                rcases hy with rfl | rfl
                · exact h11
                · exact hGa1q2
              · exact absurd hx' (Finset.notMem_empty _)
          · rcases Finset.mem_insert.mp hx with rfl | hx'
            · rcases hy with rfl | rfl
              · exact hGbA _ ha1A
              · exact hGbA _ ha2A
            · split_ifs at hx' with h22
              · rw [Finset.mem_singleton.mp hx']
                rcases hy with rfl | rfl
                · exact (G.adj_comm _ _).mp hGa1q2
                · exact (G.adj_comm _ _).mp h22
              · exact absurd hx' (Finset.notMem_empty _)
        · intro x y hxy
          have hne := G.ne_of_adj hxy
          have hpartQ : ∀ z : Fin 6, z = a ∨ z = b ∨ z = a1 ∨ z = a2 ∨ z = q1 ∨ z = q2 := by
            intro z
            rcases hpart6 z with rfl | rfl | rfl | rfl | hzb1 | hzb2
            · exact Or.inl rfl
            · exact Or.inr (Or.inl rfl)
            · exact Or.inr (Or.inr (Or.inl rfl))
            · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
            · rcases hBq b1 hb1B with h | h <;> rw [hzb1, h] <;> simp
            · rcases hBq b2 hb2B with h | h <;> rw [hzb2, h] <;> simp
          rcases hpartQ x with hx | hx | hx | hx | hx | hx <;>
          rcases hpartQ y with hy | hy | hy | hy | hy | hy <;>
          subst hx hy
          · exact absurd rfl hne
          · exact absurd hxy habH.2
          · exact absurd hxy (hH_a _ ha1A).2
          · exact absurd hxy (hH_a _ ha2A).2
          · exact ⟨1, Or.inl ⟨Finset.mem_insert_self _ _, by simp⟩⟩
          · exact ⟨1, Or.inl ⟨Finset.mem_insert_self _ _, by simp⟩⟩
          · exact absurd hxy (hHsym _ _ habH).2
          · exact absurd rfl hne
          · exact ⟨2, Or.inl ⟨Finset.mem_insert_self _ _, by simp⟩⟩
          · exact ⟨2, Or.inl ⟨Finset.mem_insert_self _ _, by simp⟩⟩
          · exact absurd hxy (hH_b _ hq1B).2
          · exact absurd hxy (hH_b _ hq2B).2
          · exact absurd hxy (hHsym _ _ (hH_a _ ha1A)).2
          · exact ⟨2, Or.inr ⟨Finset.mem_insert_self _ _, by simp⟩⟩
          · exact absurd rfl hne
          · exact ⟨0, Or.inl ⟨by simp, by simp⟩⟩
          · exact ⟨1, Or.inl ⟨Finset.mem_insert_of_mem (by simp [hxy]), by simp⟩⟩
          · exact ⟨0, Or.inl ⟨by simp, by simp⟩⟩
          · exact absurd hxy (hHsym _ _ (hH_a _ ha2A)).2
          · exact ⟨2, Or.inr ⟨Finset.mem_insert_self _ _, by simp⟩⟩
          · exact ⟨0, Or.inr ⟨by simp, by simp⟩⟩
          · exact absurd rfl hne
          · exact ⟨0, Or.inr ⟨by simp, by simp⟩⟩
          · exact ⟨2, Or.inr ⟨Finset.mem_insert_of_mem (by simp [hxy]), by simp⟩⟩
          · exact ⟨1, Or.inr ⟨Finset.mem_insert_self _ _, by simp⟩⟩
          · exact absurd hxy (hHsym _ _ (hH_b _ hq1B)).2
          · exact ⟨1, Or.inr ⟨Finset.mem_insert_of_mem (by simp [(G.adj_comm _ _).mp hxy]), by simp⟩⟩
          · exact ⟨0, Or.inl ⟨by simp, by simp⟩⟩
          · exact absurd rfl hne
          · exact ⟨0, Or.inl ⟨by simp, by simp⟩⟩
          · exact ⟨1, Or.inr ⟨Finset.mem_insert_self _ _, by simp⟩⟩
          · exact absurd hxy (hHsym _ _ (hH_b _ hq2B)).2
          · exact ⟨0, Or.inr ⟨by simp, by simp⟩⟩
          · exact ⟨2, Or.inl ⟨Finset.mem_insert_of_mem (by simp [(G.adj_comm _ _).mp hxy]), by simp⟩⟩
          · exact ⟨0, Or.inr ⟨by simp, by simp⟩⟩
          · exact absurd rfl hne
      · -- Case 2b: D3.card <= 1!
        obtain ⟨v, hv_deg⟩ : ∃ v : Fin 6, ∀ u : Fin 6, u ≠ v → degH u ≤ 2 := by
          by_cases h1 : D3.card = 1
          · obtain ⟨v, hv⟩ := Finset.card_eq_one.mp h1
            refine ⟨v, fun u huv => ?_⟩
            by_contra hgt
            have huD : u ∈ D3 := Finset.mem_filter.mpr ⟨Finset.mem_univ u, by omega⟩
            rw [hv, Finset.mem_singleton] at huD
            exact huv huD
          · have h0 : D3.card = 0 := by omega
            refine ⟨0, fun u _ => ?_⟩
            by_contra hgt
            have huD : u ∈ D3 := Finset.mem_filter.mpr ⟨Finset.mem_univ u, by omega⟩
            rw [Finset.card_eq_zero.mp h0] at huD
            exact Finset.notMem_empty u huD
        apply bc3_h_atmost_one_deg3 G hTF v
        intro u x y z huv hxy hux huy hzx hzy huz
        have hsub : ({x, y, z} : Finset (Fin 6)) ⊆ Finset.univ.filter (fun w => HAdj u w) := by
          intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ w, ?_⟩
          rcases hw with rfl | rfl | rfl <;> assumption
        have hc := Finset.card_le_card hsub
        rw [Finset.card_insert_of_notMem (by simp [hxy, hzx.symm]), Finset.card_pair hzy.symm] at hc
        have := hv_deg u huv; change _ ≤ degH u at hc; omega

end Size3Fin6

lemma coverBound : ∀ (G : SimpleGraph (Fin 6)) (C : PEqualNP.AndCount.AndCountCircuit 6), C.WellFormed ∧ (∀ I : Finset (Fin 6), (∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w) → (∀ u, u ∉ I → ∃ v ∈ I, G.Adj u v) → C.eval I = false ∧ ∀ u, u ∉ I → C.eval (insert u I) = true) → ∃ (k : ℕ) (X Y : Fin k → Finset (Fin 6)), k ≤ C.size ∧ (∀ i : Fin k, ∀ a ∈ X i, ∀ b ∈ Y i, G.Adj a b) ∧ (∀ a b : Fin 6, G.Adj a b → ∃ i : Fin k, (a ∈ X i ∧ b ∈ Y i) ∨ (b ∈ X i ∧ a ∈ Y i)) := by
  rintro G C ⟨hC, hfit⟩
  have hfit' : Fits G C := fun I hI => hfit I hI.1 hI.2
  have hbc : HasBicliqueCover G (min C.size 4) := by
    by_cases h4 : 4 ≤ C.size
    · rw [Nat.min_eq_right h4]; exact size_ge_4_fin6 G
    · rw [Nat.min_eq_left (by omega : C.size ≤ 4)]
      interval_cases hsz : C.size
      · exact size_eq_0 hfit' hsz
      · exact size_eq_1 hfit' hsz
      · exact size_eq_2 hC hfit' hsz
      · exact size_eq_3_fin6 G C hfit' hsz
  obtain ⟨X, Y, hbic, hcov⟩ := hbc
  exact ⟨min C.size 4, X, Y, Nat.min_le_left _ _, hbic, hcov⟩

end PEqualNP.Outside.L_meta_949_aux.ExistingProof

theorem PEqualNP.Outside.L_meta_949 : ¬ (∃ (G : SimpleGraph (Fin 6)) (C : PEqualNP.AndCount.AndCountCircuit 6), C.WellFormed ∧ (∀ I : Finset (Fin 6), (∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w) → (∀ u, u ∉ I → ∃ v ∈ I, G.Adj u v) → C.eval I = false ∧ ∀ u, u ∉ I → C.eval (insert u I) = true) ∧ ¬ (∃ (k : ℕ) (X Y : Fin k → Finset (Fin 6)), k ≤ C.size ∧ (∀ i : Fin k, ∀ a ∈ X i, ∀ b ∈ Y i, G.Adj a b) ∧ (∀ a b : Fin 6, G.Adj a b → ∃ i : Fin k, (a ∈ X i ∧ b ∈ Y i) ∨ (b ∈ X i ∧ a ∈ Y i)))) := by
  rintro ⟨G, C, hwell, hpartial, hnocover⟩
  exact hnocover (PEqualNP.Outside.L_meta_949_aux.ExistingProof.coverBound G C ⟨hwell, hpartial⟩)
