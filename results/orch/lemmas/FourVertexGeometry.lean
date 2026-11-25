import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2448_aux.FourVertexGeometry

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover

lemma cross_cases {V : Type*} (G : SimpleGraph V)
    (htriangle : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hfour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    (a b c d : V) (hab : G.Adj a b) (hcd : G.Adj c d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    (¬ G.Adj a d ∧ ¬ G.Adj b c ∧ ¬ G.Adj a c ∧ ¬ G.Adj b d) ∨
    (G.Adj a d ∧ ¬ G.Adj b c ∧ ¬ G.Adj a c ∧ ¬ G.Adj b d) ∨
    (¬ G.Adj a d ∧ G.Adj b c ∧ ¬ G.Adj a c ∧ ¬ G.Adj b d) ∨
    (¬ G.Adj a d ∧ ¬ G.Adj b c ∧ G.Adj a c ∧ ¬ G.Adj b d) ∨
    (¬ G.Adj a d ∧ ¬ G.Adj b c ∧ ¬ G.Adj a c ∧ G.Adj b d) := by
  classical
  by_cases ead : G.Adj a d
  · have nbc : ¬ G.Adj b c := by
      intro ebc
      exact (hfour a d c b ead hcd.symm ebc.symm hab.symm).elim hac hbd.symm
    have nac : ¬ G.Adj a c := fun eac => htriangle a c d eac hcd ead.symm
    have nbd : ¬ G.Adj b d := fun ebd => htriangle a b d hab ebd ead.symm
    exact Or.inr (Or.inl ⟨ead, nbc, nac, nbd⟩)
  · by_cases ebc : G.Adj b c
    · have nac : ¬ G.Adj a c := fun eac => htriangle a b c hab ebc eac.symm
      have nbd : ¬ G.Adj b d := fun ebd => htriangle b c d ebc hcd ebd.symm
      exact Or.inr (Or.inr (Or.inl ⟨ead, ebc, nac, nbd⟩))
    · by_cases eac : G.Adj a c
      · have nbd : ¬ G.Adj b d := by
          intro ebd
          exact (hfour a c d b eac hcd ebd.symm hab.symm).elim had hbc.symm
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ead, ebc, eac, nbd⟩)))
      · by_cases ebd : G.Adj b d
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨ead, ebc, eac, ebd⟩)))
        · exact Or.inl ⟨ead, ebc, eac, ebd⟩

def chosenEdges {V : Type*} (k : Fin 5) (a b c d : V) : List (V × V) :=
  match k.val with
  | 1 => [(a,b), (a,d), (c,d)]
  | 2 => [(a,b), (b,c), (c,d)]
  | 3 => [(a,b), (a,c), (c,d)]
  | 4 => [(a,b), (b,d), (c,d)]
  | _ => [(a,b), (c,d)]

def repairLeft (k : Fin 5) (a b c d : Bool) : Bool :=
  match k.val with
  | 1 => a && (b || d)
  | 2 => c && (b || d)
  | 3 => c && d
  | _ => a && b

def repairRight (k : Fin 5) (a b c d : Bool) : Bool :=
  match k.val with
  | 2 => a && b
  | 3 => a && (b || c)
  | 4 => d && (b || c)
  | _ => c && d

lemma repair_left_below_rectangle : ∀ (k : Fin 5) (a b c d : Bool),
    repairLeft k a b c d = true → ((a || c) && (b || d)) = true := by decide

lemma repair_right_below_rectangle : ∀ (k : Fin 5) (a b c d : Bool),
    repairRight k a b c d = true → ((a || d) && (b || c)) = true := by decide

lemma repair_output_edges {V : Type*} (k : Fin 5) (a b c d : V) (x : V → Bool) :
    (repairLeft k (x a) (x b) (x c) (x d) ||
      repairRight k (x a) (x b) (x c) (x d)) = true ↔
    ∃ u v, (u,v) ∈ chosenEdges k a b c d ∧ x u = true ∧ x v = true := by
  fin_cases k <;>
    simp [repairLeft, repairRight, chosenEdges, Bool.or_eq_true, Bool.and_eq_true,
      and_assoc, or_and_right, exists_or] <;>
    tauto

lemma chosen_edges_characterization {V : Type*} (G : SimpleGraph V)
    (a b c d : V) (hab : G.Adj a b) (hcd : G.Adj c d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (k : Fin 5)
    (ead : G.Adj a d ↔ k = 1) (ebc : G.Adj b c ↔ k = 2)
    (eac : G.Adj a c ↔ k = 3) (ebd : G.Adj b d ↔ k = 4) :
    (∀ u v, (u,v) ∈ chosenEdges k a b c d → G.Adj u v) ∧
    ∀ u v, G.Adj u v →
      (u = a ∨ u = b ∨ u = c ∨ u = d) →
      (v = a ∨ v = b ∨ v = c ∨ v = d) →
      (u,v) ∈ chosenEdges k a b c d ∨ (v,u) ∈ chosenEdges k a b c d := by
  have hba := hab.symm
  have hdc := hcd.symm
  have ead' : G.Adj d a ↔ k = 1 := ⟨fun h => ead.mp h.symm, fun h => (ead.mpr h).symm⟩
  have ebc' : G.Adj c b ↔ k = 2 := ⟨fun h => ebc.mp h.symm, fun h => (ebc.mpr h).symm⟩
  have eac' : G.Adj c a ↔ k = 3 := ⟨fun h => eac.mp h.symm, fun h => (eac.mpr h).symm⟩
  have ebd' : G.Adj d b ↔ k = 4 := ⟨fun h => ebd.mp h.symm, fun h => (ebd.mpr h).symm⟩
  constructor
  · intro u v huv
    fin_cases k <;> simp_all [chosenEdges] <;> aesop
  · intro u v huv hu hv
    rcases hu with rfl | rfl | rfl | rfl <;>
      rcases hv with rfl | rfl | rfl | rfl <;>
      fin_cases k <;> simp_all [chosenEdges]

lemma four_vertex_cover {V : Type*} (G : SimpleGraph V)
    (htriangle : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hfour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    (a b c d : V) (hab : G.Adj a b) (hcd : G.Adj c d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    ∃ k : Fin 5, (∀ u v, (u,v) ∈ chosenEdges k a b c d → G.Adj u v) ∧
    ∀ u v, G.Adj u v →
      (u = a ∨ u = b ∨ u = c ∨ u = d) →
      (v = a ∨ v = b ∨ v = c ∨ v = d) →
      (u,v) ∈ chosenEdges k a b c d ∨ (v,u) ∈ chosenEdges k a b c d := by
  rcases cross_cases G htriangle hfour a b c d hab hcd hac had hbc hbd with
    h | h | h | h | h
  · refine ⟨0, chosen_edges_characterization G a b c d hab hcd hac had hbc hbd 0 ?_ ?_ ?_ ?_⟩ <;>
      simp_all
  · refine ⟨1, chosen_edges_characterization G a b c d hab hcd hac had hbc hbd 1 ?_ ?_ ?_ ?_⟩ <;>
      simp_all
  · refine ⟨2, chosen_edges_characterization G a b c d hab hcd hac had hbc hbd 2 ?_ ?_ ?_ ?_⟩ <;>
      simp_all
  · refine ⟨3, chosen_edges_characterization G a b c d hab hcd hac had hbc hbd 3 ?_ ?_ ?_ ?_⟩ <;>
      simp_all
  · refine ⟨4, chosen_edges_characterization G a b c d hab hcd hac had hbc hbd 4 ?_ ?_ ?_ ?_⟩ <;>
      simp_all

lemma pair_members {V : Type*} (Q : V → Prop) (u v p q : V)
    (hp : p = u ∨ p = v) (hq : q = u ∨ q = v) (hne : p ≠ q)
    (hpQ : Q p) (hqQ : Q q) : Q u ∧ Q v := by
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;> simp_all

lemma active_pair_members (n : ℕ) (a b c d u v : Fin n)
    (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d)
    (hactive : (((pairInput u v a || pairInput u v c) &&
      (pairInput u v b || pairInput u v d)) ||
      ((pairInput u v a || pairInput u v d) &&
      (pairInput u v b || pairInput u v c))) = true) :
    (u = a ∨ u = b ∨ u = c ∨ u = d) ∧
      (v = a ∨ v = b ∨ v = c ∨ v = d) := by
  let Q (w : Fin n) := w = a ∨ w = b ∨ w = c ∨ w = d
  have haQ : Q a := by simp [Q]
  have hbQ : Q b := by simp [Q]
  have hcQ : Q c := by simp [Q]
  have hdQ : Q d := by simp [Q]
  simp only [Bool.or_eq_true, Bool.and_eq_true, pairInput, decide_eq_true_eq] at hactive
  rcases hactive with ⟨ha | hc, hb | hd⟩ | ⟨ha | hd, hb | hc⟩
  · exact pair_members Q u v a b ha hb hab haQ hbQ
  · exact pair_members Q u v a d ha hd had haQ hdQ
  · exact pair_members Q u v c b hc hb hbc.symm hcQ hbQ
  · exact pair_members Q u v c d hc hd hcd hcQ hdQ
  · exact pair_members Q u v a b ha hb hab haQ hbQ
  · exact pair_members Q u v a c ha hc hac haQ hcQ
  · exact pair_members Q u v d b hd hb hbd.symm hdQ hbQ
  · exact pair_members Q u v d c hd hc hcd.symm hdQ hcQ

lemma repair_choice (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (htriangle : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hfour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    (a b c d : Fin n) (hab : G.Adj a b) (hcd : G.Adj c d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    ∃ k : Fin 5,
      (∀ x : Fin n → Bool, repairLeft k (x a) (x b) (x c) (x d) = true →
        graphFun G ∅ x = true) ∧
      (∀ x : Fin n → Bool, repairRight k (x a) (x b) (x c) (x d) = true →
        graphFun G ∅ x = true) ∧
      ∀ u v : Fin n, G.Adj u v →
        (((pairInput u v a || pairInput u v c) &&
          (pairInput u v b || pairInput u v d)) ||
          ((pairInput u v a || pairInput u v d) &&
          (pairInput u v b || pairInput u v c))) = true →
        (repairLeft k (pairInput u v a) (pairInput u v b) (pairInput u v c) (pairInput u v d) ||
          repairRight k (pairInput u v a) (pairInput u v b) (pairInput u v c) (pairInput u v d)) = true := by
  obtain ⟨k, hgood, hcover⟩ := four_vertex_cover G htriangle hfour a b c d hab hcd hac had hbc hbd
  have clean : ∀ x : Fin n → Bool,
      (repairLeft k (x a) (x b) (x c) (x d) || repairRight k (x a) (x b) (x c) (x d)) = true →
      graphFun G ∅ x = true := by
    intro x hx
    obtain ⟨u, v, huv, hu, hv⟩ := (repair_output_edges k a b c d x).mp hx
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq]
    exact ⟨u, v, hgood u v huv, hu, hv⟩
  refine ⟨k, ?_, ?_, ?_⟩
  · intro x hx
    exact clean x (by simp only [hx, Bool.true_or])
  · intro x hx
    exact clean x (by simp only [hx, Bool.or_true])
  · intro u v huv hactive
    obtain ⟨hu, hv⟩ := active_pair_members n a b c d u v hab.ne hcd.ne hac had hbc hbd hactive
    apply (repair_output_edges k a b c d (pairInput u v)).mpr
    rcases hcover u v huv hu hv with he | he
    · exact ⟨u, v, he, by simp [pairInput], by simp [pairInput]⟩
    · exact ⟨v, u, he, by simp [pairInput], by simp [pairInput]⟩

end PEqualNP.Outside.L_meta_2448_aux.FourVertexGeometry
