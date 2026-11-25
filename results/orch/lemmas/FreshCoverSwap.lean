import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1031.FreshCoverSwap

lemma absorb_matching (a b c d y : Bool) :
    ((y && (a || c)) || (a && b) || (c && d)) =
      ((a || c) && (y || ((a || d) && (b || c) && (b || d)))) := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases y <;> decide

def Covers {V : Type*} (G : SimpleGraph V) (T : Finset V) : Prop :=
  ∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T

def Assigned {V : Type*} (z : V) (L : V → Set V) (u v : V) : Prop :=
  (u = z ∧ v ∈ L z) ∨ (v = z ∧ u ∈ L z)

def Pair {V : Type*} (a b u v : V) : Prop :=
  (u = a ∧ v = b) ∨ (v = a ∧ u = b)

lemma absorbed_cover_swap {V I : Type*} [DecidableEq V]
    (G H : SimpleGraph V) (T : Finset V) (S : Finset I) (y a b c d : I → V)
    (L : V → Set V) (hy : ∀ i ∈ S, y i ∈ T) (hinj : Set.InjOn y S)
    (hbase : ∀ u v, H.Adj u v → ∃ z ∈ T, Assigned z L u v)
    (hp : ∀ i ∈ S, L (y i) ⊆ {a i,c i})
    (hfinal : ∀ u v, G.Adj u v → H.Adj u v ∨
      ∃ i ∈ S, Pair (a i) (b i) u v ∨ Pair (c i) (d i) u v) :
    ∃ U : Finset V, Covers G U ∧ U.card ≤ T.card + S.card := by
  classical
  let Y := S.image y
  let A := S.image a
  let C := S.image c
  let U := ((T \ Y) ∪ A) ∪ C
  have hYsub : Y ⊆ T := by
    intro z hz
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
    exact hy i hi
  have haIn (i) (hi : i ∈ S) : a i ∈ U :=
    Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem a hi))
  have hcIn (i) (hi : i ∈ S) : c i ∈ U := Finset.mem_union_right _ (Finset.mem_image_of_mem c hi)
  have swap {z v : V} (hz : z ∈ T) (hv : v ∈ L z) : z ∈ U ∨ v ∈ U := by
    by_cases hzY : z ∈ Y
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hzY
      have hh := hp i hi hv
      rcases Set.mem_insert_iff.mp hh with h|h
      · exact Or.inr (h ▸ haIn i hi)
      · exact Or.inr ((Set.mem_singleton_iff.mp h) ▸ hcIn i hi)
    · exact Or.inl (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hz,hzY⟩)))
  refine ⟨U,?_,?_⟩
  · intro u v huv
    rcases hfinal _ _ huv with h|⟨i,hi,h|h⟩
    · obtain ⟨z,hz,⟨rfl,hv⟩|⟨rfl,hu⟩⟩ := hbase u v h
      · exact swap hz hv
      · exact (swap hz hu).symm
    · rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact Or.inl (haIn i hi)
      · exact Or.inr (haIn i hi)
    · rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact Or.inl (hcIn i hi)
      · exact Or.inr (hcIn i hi)
  · have hyCard : Y.card = S.card := Finset.card_image_of_injOn hinj
    have hsub := Finset.card_sdiff_add_card_eq_card hYsub
    have h1 := Finset.card_union_le (T \ Y) A
    have h2 := Finset.card_union_le ((T \ Y) ∪ A) C
    have h3 : A.card ≤ S.card := Finset.card_image_le
    have h4 : C.card ≤ S.card := Finset.card_image_le
    change (((T \ Y) ∪ A) ∪ C).card ≤ _
    omega

lemma absorbed_edge_count {V I : Type*} [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj] (S : Finset I) (a b c d : I → V)
    (hfinal : ∀ u v, G.Adj u v → H.Adj u v ∨
      ∃ i ∈ S, Pair (a i) (b i) u v ∨ Pair (c i) (d i) u v) :
    G.edgeFinset.card ≤ H.edgeFinset.card + 2*S.card := by
  classical
  let M := S.image (fun i => s(a i,b i))
  let N := S.image (fun i => s(c i,d i))
  have hsub : G.edgeFinset ⊆ (H.edgeFinset ∪ M) ∪ N := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ u v =>
      have huv : G.Adj u v := by simpa using he
      rcases hfinal _ _ huv with hh|⟨i,hi,h|h⟩
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (by simpa using hh))
      · apply Finset.mem_union_left
        apply Finset.mem_union_right
        refine Finset.mem_image.mpr ⟨i,hi,?_⟩
        rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
        · rfl
        · exact Sym2.eq_swap
      · apply Finset.mem_union_right
        refine Finset.mem_image.mpr ⟨i,hi,?_⟩
        rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
        · rfl
        · exact Sym2.eq_swap
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le H.edgeFinset M
  have h3 := Finset.card_union_le (H.edgeFinset ∪ M) N
  have h4 : M.card ≤ S.card := Finset.card_image_le
  have h5 : N.card ≤ S.card := Finset.card_image_le
  omega

lemma absorbed_cover_cost {V I : Type*} [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (T : Finset V) (S : Finset I) (y a b c d : I → V)
    (L : V → Set V) (hy : ∀ i ∈ S, y i ∈ T) (hinj : Set.InjOn y S)
    (hbase : ∀ u v, H.Adj u v → ∃ z ∈ T, Assigned z L u v)
    (hp : ∀ i ∈ S, L (y i) ⊆ {a i,c i})
    (hfinal : ∀ u v, G.Adj u v → H.Adj u v ∨
      ∃ i ∈ S, Pair (a i) (b i) u v ∨ Pair (c i) (d i) u v) :
    ∃ U : Finset V, Covers G U ∧ G.edgeFinset.card + U.card ≤
      H.edgeFinset.card + T.card + 3*S.card := by
  obtain ⟨U,hu,hcard⟩ := absorbed_cover_swap G H T S y a b c d L hy hinj hbase hp hfinal
  have he := absorbed_edge_count G H S a b c d hfinal
  exact ⟨U,hu,by omega⟩

def Cross {V : Type*} (A B : Set V) (p q : V) : Prop :=
  (p ∈ A ∧ q ∈ B) ∨ (p ∈ B ∧ q ∈ A)

lemma cross_symm {V : Type*} {A B : Set V} {p q : V} (h : Cross A B p q) : Cross A B q p := by
  rcases h with ⟨u,v⟩|⟨u,v⟩
  · exact Or.inr ⟨v,u⟩
  · exact Or.inl ⟨v,u⟩

lemma cross_swap {V : Type*} {A B : Set V} {p q : V} (h : Cross A B p q) : Cross B A p q :=
  h.symm

lemma clause_alignment {V : Type*} (G : SimpleGraph V) (A B C D : Set V)
    (h4 : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d)
    (hab : Disjoint A B) (hcd : Disjoint C D)
    (hAc : ∀ p ∈ A, ∀ q ∈ A, p ≠ q → G.Adj p q)
    (hBc : ∀ p ∈ B, ∀ q ∈ B, p ≠ q → G.Adj p q)
    (hCc : ∀ p ∈ C, ∀ q ∈ C, p ≠ q → G.Adj p q)
    (hDc : ∀ p ∈ D, ∀ q ∈ D, p ≠ q → G.Adj p q)
    (hAC : (A ∩ C).Subsingleton) (hBD : (B ∩ D).Subsingleton)
    {x y : V} (hxA : x ∈ A) (hxC : x ∈ C) (hyB : y ∈ B) (hyD : y ∈ D)
    {p q : V} (hpA : p ∈ A) (hqB : q ∈ B) (h2 : Cross C D p q) : p = x ∧ q = y := by
  rcases h2 with ⟨hpC,hqD⟩|⟨hpD,hqC⟩
  · exact ⟨hAC ⟨hpA,hpC⟩ ⟨hxA,hxC⟩,hBD ⟨hqB,hqD⟩ ⟨hyB,hyD⟩⟩
  · have dAB {a b} (ha : a ∈ A) (hb : b ∈ B) : a ≠ b := fun h => Set.disjoint_left.mp hab (h ▸ ha) hb
    have dCD {a b} (ha : a ∈ C) (hb : b ∈ D) : a ≠ b := fun h => Set.disjoint_left.mp hcd (h ▸ ha) hb
    have hcy := h4 x p y q (hAc _ hxA _ hpA (dCD hxC hpD)) (hDc _ hpD _ hyD (dAB hpA hyB))
      (hBc _ hyB _ hqB (dCD hqC hyD).symm) (hCc _ hqC _ hxC (dAB hxA hqB).symm)
    exact (hcy.elim (dAB hxA hyB) (dAB hpA hqB)).elim

lemma matching_clause_intersection {V : Type*} (G : SimpleGraph V) (A B C D : Set V)
    (h4 : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d)
    (hab : Disjoint A B) (hcd : Disjoint C D)
    (hAc : ∀ p ∈ A, ∀ q ∈ A, p ≠ q → G.Adj p q)
    (hBc : ∀ p ∈ B, ∀ q ∈ B, p ≠ q → G.Adj p q)
    (hCc : ∀ p ∈ C, ∀ q ∈ C, p ≠ q → G.Adj p q)
    (hDc : ∀ p ∈ D, ∀ q ∈ D, p ≠ q → G.Adj p q)
    (hAC : (A ∩ C).Subsingleton) (hBD : (B ∩ D).Subsingleton)
    (hAD : (A ∩ D).Subsingleton) (hBC : (B ∩ C).Subsingleton)
    {u v p q : V} (h1 : Cross A B u v) (h2 : Cross C D u v)
    (h3 : Cross A B p q) (h4' : Cross C D p q) : Pair u v p q := by
  have base {x y s t : V} (hxA : x ∈ A) (hyB : y ∈ B) (hsA : s ∈ A) (htB : t ∈ B)
      (hxy : Cross C D x y) (hst : Cross C D s t) : s = x ∧ t = y := by
    rcases hxy with ⟨hxC,hyD⟩|⟨hxD,hyC⟩
    · exact clause_alignment G A B C D h4 hab hcd hAc hBc hCc hDc hAC hBD hxA hxC hyB hyD hsA htB hst
    · exact clause_alignment G A B D C h4 hab hcd.symm hAc hBc hDc hCc hAD hBC hxA hxD hyB hyC hsA htB
        (cross_swap hst)
  rcases h1 with ⟨hu,hv⟩|⟨hu,hv⟩ <;> rcases h3 with ⟨hp,hq⟩|⟨hp,hq⟩
  · exact Or.inl (base hu hv hp hq h2 h4')
  · exact Or.inr (base hu hv hq hp h2 (cross_symm h4'))
  · exact Or.inr (base hv hu hp hq (cross_symm h2) h4').symm
  · exact Or.inl (base hv hu hq hp (cross_symm h2) (cross_symm h4')).symm

def BinaryCNF {V : Type*} (R : V → V → Prop) (X : Set V) : Prop :=
  ∀ a b, R a b → a ∈ X ∨ b ∈ X

lemma binary_cnf_order {V : Type*} (R S : SimpleGraph V) :
    (∀ X : Set V, BinaryCNF R.Adj X → BinaryCNF S.Adj X) ↔ S ≤ R := by
  classical
  constructor
  · intro h a b hs
    by_contra hn
    let X : Set V := ({a,b} : Set V)ᶜ
    have hRX : BinaryCNF R.Adj X := by
      intro u v huv
      by_contra! hnot
      have hU : u = a ∨ u = b := by
        by_cases h : u = a
        · exact Or.inl h
        · exact Or.inr (by simpa [X,h] using hnot.1)
      have hV : v = a ∨ v = b := by
        by_cases h : v = a
        · exact Or.inl h
        · exact Or.inr (by simpa [X,h] using hnot.2)
      rcases hU with rfl|rfl <;> rcases hV with rfl|rfl
      · exact huv.ne rfl
      · exact hn huv
      · exact hn huv.symm
      · exact huv.ne rfl
    have hcover := h X hRX a b hs
    simp [X] at hcover
  · intro h X hr a b hs
    exact hr a b (h hs)

end PEqualNP.Outside.L_meta_1031.FreshCoverSwap
