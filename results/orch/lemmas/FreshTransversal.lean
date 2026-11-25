import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1031.FreshTransversal

def NoSquare {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d

lemma common_pair_eq {V : Type*} {G : SimpleGraph V} (h4 : NoSquare G) {x y a b : V}
    (hab : a ≠ b) (hxa : G.Adj x a) (hxb : G.Adj x b)
    (hya : G.Adj y a) (hyb : G.Adj y b) : x = y :=
  (h4 x a y b hxa hya.symm hyb hxb.symm).resolve_right hab

lemma three_hits {V : Type*} {G : SimpleGraph V} (h4 : NoSquare G) {p q z a b c : V}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hza : G.Adj z a) (hzb : G.Adj z b) (hzc : G.Adj z c)
    (ha : G.Adj p a ∨ G.Adj q a) (hb : G.Adj p b ∨ G.Adj q b)
    (hc : G.Adj p c ∨ G.Adj q c) : z = p ∨ z = q := by
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact Or.inl (common_pair_eq h4 hab hza hzb ha hb)
  · rcases hc with hc | hc
    · exact Or.inl (common_pair_eq h4 hac hza hzc ha hc)
    · exact Or.inr (common_pair_eq h4 hbc hzb hzc hb hc)
  · rcases hc with hc | hc
    · exact Or.inl (common_pair_eq h4 hbc hzb hzc hb hc)
    · exact Or.inr (common_pair_eq h4 hac hza hzc ha hc)
  · exact Or.inr (common_pair_eq h4 hab hza hzb ha hb)

def Joins {V ι : Type*} (G : SimpleGraph V) (L R : ι → V) (x : V) : Prop :=
  ∀ i, G.Adj x (L i) ∨ G.Adj x (R i)

def Opposed {V ι : Type*} (G : SimpleGraph V) (L R : ι → V) (x y : V) : Prop :=
  ∀ i, (G.Adj x (L i) ∧ G.Adj y (R i)) ∨ (G.Adj x (R i) ∧ G.Adj y (L i))

def DisjointEdges {V ι : Type*} (L R : ι → V) : Prop :=
  Pairwise fun i j => Disjoint ({L i, R i} : Set V) {L j, R j}

lemma opposed_symm {V ι : Type*} {G : SimpleGraph V} {L R : ι → V} {x y : V}
    (h : Opposed G L R x y) : Opposed G L R y x := by
  intro i
  rcases h i with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · exact Or.inr ⟨h2,h1⟩
  · exact Or.inl ⟨h2,h1⟩

lemma endpoint_ne {V ι : Type*} {L R : ι → V} (hd : DisjointEdges L R)
    {i j : ι} (hij : i ≠ j) {a b : V}
    (ha : a ∈ ({L i,R i} : Set V)) (hb : b ∈ ({L j,R j} : Set V)) : a ≠ b := by
  rintro rfl
  exact Set.disjoint_left.mp (hd hij) ha hb

lemma endpoint_hit {V ι : Type*} {G : SimpleGraph V} {L R : ι → V} {x : V}
    (h : Joins G L R x) (i : ι) : ∃ a ∈ ({L i,R i} : Set V), G.Adj x a := by
  rcases h i with h | h
  · exact ⟨L i,by simp,h⟩
  · exact ⟨R i,by simp,h⟩

lemma opposed_dominate {V ι : Type*} {G : SimpleGraph V} {L R : ι → V} {p q : V}
    (h : Opposed G L R p q) {i : ι} {a : V} (ha : a ∈ ({L i,R i} : Set V)) :
    G.Adj p a ∨ G.Adj q a := by
  rcases Set.mem_insert_iff.mp ha with he | he
  · subst a
    rcases h i with hh | hh
    · exact Or.inl hh.1
    · exact Or.inr hh.2
  · obtain rfl := Set.mem_singleton_iff.mp he
    rcases h i with hh | hh
    · exact Or.inr hh.2
    · exact Or.inl hh.1

lemma three_bridges_unique {V ι : Type*} {G : SimpleGraph V} (h4 : NoSquare G)
    {L R : ι → V} (hd : DisjointEdges L R) {i j k : ι} (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) {p q z : V} (hpq : Opposed G L R p q)
    (hz : Joins G L R z) : z=p ∨ z=q := by
  obtain ⟨a,hai,hza⟩ := endpoint_hit hz i
  obtain ⟨b,hbj,hzb⟩ := endpoint_hit hz j
  obtain ⟨c,hck,hzc⟩ := endpoint_hit hz k
  exact three_hits h4 (endpoint_ne hd hij hai hbj) (endpoint_ne hd hik hai hck)
    (endpoint_ne hd hjk hbj hck) hza hzb hzc (opposed_dominate hpq hai)
    (opposed_dominate hpq hbj) (opposed_dominate hpq hck)

lemma cross_on_two {V : Type*} {G : SimpleGraph V} (h4 : NoSquare G) {p q z a b c d : V}
    (hac : a ≠ c) (hbd : b ≠ d) (hpa : G.Adj p a) (hpc : G.Adj p c)
    (hqb : G.Adj q b) (hqd : G.Adj q d) (hzp : z ≠ p) (hzq : z ≠ q)
    (hz1 : G.Adj z a ∨ G.Adj z b) (hz2 : G.Adj z c ∨ G.Adj z d) :
    (G.Adj z a ∧ G.Adj z d) ∨ (G.Adj z b ∧ G.Adj z c) := by
  rcases hz1 with ha | hb <;> rcases hz2 with hc | hd
  · exact (hzp (common_pair_eq h4 hac ha hc hpa hpc)).elim
  · exact Or.inl ⟨ha,hd⟩
  · exact Or.inr ⟨hb,hc⟩
  · exact (hzq (common_pair_eq h4 hbd hb hd hqb hqd)).elim

lemma mate_hit {V ι : Type*} {G : SimpleGraph V} {L R : ι → V} {x y z : V}
    (hyd : Opposed G L R x y) (hzd : Opposed G L R x z)
    (i : ι) (hex : ¬ (G.Adj x (L i) ∧ G.Adj x (R i))) :
    ∃ a ∈ ({L i,R i} : Set V), G.Adj y a ∧ G.Adj z a := by
  rcases hyd i with ⟨hx,hy⟩ | ⟨hx,hy⟩ <;> rcases hzd i with ⟨hx',hz⟩ | ⟨hx',hz⟩
  · exact ⟨R i,by simp,hy,hz⟩
  · exact (hex ⟨hx,hx'⟩).elim
  · exact (hex ⟨hx',hx⟩).elim
  · exact ⟨L i,by simp,hy,hz⟩

lemma mate_unique {V ι : Type*} {G : SimpleGraph V} (h4 : NoSquare G)
    {L R : ι → V} (hd : DisjointEdges L R) {i j : ι} (hij : i ≠ j)
    {x y z : V} (hyd : Opposed G L R x y) (hzd : Opposed G L R x z)
    (hex : ∀ k, ¬ (G.Adj x (L k) ∧ G.Adj x (R k))) : y=z := by
  obtain ⟨a,hai,hya,hza⟩ := mate_hit hyd hzd i (hex i)
  obtain ⟨b,hbj,hyb,hzb⟩ := mate_hit hyd hzd j (hex j)
  exact common_pair_eq h4 (endpoint_ne hd hij hai hbj) hya hyb hza hzb

lemma opposed_pairs_eq_or_disjoint {V ι : Type*} {G : SimpleGraph V} (h4 : NoSquare G)
    {L R : ι → V} (hd : DisjointEdges L R) {i j : ι} (hij : i ≠ j)
    (hex : ∀ x k, ¬ (G.Adj x (L k) ∧ G.Adj x (R k)))
    {p q r s : V} (hpq : Opposed G L R p q) (hrs : Opposed G L R r s) :
    ({p,q} : Set V) = {r,s} ∨ Disjoint ({p,q} : Set V) {r,s} := by
  classical
  by_cases hpr : p=r
  · subst r
    obtain rfl := mate_unique h4 hd hij hpq hrs (hex p)
    exact Or.inl rfl
  by_cases hps : p=s
  · subst s
    obtain rfl := mate_unique h4 hd hij hpq (opposed_symm hrs) (hex p)
    exact Or.inl (Set.pair_comm _ _)
  by_cases hqr : q=r
  · subst r
    obtain rfl := mate_unique h4 hd hij (opposed_symm hpq) hrs (hex q)
    exact Or.inl (Set.pair_comm _ _)
  by_cases hqs : q=s
  · subst s
    obtain rfl := mate_unique h4 hd hij (opposed_symm hpq) (opposed_symm hrs) (hex q)
    exact Or.inl rfl
  right
  apply Set.disjoint_left.mpr
  intro x hx hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with h | h
  · exact hpr h
  · exact hps h
  · exact hqr h
  · exact hqs h

lemma two_bridges_eq_or_disjoint {V ι : Type*} {G : SimpleGraph V} (h4 : NoSquare G)
    (h3 : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a) {L R : ι → V}
    (hbr : ∀ k, G.Adj (L k) (R k)) (hd : DisjointEdges L R) {i j : ι} (hij : i ≠ j)
    {p q r s : V} (hpq : Opposed G L R p q) (hrs : Opposed G L R r s) :
    ({p,q} : Set V) = {r,s} ∨ Disjoint ({p,q} : Set V) {r,s} :=
  opposed_pairs_eq_or_disjoint h4 hd hij
    (fun x k h => h3 x (L k) (R k) h.1 (hbr k) h.2.symm) hpq hrs

end PEqualNP.Outside.L_meta_1031.FreshTransversal
