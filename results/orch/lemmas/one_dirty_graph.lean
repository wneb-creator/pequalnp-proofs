import Mathlib.Combinatorics.SimpleGraph.Basic

namespace PEqualNP.Outside.L_meta_1031_aux.OneDirtyGraph

def pairInput {α : Type} [DecidableEq α] (u v : α) : α → Bool :=
  fun k => decide (k = u ∨ k = v)

def singleInput {α : Type} [DecidableEq α] (u : α) : α → Bool :=
  fun k => decide (k = u)

def HasEdge {α : Type} (G : SimpleGraph α) (x : α → Bool) : Prop :=
  ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true

lemma hasEdge_pair_iff {α : Type} [DecidableEq α] (G : SimpleGraph α) (u v : α) :
    HasEdge G (pairInput u v) ↔ G.Adj u v := by
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    simp only [pairInput, decide_eq_true_eq] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact False.elim (G.ne_of_adj hab rfl)
    · exact hab
    · exact hab.symm
    · exact False.elim (G.ne_of_adj hab rfl)
  · intro huv
    exact ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩

lemma no_shared_literal_support {α : Type} [DecidableEq α]
    (G : SimpleGraph α)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (a d : α) (had : G.Adj a d) (H : (α → Bool) → Bool)
    (ha : ∀ x, H x = true → x a = true → HasEdge G x)
    (hd : ∀ x, H x = true → x d = true → HasEdge G x) :
    ∀ z, ¬ (∀ x, x z = true → H x = true) := by
  intro z hz
  have hza : G.Adj z a := (hasEdge_pair_iff G z a).mp
    (ha (pairInput z a) (hz _ (by simp [pairInput])) (by simp [pairInput]))
  have hzd : G.Adj z d := (hasEdge_pair_iff G z d).mp
    (hd (pairInput z d) (hz _ (by simp [pairInput])) (by simp [pairInput]))
  exact htri a d z had hzd.symm hza

lemma shared_monotone_signal_false_on_singletons {α : Type} [DecidableEq α]
    (G : SimpleGraph α)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (a d : α) (had : G.Adj a d) (H : (α → Bool) → Bool)
    (hmono : ∀ x y, (∀ i, x i = true → y i = true) → H x = true → H y = true)
    (ha : ∀ x, H x = true → x a = true → HasEdge G x)
    (hd : ∀ x, H x = true → x d = true → HasEdge G x) :
    ∀ z, H (singleInput z) = false := by
  intro z
  apply Bool.eq_false_iff.mpr
  intro hz
  apply no_shared_literal_support G htri a d had H ha hd z
  intro x hx
  apply hmono (singleInput z) x _ hz
  intro i hi
  have hiz : i = z := by simpa only [singleInput, decide_eq_true_eq] using hi
  simpa only [hiz] using hx

lemma shared_or_signal_has_no_literal_branch {α : Type} [DecidableEq α]
    (G : SimpleGraph α)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (a d : α) (had : G.Adj a d) (g : (α → Bool) → Bool) (P : List α)
    (ha : ∀ x, (g x || P.any x) = true → x a = true → HasEdge G x)
    (hd : ∀ x, (g x || P.any x) = true → x d = true → HasEdge G x) :
    P = [] := by
  cases P with
  | nil => rfl
  | cons z zs =>
    exfalso
    apply no_shared_literal_support G htri a d had (fun x => g x || (z :: zs).any x) ha hd z
    intro x hx
    simp [hx]

lemma shared_product_edges_have_two_centers {α : Type} [DecidableEq α]
    (G : SimpleGraph α)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hfour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    (a d : α) (had : G.Adj a d) (A B : List α) (haa : a ∈ A) (hdb : d ∈ B)
    (ha : ∀ x, (A.any x && B.any x) = true → x a = true → HasEdge G x)
    (hd : ∀ x, (A.any x && B.any x) = true → x d = true → HasEdge G x)
    (u v : α) (huv : G.Adj u v)
    (hprod : (A.any (pairInput u v) && B.any (pairInput u v)) = true) :
    u = a ∨ v = a ∨ u = d ∨ v = d := by
  have hdisj (z : α) (hzA : z ∈ A) (hzB : z ∈ B) : False := by
    apply no_shared_literal_support G htri a d had (fun x => A.any x && B.any x) ha hd z
    intro x hx
    exact Bool.and_eq_true_iff.mpr ⟨List.any_eq_true.mpr ⟨z, hzA, hx⟩,
      List.any_eq_true.mpr ⟨z, hzB, hx⟩⟩
  have cross (p q : α) (hp : p ∈ A) (hq : q ∈ B) (hpq : G.Adj p q) :
      p = a ∨ q = d := by
    have hpd : G.Adj p d := (hasEdge_pair_iff G p d).mp
      (hd (pairInput p d) (Bool.and_eq_true_iff.mpr
        ⟨List.any_eq_true.mpr ⟨p, hp, by simp [pairInput]⟩,
          List.any_eq_true.mpr ⟨d, hdb, by simp [pairInput]⟩⟩) (by simp [pairInput]))
    have haq : G.Adj a q := (hasEdge_pair_iff G a q).mp
      (ha (pairInput a q) (Bool.and_eq_true_iff.mpr
        ⟨List.any_eq_true.mpr ⟨a, haa, by simp [pairInput]⟩,
          List.any_eq_true.mpr ⟨q, hq, by simp [pairInput]⟩⟩) (by simp [pairInput]))
    exact hfour p q a d hpq haq.symm had hpd.symm
  obtain ⟨hA, hB⟩ := Bool.and_eq_true_iff.mp hprod
  obtain ⟨p, hp, hpv⟩ := List.any_eq_true.mp hA
  obtain ⟨q, hq, hqv⟩ := List.any_eq_true.mp hB
  simp only [pairInput, decide_eq_true_eq] at hpv hqv
  rcases hpv with rfl | rfl <;> rcases hqv with rfl | rfl
  · exact (hdisj _ hp hq).elim
  · rcases cross p q hp hq huv with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr h))
  · rcases cross p q hp hq huv.symm with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  · exact (hdisj _ hp hq).elim

end PEqualNP.Outside.L_meta_1031_aux.OneDirtyGraph
