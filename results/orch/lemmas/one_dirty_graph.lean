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

def starProjection {α : Type} (a d : α) (A B : List α) (x : α → Bool) : Bool :=
  (x a && B.any x) || (x d && A.any x)

lemma starProjection_below_product {α : Type} (a d : α) (A B : List α)
    (haa : a ∈ A) (hdb : d ∈ B) (x : α → Bool) :
    starProjection a d A B x = true → (A.any x && B.any x) = true := by
  simp only [starProjection, Bool.or_eq_true, Bool.and_eq_true]
  rintro (⟨ha, hB⟩ | ⟨hd, hA⟩)
  · exact ⟨List.any_eq_true.mpr ⟨a, haa, ha⟩, hB⟩
  · exact ⟨hA, List.any_eq_true.mpr ⟨d, hdb, hd⟩⟩

lemma starProjection_sound {α : Type} (G : SimpleGraph α)
    (a d : α) (A B : List α) (haa : a ∈ A) (hdb : d ∈ B)
    (ha : ∀ x, (A.any x && B.any x) = true → x a = true → HasEdge G x)
    (hd : ∀ x, (A.any x && B.any x) = true → x d = true → HasEdge G x) :
    ∀ x, starProjection a d A B x = true → HasEdge G x := by
  intro x hx
  have hprod := starProjection_below_product a d A B haa hdb x hx
  simp only [starProjection, Bool.or_eq_true, Bool.and_eq_true] at hx
  rcases hx with ⟨h, _⟩ | ⟨h, _⟩
  · exact ha x hprod h
  · exact hd x hprod h

lemma starProjection_preserves_graph_pairs {α : Type} [DecidableEq α]
    (G : SimpleGraph α)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hfour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    (a d : α) (had : G.Adj a d) (A B : List α) (haa : a ∈ A) (hdb : d ∈ B)
    (ha : ∀ x, (A.any x && B.any x) = true → x a = true → HasEdge G x)
    (hd : ∀ x, (A.any x && B.any x) = true → x d = true → HasEdge G x)
    (u v : α) (huv : G.Adj u v) :
    starProjection a d A B (pairInput u v) =
      (A.any (pairInput u v) && B.any (pairInput u v)) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · exact starProjection_below_product a d A B haa hdb (pairInput u v)
  · intro hprod
    have hcover := shared_product_edges_have_two_centers G htri hfour a d had A B haa hdb
      ha hd u v huv hprod
    have hcenter : pairInput u v a = true ∨ pairInput u v d = true := by
      rcases hcover with h | h | h | h
      · exact Or.inl (by simp [pairInput, h])
      · exact Or.inl (by simp [pairInput, h])
      · exact Or.inr (by simp [pairInput, h])
      · exact Or.inr (by simp [pairInput, h])
    obtain ⟨hA, hB⟩ := Bool.and_eq_true_iff.mp hprod
    simp only [starProjection, Bool.or_eq_true, Bool.and_eq_true]
    rcases hcenter with h | h
    · exact Or.inl ⟨h, hB⟩
    · exact Or.inr ⟨h, hA⟩

lemma single_star_replacement {α : Type} [DecidableEq α]
    (G : SimpleGraph α) (a : α) (A B : (α → Bool) → Bool)
    (hforces : ∀ x, x a = true → A x = true)
    (hstar : ∀ u v, G.Adj u v → (A (pairInput u v) && B (pairInput u v)) = true →
      u = a ∨ v = a)
    (hsound : ∀ x, (A x && B x) = true → x a = true → HasEdge G x) :
    (∀ x, (x a && B x) = true → (A x && B x) = true) ∧
      (∀ u v, G.Adj u v →
        (pairInput u v a && B (pairInput u v)) =
          (A (pairInput u v) && B (pairInput u v))) ∧
      (∀ x, (x a && B x) = true → HasEdge G x) := by
  have hshrink : ∀ x, (x a && B x) = true → (A x && B x) = true := by
    intro x hx
    obtain ⟨ha, hB⟩ := Bool.and_eq_true_iff.mp hx
    exact Bool.and_eq_true_iff.mpr ⟨hforces x ha, hB⟩
  refine ⟨hshrink, ?_, ?_⟩
  · intro u v huv
    apply Bool.eq_iff_iff.mpr
    constructor
    · exact hshrink (pairInput u v)
    · intro hprod
      have ha : pairInput u v a = true := by
        rcases hstar u v huv hprod with h | h <;> simp [pairInput, h]
      exact Bool.and_eq_true_iff.mpr ⟨ha, (Bool.and_eq_true_iff.mp hprod).2⟩
  · intro x hx
    exact hsound x (hshrink x hx) (Bool.and_eq_true_iff.mp hx).1

end PEqualNP.Outside.L_meta_1031_aux.OneDirtyGraph
