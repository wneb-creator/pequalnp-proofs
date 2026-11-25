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

end PEqualNP.Outside.L_meta_1031_aux.OneDirtyGraph
