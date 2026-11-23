import Mathlib

namespace PEqualNP.Outside.L_meta_984.Slack

def kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs

def Run {α : Type} (inv : α → α) (meet join : α → α → α)
    (y : α) (t : ℕ) (ws : List α) : Prop :=
  ∀ P : ℕ → List α → Prop, P 0 [y] →
    (∀ {s xs zs}, List.Perm xs zs → P s xs → P s zs) →
    (∀ {s a r} (save : Bool), P s (inv a :: kept save a r) → P (s + 1) (a :: r)) →
    (∀ {s a b r} (c ka kb : Bool),
      P s ((if c then meet a b else join a b) :: kept ka a (kept kb b r)) →
      P (s + 1) (a :: b :: r)) → P t ws

lemma scale_bound {target d c q p : ℕ} (hc : c ≤ d)
    (ht : target ≤ 2 ^ (d-c) * q) (hq : q ≤ 2 ^ c * p) :
    target ≤ 2 ^ d * p := by
  calc
    target ≤ 2 ^ (d-c) * q := ht
    _ ≤ 2 ^ (d-c) * (2 ^ c * p) := Nat.mul_le_mul_left _ hq
    _ = 2 ^ d * p := by
      rw [← Nat.mul_assoc, ← Nat.pow_add, Nat.sub_add_cancel hc]

theorem run_score_slack {α : Type} {meet join : α → α → α}
    {y : α} {s : ℕ} {ws : List α}
    (h : Run (fun a => a) meet join y s ws)
    (v : α → ℕ)
    (hand : ∀ a b, v (meet a b) ≤ v a + v b)
    (hor : ∀ a b, v (join a b) ≤ v a + v b)
    (d : ℕ) (hlen : ws.length + d = s + 1) :
    v y ≤ 2 ^ d * (ws.map v).sum := by
  have hp : ws.length ≤ s+1 ∧
      ∀ d, ws.length+d=s+1 → v y ≤ 2^d * (ws.map v).sum := by
    apply h (fun s ws => ws.length ≤ s+1 ∧
      ∀ d, ws.length+d=s+1 → v y ≤ 2^d * (ws.map v).sum)
    · constructor
      · simp
      · intro d hd
        have hd0 : d=0 := by simpa using hd
        subst d
        simp
    · intro t xs zs p ih
      constructor
      · simpa only [← p.length_eq] using ih.1
      · intro d hd
        have hd' : xs.length+d=t+1 := by simpa only [p.length_eq] using hd
        simpa only [(p.map v).sum_eq] using ih.2 d hd'
    · intro t a r save ih
      cases save
      · simp only [kept, Bool.false_eq_true, ite_false, List.length_cons,
          List.map_cons, List.sum_cons] at ih ⊢
        constructor
        · omega
        · intro d hd
          have hc : 1 ≤ d := by omega
          apply scale_bound hc (ih.2 (d-1) (by omega))
          simp
          omega
      · simp only [kept, ite_true, List.length_cons, List.map_cons, List.sum_cons] at ih ⊢
        constructor
        · omega
        · intro d hd
          have hc : 2 ≤ d := by omega
          apply scale_bound hc (ih.2 (d-2) (by omega))
          norm_num
          omega
    · intro t a b r conj ka kb ih
      have hv : v (if conj then meet a b else join a b) ≤ v a + v b := by
        cases conj
        · exact hor a b
        · exact hand a b
      cases ka <;> cases kb
      · simp only [kept, Bool.false_eq_true, ite_false, List.length_cons,
          List.map_cons, List.sum_cons] at ih ⊢
        constructor
        · omega
        · intro d hd
          have hh := ih.2 d (by omega)
          exact hh.trans (Nat.mul_le_mul_left _ (by omega))
      · simp only [kept, Bool.false_eq_true, ite_false, ite_true, List.length_cons,
          List.map_cons, List.sum_cons] at ih ⊢
        constructor
        · omega
        · intro d hd
          have hc : 1 ≤ d := by omega
          apply scale_bound hc (ih.2 (d-1) (by omega))
          norm_num
          omega
      · simp only [kept, Bool.false_eq_true, ite_false, ite_true, List.length_cons,
          List.map_cons, List.sum_cons] at ih ⊢
        constructor
        · omega
        · intro d hd
          have hc : 1 ≤ d := by omega
          apply scale_bound hc (ih.2 (d-1) (by omega))
          norm_num
          omega
      · simp only [kept, ite_true, List.length_cons, List.map_cons, List.sum_cons] at ih ⊢
        constructor
        · omega
        · intro d hd
          have hc : 2 ≤ d := by omega
          apply scale_bound hc (ih.2 (d-2) (by omega))
          norm_num
          omega
  exact hp.2 d hlen

end PEqualNP.Outside.L_meta_984.Slack
