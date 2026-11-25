import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583.BlockCounts

set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

def closedLeft {m n : ℕ} (I : Fin m → Fin n → Prop) [DecidableRel I]
    (X : Finset (Fin m)) : Prop :=
  ∀ a, a ∈ X ↔ ∀ b, (∀ c ∈ X, ¬ I c b) → ¬ I a b

instance {m n : ℕ} (I : Fin m → Fin n → Prop) [DecidableRel I]
    (X : Finset (Fin m)) : Decidable (closedLeft I X) :=
  inferInstanceAs (Decidable (∀ a, a ∈ X ↔ ∀ b, (∀ c ∈ X, ¬ I c b) → ¬ I a b))

def I5 (l : Fin 5) (p : Fin 11) : Prop :=
  (l.val, p.val) ∈ ([(0, 0), (0, 1), (1, 1), (1, 2), (2, 2), (0, 3), (2, 3), (3, 3), (1, 4), (3, 4), (2, 5), (4, 5), (3, 6), (0, 7), (4, 7), (1, 8), (4, 8), (2, 9), (3, 10), (4, 10)] : List (ℕ × ℕ))

instance : DecidableRel I5 := fun _ _ => inferInstanceAs (Decidable (_ ∈ (_ : List (ℕ × ℕ))))

 theorem maximal_negative_count5 :
    ((Finset.univ : Finset (Finset (Fin 5))).filter (closedLeft I5)).card = 30 := by
  decide +kernel

def I6 (l : Fin 6) (p : Fin 11) : Prop :=
  (l.val, p.val) ∈ ([(0, 0), (5, 0), (0, 1), (1, 1), (1, 2), (2, 2), (0, 3), (2, 3), (3, 3), (1, 4), (3, 4), (2, 5), (4, 5), (3, 6), (5, 6), (0, 7), (4, 7), (1, 8), (4, 8), (5, 8), (2, 9), (5, 9), (3, 10), (4, 10)] : List (ℕ × ℕ))

instance : DecidableRel I6 := fun _ _ => inferInstanceAs (Decidable (_ ∈ (_ : List (ℕ × ℕ))))

 theorem maximal_negative_count6 :
    ((Finset.univ : Finset (Finset (Fin 6))).filter (closedLeft I6)).card = 52 := by
  decide +kernel

end PEqualNP.Outside.L_meta_2583.BlockCounts
