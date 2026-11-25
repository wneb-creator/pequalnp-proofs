import PEqualNP.Outside.L_gct_231

namespace PEqualNP.Outside.L_gct_231

lemma basic_star_row_relations (V : Fin 4 × Fin 4 → ℂ)
    (hs : ∀ i j : Fin 4, V (i,j) = V (j,i))
    (hp : ∀ a z : ℂ, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1 + starMatrix a (-a) (i,j) +
        z * V (i,j)) = 24) :
    V (1,1) = V (2,2) ∧ V (1,1) = V (1,2) ∧ V (1,3) = V (2,3) := by
  have hp' : ∀ a z : ℂ, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1 + starMatrix a ((-1)*a) (i,j) +
        z * V (i,j)) = 24 := by simpa using hp
  rcases star_line_constraints (-1) V hs hp' with ⟨h1,h2,hq⟩
  have hsq : (V (1,3) - V (2,3))^2 = 0 := by
    unfold starLineQuad at hq
    linear_combination hq - V (3,3) * h2
  have h13 : V (1,3) = V (2,3) := sub_eq_zero.mp (eq_zero_of_pow_eq_zero hsq)
  have h11 : V (1,1) = V (2,2) := by linear_combination h1 - h13
  have h12 : V (1,1) = V (1,2) := by linear_combination (h2 + h11) / 2
  exact ⟨h11,h12,h13⟩

end PEqualNP.Outside.L_gct_231
