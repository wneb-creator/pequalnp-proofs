import PEqualNP.Outside.L_gct_231

namespace PEqualNP.Outside.L_gct_231

def incidentGenerator1 (_x0 _x1 _x2 x3 _x4 x5 _x6 x7 _x8 x9 : ℂ) : ℂ :=
  4*x3*x9 - 4*x3 + 4*x5*x7 - 4*x5 - 4*x7 - 4*x9 - 4

def incidentGenerator2 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : ℂ) : ℂ :=
  -4*x0*x3 - 8*x0*x7 - 4*x0*x9 - 8*x0 - 4*x1*x3 + 4*x1*x5 - 4*x1*x7 + 4*x1*x9 + 4*x2*x9 - 4*x2 +
    4*x3*x8 - 8*x3 + 4*x4*x7 - 4*x4 + 4*x5*x6 - 4*x5 - 4*x6 - 4*x7 - 4*x8 - 8

def incidentGenerator3 (x0 x1 x2 _x3 x4 _x5 x6 _x7 x8 _x9 : ℂ) : ℂ :=
  -2*x0^2 - 2*x0*x1 - 4*x0*x2 - 8*x0*x6 - 4*x0*x8 - 2*x0 - 2*x1^2 - 4*x1*x2 + 4*x1*x4 - 4*x1*x6 +
    4*x1*x8 - 2*x1 + 4*x2*x8 - 8*x2 + 4*x4*x6 - 4*x4 - 4*x6 - 2

def incidentGenerator4 (_x0 _x1 _x2 x3 _x4 x5 _x6 x7 _x8 x9 : ℂ) : ℂ :=
  -2*x3^2*x5 - 2*x3*x5^2 - 2*x3*x5*x7 - 2*x3*x5*x9 - 2*x3*x5 - 2*x3*x7*x9 + 2*x3*x7 - 2*x5*x7*x9 +
    2*x5*x9 - 2*x7^2*x9 - 2*x7*x9^2 - 2*x7*x9

def incidentGenerator5 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : ℂ) : ℂ :=
  -x0*x3^2 - 2*x0*x3*x7 - 2*x0*x3 + 2*x0*x7*x9 + x0*x9^2 + 2*x0*x9 - x1*x3^2 - 2*x1*x3*x7 - 2*x1*x3
    + x1*x5^2 + 2*x1*x5*x9 + 2*x1*x5 - x1*x7^2 - 2*x1*x7 + x1*x9^2 + 2*x1*x9 - 4*x2*x3*x5 -
    2*x2*x5^2 - 2*x2*x5*x7 - 2*x2*x5*x9 - 2*x2*x5 - 2*x2*x7*x9 + 2*x2*x7 - 2*x3^2*x4 - 4*x3*x4*x5 -
    2*x3*x4*x7 - 2*x3*x4*x9 - 2*x3*x4 - 2*x3*x5*x6 - 2*x3*x5*x8 + 2*x3*x5 - 2*x3*x6*x9 + 2*x3*x6 -
    2*x3*x7*x8 - 2*x3*x7 - 2*x4*x7*x9 + 2*x4*x9 + x5^2 - 2*x5*x6*x9 - 2*x5*x7*x8 + 2*x5*x8 + 2*x5 -
    4*x6*x7*x9 - 2*x6*x9^2 - 2*x6*x9 - 2*x7^2*x8 - x7^2 - 4*x7*x8*x9 - 2*x7*x8 - 2*x7

def incidentGenerator6 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : ℂ) : ℂ :=
  -2*x0^2*x3 - 2*x0*x1*x3 + 2*x0*x1*x5 - 2*x0*x1 - 2*x0*x2*x3 - 2*x0*x2*x7 - 2*x0*x2 - 2*x0*x3*x6 -
    4*x0*x3 - 2*x0*x5 + 2*x0*x6*x9 + 2*x0*x7*x8 - 4*x0*x7 + 2*x0*x8*x9 + 2*x0*x8 - 2*x0*x9 - 2*x0 -
    2*x1^2 - 2*x1*x2*x3 - 2*x1*x2*x7 - 2*x1*x2 - 2*x1*x3*x6 + 2*x1*x4*x5 + 2*x1*x4*x9 + 2*x1*x4 +
    2*x1*x5*x8 - 2*x1*x6*x7 - 2*x1*x6 - 2*x1*x7 + 2*x1*x8*x9 + 2*x1*x8 + 2*x1*x9 - 2*x1 - 2*x2^2*x5
    - 4*x2*x3*x4 - 4*x2*x4*x5 - 2*x2*x4*x7 - 2*x2*x4*x9 - 2*x2*x4 - 2*x2*x5*x6 - 2*x2*x5*x8 +
    2*x2*x5 - 2*x2*x6*x9 + 2*x2*x6 - 2*x2*x7*x8 - 2*x2*x7 - 2*x3*x4^2 - 2*x3*x4*x6 - 2*x3*x4*x8 +
    2*x3*x4 - 2*x3*x6*x8 - 2*x3*x6 + 2*x4*x5 - 2*x4*x6*x9 - 2*x4*x7*x8 + 2*x4*x8 + 2*x4 - 2*x5*x6*x8
    - 2*x6^2*x9 - 4*x6*x7*x8 - 2*x6*x7 - 4*x6*x8*x9 - 2*x6*x8 - 2*x6 - 2*x7*x8^2 - 2*x7

def incidentGenerator7 (x0 x1 x2 _x3 x4 _x5 x6 _x7 x8 _x9 : ℂ) : ℂ :=
  -x0^2*x1 - 2*x0^2*x2 - x0^2 - x0*x1^2 - 2*x0*x1*x2 + 2*x0*x1*x4 - 2*x0*x1 - x0*x2^2 - 2*x0*x2*x6 -
    4*x0*x2 - 2*x0*x4 + 2*x0*x6*x8 - 4*x0*x6 + x0*x8^2 - 2*x0*x8 - x0 - x1^2 - x1*x2^2 - 2*x1*x2*x6
    + x1*x4^2 + 2*x1*x4*x8 - x1*x6^2 - 2*x1*x6 + x1*x8^2 + 2*x1*x8 - x1 - 2*x2^2*x4 - 2*x2*x4^2 -
    2*x2*x4*x6 - 2*x2*x4*x8 + 2*x2*x4 - 2*x2*x6*x8 - 2*x2*x6 + x4^2 - 2*x4*x6*x8 - 2*x6^2*x8 - x6^2
    - 2*x6*x8^2 - 2*x6

def incidentGenerator8 (_x0 _x1 _x2 x3 _x4 x5 _x6 x7 _x8 x9 : ℂ) : ℂ :=
  x3^2*x9^2 - 2*x3^2*x9 + x3^2 + 2*x3*x5*x7*x9 - 2*x3*x5*x7 - 2*x3*x5*x9 + 2*x3*x5 - 2*x3*x7*x9 +
    2*x3*x7 - 2*x3*x9^2 + 2*x3 + x5^2*x7^2 - 2*x5^2*x7 + x5^2 - 2*x5*x7^2 - 2*x5*x7*x9 + 2*x5*x9 +
    2*x5 + x7^2 + 2*x7*x9 + 2*x7 + x9^2 + 2*x9 + 1

def incidentGenerator9 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : ℂ) : ℂ :=
  -2*x0*x3^2*x5 - 2*x0*x3*x5^2 - 2*x0*x3*x5*x7 - 2*x0*x3*x5*x9 - 2*x0*x3*x5 - 2*x0*x3*x7 -
    2*x1*x3*x7 + 2*x1*x5*x9 + 2*x2*x3*x9^2 - 4*x2*x3*x9 + 2*x2*x3 + 2*x2*x5*x7*x9 - 2*x2*x5*x7 -
    2*x2*x5*x9 + 2*x2*x5 - 2*x2*x7*x9 + 2*x2*x7 - 2*x2*x9^2 + 2*x2 + 2*x3^2*x8*x9 - 2*x3^2*x8 +
    2*x3*x4*x7*x9 - 2*x3*x4*x7 - 2*x3*x4*x9 + 2*x3*x4 + 2*x3*x5*x6*x9 - 2*x3*x5*x6 + 2*x3*x5*x7*x8 -
    2*x3*x5*x8 - 2*x3*x6*x9 + 2*x3*x6 - 2*x3*x7*x8 - 2*x3*x7*x9 - 2*x3*x7 - 4*x3*x8*x9 +
    2*x4*x5*x7^2 - 4*x4*x5*x7 + 2*x4*x5 - 2*x4*x7^2 - 2*x4*x7*x9 + 2*x4*x9 + 2*x4 + 2*x5^2*x6*x7 -
    2*x5^2*x6 - 4*x5*x6*x7 - 2*x5*x6*x9 - 2*x5*x7*x8 - 2*x5*x7*x9 + 2*x5*x8 + 2*x6*x7 + 2*x6*x9 +
    2*x6 - 2*x7^2*x9 + 2*x7*x8 - 2*x7*x9^2 - 2*x7*x9 + 2*x8*x9 + 2*x8

def incidentGenerator10 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : ℂ) : ℂ :=
  -x0^2*x3^2 - x0*x1*x3^2 + x0*x1*x5^2 - x0*x1 - 4*x0*x2*x3*x5 - 2*x0*x2*x5^2 - 2*x0*x2*x5*x7 -
    2*x0*x2*x5*x9 - 2*x0*x2*x5 - 2*x0*x2*x7 - 2*x0*x3^2*x4 - 4*x0*x3*x4*x5 - 2*x0*x3*x4*x7 -
    2*x0*x3*x4*x9 - 2*x0*x3*x4 - 2*x0*x3*x5*x6 - 2*x0*x3*x5*x8 + 2*x0*x3*x5 - 2*x0*x3*x6 +
    2*x0*x3*x7 + 2*x0*x3*x9 + 2*x0*x3 + x0*x5^2 + 2*x0*x5*x7 + 2*x0*x5*x9 + 2*x0*x5 + 2*x0*x7*x9 +
    2*x0*x7 + x0*x9^2 + 2*x0*x9 + x0 - x1^2 - 2*x1*x2*x7 - 2*x1*x3*x6 + 2*x1*x4*x9 + 2*x1*x5*x8 -
    x1*x7^2 + x1*x9^2 - x1 + x2^2*x9^2 - 2*x2^2*x9 + x2^2 + 4*x2*x3*x8*x9 - 4*x2*x3*x8 +
    2*x2*x4*x7*x9 - 2*x2*x4*x7 - 2*x2*x4*x9 + 2*x2*x4 + 2*x2*x5*x6*x9 - 2*x2*x5*x6 + 2*x2*x5*x7*x8 -
    2*x2*x5*x8 - 2*x2*x6*x9 + 2*x2*x6 - 2*x2*x7*x8 - 2*x2*x7*x9 - 2*x2*x7 - 4*x2*x8*x9 + x3^2*x8^2 +
    2*x3*x4*x6*x9 - 2*x3*x4*x6 + 2*x3*x4*x7*x8 - 2*x3*x4*x8 + 2*x3*x5*x6*x8 - 2*x3*x6*x8 -
    2*x3*x6*x9 - 2*x3*x6 - 2*x3*x7*x8 - 2*x3*x8^2 + x4^2*x7^2 - 2*x4^2*x7 + x4^2 + 4*x4*x5*x6*x7 -
    4*x4*x5*x6 - 4*x4*x6*x7 - 2*x4*x6*x9 - 2*x4*x7*x8 - 2*x4*x7*x9 + 2*x4*x8 + x5^2*x6^2 - 2*x5*x6^2
    - 2*x5*x6*x8 - 2*x5*x6*x9 - 2*x5*x7*x8 + x6^2 - 4*x6*x7*x9 + 2*x6*x8 - 2*x6*x9^2 - 2*x6*x9 -
    2*x7^2*x8 - x7^2 - 4*x7*x8*x9 - 2*x7*x8 + x8^2

def incidentGenerator11 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : ℂ) : ℂ :=
  -2*x0^2*x2*x3 - 2*x0*x1*x2*x3 + 2*x0*x1*x4*x5 - 2*x0*x2^2*x5 - 4*x0*x2*x3*x4 - 4*x0*x2*x4*x5 -
    2*x0*x2*x4*x7 - 2*x0*x2*x4*x9 - 2*x0*x2*x4 - 2*x0*x2*x5*x6 - 2*x0*x2*x5*x8 + 2*x0*x2*x5 -
    2*x0*x2*x6 + 2*x0*x2*x7 + 2*x0*x2*x9 + 2*x0*x2 - 2*x0*x3*x4^2 - 2*x0*x3*x4*x6 - 2*x0*x3*x4*x8 +
    2*x0*x3*x4 + 2*x0*x3*x6 + 2*x0*x3*x8 + 2*x0*x4*x5 + 2*x0*x4*x7 + 2*x0*x4*x9 + 2*x0*x4 +
    2*x0*x5*x6 + 2*x0*x5*x8 + 2*x0*x6*x9 + 2*x0*x6 + 2*x0*x7*x8 + 2*x0*x8*x9 + 2*x0*x8 - 2*x1*x2*x6
    + 2*x1*x4*x8 - 2*x1*x6*x7 + 2*x1*x8*x9 + 2*x2^2*x8*x9 - 2*x2^2*x8 + 2*x2*x3*x8^2 + 2*x2*x4*x6*x9
    - 2*x2*x4*x6 + 2*x2*x4*x7*x8 - 2*x2*x4*x8 + 2*x2*x5*x6*x8 - 2*x2*x6*x8 - 2*x2*x6*x9 - 2*x2*x6 -
    2*x2*x7*x8 - 2*x2*x8^2 + 2*x3*x4*x6*x8 - 2*x3*x6*x8 + 2*x4^2*x6*x7 - 2*x4^2*x6 + 2*x4*x5*x6^2 -
    2*x4*x6^2 - 2*x4*x6*x8 - 2*x4*x6*x9 - 2*x4*x7*x8 - 2*x5*x6*x8 - 2*x6^2*x9 - 4*x6*x7*x8 - 2*x6*x7
    - 4*x6*x8*x9 - 2*x6*x8 - 2*x7*x8^2

def incidentGenerator12 (x0 x1 x2 _x3 x4 _x5 x6 _x7 x8 _x9 : ℂ) : ℂ :=
  -x0^2*x1 - x0^2*x2^2 - x0*x1^2 - x0*x1*x2^2 + x0*x1*x4^2 - x0*x1 - 2*x0*x2^2*x4 - 2*x0*x2*x4^2 -
    2*x0*x2*x4*x6 - 2*x0*x2*x4*x8 + 2*x0*x2*x4 + 2*x0*x2*x6 + 2*x0*x2*x8 + x0*x4^2 + 2*x0*x4*x6 +
    2*x0*x4*x8 + 2*x0*x6*x8 + x0*x8^2 - x1*x6^2 + x1*x8^2 + x2^2*x8^2 + 2*x2*x4*x6*x8 - 2*x2*x6*x8 +
    x4^2*x6^2 - 2*x4*x6*x8 - 2*x6^2*x8 - x6^2 - 2*x6*x8^2

def incidentH (x3 x5 x7 x9 : ℂ) : Fin 4 × Fin 4 → ℂ :=
  fun p => (!![0,1,x3,x5; 1,0,x7,x9; x3,x7,0,-1-x3-x5-x7-x9;
    x5,x9,-1-x3-x5-x7-x9,0] : Matrix (Fin 4) (Fin 4) ℂ) p.1 p.2

def incidentV (x0 x1 x2 x4 x6 x8 : ℂ) : Fin 4 × Fin 4 → ℂ :=
  fun p => (!![1,0,x2,x4; 0,x0,x6,x8; x2,x6,x1,-x2-x4-x6-x8;
    x4,x8,-x2-x4-x6-x8,-1-x0-x1] : Matrix (Fin 4) (Fin 4) ℂ) p.1 p.2

set_option maxHeartbeats 8000000 in
lemma permanent_incident_chart (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 a z : ℂ) :
    Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      1+a*incidentH x3 x5 x7 x9 (i,j)+z*incidentV x0 x1 x2 x4 x6 x8 (i,j)) =
    24 + incidentGenerator1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 * a^2 +
      incidentGenerator2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 * a * z +
      incidentGenerator3 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 * z^2 +
      incidentGenerator4 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 * a^3 +
      incidentGenerator5 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 * a^2 * z +
      incidentGenerator6 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 * a * z^2 +
      incidentGenerator7 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 * z^3 +
      incidentGenerator8 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 * a^4 +
      incidentGenerator9 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 * a^3 * z +
      incidentGenerator10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 * a^2 * z^2 +
      incidentGenerator11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 * a * z^3 +
      incidentGenerator12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 * z^4 := by
  rw [permanent_four]
  simp [incidentH,incidentV]
  dsimp [incidentGenerator1,incidentGenerator2,incidentGenerator3,incidentGenerator4,incidentGenerator5,incidentGenerator6,incidentGenerator7,incidentGenerator8,incidentGenerator9,incidentGenerator10,incidentGenerator11,incidentGenerator12]
  ring

lemma incident_bivariate_coefficients (g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 : ℂ)
    (hp : ∀ a z : ℂ,
      g1*a^2+g2*a*z+g3*z^2+g4*a^3+g5*a^2*z+g6*a*z^2+g7*z^3+
        g8*a^4+g9*a^3*z+g10*a^2*z^2+g11*a*z^3+g12*z^4=0) :
    g1=0 ∧ g2=0 ∧ g3=0 ∧ g4=0 ∧ g5=0 ∧ g6=0 ∧ g7=0 ∧
      g8=0 ∧ g9=0 ∧ g10=0 ∧ g11=0 ∧ g12=0 := by
  have hd (z : ℂ) : g1+g2*z+g3*z^2=0 ∧
      g4+g5*z+g6*z^2+g7*z^3=0 ∧
      g8+g9*z+g10*z^2+g11*z^3+g12*z^4=0 := by
    have h := quartic_all_coefficients 0 (g1+g2*z+g3*z^2)
      (g4+g5*z+g6*z^2+g7*z^3) (g8+g9*z+g10*z^2+g11*z^3+g12*z^4) (by
        intro t
        have ht := hp t (t*z)
        linear_combination ht)
    exact h.2
  have h1 : g1=0 := by simpa using (hd 0).1
  have h4 : g4=0 := by simpa using (hd 0).2.1
  have h8 : g8=0 := by simpa using (hd 0).2.2
  obtain ⟨h2,h3,_,_⟩ := quartic_all_coefficients g2 g3 0 0 (by
    intro z
    linear_combination (hd z).1-h1)
  obtain ⟨h5,h6,h7,_⟩ := quartic_all_coefficients g5 g6 g7 0 (by
    intro z
    linear_combination (hd z).2.1-h4)
  obtain ⟨h9,h10,h11,h12⟩ := quartic_all_coefficients g9 g10 g11 g12 (by
    intro z
    linear_combination (hd z).2.2-h8)
  exact ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12⟩

set_option maxHeartbeats 4000000 in
lemma incident_level_tangent (T : Fin 4 × Fin 4 → ℂ)
    (hs : ∀ i j : Fin 4, T (i,j)=T (j,i))
    (hp : ∀ z : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      1+z*T (i,j))=24) :
    T (0,0)+2*T (0,1)+2*T (0,2)+2*T (0,3)+T (1,1)+
      2*T (1,2)+2*T (1,3)+T (2,2)+2*T (2,3)+T (3,3)=0 := by
  have h1 := hp 1
  have h2 := hp (-1)
  have h3 := hp 2
  have h4 := hp (-2)
  rw [permanent_four] at h1 h2 h3 h4
  simp only [Matrix.of_apply,hs 1 0,hs 2 0,hs 3 0,hs 2 1,hs 3 1,hs 3 2] at h1 h2 h3 h4
  linear_combination (1/9:ℂ)*h1-(1/9:ℂ)*h2-(1/72:ℂ)*h3+(1/72:ℂ)*h4

lemma normalized_incident_reconstruction (H V : Fin 4 × Fin 4 → ℂ)
    (hHs : ∀ i j : Fin 4, H (i,j)=H (j,i))
    (hVs : ∀ i j : Fin 4, V (i,j)=V (j,i))
    (hHz : ∀ i : Fin 4, H (i,i)=0)
    (hVtrace : (∑ i : Fin 4, V (i,i))=0)
    (hV00 : V (0,0)=1) (hH01 : H (0,1)=1) (hV01 : V (0,1)=0)
    (hp : ∀ a z : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      1+a*H (i,j)+z*V (i,j))=24) :
    H (2,3)=-1-H (0,2)-H (0,3)-H (1,2)-H (1,3) ∧
    V (2,3)=-V (0,2)-V (0,3)-V (1,2)-V (1,3) ∧
    V (3,3)=-1-V (1,1)-V (2,2) := by
  have hHt := incident_level_tangent H hHs (by intro z; simpa using hp z 0)
  have hVt := incident_level_tangent V hVs (by intro z; simpa using hp 0 z)
  have htr : V (0,0)+V (1,1)+V (2,2)+V (3,3)=0 := by
    simpa [Fin.sum_univ_succ,add_assoc] using hVtrace
  simp only [hHz,hH01] at hHt
  rw [hV01] at hVt
  refine ⟨?_,?_,?_⟩
  · linear_combination hHt/2
  · linear_combination hVt/2-htr/2
  · rw [hV00] at htr
    linear_combination htr

set_option maxHeartbeats 2000000 in
lemma normalized_incident_generators_zero (H V : Fin 4 × Fin 4 → ℂ)
    (hHs : ∀ i j : Fin 4, H (i,j)=H (j,i))
    (hVs : ∀ i j : Fin 4, V (i,j)=V (j,i))
    (hHz : ∀ i : Fin 4, H (i,i)=0)
    (hVtrace : (∑ i : Fin 4, V (i,i))=0)
    (hV00 : V (0,0)=1) (hH01 : H (0,1)=1) (hV01 : V (0,1)=0)
    (hp : ∀ a z : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      1+a*H (i,j)+z*V (i,j))=24) :
    incidentGenerator1 (V (1,1)) (V (2,2)) (V (0,2)) (H (0,2)) (V (0,3)) (H (0,3))
      (V (1,2)) (H (1,2)) (V (1,3)) (H (1,3))=0 ∧
    incidentGenerator2 (V (1,1)) (V (2,2)) (V (0,2)) (H (0,2)) (V (0,3)) (H (0,3))
      (V (1,2)) (H (1,2)) (V (1,3)) (H (1,3))=0 ∧
    incidentGenerator3 (V (1,1)) (V (2,2)) (V (0,2)) (H (0,2)) (V (0,3)) (H (0,3))
      (V (1,2)) (H (1,2)) (V (1,3)) (H (1,3))=0 ∧
    incidentGenerator4 (V (1,1)) (V (2,2)) (V (0,2)) (H (0,2)) (V (0,3)) (H (0,3))
      (V (1,2)) (H (1,2)) (V (1,3)) (H (1,3))=0 ∧
    incidentGenerator5 (V (1,1)) (V (2,2)) (V (0,2)) (H (0,2)) (V (0,3)) (H (0,3))
      (V (1,2)) (H (1,2)) (V (1,3)) (H (1,3))=0 ∧
    incidentGenerator6 (V (1,1)) (V (2,2)) (V (0,2)) (H (0,2)) (V (0,3)) (H (0,3))
      (V (1,2)) (H (1,2)) (V (1,3)) (H (1,3))=0 ∧
    incidentGenerator7 (V (1,1)) (V (2,2)) (V (0,2)) (H (0,2)) (V (0,3)) (H (0,3))
      (V (1,2)) (H (1,2)) (V (1,3)) (H (1,3))=0 ∧
    incidentGenerator8 (V (1,1)) (V (2,2)) (V (0,2)) (H (0,2)) (V (0,3)) (H (0,3))
      (V (1,2)) (H (1,2)) (V (1,3)) (H (1,3))=0 ∧
    incidentGenerator9 (V (1,1)) (V (2,2)) (V (0,2)) (H (0,2)) (V (0,3)) (H (0,3))
      (V (1,2)) (H (1,2)) (V (1,3)) (H (1,3))=0 ∧
    incidentGenerator10 (V (1,1)) (V (2,2)) (V (0,2)) (H (0,2)) (V (0,3)) (H (0,3))
      (V (1,2)) (H (1,2)) (V (1,3)) (H (1,3))=0 ∧
    incidentGenerator11 (V (1,1)) (V (2,2)) (V (0,2)) (H (0,2)) (V (0,3)) (H (0,3))
      (V (1,2)) (H (1,2)) (V (1,3)) (H (1,3))=0 ∧
    incidentGenerator12 (V (1,1)) (V (2,2)) (V (0,2)) (H (0,2)) (V (0,3)) (H (0,3))
      (V (1,2)) (H (1,2)) (V (1,3)) (H (1,3))=0 := by
  obtain ⟨hH23,hV23,hV33⟩ := normalized_incident_reconstruction
    H V hHs hVs hHz hVtrace hV00 hH01 hV01 hp
  have hH : H=incidentH (H (0,2)) (H (0,3)) (H (1,2)) (H (1,3)) := by
    funext p
    rcases p with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;>
      simp [incidentH,hHz,hH01,hH23,hHs 1 0,hHs 2 0,hHs 3 0,hHs 2 1,hHs 3 1,hHs 3 2]
  have hV : V=incidentV (V (1,1)) (V (2,2)) (V (0,2)) (V (0,3))
      (V (1,2)) (V (1,3)) := by
    funext p
    rcases p with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;>
      simp [incidentV,hV00,hV01,hV23,hV33,hVs 1 0,hVs 2 0,hVs 3 0,hVs 2 1,hVs 3 1,hVs 3 2]
  apply incident_bivariate_coefficients
  intro a z
  have h := hp a z
  rw [hH,hV,permanent_incident_chart] at h
  linear_combination h

end PEqualNP.Outside.L_gct_231
