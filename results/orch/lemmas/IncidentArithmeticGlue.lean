import PEqualNP.Outside.L_gct_231

namespace PEqualNP.Outside.L_gct_231

def NormalizedIncidentArithmetic : Prop :=
  ∀ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 zz : ℂ,
    incidentGenerator1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9=0 →
    incidentGenerator2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9=0 →
    incidentGenerator3 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9=0 →
    incidentGenerator4 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9=0 →
    incidentGenerator5 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9=0 →
    incidentGenerator6 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9=0 →
    incidentGenerator7 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9=0 →
    incidentGenerator8 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9=0 →
    incidentGenerator9 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9=0 →
    incidentGenerator10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9=0 →
    incidentGenerator11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9=0 →
    incidentGenerator12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9=0 →
    zz*(-1-x3-x5-x7-x9)-1=0 → False

lemma normalized_incident_opposite_edge_of_arithmetic
    (ha : NormalizedIncidentArithmetic) (H V : Fin 4 × Fin 4 → ℂ)
    (hHs : ∀ i j : Fin 4, H (i,j)=H (j,i))
    (hVs : ∀ i j : Fin 4, V (i,j)=V (j,i))
    (hHz : ∀ i : Fin 4, H (i,i)=0)
    (hVtrace : (∑ i : Fin 4, V (i,i))=0)
    (hV00 : V (0,0)=1) (hH01 : H (0,1)=1) (hV01 : V (0,1)=0)
    (hp : ∀ a z : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      1+a*H (i,j)+z*V (i,j))=24) : H (2,3)=0 := by
  by_contra hn
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12⟩ :=
    normalized_incident_generators_zero H V hHs hVs hHz hVtrace hV00 hH01 hV01 hp
  have hH23 := (normalized_incident_reconstruction
    H V hHs hVs hHz hVtrace hV00 hH01 hV01 hp).1
  apply ha (V (1,1)) (V (2,2)) (V (0,2)) (H (0,2)) (V (0,3)) (H (0,3))
    (V (1,2)) (H (1,2)) (V (1,3)) (H (1,3)) (H (2,3))⁻¹
    h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  rw [← hH23]
  field_simp [hn]
  ring

lemma normalized_incident_of_arithmetic (ha : NormalizedIncidentArithmetic) :
    NormalizedIncidentOppositeEdge := by
  intro H V hHs hVs hHz hVtrace hV00 hH01 hV01 hp
  exact normalized_incident_opposite_edge_of_arithmetic
    ha H V hHs hVs hHz hVtrace hV00 hH01 hV01 hp

end PEqualNP.Outside.L_gct_231
