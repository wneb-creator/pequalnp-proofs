import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2590.Petersen

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edgeList : List (Fin 10 × Fin 10) :=
  [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),
    (5,7),(7,9),(9,6),(6,8),(8,5)]

def adjacent (u v : Fin 10) : Bool := edgeList.contains (u,v) || edgeList.contains (v,u)

def graph : SimpleGraph (Fin 10) where
  Adj u v := adjacent u v = true
  symm := ⟨by intro u v h; simpa only [adjacent,Bool.or_comm] using h⟩
  loopless := ⟨by decide +kernel⟩

abbrev graphDec : DecidableRel graph.Adj := fun u v =>
  inferInstanceAs (Decidable (adjacent u v = true))

def pet (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

lemma edge_count : letI : DecidableRel graph.Adj := graphDec
    graph.edgeFinset.card = 15 := by
  letI : DecidableRel graph.Adj := graphDec
  decide +kernel

set_option maxHeartbeats 1000000 in
lemma no_four : letI : DecidableRel graph.Adj := graphDec
    PEqualNP.TopForm.NoFourCycle graph := by
  letI : DecidableRel graph.Adj := graphDec
  decide +kernel

set_option maxHeartbeats 1000000 in
lemma bool_cover_six : ∀ x : Fin 10 → Bool,
    (∀ u v, graph.Adj u v → x u = true ∨ x v = true) →
      6 ≤ (Finset.univ.filter fun u => x u = true).card := by
  change ∀ x : Fin 10 → Bool,
    (∀ u v, adjacent u v = true → x u = true ∨ x v = true) →
      6 ≤ (Finset.univ.filter fun u => x u = true).card
  decide +kernel

lemma cover_six (T : Finset (Fin 10))
    (h : ∀ u v, graph.Adj u v → u ∈ T ∨ v ∈ T) : 6 ≤ T.card := by
  have hb := bool_cover_six (fun u => decide (u ∈ T)) (by simpa using h)
  have he : (Finset.univ.filter fun u : Fin 10 => decide (u ∈ T) = true) = T := by
    ext u
    simp
  simpa only [he] using hb

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
lemma pet_graph : letI : DecidableRel graph.Adj := graphDec
    ∀ x : Fin 10 → Bool,
    pet x = decide (∃ u v, graph.Adj u v ∧ x u = true ∧ x v = true) := by
  letI : DecidableRel graph.Adj := graphDec
  decide +kernel

lemma cover_six_witness : ∃ T : Finset (Fin 10), T.card = 6 ∧
    ∀ u v, graph.Adj u v → u ∈ T ∨ v ∈ T := by
  refine ⟨{0,1,3,7,8,9},by decide,?_⟩
  change ∀ u v : Fin 10, adjacent u v = true →
    u ∈ ({0,1,3,7,8,9} : Finset (Fin 10)) ∨ v ∈ ({0,1,3,7,8,9} : Finset (Fin 10))
  decide +kernel

end PEqualNP.Outside.L_meta_2590.Petersen
