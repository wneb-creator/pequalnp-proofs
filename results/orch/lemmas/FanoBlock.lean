import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Fin

namespace PEqualNP.Outside.L_meta_2583

def fanoIncident (p l : Fin 7) : Bool :=
  p == l || p == l + 1 || p == l + 3

def fanoUncovered (A B : Finset (Fin 7)) : Finset (Fin 7 × Fin 7) :=
  Finset.univ.filter fun e => fanoIncident e.1 e.2 = true ∧ e.1 ∉ A ∧ e.2 ∉ B

def fanoEndpoints (A B : Finset (Fin 7)) : ℕ :=
  ((fanoUncovered A B).image Prod.fst).card + ((fanoUncovered A B).image Prod.snd).card

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma fano_five_cover_six_edges : ∀ A B : Finset (Fin 7),
    A.card + B.card = 5 → (fanoUncovered A B).card = 6 →
      fanoEndpoints A B = 7 ∨ fanoEndpoints A B = 9 := by
  decide

end PEqualNP.Outside.L_meta_2583
