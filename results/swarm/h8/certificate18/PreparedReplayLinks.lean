import LinkedReplay

namespace PEqualNP.Outside.L_meta_2373_aux.Cert18.Replay.LinkedReplay
open PEqualNP.Outside.L_meta_6581

abbrev IndexedLink (n : Nat) := Fin n × Fin 120

def prepareReplayLinks {n : Nat} (getCode : Nat → Nat) (fuel : Nat)
    (budget : Fin n → Nat) (i : Fin n) (links : List (IndexedLink n)) : List PreparedLink :=
  (links.filter fun l => decide (budget l.1 < budget i)).map fun l =>
    (budget l.1, replayBank getCode fuel l.1.val l.2)

lemma prepareReplayLinks_sound {n : Nat} {getCode : Nat → Nat} {fuel : Nat}
    {states : Fin n → State} {budget : Fin n → Nat} {i : Fin n}
    {links : List (IndexedLink n)}
    (state_eq : ∀ j, (states j).live = (decodeStateBy getCode fuel j.val).live)
    (earlier : ∀ j, budget j < budget i → Impossible Extended.target (budget j) (states j).live) :
    ∀ l ∈ prepareReplayLinks getCode fuel budget i links, Impossible Extended.target l.1 l.2 := by
  intro l hl
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hl
  have hv' := List.mem_filter.mp hv
  have old := Automorphism.impossible_preimage
    (earlier v.1 (of_decide_eq_true hv'.2)) (autoMoves v.2) (autoMoves_valid v.2)
  change Impossible Extended.target (budget v.1) (replayBank getCode fuel v.1.val v.2)
  rw [replayBank_eq,←state_eq v.1]
  exact old

end PEqualNP.Outside.L_meta_2373_aux.Cert18.Replay.LinkedReplay
