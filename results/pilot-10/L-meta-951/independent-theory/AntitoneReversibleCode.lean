import Mathlib

namespace PEqualNP.Outside.L_meta_951.ReversibleCode

def selector (x : Fin 3 → Bool) : Bool :=
  !(x 2 || (x 0 && x 1))

def decoder (y : Fin 4 → Bool) : Fin 3 → Bool :=
  ![(y 1 && y 2) || (y 0 && y 1) || (y 0 && y 3),
    (y 0 && y 2) || (y 0 && y 1) || (y 1 && y 3),
    y 2]

def encode (x : Fin 3 → Bool) : Fin 3 → Bool :=
  decoder ![x 0, x 1, x 2, selector x]

theorem selector_antitone : Antitone selector := by decide

theorem decoder_monotone : Monotone decoder := by decide

theorem decode_encode : ∀ x : Fin 3 → Bool,
    decoder ![encode x 0, encode x 1, encode x 2, selector x] = x := by decide

theorem encode_involutive : Function.Involutive encode := by
  change ∀ x, encode (encode x) = x
  decide

theorem encode_not_monotone : ¬ Monotone encode := by decide

end PEqualNP.Outside.L_meta_951.ReversibleCode
