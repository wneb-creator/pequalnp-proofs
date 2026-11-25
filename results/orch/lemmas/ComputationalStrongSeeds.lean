import ComputationalBounds

namespace PEqualNP.Outside.L_meta_10760_aux

def strongTrueTwo : List (ℕ × ℕ) := [(1536, 4), (4608, 4), (3072, 4), (33792, 4), (6144, 4), (18432, 4), (12288, 4), (24576, 4), (40960, 4)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def strongTrueTwo_check : strongTrueTwo.all (fun e => okE [] (pr [] e.1) e) = true := by decide +kernel

lemma strongTrueTwo_sound : ∀ e ∈ strongTrueTwo, Imp [] e.1 e.2 :=
  okAll strongTrueTwo_check (by simp)

def strongMixedThree : List (ℕ × ℕ) := [(522, 3), (1033, 3), (1041, 3), (1057, 3), (1036, 3), (1044, 3), (1060, 3), (1096, 3), (1104, 3), (1120, 3), (2051, 3), (2057, 3), (2081, 3), (2066, 3), (2114, 3), (2072, 3), (2120, 3), (2096, 3), (2144, 3), (4099, 3), (4129, 3), (4161, 3), (4102, 3), (4114, 3), (4132, 3), (4164, 3), (4144, 3), (4176, 3), (8201, 3), (8225, 3), (8257, 3), (8202, 3), (8226, 3), (8258, 3), (8204, 3), (8228, 3), (8260, 3), (16404, 3), (32786, 3)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def strongMixedThree_check : strongMixedThree.all (fun e => okE [] (pr [] e.1) e) = true := by decide +kernel

lemma strongMixedThree_sound : ∀ e ∈ strongMixedThree, Imp [] e.1 e.2 :=
  okAll strongMixedThree_check (by simp)

def strongNew : List (ℕ × ℕ) := strongTrueTwo ++ strongMixedThree

lemma strongNew_sound : ∀ e ∈ strongNew, Imp [] e.1 e.2 :=
  apI strongTrueTwo_sound strongMixedThree_sound

end PEqualNP.Outside.L_meta_10760_aux
