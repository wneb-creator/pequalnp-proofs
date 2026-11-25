import Computational

namespace PEqualNP.Outside.L_meta_10760_aux

def tg4 : List (Nat × Nat) := [(628, 1), (16459, 1), (32813, 1)]
def ta4 : List (Nat × Nat) := allSeeds
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tcheck4 : tg4.all (fun e => okE [] (pr ta4 e.1) e) = true := by decide +kernel
def tg3 : List (Nat × Nat) := [(564, 2), (596, 2), (612, 2), (624, 2), (1080, 4), (2129, 4), (4194, 4), (8199, 4), (16395, 2), (16451, 2), (16457, 2), (16458, 2), (32781, 2), (32805, 2), (32809, 2), (32812, 2)]
def ta3 : List (Nat × Nat) := allSeeds ++ tg4
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tcheck3 : tg3.all (fun e => okE [] (pr ta3 e.1) e) = true := by decide +kernel
def tg2 : List (Nat × Nat) := [(532, 3), (548, 3), (560, 3), (580, 3), (592, 3), (608, 3), (1048, 5), (1064, 5), (1072, 5), (2065, 5), (2113, 5), (2128, 5), (4130, 5), (4162, 5), (4192, 5), (8195, 5), (8197, 5), (8198, 5), (16387, 3), (16393, 3), (16394, 3), (16449, 3), (16450, 3), (16456, 3), (32773, 3), (32777, 3), (32780, 3), (32801, 3), (32804, 3), (32808, 3)]
def ta2 : List (Nat × Nat) := allSeeds ++ tg4 ++ tg3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tcheck2 : tg2.all (fun e => okE [] (pr ta2 e.1) e) = true := by decide +kernel
def tg1 : List (Nat × Nat) := [(514, 3), (516, 4), (520, 3), (528, 4), (544, 4), (576, 4), (1025, 4), (1028, 4), (1032, 6), (1040, 6), (1056, 6), (1088, 4), (2049, 6), (2050, 4), (2056, 4), (2064, 6), (2080, 4), (2112, 6), (4097, 4), (4098, 6), (4100, 4), (4112, 4), (4128, 6), (4160, 6), (8193, 6), (8194, 6), (8196, 6), (8200, 4), (8224, 4), (8256, 4), (16385, 4), (16386, 4), (16388, 3), (16392, 4), (16400, 3), (16448, 4), (32769, 4), (32770, 3), (32772, 4), (32776, 4), (32784, 3), (32800, 4)]
def ta1 : List (Nat × Nat) := allSeeds ++ tg4 ++ tg3 ++ tg2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tcheck1 : tg1.all (fun e => okE [] (pr ta1 e.1) e) = true := by decide +kernel
def tg0 : List (Nat × Nat) := [(512, 5), (1024, 7), (2048, 7), (4096, 7), (8192, 7), (16384, 5), (32768, 5)]
def ta0 : List (Nat × Nat) := allSeeds ++ tg4 ++ tg3 ++ tg2 ++ tg1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tcheck0 : tg0.all (fun e => okE [] (pr ta0 e.1) e) = true := by decide +kernel
def extendedSeeds : List (Nat × Nat) := allSeeds ++ tg4 ++ tg3 ++ tg2 ++ tg1 ++ tg0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma six1 : okE [] (pr extendedSeeds 1) (1, 10) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma six2 : okE [] (pr extendedSeeds 2) (2, 10) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma six4 : okE [] (pr extendedSeeds 4) (4, 10) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma six8 : okE [] (pr extendedSeeds 8) (8, 10) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma six16 : okE [] (pr extendedSeeds 16) (16, 10) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma six32 : okE [] (pr extendedSeeds 32) (32, 10) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma six64 : okE [] (pr extendedSeeds 64) (64, 9) = true := by decide +kernel
lemma ta4_sound : ∀ e ∈ ta4, Imp [] e.1 e.2 := allSeeds_sound
lemma ti4 : ∀ e ∈ tg4, Imp [] e.1 e.2 := okAll tcheck4 ta4_sound
lemma ta3_sound : ∀ e ∈ ta3, Imp [] e.1 e.2 := apI ta4_sound ti4
lemma ti3 : ∀ e ∈ tg3, Imp [] e.1 e.2 := okAll tcheck3 ta3_sound
lemma ta2_sound : ∀ e ∈ ta2, Imp [] e.1 e.2 := apI ta3_sound ti3
lemma ti2 : ∀ e ∈ tg2, Imp [] e.1 e.2 := okAll tcheck2 ta2_sound
lemma ta1_sound : ∀ e ∈ ta1, Imp [] e.1 e.2 := apI ta2_sound ti2
lemma ti1 : ∀ e ∈ tg1, Imp [] e.1 e.2 := okAll tcheck1 ta1_sound
lemma ta0_sound : ∀ e ∈ ta0, Imp [] e.1 e.2 := apI ta1_sound ti1
lemma ti0 : ∀ e ∈ tg0, Imp [] e.1 e.2 := okAll tcheck0 ta0_sound
lemma extendedSeeds_sound : ∀ e ∈ extendedSeeds, Imp [] e.1 e.2 := apI ta0_sound ti0
def grpSix : List (Nat × Nat) := [(1,10),(2,10),(4,10),(8,10),(16,10),(32,10),(64,9)]
lemma sixchecks : grpSix.all (fun e => okE [] (pr extendedSeeds e.1) e) = true := by
  simp [grpSix, six1, six2, six4, six8, six16, six32, six64]
lemma grpSix_sound : ∀ e ∈ grpSix, Imp [] e.1 e.2 := okAll sixchecks extendedSeeds_sound
def rootSeeds : List (Nat × Nat) := grpSix ++ tg0
lemma rootSeeds_sound : ∀ e ∈ rootSeeds, Imp [] e.1 e.2 := apI grpSix_sound ti0

end PEqualNP.Outside.L_meta_10760_aux
