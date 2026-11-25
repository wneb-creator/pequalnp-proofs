import PackingOrbitsDefs

namespace PEqualNP.Outside.L_meta_1896_aux.PackingOrbits

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pairMask_ends : ∀ i : Fin 325,
    pairMask i = (1 <<< (pairEnds i).1.val) ||| (1 <<< (pairEnds i).2.val) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pairLocalCheck_all : ∀ i : Fin 325, pairLocalCheck i = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma vertexLocalCheck_all : ∀ v : Fin 26, vertexLocalCheck v = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_0 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 0 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_1 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 1 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_2 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 2 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_3 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 3 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_4 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 4 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_5 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 5 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_6 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 6 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_7 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 7 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_8 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 8 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_9 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 9 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_10 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 10 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_11 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 11 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_12 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 12 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_13 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 13 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_14 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 14 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_15 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 15 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_16 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 16 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_17 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 17 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_18 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 18 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_19 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 19 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_20 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 20 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_21 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 21 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_22 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 22 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_23 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 23 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_24 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 24 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_25 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 25 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_26 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 26 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_27 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 27 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_28 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 28 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_29 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 29 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_30 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 30 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_31 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 31 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_32 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 32 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_33 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 33 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_34 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 34 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_35 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 35 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_36 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 36 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_37 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 37 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_38 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 38 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_39 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 39 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_40 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 40 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_41 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 41 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_42 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 42 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_43 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 43 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_44 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 44 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_45 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 45 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_46 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 46 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_47 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 47 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_48 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 48 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_49 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 49 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_50 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 50 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_51 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 51 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_52 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 52 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_53 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 53 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_54 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 54 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_55 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 55 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_56 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 56 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_57 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 57 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_58 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 58 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_59 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 59 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_60 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 60 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_61 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 61 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_62 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 62 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_63 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 63 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_64 : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * 64 + k.val, by omega⟩ j = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_all : ∀ i j : Fin 325, localCheck i j = true := by
  have h : ∀ g : Fin 65, ∀ k : Fin 5, ∀ j : Fin 325,
      localCheck ⟨5 * g.val + k.val, by omega⟩ j = true := by
    exact (Fin.cases localCheck_group_0 (Fin.cases localCheck_group_1 (Fin.cases localCheck_group_2 (Fin.cases localCheck_group_3 (Fin.cases localCheck_group_4 (Fin.cases localCheck_group_5 (Fin.cases localCheck_group_6 (Fin.cases localCheck_group_7 (Fin.cases localCheck_group_8 (Fin.cases localCheck_group_9 (Fin.cases localCheck_group_10 (Fin.cases localCheck_group_11 (Fin.cases localCheck_group_12 (Fin.cases localCheck_group_13 (Fin.cases localCheck_group_14 (Fin.cases localCheck_group_15 (Fin.cases localCheck_group_16 (Fin.cases localCheck_group_17 (Fin.cases localCheck_group_18 (Fin.cases localCheck_group_19 (Fin.cases localCheck_group_20 (Fin.cases localCheck_group_21 (Fin.cases localCheck_group_22 (Fin.cases localCheck_group_23 (Fin.cases localCheck_group_24 (Fin.cases localCheck_group_25 (Fin.cases localCheck_group_26 (Fin.cases localCheck_group_27 (Fin.cases localCheck_group_28 (Fin.cases localCheck_group_29 (Fin.cases localCheck_group_30 (Fin.cases localCheck_group_31 (Fin.cases localCheck_group_32 (Fin.cases localCheck_group_33 (Fin.cases localCheck_group_34 (Fin.cases localCheck_group_35 (Fin.cases localCheck_group_36 (Fin.cases localCheck_group_37 (Fin.cases localCheck_group_38 (Fin.cases localCheck_group_39 (Fin.cases localCheck_group_40 (Fin.cases localCheck_group_41 (Fin.cases localCheck_group_42 (Fin.cases localCheck_group_43 (Fin.cases localCheck_group_44 (Fin.cases localCheck_group_45 (Fin.cases localCheck_group_46 (Fin.cases localCheck_group_47 (Fin.cases localCheck_group_48 (Fin.cases localCheck_group_49 (Fin.cases localCheck_group_50 (Fin.cases localCheck_group_51 (Fin.cases localCheck_group_52 (Fin.cases localCheck_group_53 (Fin.cases localCheck_group_54 (Fin.cases localCheck_group_55 (Fin.cases localCheck_group_56 (Fin.cases localCheck_group_57 (Fin.cases localCheck_group_58 (Fin.cases localCheck_group_59 (Fin.cases localCheck_group_60 (Fin.cases localCheck_group_61 (Fin.cases localCheck_group_62 (Fin.cases localCheck_group_63 (Fin.cases localCheck_group_64 (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  intro i j
  have hi := h ⟨i.val / 5, by omega⟩ ⟨i.val % 5, Nat.mod_lt _ (by decide)⟩ j
  have heq : (⟨5 * (i.val / 5) + i.val % 5, by omega⟩ : Fin 325) = i := by
    apply Fin.ext
    omega
  simpa only [heq] using hi

end PEqualNP.Outside.L_meta_1896_aux.PackingOrbits
