import FewNotGeneric
import ProjectionMassTwo
import LiveFirstBinary

namespace PEqualNP.Outside.L_meta_2592.FewNot

lemma pins_seventeen {k S} (run : Extended.Live true Extended.target k S)
    (raw : ∀ v ∈ S, v ∈ Extended.pins) : 17 ≤ k := by
  apply Extended.live_floor_from_pair_floor Extended.pins Extended.target 16
    (by decide +kernel) (fun d a b hd ha hb _ _ hab k S hr hs =>
      pair_sixteen hd ha hb hab hr hs) run raw

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma seed_distinct : ∀ (j : Fin 9) (d : Fin 4), Extended.first ≠
    Extended.bin d.val Extended.first (Extended.pins.getD (j.val+1) Extended.zero) := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma seed_projects_zero : ∀ (j : Fin 9) (d : Fin 4), d.val = 0 ∨ d.val = 2 →
    projected (Extended.bin d.val Extended.first (Extended.pins.getD (j.val+1) Extended.zero)) = zero := by
  decide +kernel

lemma seeded_seventeen {j : Fin 9} {d : Fin 4} (hd : d.val = 0 ∨ d.val = 2)
    {k S} (run : Extended.Live true Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ seeded j d) : 17 ≤ k := by
  let extra := Extended.bin d.val Extended.first (Extended.pins.getD (j.val+1) Extended.zero)
  by_cases hmem : extra ∈ S
  · apply projection_seventeen run Extended.first extra (seeded_first_needed run raw) hmem
      (seed_distinct j d) embed
    · rw [observe_projected]
      exact congrArg observe (by decide +kernel)
    · intro v hv
      exact seeded_available (raw v hv)
    · rw [observe_projected, show projected Extended.first = zero by decide +kernel]
      exact ⟨false, by funext r; simp [observe,bit,zero]⟩
    · rw [observe_projected,seed_projects_zero j d hd]
      exact ⟨false, by funext r; simp [observe,bit,zero]⟩
  · apply pins_seventeen run
    intro v hv
    have h := raw v hv
    simp only [seeded,List.mem_append,List.mem_singleton] at h
    rcases h with hp | he
    · exact hp
    · exfalso
      apply hmem
      change Extended.bin d.val Extended.first (Extended.pins.getD (j.val+1) Extended.zero) ∈ S
      rwa [← he]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma seed_first_diff : ∀ (j : Fin 9) (d : Fin 4),
    Extended.bit (seedRow j d) Extended.first ≠
    Extended.bit (seedRowNext j d) Extended.first := by decide +kernel

lemma pair_pin_needed_moved (σ : Equiv.Perm (Fin 10)) (i j : Fin 10) (hij : i ≠ j)
    (hi : σ i = 0)
    (invariant : ∀ x : Fin 10 → Bool, Extended.f10 (fun v => x (σ v)) = Extended.f10 x)
    (d : Fin 4) {k S} (run : Extended.Live true Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ Extended.pins ∨ a = Extended.bin d.val (pin i) (pin j)) :
    pin i ∈ S := by
  have hj : σ j ≠ 0 := by
    intro h
    apply hij
    exact σ.injective (hi.trans h.symm)
  have hjval : (σ j).val ≠ 0 := by
    intro h
    exact hj (Fin.ext h)
  let l : Fin 9 := ⟨(σ j).val - 1, by have := (σ j).isLt; omega⟩
  have leq : l.val + 1 = (σ j).val := by dsimp [l]; omega
  have canon : Extended.bin d.val (pin (σ i)) (pin (σ j)) =
      Extended.bin d.val Extended.first (Extended.pins.getD (l.val + 1) Extended.zero) := by
    rw [leq, hi]
    rfl
  have needed : pin i ∈ S := by
    have diff : Extended.bit (Extended.rowMove σ (seedRow l d)) Extended.target ≠
        Extended.bit (Extended.rowMove σ (seedRowNext l d)) Extended.target := by
      rw [Extended.rowMove_target σ invariant, Extended.rowMove_target σ invariant]
      exact seed_target_diff l d
    obtain ⟨a, ha, hchange⟩ := Extended.live_row_difference run diff
    rcases raw a ha with hp | rfl
    · obtain ⟨v, rfl⟩ := pin_index hp
      by_cases hv : σ v = 0
      · have vi : v = i := σ.injective (hv.trans hi.symm)
        simpa only [vi] using ha
      · exfalso
        apply hchange
        rw [moved_pin, moved_pin]
        exact seed_pin_stable l d (σ v) hv
    · exfalso
      apply hchange
      rw [moved_bin, moved_bin, canon]
      exact seed_extra_stable l d
  exact needed

lemma pair_seventeen_moved (σ : Equiv.Perm (Fin 10)) (i j : Fin 10) (hij : i ≠ j)
    (hi : σ i = 0)
    (invariant : ∀ x : Fin 10 → Bool, Extended.f10 (fun v => x (σ v)) = Extended.f10 x)
    (d : Fin 4) (hd : d.val = 0 ∨ d.val = 2) {k S}
    (run : Extended.Live true Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ Extended.pins ∨ a = Extended.bin d.val (pin i) (pin j)) :
    17 ≤ k := by
  let extra := Extended.bin d.val (pin i) (pin j)
  by_cases hmem : extra ∈ S
  · have hj : σ j ≠ 0 := by
      intro h
      exact hij (σ.injective (hi.trans h.symm))
    have hjval : (σ j).val ≠ 0 := by intro h; exact hj (Fin.ext h)
    let l : Fin 9 := ⟨(σ j).val - 1, by have := (σ j).isLt; omega⟩
    have leq : l.val + 1 = (σ j).val := by dsimp [l]; omega
    have canon : Extended.bin d.val (pin (σ i)) (pin (σ j)) =
        Extended.bin d.val Extended.first (Extended.pins.getD (l.val + 1) Extended.zero) := by
      rw [leq, hi]
      rfl
    have distinct : pin i ≠ extra := by
      intro h
      have eq0 := congrArg (Extended.bit (Extended.rowMove σ (seedRow l d))) h
      have eq1 := congrArg (Extended.bit (Extended.rowMove σ (seedRowNext l d))) h
      change Extended.bit (Extended.rowMove σ (seedRow l d)) (pin i) =
        Extended.bit (Extended.rowMove σ (seedRow l d)) (Extended.bin d.val (pin i) (pin j)) at eq0
      change Extended.bit (Extended.rowMove σ (seedRowNext l d)) (pin i) =
        Extended.bit (Extended.rowMove σ (seedRowNext l d)) (Extended.bin d.val (pin i) (pin j)) at eq1
      rw [moved_pin, moved_bin, canon, hi] at eq0 eq1
      exact seed_first_diff l d (eq0.trans ((seed_extra_stable l d).trans eq1.symm))
    apply projection_seventeen run (pin i) extra
      (pair_pin_needed_moved σ i j hij hi invariant d run raw) hmem distinct (vertexEmbedding σ)
    · change (fun r => Extended.bit (vertexEmbedding σ r) Extended.target) = observe graph
      rw [vertexEmbedding_target σ invariant]
      change restrictRows embed (Extended.observe Extended.target) = observe graph
      rw [observe_projected]
      exact congrArg observe (by decide +kernel)
    · intro a ha
      rcases raw a ha with hp | rfl
      · obtain ⟨v, rfl⟩ := pin_index hp
        change Available true (inputs.map observe)
          (fun r => Extended.bit (vertexEmbedding σ r) (pin v))
        rw [vertexEmbedding_pin σ v]
        exact pin_available (σ v)
      · rw [embedding_bin, canon]
        apply seeded_available (j := l) (d := d)
        simp [seeded]
    · exact ⟨false, vertexEmbedding_zero σ i hi⟩
    · change Constant (restrictRows (vertexEmbedding σ)
        (Extended.observe (Extended.bin d.val (pin i) (pin j))))
      rw [embedding_bin, canon, observe_projected, seed_projects_zero l d hd]
      exact ⟨false, by funext r; simp [observe,bit,zero]⟩
  · apply pins_seventeen run
    intro v hv
    rcases raw v hv with hp | he
    · exact hp
    · exfalso
      apply hmem
      change Extended.bin d.val (pin i) (pin j) ∈ S
      rwa [← he]

lemma pair_seventeen_direct {d : Nat} {a b : Extended.Sig}
    (hd : d = 0 ∨ d = 2) (ha : a ∈ Extended.pins) (hb : b ∈ Extended.pins)
    (distinct : a ≠ b) {k S} (run : Extended.Live true Extended.target k S)
    (raw : ∀ v ∈ S, v ∈ Extended.pins ∨ v = Extended.bin d a b) : 17 ≤ k := by
  obtain ⟨i, rfl⟩ := pin_index ha
  obtain ⟨j, rfl⟩ := pin_index hb
  have hij : i ≠ j := by intro h; exact distinct (h ▸ rfl)
  obtain ⟨σ, hi, _, invariant⟩ := PEqualNP.Outside.L_meta_2592.Automorphisms.canonical_pair i j hij
  have hlt : d < 4 := by omega
  have invariant' : ∀ x : Fin 10 → Bool, Extended.f10 (fun v => x (σ v)) = Extended.f10 x := by
    intro x
    simpa [Extended.f10, PEqualNP.Outside.L_meta_2592.Automorphisms.value,
      PEqualNP.Outside.L_meta_2592.Automorphisms.edges, List.any_cons, List.any_nil,
      Bool.or_false, Bool.or_assoc] using invariant x
  exact pair_seventeen_moved σ i j hij hi invariant' ⟨d, hlt⟩ hd run raw

lemma pair_seventeen {d : Nat} {a b : Extended.Sig}
    (allowed : Extended.allowed true d) (nonOr : d ≠ 1)
    (ha : a ∈ Extended.pins) (hb : b ∈ Extended.pins)
    (distinct : a ≠ b) {k S} (run : Extended.Live true Extended.target k S)
    (raw : ∀ v ∈ S, v ∈ Extended.pins ∨ v = Extended.bin d a b) : 17 ≤ k := by
  have cases : d = 0 ∨ d = 2 ∨ d = 3 := by
    rcases allowed with hd | ⟨_, hd⟩ <;> omega
  rcases cases with hd | hd | hd
  · exact pair_seventeen_direct (Or.inl hd) ha hb distinct run raw
  · exact pair_seventeen_direct (Or.inr hd) ha hb distinct run raw
  · subst d
    apply pair_seventeen_direct (Or.inr rfl) hb ha distinct.symm run
    intro v hv
    rcases raw v hv with hp | he
    · exact Or.inl hp
    · right
      simpa [Extended.bin, BitVec.and_comm] using he

end PEqualNP.Outside.L_meta_2592.FewNot
