import FewNotBase
import PermutationSupport
import RowEmbeddingSupport

namespace PEqualNP.Outside.L_meta_2592.FewNot

lemma projection_sixteen {k S} (run : Extended.Live true Extended.target k S)
    (frontSignal : Extended.Sig) (frontMem : frontSignal ∈ S)
    (rows : Row → Extended.Row)
    (same : restrictRows rows (Extended.observe Extended.target) = observe graph)
    (supplied : ∀ a ∈ S,
      Available true (inputs.map observe) (restrictRows rows (Extended.observe a)))
    (constant : Constant (restrictRows rows (Extended.observe frontSignal))) : 16 ≤ k := by
  classical
  let front := frontSignal :: (S.erase frontSignal).toList
  have nd : front.Nodup := by
    apply List.nodup_cons.mpr
    exact ⟨by simp, Finset.nodup_toList _⟩
  have eqS : front.toFinset = S := by
    ext a
    by_cases ha : a = frontSignal <;> simp [front, ha, frontMem]
  have hrun := Extended.list_run run front nd eqS
  have supplyRoots : supply true (inputs.map observe)
      ((front.map Extended.observe).map (restrictRows rows)) := by
    intro v hv
    obtain ⟨_, hin, rfl⟩ := List.mem_map.mp hv
    obtain ⟨a, hmFront, rfl⟩ := List.mem_map.mp hin
    exact supplied a (eqS ▸ List.mem_toFinset.mpr hmFront)
  have need := projected_bound rows hrun (same ▸ observe_proper graph_proper)
    Reach.start supplyRoots (L := 15) (same ▸ nineFloor)
  have charge : 1 ≤ mass ((front.map Extended.observe).map (restrictRows rows)) := by
    simp [front, mass_cons, cost, constant]
  omega



def seeded (j : Fin 9) (d : Fin 4) : List Extended.Sig :=
  Extended.pins ++ [Extended.bin d.val Extended.first (Extended.pins.getD (j.val + 1) Extended.zero)]

def seedRow (j : Fin 9) (d : Fin 4) : Extended.Row :=
  if d.val = 0 ∨ d.val = 3 then
    if j.val = 0 then 64 else 128
  else
    (![128, 96, 384, 64, 16, 68, 129, 136, 130] : Fin 9 → Extended.Row) j

def seedRowNext (j : Fin 9) (d : Fin 4) : Extended.Row :=
  ⟨(seedRow j d).val + 512, by
    fin_cases j <;> fin_cases d <;> decide⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma seed_target_diff : ∀ (j : Fin 9) (d : Fin 4),
    Extended.bit (seedRow j d) Extended.target ≠
      Extended.bit (seedRowNext j d) Extended.target := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma seed_stable : ∀ (j : Fin 9) (d : Fin 4),
    (seeded j d).all (fun a =>
      (Extended.bit (seedRow j d) a == Extended.bit (seedRowNext j d) a) ||
        (a == Extended.first)) = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma seed_permitted : ∀ (j : Fin 9) (d : Fin 4),
    (seeded j d).all (fun a =>
      (projected a == zero) || inputs.contains (projected a)) = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma seed_zero : ∀ (j : Fin 9) (d : Fin 4),
    Extended.bit 0 (Extended.bin d.val Extended.first
      (Extended.pins.getD (j.val + 1) Extended.zero)) = false := by decide +kernel


set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma seed_extra_stable : ∀ (j : Fin 9) (d : Fin 4),
    Extended.bit (seedRow j d)
      (Extended.bin d.val Extended.first (Extended.pins.getD (j.val + 1) Extended.zero)) =
    Extended.bit (seedRowNext j d)
      (Extended.bin d.val Extended.first (Extended.pins.getD (j.val + 1) Extended.zero)) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma seed_pin_stable : ∀ (j : Fin 9) (d : Fin 4) (v : Fin 10), v ≠ 0 →
    Extended.bit (seedRow j d) (Extended.pins.getD v.val Extended.zero) =
      Extended.bit (seedRowNext j d) (Extended.pins.getD v.val Extended.zero) := by
  decide +kernel


lemma seeded_first_needed {j d k S} (run : Extended.Live true Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ seeded j d) : Extended.first ∈ S := by
  obtain ⟨a, ha, hchange⟩ := Extended.live_row_difference run (seed_target_diff j d)
  have chk := List.all_eq_true.mp (seed_stable j d) a (raw a ha)
  simp only [Bool.or_eq_true, beq_iff_eq] at chk
  exact chk.resolve_left hchange ▸ ha

lemma seeded_sixteen {j d k S} (run : Extended.Live true Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ seeded j d) : 16 ≤ k := by
  apply projection_sixteen run Extended.first (seeded_first_needed run raw) embed
  · rw [observe_projected]
    exact congrArg observe (by decide +kernel)
  · intro a ha
    rw [observe_projected]
    have chk := List.all_eq_true.mp (seed_permitted j d) a (raw a ha)
    simp only [Bool.or_eq_true, beq_iff_eq] at chk
    rcases chk with hz | hm
    · exact Or.inr (Or.inl ⟨false, hz ▸ by funext r; simp [observe, bit, zero]⟩)
    · exact Or.inl (List.mem_map.mpr ⟨_, by simpa using hm, rfl⟩)
  · rw [observe_projected, show projected Extended.first = zero by decide +kernel]
    exact ⟨false, by funext r; simp [observe, bit, zero]⟩



abbrev pin (i : Fin 10) : Extended.Sig := Extended.pins.getD i.val Extended.zero

lemma pins_ofFn : List.ofFn pin = Extended.pins := by decide +kernel

lemma pin_mem (i : Fin 10) : pin i ∈ Extended.pins := by
  rw [← pins_ofFn]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩

lemma pin_index {a : Extended.Sig} (h : a ∈ Extended.pins) : ∃ i : Fin 10, pin i = a := by
  rw [← pins_ofFn] at h
  exact List.mem_ofFn.mp h

lemma moved_pin (σ : Fin 10 → Fin 10) (r : Extended.Row) (i : Fin 10) :
    Extended.bit (Extended.rowMove σ r) (pin i) = Extended.bit r (pin (σ i)) :=
  Extended.rowMove_assign σ r i

lemma moved_bin (σ : Fin 10 → Fin 10) (r : Extended.Row) (d : Nat) (i j : Fin 10) :
    Extended.bit (Extended.rowMove σ r) (Extended.bin d (pin i) (pin j)) =
      Extended.bit r (Extended.bin d (pin (σ i)) (pin (σ j))) := by
  simp only [Extended.bit_bin, moved_pin]

lemma embedding_bin (σ : Fin 10 → Fin 10) (d : Nat) (i j : Fin 10) :
    restrictRows (vertexEmbedding σ) (Extended.observe (Extended.bin d (pin i) (pin j))) =
      restrictRows embed (Extended.observe (Extended.bin d (pin (σ i)) (pin (σ j)))) := by
  funext r
  exact moved_bin σ (embed r) d i j

lemma seeded_available {j d a} (ha : a ∈ seeded j d) :
    Available true (inputs.map observe) (restrictRows embed (Extended.observe a)) := by
  rw [observe_projected]
  have chk := List.all_eq_true.mp (seed_permitted j d) a ha
  simp only [Bool.or_eq_true, beq_iff_eq] at chk
  rcases chk with hz | hm
  · exact Or.inr (Or.inl ⟨false, hz ▸ by funext r; simp [observe, bit, zero]⟩)
  · exact Or.inl (List.mem_map.mpr ⟨_, by simpa using hm, rfl⟩)

lemma pin_available (i : Fin 10) :
    Available true (inputs.map observe) (restrictRows embed (Extended.observe (pin i))) := by
  apply seeded_available (j := 0) (d := 0)
  exact List.mem_append.mpr (Or.inl (pin_mem i))

lemma pair_sixteen_moved (σ : Equiv.Perm (Fin 10)) (i j : Fin 10) (hij : i ≠ j)
    (hi : σ i = 0)
    (invariant : ∀ x : Fin 10 → Bool, Extended.f10 (fun v => x (σ v)) = Extended.f10 x)
    (d : Fin 4) {k S} (run : Extended.Live true Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ Extended.pins ∨ a = Extended.bin d.val (pin i) (pin j)) :
    16 ≤ k := by
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
  apply projection_sixteen run (pin i) needed (vertexEmbedding σ)
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

lemma pair_sixteen {d : Nat} {a b : Extended.Sig}
    (allowed : Extended.allowed true d) (ha : a ∈ Extended.pins) (hb : b ∈ Extended.pins)
    (distinct : a ≠ b) {k S} (run : Extended.Live true Extended.target k S)
    (raw : ∀ v ∈ S, v ∈ Extended.pins ∨ v = Extended.bin d a b) : 16 ≤ k := by
  obtain ⟨i, rfl⟩ := pin_index ha
  obtain ⟨j, rfl⟩ := pin_index hb
  have hij : i ≠ j := by intro h; exact distinct (h ▸ rfl)
  obtain ⟨σ, hi, _, invariant⟩ := PEqualNP.Outside.L_meta_2592.Automorphisms.canonical_pair i j hij
  have hd : d < 4 := by
    rcases allowed with h | ⟨_, h⟩ <;> omega
  have invariant' : ∀ x : Fin 10 → Bool, Extended.f10 (fun v => x (σ v)) = Extended.f10 x := by
    intro x
    simpa [Extended.f10, PEqualNP.Outside.L_meta_2592.Automorphisms.value,
      PEqualNP.Outside.L_meta_2592.Automorphisms.edges, List.any_cons, List.any_nil,
      Bool.or_false, Bool.or_assoc] using invariant x
  exact pair_sixteen_moved σ i j hij hi invariant' ⟨d, hd⟩ run raw

end PEqualNP.Outside.L_meta_2592.FewNot
