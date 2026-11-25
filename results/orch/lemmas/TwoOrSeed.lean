import FewNotGeneric

namespace PEqualNP.Outside.L_meta_2592.FewNot

def twoOrBase (j k : Fin 9) : Fin 512 :=
  (![128,0,384,192,144,0,129,136,130,0,48,0,96,48,52,0,104,50,384,0,272,0,272,276,385,0,274,192,96,0,64,80,68,65,72,0,144,48,272,80,16,20,0,0,18,0,52,276,68,20,20,69,0,0,129,0,385,65,0,69,65,73,0,136,104,0,72,0,0,73,72,138,130,50,274,0,18,0,0,138,18] : Fin 81 → Fin 512) ⟨9*j.val+k.val,by omega⟩

def twoOrRow (j k : Fin 9) : Extended.Row :=
  ⟨(twoOrBase j k).val,lt_trans (twoOrBase j k).isLt (by decide)⟩

def twoOrNext (j k : Fin 9) : Extended.Row :=
  ⟨(twoOrBase j k).val+512,by have := (twoOrBase j k).isLt; omega⟩

def twoOrPairRow (j k : Fin 9) : Extended.Row :=
  Extended.encode (fun v => decide (v.val = j.val+1 ∨ v.val = k.val+1))

def twoOrIndependent (j k : Fin 9) : Prop :=
  Extended.bit (twoOrPairRow j k) Extended.target = false

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma twoOr_witness : ∀ j k : Fin 9, twoOrIndependent j k →
    Extended.bit (twoOrRow j k) Extended.target ≠ Extended.bit (twoOrNext j k) Extended.target ∧
    Extended.bit (twoOrRow j k)
      (Extended.bin 1 Extended.first (pin ⟨j.val+1,by omega⟩)) =
      Extended.bit (twoOrNext j k) (Extended.bin 1 Extended.first (pin ⟨j.val+1,by omega⟩)) ∧
    Extended.bit (twoOrRow j k)
      (Extended.bin 1 Extended.first (pin ⟨k.val+1,by omega⟩)) =
      Extended.bit (twoOrNext j k) (Extended.bin 1 Extended.first (pin ⟨k.val+1,by omega⟩)) ∧
    (∀ v : Fin 10, v ≠ 0 →
      Extended.bit (twoOrRow j k) (pin v) = Extended.bit (twoOrNext j k) (pin v)) := by
  unfold twoOrIndependent
  decide +kernel

lemma or_pin_available (j : Fin 10) (hj : j ≠ 0) :
    Available true (inputs.map observe)
      (restrictRows embed (Extended.observe (Extended.bin 1 Extended.first (pin j)))) := by
  let l : Fin 9 := ⟨j.val-1,by have := j.isLt; omega⟩
  have hjval : j.val ≠ 0 := by intro h; exact hj (Fin.ext h)
  have he : l.val+1 = j.val := by dsimp [l];omega
  apply seeded_available (j := l) (d := 1)
  simp only [seeded,List.mem_append,List.mem_singleton]
  right
  change Extended.bin 1 Extended.first (Extended.pins.getD j.val Extended.zero) =
    Extended.bin 1 Extended.first (Extended.pins.getD (l.val+1) Extended.zero)
  rw [he]

lemma twoOr_sixteen_moved (σ : Equiv.Perm (Fin 10)) (i j l : Fin 10)
    (hij : i ≠ j) (hil : i ≠ l) (hi : σ i = 0)
    (invariant : ∀ x : Fin 10 → Bool, Extended.f10 (fun v => x (σ v)) = Extended.f10 x)
    (independent : Extended.f10 (fun v => decide (v = σ j ∨ v = σ l)) = false)
    {k S} (run : Extended.Live true Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ Extended.pins ∨
      a = Extended.bin 1 (pin i) (pin j) ∨ a = Extended.bin 1 (pin i) (pin l)) : 16 ≤ k := by
  have hj : σ j ≠ 0 := by intro h; exact hij (σ.injective (hi.trans h.symm))
  have hl : σ l ≠ 0 := by intro h; exact hil (σ.injective (hi.trans h.symm))
  have hjv : (σ j).val ≠ 0 := by intro h; exact hj (Fin.ext h)
  have hlv : (σ l).val ≠ 0 := by intro h; exact hl (Fin.ext h)
  let jj : Fin 9 := ⟨(σ j).val-1,by have := (σ j).isLt;omega⟩
  let ll : Fin 9 := ⟨(σ l).val-1,by have := (σ l).isLt;omega⟩
  have ej : jj.val+1 = (σ j).val := by dsimp [jj];omega
  have el : ll.val+1 = (σ l).val := by dsimp [ll];omega
  have ind : twoOrIndependent jj ll := by
    change Extended.bit (Extended.encode _) Extended.target = false
    rw [Extended.rowTarget]
    have has : Extended.assign (Extended.encode (fun v : Fin 10 =>
        decide (v.val = jj.val+1 ∨ v.val = ll.val+1))) =
        (fun v => decide (v.val = jj.val+1 ∨ v.val = ll.val+1)) :=
      funext (Extended.assign_encode _)
    rw [has]
    have heq : (fun v : Fin 10 => decide (v.val = jj.val+1 ∨ v.val = ll.val+1)) =
        (fun v : Fin 10 => decide (v = σ j ∨ v = σ l)) := by
      funext v
      rw [ej,el]
      simp only [Fin.ext_iff]
    rwa [heq]
  obtain ⟨ht,hjstable,hlstable,hpins⟩ := twoOr_witness jj ll ind
  have needed : pin i ∈ S := by
    have diff : Extended.bit (Extended.rowMove σ (twoOrRow jj ll)) Extended.target ≠
        Extended.bit (Extended.rowMove σ (twoOrNext jj ll)) Extended.target := by
      rw [Extended.rowMove_target σ invariant,Extended.rowMove_target σ invariant]
      exact ht
    obtain ⟨a,ha,hchange⟩ := Extended.live_row_difference run diff
    rcases raw a ha with hp | rfl | rfl
    · obtain ⟨v,rfl⟩ := pin_index hp
      by_cases hv : σ v = 0
      · have hv' : v = i := σ.injective (hv.trans hi.symm)
        simpa only [hv'] using ha
      · exact False.elim (hchange (by rw [moved_pin,moved_pin];exact hpins (σ v) hv))
    · exfalso
      apply hchange
      rw [moved_bin,moved_bin,hi]
      have hpj : (⟨jj.val+1,by omega⟩ : Fin 10) = σ j := Fin.ext ej
      simpa only [hpj,show pin 0 = Extended.first from rfl] using hjstable
    · exfalso
      apply hchange
      rw [moved_bin,moved_bin,hi]
      have hpl : (⟨ll.val+1,by omega⟩ : Fin 10) = σ l := Fin.ext el
      simpa only [hpl,show pin 0 = Extended.first from rfl] using hlstable
  apply projection_sixteen run (pin i) needed (vertexEmbedding σ)
  · change (fun r => Extended.bit (vertexEmbedding σ r) Extended.target) = observe graph
    rw [vertexEmbedding_target σ invariant]
    change restrictRows embed (Extended.observe Extended.target) = observe graph
    rw [observe_projected]
    exact congrArg observe (by decide +kernel)
  · intro a ha
    rcases raw a ha with hp | rfl | rfl
    · obtain ⟨v,rfl⟩ := pin_index hp
      change Available true (inputs.map observe) (fun r => Extended.bit (vertexEmbedding σ r) (pin v))
      rw [vertexEmbedding_pin σ v]
      exact pin_available (σ v)
    · rw [embedding_bin,hi]
      exact or_pin_available (σ j) hj
    · rw [embedding_bin,hi]
      exact or_pin_available (σ l) hl
  · exact ⟨false,vertexEmbedding_zero σ i hi⟩

lemma twoOr_sixteen (i j l : Fin 10) (hij : i ≠ j) (hil : i ≠ l)
    (independent : Extended.f10 (fun v => decide (v = j ∨ v = l)) = false)
    {k S} (run : Extended.Live true Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ Extended.pins ∨
      a = Extended.bin 1 (pin i) (pin j) ∨ a = Extended.bin 1 (pin i) (pin l)) : 16 ≤ k := by
  obtain ⟨σ, hi, _, invariant⟩ := PEqualNP.Outside.L_meta_2592.Automorphisms.canonical_pair i j hij
  have invariant' : ∀ x : Fin 10 → Bool, Extended.f10 (fun v => x (σ v)) = Extended.f10 x := by
    intro x
    simpa [Extended.f10, PEqualNP.Outside.L_meta_2592.Automorphisms.value,
      PEqualNP.Outside.L_meta_2592.Automorphisms.edges, List.any_cons, List.any_nil,
      Bool.or_false, Bool.or_assoc] using invariant x
  apply twoOr_sixteen_moved σ i j l hij hil hi invariant' _ run raw
  have eq := invariant' (fun v => decide (v = σ j ∨ v = σ l))
  have preimage : (fun v => decide (σ v = σ j ∨ σ v = σ l)) =
      (fun v : Fin 10 => decide (v = j ∨ v = l)) := by
    funext v
    simp only [Equiv.apply_eq_iff_eq]
  rw [preimage,independent] at eq
  exact eq.symm

end PEqualNP.Outside.L_meta_2592.FewNot
