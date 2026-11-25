namespace PEqualNP.Outside.L_meta_2592.Signed.Extended
lemma live_to_true {u k S T} (run : Live u T k S) : Live true T k S := by
  induction k generalizing S with
  | zero => exact run
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,ha,hb,diff,fresh,tail⟩ := run
    have hd' : allowed true d := by
      rcases hd with h | ⟨_,h⟩
      · exact Or.inl h
      · exact Or.inr ⟨rfl,h⟩
    exact ⟨U,a,b,d,hd',rfl,ha,hb,diff,fresh,ih tail⟩
end PEqualNP.Outside.L_meta_2592.Signed.Extended
namespace PEqualNP.Outside.L_meta_2592.Signed
lemma pin_projection_mode (u : Bool) (a : Extended.Sig) (mem : a ∈ Extended.pins) :
    ∃ rows : Row → Extended.Row,
      restrictRows rows (Extended.observe a) = (fun _ => false) ∧
      restrictRows rows (Extended.observe Extended.target) = observe graph ∧
      ∀ b ∈ Extended.pins,
        Available u (inputs.map observe) (restrictRows rows (Extended.observe b)) := by
  have listing : List.ofFn (fun i : Fin 10 => Extended.pins.getD i.val Extended.zero) =
      Extended.pins := by rfl
  rw [←listing] at mem
  obtain ⟨v, rfl⟩ := List.mem_ofFn.mp mem
  obtain ⟨targetEq, zeroEq, supplyEq⟩ := projectionChecked v
  have isZero : observe zero = fun _ => false := by funext r; simp [observe, bit, zero]
  refine ⟨rowsAt v, ?_, ?_, ?_⟩
  · rw [observe_projectedBy, zeroEq]
    exact isZero
  · rw [observe_projectedBy, targetEq]
  · intro b hb
    rw [observe_projectedBy]
    have allowed := List.all_eq_true.mp supplyEq b hb
    simp only [Bool.or_eq_true, beq_iff_eq] at allowed
    rcases allowed with hz | hin
    · exact Or.inr (Or.inl ⟨false, hz ▸ isZero⟩)
    · exact Or.inl (List.mem_map.mpr ⟨_, by simpa using hin, rfl⟩)

lemma atLeastEighteenMono (floor16 : Lower false inputs graph 16) {k S} (run : Extended.Live false Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ Extended.pins) : 18 ≤ k := by
  classical
  cases k with
  | zero =>
    obtain ⟨rfl, _⟩ := run
    have member := raw Extended.target (by simp)
    exact False.elim ((by decide +kernel : Extended.target ∉ Extended.pins) member)
  | succ k =>
    obtain ⟨U, a, b, d, hd, rfl, ha, hb, distinct, fresh, tail⟩ := run
    have aPin : a ∈ Extended.pins := raw a (by simp)
    have bPin : b ∈ Extended.pins := raw b (by simp)
    have rawU : ∀ z ∈ U, z ∈ Extended.pins := by
      intro z hz
      exact raw z (by simp [hz])
    have hd4 : d < 4 := by rcases hd with h | ⟨_, h⟩ <;> omega
    obtain ⟨aKept, bKept⟩ := Extended.first_gate_keeps_both aPin bPin distinct hd4 rawU (Extended.live_to_true tail)
    have freshU : Extended.bin d a b ∉ U := by
      intro member
      exact fresh (by simp [member])
    have tailRun := Extended.tail_with_retained_inputs distinct aKept bKept freshU tail
    obtain ⟨rows, fixed, same, supplied⟩ := pin_projection_mode false a aPin
    have sup : supply false (inputs.map observe)
        ((Extended.observe a :: Extended.observe b ::
          ((U.erase a).erase b).toList.map Extended.observe).map (restrictRows rows)) := by
      intro v hv
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
      rcases List.mem_cons.mp hw with rfl | hw
      · exact supplied a aPin
      · rcases List.mem_cons.mp hw with rfl | hw
        · exact supplied b bPin
        · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hw
          exact supplied z (rawU z ((Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_toList.mp hz)).2).2))
    have op : allowed false d := hd
    have bound := kept_projection_charge rows op tailRun
      (same ▸ observe_proper graph_proper) sup (Or.inl ⟨rfl, ⟨false, fixed⟩⟩)
      (by
        intro q bs reach hit
        apply floor16 q bs reach
        rwa [same] at hit)
    omega

end PEqualNP.Outside.L_meta_2592.Signed
