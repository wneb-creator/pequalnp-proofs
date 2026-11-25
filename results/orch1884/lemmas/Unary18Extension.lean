namespace Extended

def unaryWord (h : Bool → Bool) : Sig :=
  if h false then (if h true then one else neg (pins.getD 0 zero))
  else (if h true then pins.getD 0 zero else zero)

def unaryInitial (m : Fin 10 → Fin 10) (h : Bool → Bool) : List Sig :=
  List.ofFn (fun i => pins.getD (m i).val zero) ++ [unaryWord h]

lemma unary_bits (h : Bool → Bool) (r : Row) :
    bit r (unaryWord h) = h (assign r 0) := by
  change bit r (unaryWord h) = h (bit r (pins.getD 0 zero))
  cases hf : h false <;> cases ht : h true <;>
    cases hb : bit r (pins.getD 0 zero) <;>
    simp only [unaryWord, hf, ht, Bool.false_eq_true, ite_false, ite_true,
      bit_zero, bit_one, bit_neg, hb, Bool.not_true, Bool.not_false]

lemma unary_rows (m : Fin 10 → Fin 10) (h : Bool → Bool) (r : Row) :
    (unaryInitial m h).map (bit r) = List.ofFn (assign r ∘ m) ++ [h (assign r 0)] := by
  simp [unaryInitial, List.map_ofFn, Function.comp_def, assign, unary_bits]

lemma pin_mem (i : Fin 10) : pins.getD i.val zero ∈ initial := by
  have eq : List.ofFn (fun i : Fin 10 => pins.getD i.val zero) = initial := by decide +kernel
  rw [← eq]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩

lemma live_roots_proper {u T k S} (run : Live u T k S) : ∀ a ∈ S, proper a := by
  induction run using Live.ind with
  | stop hp => simpa using hp
  | @binary k U a b d hd ha hb hab hf tail ih =>
    intro v h
    rcases Finset.mem_insert.mp h with rfl | h
    · exact ha
    rcases Finset.mem_insert.mp h with rfl | h
    · exact hb
    exact ih _ (Finset.mem_insert_of_mem h)

theorem realizeUnaryMono (C : Circuit) (m : Fin 10 → Fin 10) (h : Bool → Bool)
    (legal : PEqualNP.MetaComplexity.Monotone2 C)
    (correct : ∀ x : Fin 10 → Bool,
      C.eval (List.ofFn (x ∘ m) ++ [h (x 0)]) = f10 x) :
    ∃ k S, k ≤ C.size ∧ Live false target k S ∧
      ∀ a ∈ S, a ∈ initial ∨ a = neg (pins.getD 0 zero) := by
  have fan : PEqualNP.MetaComplexity.FanInTwo C := by
    intro g hg
    obtain ⟨ho, hl⟩ := legal g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ho ⊢
    exact ⟨ho.imp id Or.inl, hl⟩
  have mono : ∀ g ∈ C.gates, isNot g = false := by
    intro g hg
    have ho := (legal g hg).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ho
    rcases ho with ho | ho <;> simp [isNot, ho]
  have he : (execute C.gates (unaryInitial m h)).getD C.output zero = target := by
    apply bit_ext
    intro r
    rw [← b_read, execute_bits _ _ _ (fun g hg => (fan g hg).1)]
    change (C.wires ((unaryInitial m h).map (bit r))).getD C.output false = _
    rw [unary_rows]
    exact (correct _).trans (rowTarget r).symm
  have hp : proper target := by unfold proper; decide +kernel
  have out := get_rep (u := false) (execute C.gates (unaryInitial m h)) C.output
  rw [he] at out
  unfold Repr at out
  simp only [nrm, Bool.false_and, Bool.false_eq_true, ite_false] at out
  obtain ⟨k, S, hk, run, hs⟩ := extract C.gates (unaryInitial m h) fan (u := false)
    (fun _ => mono) hp (out.resolve_right (fun h => h hp))
  have hnrm : nrm false = id := rfl
  rw [hnrm, List.map_id] at hs
  refine ⟨k, S, hk.trans List.countP_le_length, run, ?_⟩
  intro a ha
  have pa := live_roots_proper run a ha
  have hm := hs a ha
  simp only [unaryInitial, List.mem_append, List.mem_singleton] at hm
  rcases hm with hm | rfl
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hm
    exact Or.inl (pin_mem (m i))
  · cases hf : h false <;> cases ht : h true <;>
      simp only [unaryWord, hf, ht, Bool.false_eq_true, ite_false, ite_true] at pa ⊢
    · exact False.elim (pa.1 rfl)
    · exact Or.inl (pin_mem 0)
    · exact Or.inr trivial
    · exact False.elim (pa.2 rfl)

lemma binary_increase {d : Nat} (hd : allowed false d) (a b : Sig) (r s : Row)
    (hr : bit r (bin d a b) = false) (hs : bit s (bin d a b) = true) :
    (bit r a = false ∧ bit s a = true) ∨ (bit r b = false ∧ bit s b = true) := by
  have hlt : d < 2 := by simpa [allowed] using hd
  have hd' : d = 0 ∨ d = 1 := by omega
  rcases hd' with rfl | rfl
  all_goals
    cases hra : bit r a <;> cases hrb : bit r b <;>
      cases hsa : bit s a <;> cases hsb : bit s b <;>
      simp_all [bin, bit]

theorem live_row_increase {T k S} (h : Live false T k S) {r s : Row}
    (hr : bit r T = false) (hs : bit s T = true) :
    ∃ a ∈ S, bit r a = false ∧ bit s a = true := by
  induction h using Live.ind with
  | stop hp => exact ⟨_, by simp, hr, hs⟩
  | @binary k U a b d hd ha hb hab hf tail ih =>
    obtain ⟨v, hv, hvr, hvs⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rcases binary_increase hd a b r s hvr hvs with ha | hb
      · exact ⟨a, by simp, ha⟩
      · exact ⟨b, by simp, hb⟩
    · exact ⟨v, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu), hvr, hvs⟩

end Extended

namespace Geometry

lemma base_bit_one (r : Row) : bit r one = true := by
  have all : ∀ r : Row, bit r one = true := by decide +kernel
  exact all r

lemma unary_needs_positive {k S} (run : Extended.Live false Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ Extended.initial ∨ a = Extended.neg (pin 0)) : pin 0 ∈ S := by
  obtain ⟨a, ha, hfalse, htrue⟩ := Extended.live_row_increase run
    (r := 128) (s := 640) (by decide +kernel) (by decide +kernel)
  rcases raw a ha with hpin | rfl
  · obtain ⟨i, rfl⟩ := (pin_mem_iff a).mp hpin
    have unique : ∀ i : Fin 10,
        Extended.bit 128 (pin i) = false → Extended.bit 640 (pin i) = true → i = 0 := by
      decide +kernel
    simpa [unique i hfalse htrue] using ha
  · have opposite : Extended.bit 128 (Extended.neg (pin 0)) = true := by decide +kernel
    rw [opposite] at hfalse
    contradiction

lemma unary_binary_floor_eighteen (nineMonoFloor : Lower false inputs graph 16)
    {k S} (run : Extended.Live false Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ Extended.initial ∨ a = Extended.neg (pin 0)) : 18 ≤ k := by
  classical
  by_cases hneg : Extended.neg (pin 0) ∈ S
  · have hpos := unary_needs_positive run raw
    let q := Extended.neg (pin 0)
    have hneq : q ≠ pin 0 := by decide +kernel
    let front := pin 0 :: q :: ((S.erase (pin 0)).erase q).toList
    have nd : front.Nodup := by
      apply List.nodup_cons.mpr
      refine ⟨?_, ?_⟩
      · simp [q, Ne.symm hneq]
      · apply List.nodup_cons.mpr
        exact ⟨by simp, Finset.nodup_toList _⟩
    have eqS : front.toFinset = S := by
      ext a
      by_cases ha : a = pin 0 <;> by_cases hqa : a = q <;>
        simp [front, ha, hqa, hpos, hneg, q]
    have hrun := Extended.list_run run front nd eqS
    have same : restrictRows (embedV 0) (Extended.observe Extended.target) = observe graph := by
      rw [observe_projectV, project_target]
    have projq : projectV 0 q = one := by decide +kernel
    have roots : supply false (inputs.map observe)
        ((front.map Extended.observe).map (restrictRows (embedV 0))) := by
      intro a ha
      obtain ⟨_, hm, rfl⟩ := List.mem_map.mp ha
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hm
      rw [observe_projectV]
      rcases raw b (eqS ▸ List.mem_toFinset.mpr hb) with horig | rfl
      · obtain ⟨i, rfl⟩ := (pin_mem_iff b).mp horig
        exact projected_available_mono _ (project_pin 0 i)
      · change Available false (inputs.map observe) (observe (projectV 0 q))
        rw [projq]
        exact Or.inr (Or.inl ⟨true, by funext r; exact base_bit_one r⟩)
    have lower := projected_bound (embedV 0) hrun (same ▸ observe_proper graph_proper)
      Reach.start roots (L := 16) (same ▸ nineMonoFloor)
    have cpin : Constant (restrictRows (embedV 0) (Extended.observe (pin 0))) := by
      rw [observe_projectV, project_self]
      exact ⟨false, by funext r; simp [observe, bit, zero]⟩
    have cq : Constant (restrictRows (embedV 0) (Extended.observe q)) := by
      rw [observe_projectV, projq]
      exact ⟨true, by funext r; exact base_bit_one r⟩
    have charge : 2 ≤ mass ((front.map Extended.observe).map (restrictRows (embedV 0))) := by
      simp [front, mass_cons, cost, cpin, cq]
      omega
    omega
  · apply binary_floor_eighteen nineMonoFloor run
    intro a ha
    exact (raw a ha).resolve_right (fun he => hneg (he ▸ ha))

end Geometry

theorem unary_mono_eighteen (nineMonoFloor : Lower false inputs graph 16)
    (C : Circuit) (m : Fin 10 → Fin 10) (h : Bool → Bool)
    (legal : PEqualNP.MetaComplexity.Monotone2 C)
    (correct : ∀ x : Fin 10 → Bool,
      C.eval (List.ofFn (x ∘ m) ++ [h (x 0)]) = Extended.f10 x) : 18 ≤ C.size := by
  obtain ⟨k, S, hk, run, raw⟩ := Extended.realizeUnaryMono C m h legal correct
  exact (Geometry.unary_binary_floor_eighteen nineMonoFloor run raw).trans hk
