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

lemma normalized_pin (i : Fin 10) :
    nrm true (pins.getD i.val zero) = pins.getD i.val zero := by
  apply nrm_id
  fin_cases i <;> decide +kernel

lemma normalized_unary (h : Bool → Bool) :
    nrm true (unaryWord h) = zero ∨ nrm true (unaryWord h) = pins.getD 0 zero := by
  cases hf : h false <;> cases ht : h true <;>
    simp only [unaryWord, hf, ht, Bool.false_eq_true, ite_false, ite_true] <;>
    decide +kernel

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

theorem realizeUnary (C : Circuit) (m : Fin 10 → Fin 10) (h : Bool → Bool)
    (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (correct : ∀ x : Fin 10 → Bool,
      C.eval (List.ofFn (x ∘ m) ++ [h (x 0)]) = f10 x) :
    ∃ k S, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live true target k S ∧
      ∀ a ∈ S, a ∈ initial := by
  have he : (execute C.gates (unaryInitial m h)).getD C.output zero = target := by
    apply bit_ext
    intro r
    rw [← b_read, execute_bits _ _ _ (fun g hg => (legal g hg).1)]
    change (C.wires ((unaryInitial m h).map (bit r))).getD C.output false = _
    rw [unary_rows]
    exact (correct _).trans (rowTarget r).symm
  have hp : proper target := by unfold proper; decide +kernel
  have out := get_rep (u := true) (execute C.gates (unaryInitial m h)) C.output
  rw [he] at out
  unfold Repr at out
  rw [nrm_id (show bit 0 target = false by decide +kernel)] at out
  obtain ⟨k, S, hk, run, hs⟩ := extract C.gates (unaryInitial m h) legal (u := true)
    (by simp) hp (out.resolve_right (fun h => h hp))
  refine ⟨k, S, hk, run, ?_⟩
  intro a ha
  have pa := live_roots_proper run a ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp (hs a ha)
  simp only [unaryInitial, List.mem_append, List.mem_singleton] at hb
  rcases hb with hb | rfl
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
    rw [normalized_pin]
    exact pin_mem (m i)
  · rcases normalized_unary h with hz | hi
    · exact False.elim (pa.1 hz)
    · rw [hi]
      exact pin_mem 0

lemma live_to_extended {u T k S} (run : Live u T k S) : Extended.Live u T k S := by
  induction run using Live.ind with
  | stop hp => exact Extended.Live.stop hp
  | binary hd ha hb hab hf tail ih => exact Extended.Live.binary hd ha hb hab hf ih

end UnaryModel

theorem unary_seventeen_plus_not (C : Circuit) (m : Fin 10 → Fin 10) (h : Bool → Bool)
    (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (correct : ∀ x : Fin 10 → Bool,
      C.eval (List.ofFn (x ∘ m) ++ [h (x 0)]) = UnaryModel.f10 x) :
    17 + PEqualNP.NotBracket.notCount C ≤ C.size := by
  obtain ⟨k, S, hk, run, raw⟩ := UnaryModel.realizeUnary C m h legal correct
  have run' : Extended.Live true Extended.target k S := UnaryModel.live_to_extended run
  have raw' : ∀ a ∈ S, a ∈ Extended.initial := raw
  have floor := Geometry.binary_floor_seventeen run' raw'
  have sameNot :
      (fun g : Gate => @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq g.op GateOp.not)) =
        UnaryModel.isNot := by
    funext g
    obtain ⟨op, ins⟩ := g
    cases op <;> rfl
  have count : PEqualNP.NotBracket.notCount C = C.gates.countP UnaryModel.isNot := by
    rw [PEqualNP.NotBracket.notCount, sameNot, List.countP_eq_length_filter]
  have negSame : (fun g : Gate => decide (¬ UnaryModel.isNot g = true)) =
      (fun g => !UnaryModel.isNot g) := by
    funext g
    cases UnaryModel.isNot g <;> rfl
  have total := List.length_eq_countP_add_countP UnaryModel.isNot (l := C.gates)
  rw [negSame] at total
  rw [count]
  change 17 + C.gates.countP UnaryModel.isNot ≤ C.gates.length
  omega

theorem unary_at_most_one_not (C : Circuit) (m : Fin 10 → Fin 10) (h : Bool → Bool)
    (legal : PEqualNP.MetaComplexity.FanInTwo C) (small : C.size ≤ 18)
    (correct : ∀ x : Fin 10 → Bool,
      C.eval (List.ofFn (x ∘ m) ++ [h (x 0)]) = UnaryModel.f10 x) :
    PEqualNP.NotBracket.notCount C ≤ 1 := by
  have lower := unary_seventeen_plus_not C m h legal correct
  omega
