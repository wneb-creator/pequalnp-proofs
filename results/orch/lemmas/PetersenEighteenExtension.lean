import PetersenSeventeenFull

namespace PEqualNP.Outside.L_meta_2373.LiftSeventeen

lemma mass_two {A R : Type} (f : A → Live1024.Wire R) {a b : A} {xs : List A}
    (ha : a ∈ xs) (hb : b ∈ xs) (hne : a ≠ b)
    (ca : Live1024.Constant (f a)) (cb : Live1024.Constant (f b)) :
    2 ≤ Live1024.mass (xs.map f) := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    rw [List.map_cons, Live1024.mass_cons]
    rcases List.mem_cons.mp ha with rfl | hatail
    · have hb' : b ∈ xs := (List.mem_cons.mp hb).resolve_left (Ne.symm hne)
      have bound : 1 ≤ Live1024.mass (xs.map f) :=
        mass_positive (List.mem_map.mpr ⟨b, hb', rfl⟩) cb
      simp only [Live1024.cost, if_pos ca]
      omega
    · rcases List.mem_cons.mp hb with rfl | hbtail
      · have bound : 1 ≤ Live1024.mass (xs.map f) :=
          mass_positive (List.mem_map.mpr ⟨a, hatail, rfl⟩) ca
        simp only [Live1024.cost, if_pos cb]
        omega
      · have bound := ih hatail hbtail
        omega

lemma projected_tail_lower_two (rows : NineSigned.Row → Live1024.Row)
    (goal : projected rows Live1024.graph = NineSigned.observe NineSigned.graph)
    (S : Finset Live1024.Sig) (k : Nat) (run : Live1024.Live true Live1024.graph k S)
    (covered : ∀ a ∈ S, Live1024.Available true (NineSigned.inputs.map NineSigned.observe)
      (projected rows a))
    (constants : ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧
      Live1024.Constant (projected rows a) ∧ Live1024.Constant (projected rows b)) : 17 ≤ k := by
  have trace := Live1024.list_run run S.toList (Finset.nodup_toList S) (by simp)
  have nc : ¬ Live1024.Constant (Live1024.restrictRows rows (Live1024.observe Live1024.graph)) := by
    change ¬ Live1024.Constant (projected rows Live1024.graph)
    rw [goal]
    exact NineSigned.observe_proper NineSigned.graph_proper
  have supply : Live1024.supply true (NineSigned.inputs.map NineSigned.observe)
      ((S.toList.map Live1024.observe).map (Live1024.restrictRows rows)) := by
    intro v hv
    obtain ⟨_, hm, rfl⟩ := List.mem_map.mp hv
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
    exact covered a (Finset.mem_toList.mp ha)
  have prior (q : Nat) (bank : List (Live1024.Wire NineSigned.Row))
      (h : Live1024.Reach true (NineSigned.inputs.map NineSigned.observe) q bank)
      (hv : Live1024.Available true bank
        (Live1024.restrictRows rows (Live1024.observe Live1024.graph))) : 15 ≤ q := by
    change Live1024.Available true bank (projected rows Live1024.graph) at hv
    rw [goal] at hv
    exact NineSigned.nine_reach_lower q bank (reach_bridge h) hv
  have bound := Live1024.projected_bound rows trace nc Live1024.Reach.start supply prior
  obtain ⟨a, ha, b, hb, hne, ca, cb⟩ := constants
  have mass := mass_two (projected rows) (Finset.mem_toList.mpr ha)
    (Finset.mem_toList.mpr hb) hne ca cb
  have eq : ((S.toList.map Live1024.observe).map (Live1024.restrictRows rows)) =
      S.toList.map (projected rows) := by simp [List.map_map, projected, Function.comp_def]
  rw [eq] at bound
  omega

lemma first_non_or_lower
    (rows : Fin 10 → NineSigned.Row → Live1024.Row)
    (goal : ∀ i, projected (rows i) Live1024.graph = NineSigned.observe NineSigned.graph)
    (fixed : ∀ i, projected (rows i) (input i) = (fun _ => false))
    (covered : ∀ i j, Live1024.Available true (NineSigned.inputs.map NineSigned.observe)
      (projected (rows i) (input j)))
    (i j : Fin 10) (U : Finset Live1024.Sig) (d k : Nat)
    (sub : ∀ w ∈ U, w ∈ Live1024.inputs)
    (hd : Live1024.allowed true d) (nonOr : d ≠ 1)
    (fresh : Live1024.bin d (input i) (input j) ∉ insert (input i) (insert (input j) U))
    (tail : Live1024.Live true Live1024.graph k (insert (Live1024.bin d (input i) (input j)) U))
    (retained : input i ∈ U ∧ input j ∈ U) : 18 ≤ k + 1 := by
  have finish (p : Fin 10) (hp : input p ∈ U)
      (hz : projected (rows p) (Live1024.bin d (input i) (input j)) = (fun _ => false)) :
      18 ≤ k + 1 := by
    have neq : Live1024.bin d (input i) (input j) ≠ input p := by
      intro heq
      exact fresh (heq ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hp))
    have lower := projected_tail_lower_two (rows p) (goal p)
      (insert (Live1024.bin d (input i) (input j)) U) k tail
      (fun w hw => by
        rcases Finset.mem_insert.mp hw with rfl | old
        · exact Or.inr (Or.inl ⟨false, hz⟩)
        · obtain ⟨t, rfl⟩ := input_index w (sub w old)
          exact covered p t)
      ⟨Live1024.bin d (input i) (input j), Finset.mem_insert_self _ _,
        input p, Finset.mem_insert_of_mem hp, neq, ⟨false, hz⟩, ⟨false, fixed p⟩⟩
    omega
  rcases Live1024.allowed_four hd with rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩
  · apply finish i retained.1
    rw [projected_bin, fixed i]
    funext r
    simp [Live1024.comb, Live1024.combine]
  · exact False.elim (nonOr rfl)
  · apply finish i retained.1
    rw [projected_bin, fixed i]
    funext r
    simp [Live1024.comb, Live1024.combine]
  · apply finish j retained.2
    rw [projected_bin, fixed j]
    funext r
    simp [Live1024.comb, Live1024.combine, Live1024.inv]

end PEqualNP.Outside.L_meta_2373.LiftSeventeen

namespace PEqualNP.Outside.L_meta_2373

def pairInput (a c : Fin 10) (i : Fin 10) : Bool := decide (i = a ∨ i = c)


def singleInput (c i : Fin 10) : Bool := decide (i = c)

def tripleInput (a b c i : Fin 10) : Bool := decide (i = a ∨ i = b ∨ i = c)

lemma singleton_no_edge : ∀ c : Fin 10, edge (singleInput c) = false := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma zero_separator : ∀ a b : Fin 10, a ≠ b → ∃ c : Fin 10,
    c ≠ a ∧ c ≠ b ∧ edge (pairInput a c) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma one_separator : ∀ a b : Fin 10, a ≠ b → ∃ c : Fin 10,
    c ≠ a ∧ edge (pairInput b c) = false ∧ edge (tripleInput a b c) = true := by
  decide +kernel

lemma conditional_influence (a b : Fin 10) (hab : a ≠ b) (t : Bool) :
    ∃ x y : Fin 10 → Bool,
      (∀ i, i ≠ a → x i = y i) ∧ x b = t ∧ y b = t ∧
      x a = false ∧ y a = true ∧ edge x ≠ edge y := by
  cases t
  · obtain ⟨c, hca, hcb, he⟩ := zero_separator a b hab
    refine ⟨singleInput c, pairInput a c, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hia
      simp [singleInput, pairInput, hia]
    · simp [singleInput, Ne.symm hcb]
    · simp [pairInput, Ne.symm hab, Ne.symm hcb]
    · simp [singleInput, Ne.symm hca]
    · simp [pairInput]
    · rw [singleton_no_edge, he]
      decide
  · obtain ⟨c, hca, he0, he1⟩ := one_separator a b hab
    refine ⟨pairInput b c, tripleInput a b c, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hia
      simp [pairInput, tripleInput, hia]
    · simp [pairInput]
    · simp [tripleInput]
    · simp [pairInput, hab, Ne.symm hca]
    · simp [tripleInput]
    · rw [he0, he1]
      decide

def boolBin (d : Nat) (a b : Bool) : Bool :=
  if d = 0 then a && b else if d = 1 then a || b else
    if d = 2 then a && !b else !a && b

lemma no_binary_identification_left (d : Nat) (hd : d < 4) (a b : Fin 10)
    (hab : a ≠ b) : ∃ x y : Fin 10 → Bool,
      (∀ i, i ≠ a → x i = y i) ∧
      boolBin d (x a) (x b) = boolBin d (y a) (y b) ∧ edge x ≠ edge y := by
  obtain ⟨x, y, same, xb, yb, xa, ya, different⟩ :=
    conditional_influence a b hab (decide (d = 1 ∨ d = 2))
  refine ⟨x, y, same, ?_, different⟩
  have hcases : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
  rcases hcases with rfl | rfl | rfl | rfl <;> simp_all [boolBin]



namespace Live1024

def singleRow (c : Fin 10) : Row := Fin.ofNat 1024 (1 <<< c.val)

def tripleRow (a b c : Fin 10) : Row :=
  Fin.ofNat 1024 ((1 <<< a.val) ||| (1 <<< b.val) ||| (1 <<< c.val))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma singleRow_input : ∀ c i : Fin 10,
    bit (singleRow c) (inputs.getD i.val zero) = singleInput c i := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma pairRow_input : ∀ a c i : Fin 10,
    bit (pairRow a c) (inputs.getD i.val zero) = pairInput a c i := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tripleRow_input : ∀ a b c i : Fin 10,
    bit (tripleRow a b c) (inputs.getD i.val zero) = tripleInput a b c i := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma singleRow_graph : ∀ c : Fin 10,
    bit (singleRow c) graph = PEqualNP.Outside.L_meta_2373.edge (singleInput c) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma pairRow_graph : ∀ a c : Fin 10,
    bit (pairRow a c) graph = PEqualNP.Outside.L_meta_2373.edge (pairInput a c) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tripleRow_graph : ∀ a b c : Fin 10,
    bit (tripleRow a b c) graph = PEqualNP.Outside.L_meta_2373.edge (tripleInput a b c) := by
  decide +kernel

lemma conditional_influence_rows (a b : Fin 10) (hab : a ≠ b) (t : Bool) :
    ∃ r s : Row,
      (∀ i : Fin 10, i ≠ a →
        bit r (inputs.getD i.val zero) = bit s (inputs.getD i.val zero)) ∧
      bit r (inputs.getD b.val zero) = t ∧ bit s (inputs.getD b.val zero) = t ∧
      bit r graph ≠ bit s graph := by
  cases t
  · obtain ⟨c, hca, hcb, he⟩ := zero_separator a b hab
    refine ⟨singleRow c, pairRow a c, ?_, ?_, ?_, ?_⟩
    · intro i hia
      rw [singleRow_input, pairRow_input]
      simp [singleInput, pairInput, hia]
    · rw [singleRow_input]
      simp [singleInput, Ne.symm hcb]
    · rw [pairRow_input]
      simp [pairInput, Ne.symm hab, Ne.symm hcb]
    · rw [singleRow_graph, pairRow_graph, singleton_no_edge, he]
      decide
  · obtain ⟨c, hca, he0, he1⟩ := one_separator a b hab
    refine ⟨pairRow b c, tripleRow a b c, ?_, ?_, ?_, ?_⟩
    · intro i hia
      rw [pairRow_input, tripleRow_input]
      simp [pairInput, tripleInput, hia]
    · rw [pairRow_input]
      simp [pairInput]
    · rw [tripleRow_input]
      simp [tripleInput]
    · rw [pairRow_graph, tripleRow_graph, he0, he1]
      decide

lemma bit_bin_eq_boolBin (r : Row) (d : Nat) (a b : Sig) :
    bit r (bin d a b) = boolBin d (bit r a) (bit r b) := by
  unfold bin boolBin
  split_ifs <;> simp [bit, r.isLt]

lemma no_binary_identification_left_rows (d : Nat) (hd : d < 4) (a b : Fin 10)
    (hab : a ≠ b) : ∃ r s : Row,
      (∀ i : Fin 10, i ≠ a →
        bit r (inputs.getD i.val zero) = bit s (inputs.getD i.val zero)) ∧
      bit r (bin d (inputs.getD a.val zero) (inputs.getD b.val zero)) =
        bit s (bin d (inputs.getD a.val zero) (inputs.getD b.val zero)) ∧
      bit r graph ≠ bit s graph := by
  obtain ⟨r, s, same, xb, yb, different⟩ :=
    conditional_influence_rows a b hab (decide (d = 1 ∨ d = 2))
  refine ⟨r, s, same, ?_, different⟩
  rw [bit_bin_eq_boolBin, bit_bin_eq_boolBin]
  have hcases : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
  rcases hcases with rfl | rfl | rfl | rfl <;> simp_all [boolBin]



abbrev inputColumn (i : Fin 10) : Sig := inputs.getD i.val zero

lemma first_binary_operands_retained (a b : Fin 10) (hab : a ≠ b)
    (U : Finset Sig) (d k : Nat)
    (pool : inputs.toFinset = insert (inputColumn a) (insert (inputColumn b) U))
    (legal : allowed true d)
    (tail : Live true graph k (insert (bin d (inputColumn a) (inputColumn b)) U)) :
    inputColumn a ∈ U ∧ inputColumn b ∈ U := by
  have sub (w : Sig) (hw : w ∈ U) : w ∈ inputs :=
    List.mem_toFinset.mp (by rw [pool]; simp [hw])
  have index (w : Sig) (hw : w ∈ U) : ∃ i : Fin 10, inputColumn i = w := by
    have hi := sub w hw
    rw [← input_list] at hi
    exact List.mem_ofFn.mp hi
  have retain (p q : Fin 10) (hpq : p ≠ q) (e : Nat) (he : e < 4)
      (run : Live true graph k (insert (bin e (inputColumn p) (inputColumn q)) U)) :
      inputColumn p ∈ U := by
    by_contra missing
    obtain ⟨r, s, oldSame, newSame, different⟩ :=
      no_binary_identification_left_rows e he p q hpq
    obtain ⟨w, hw, diff⟩ := live_row_difference run different
    rcases Finset.mem_insert.mp hw with rfl | old
    · exact diff newSame
    · obtain ⟨i, rfl⟩ := index w old
      have hne : i ≠ p := by
        rintro rfl
        exact missing old
      exact diff (oldSame i hne)
  have four : d < 4 := by
    rcases legal with h | ⟨_, h⟩ <;> omega
  have flipped : flipOp d < 4 := by
    rcases (flip_flip legal).1 with h | ⟨_, h⟩ <;> omega
  refine ⟨retain a b hab d four tail, ?_⟩
  apply retain b a hab.symm (flipOp d) flipped
  rw [← bin_flip legal (inputColumn a) (inputColumn b)]
  exact tail

end Live1024

end PEqualNP.Outside.L_meta_2373

namespace PEqualNP.Outside.L_meta_2373.LiftSeventeen

lemma first_non_or_lower_eighteen
    (i j : Fin 10) (U : Finset Live1024.Sig) (d k : Nat) (ij : i ≠ j)
    (pool : Live1024.inputs.toFinset = insert (input i) (insert (input j) U))
    (hd : Live1024.allowed true d) (nonOr : d ≠ 1)
    (fresh : Live1024.bin d (input i) (input j) ∉ insert (input i) (insert (input j) U))
    (tail : Live1024.Live true Live1024.graph k (insert (Live1024.bin d (input i) (input j)) U)) :
    18 ≤ k + 1 := by
  apply first_non_or_lower rowMap (fun i => funext (rowMap_graph i))
    (fun i => funext (rowMap_missing i))
    (fun i j => rowMap_available_of rowMap_missing rowMap_input i j) i j U d k
    (fun w hw => List.mem_toFinset.mp (by rw [pool]; simp [hw])) hd nonOr fresh tail
  exact Live1024.first_binary_operands_retained i j ij U d k pool hd tail

lemma short_live_starts_or {n : Nat}
    (run : Live1024.Live true Live1024.graph n Live1024.inputs.toFinset) (small : n ≤ 17) :
    ∃ (k : Nat) (U : Finset Live1024.Sig) (i j : Fin 10),
      n = k + 1 ∧ i ≠ j ∧
      Live1024.inputs.toFinset = insert (input i) (insert (input j) U) ∧
      input i ∈ U ∧ input j ∈ U ∧
      Live1024.bin 1 (input i) (input j) ∉ insert (input i) (insert (input j) U) ∧
      Live1024.Live true Live1024.graph k (insert (Live1024.bin 1 (input i) (input j)) U) := by
  cases n with
  | zero =>
    have lower := live_lower_seventeen run
    omega
  | succ k =>
    obtain ⟨U, a, b, d, hd, pool, ha, hb, hab, fresh, tail⟩ := run
    have ma : a ∈ Live1024.inputs := List.mem_toFinset.mp (by rw [pool]; simp)
    have mb : b ∈ Live1024.inputs := List.mem_toFinset.mp (by rw [pool]; simp)
    obtain ⟨i, rfl⟩ := input_index a ma
    obtain ⟨j, rfl⟩ := input_index b mb
    have ij : i ≠ j := by rintro rfl; exact hab rfl
    have op : d = 1 := by
      by_contra hn
      have bound := first_non_or_lower_eighteen i j U d k ij pool hd hn fresh tail
      omega
    subst d
    have retained := Live1024.first_binary_operands_retained i j ij U 1 k pool hd tail
    exact ⟨k, U, i, j, rfl, ij, pool, retained.1, retained.2, fresh, tail⟩

end PEqualNP.Outside.L_meta_2373.LiftSeventeen

namespace PEqualNP.Outside.L_meta_2373.LiftSeventeen

lemma two_not_starts_or (C : PEqualNP.CircuitLowerBounds.Circuit)
    (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : PEqualNP.MetaComplexity.circuitFun 10 C = Live1024.edge)
    (small : C.size ≤ 19) (many : 2 ≤ PEqualNP.NotBracket.notCount C) :
    ∃ (U : Finset Live1024.Sig) (i j : Fin 10), i ≠ j ∧
      Live1024.inputs.toFinset = insert (input i) (insert (input j) U) ∧
      input i ∈ U ∧ input j ∈ U ∧
      Live1024.bin 1 (input i) (input j) ∉ insert (input i) (insert (input j) U) ∧
      Live1024.Live true Live1024.graph 16 (insert (Live1024.bin 1 (input i) (input j)) U) := by
  obtain ⟨k, hk, run⟩ := Live1024.circuit_live_signed C legal computes
  have lower := live_lower_seventeen run
  have total := binary_not_partition C.gates
  rw [notCount_eq_countP] at many
  change C.gates.length ≤ 19 at small
  have bound : k ≤ 17 := by omega
  obtain ⟨l, U, i, j, kl, ij, pool, hi, hj, fresh, tail⟩ := short_live_starts_or run bound
  have eq : l = 16 := by omega
  exact ⟨U, i, j, ij, pool, hi, hj, fresh, eq ▸ tail⟩

end PEqualNP.Outside.L_meta_2373.LiftSeventeen

namespace PEqualNP.Outside.L_meta_2373.LiftSeventeen

lemma signed_seventeen_or_roots
    (run : Live1024.Live true Live1024.graph 17 Live1024.inputs.toFinset) :
    ∃ i j : Fin 10, i ≠ j ∧
      Live1024.Live true Live1024.graph 16
        (insert (Live1024.bin 1 (input i) (input j)) Live1024.inputs.toFinset) := by
  obtain ⟨k, U, i, j, hk, ij, pool, hi, hj, fresh, tail⟩ := short_live_starts_or run (by omega)
  have keq : k = 16 := by omega
  have ueq : U = Live1024.inputs.toFinset := by
    rw [pool, Finset.insert_eq_of_mem hj, Finset.insert_eq_of_mem hi]
  exact ⟨i, j, ij, keq ▸ ueq ▸ tail⟩

lemma two_not_or_roots (C : PEqualNP.CircuitLowerBounds.Circuit)
    (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : PEqualNP.MetaComplexity.circuitFun 10 C = Live1024.edge)
    (small : C.size ≤ 19) (many : 2 ≤ PEqualNP.NotBracket.notCount C) :
    ∃ i j : Fin 10, i ≠ j ∧
      Live1024.Live true Live1024.graph 16
        (insert (Live1024.bin 1 (input i) (input j)) Live1024.inputs.toFinset) := by
  obtain ⟨U, i, j, ij, pool, hi, hj, fresh, tail⟩ := two_not_starts_or C legal computes small many
  have ueq : U = Live1024.inputs.toFinset := by
    rw [pool, Finset.insert_eq_of_mem hj, Finset.insert_eq_of_mem hi]
  exact ⟨i, j, ij, ueq ▸ tail⟩

end PEqualNP.Outside.L_meta_2373.LiftSeventeen
