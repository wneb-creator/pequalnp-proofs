import PEqualNP.Outside.L_meta_2592

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_2592.Signed

def vertexMoves : List (List Nat) := [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9], [1, 0, 4, 3, 2, 6, 5, 9, 8, 7], [2, 1, 0, 4, 3, 7, 6, 5, 9, 8], [3, 2, 1, 0, 4, 8, 7, 6, 5, 9], [1, 2, 3, 4, 0, 6, 7, 8, 9, 5], [1, 2, 3, 8, 6, 0, 7, 4, 5, 9], [2, 1, 6, 8, 3, 7, 0, 9, 5, 4], [3, 2, 1, 6, 8, 4, 7, 0, 9, 5], [8, 3, 2, 1, 6, 5, 4, 7, 0, 9], [2, 3, 8, 6, 1, 7, 4, 5, 9, 0]]
def pinPositions : List Nat := [9, 7, 5, 8, 6, 4, 2, 0, 3, 1]

def rowsAt (v : Fin 10) (r : Row) : Extended.Row :=
  Fin.ofNat 1024 (((List.range 10).map fun i =>
    if r.val.testBit (pinPositions.getD ((vertexMoves.getD v.val []).getD i 0) 0)
    then 2 ^ (pinPositions.getD i 0) else 0).sum)

def projectedBy (v : Fin 10) (a : Extended.Sig) : Sig :=
  table (fun r => Extended.bit (rowsAt v r) a)

lemma observe_projectedBy (v : Fin 10) (a : Extended.Sig) :
    restrictRows (rowsAt v) (Extended.observe a) = observe (projectedBy v a) := by
  exact (observe_table _).symm

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma projectionChecked : ∀ v : Fin 10,
    projectedBy v Extended.target = graph ∧
    projectedBy v (Extended.pins.getD v.val Extended.zero) = zero ∧
    Extended.pins.all (fun a => (projectedBy v a == zero) || inputs.contains (projectedBy v a)) = true := by
  decide +kernel

lemma pin_projection_false (a : Extended.Sig) (mem : a ∈ Extended.pins) :
    ∃ rows : Row → Extended.Row,
      restrictRows rows (Extended.observe a) = (fun _ => false) ∧
      restrictRows rows (Extended.observe Extended.target) = observe graph ∧
      ∀ b ∈ Extended.pins,
        Available true (inputs.map observe) (restrictRows rows (Extended.observe b)) := by
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

lemma pin_projection (a : Extended.Sig) (mem : a ∈ Extended.pins) :
    ∃ rows : Row → Extended.Row,
      Constant (restrictRows rows (Extended.observe a)) ∧
      restrictRows rows (Extended.observe Extended.target) = observe graph ∧
      ∀ b ∈ Extended.pins,
        Available true (inputs.map observe) (restrictRows rows (Extended.observe b)) := by
  obtain ⟨rows, fixed, target, supplied⟩ := pin_projection_false a mem
  exact ⟨rows, ⟨false, fixed⟩, target, supplied⟩

lemma from_constant_comb {R u} (op) {a b : Wire R} {bank}
    (hd : allowed u op) (h : Constant a ∨ Constant b)
    (ha : Available u bank a) (hb : Available u bank b) :
    Available u bank (comb op a b) := by
  rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  · exact from_constant false h ha hb
  · exact from_constant true h ha hb
  · apply from_constant false _ ha (avail_inv hu hb)
    exact h.imp id inv_constant
  · apply from_constant false _ (avail_inv hu ha) hb
    exact h.imp inv_constant id

lemma kept_projection_charge {R S : Type} {u} (rows : S → R)
    {goal : Wire R} {s op ka kb a b rest}
    (hd : allowed u op)
    (tail : Run u goal s (comb op a b :: kept ka a (kept kb b rest)))
    (nc : ¬Constant (restrictRows rows goal))
    {roots : List (Wire S)} {L : Nat}
    (sup : supply u roots ((a :: b :: rest).map (restrictRows rows)))
    (retained : (ka = true ∧ Constant (restrictRows rows a)) ∨
      (kb = true ∧ Constant (restrictRows rows b)))
    (floor : ∀ q bs, Reach u roots q bs →
      Available u bs (restrictRows rows goal) → L ≤ q) :
    L + 1 + cost (restrictRows rows (comb op a b)) ≤ s := by
  classical
  have hconst : Constant (restrictRows rows a) ∨ Constant (restrictRows rows b) :=
    retained.elim (fun h => Or.inl h.2) (fun h => Or.inr h.2)
  have ha : Available u roots (restrictRows rows a) := sup _ (by simp)
  have hb : Available u roots (restrictRows rows b) := sup _ (by simp)
  have combined : Available u roots (restrictRows rows (comb op a b)) := by
    rw [restrict_comb]
    exact from_constant_comb op hd hconst ha hb
  have after : supply u roots
      ((comb op a b :: kept ka a (kept kb b rest)).map (restrictRows rows)) := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    rcases List.mem_cons.mp hw with rfl | hw
    · exact combined
    · apply sup
      apply List.mem_map.mpr
      refine ⟨w, ?_, rfl⟩
      rcases mem_kept hw with rfl | hw
      · simp
      · rcases mem_kept hw with rfl | hw
        · simp
        · simp [hw]
  have lower := projected_bound rows tail nc Reach.start after floor
  have charge : cost (restrictRows rows (comb op a b)) + 1 ≤ mass
      ((comb op a b :: kept ka a (kept kb b rest)).map (restrictRows rows)) := by
    simp only [List.map_cons, restrict_kept, mass_cons]
    rcases retained with ⟨rfl, ca⟩ | ⟨rfl, cb⟩
    · cases kb <;> simp [kept, mass_cons, cost, ca] <;> omega
    · cases ka <;> simp [kept, mass_cons, cost, cb] <;> omega

  omega


lemma nonOr_projection_charge {R S : Type} {u} (rows : S → R)
    {goal : Wire R} {s op a b rest}
    (hd : allowed u op)
    (tail : Run u goal s (comb op a b :: kept true a (kept true b rest)))
    (nc : ¬Constant (restrictRows rows goal))
    {roots : List (Wire S)} {L : Nat}
    (sup : supply u roots ((a :: b :: rest).map (restrictRows rows)))
    (fixed : ((op = 0 ∨ op = 2) ∧ restrictRows rows a = (fun _ => false)) ∨
      (op = 3 ∧ restrictRows rows b = (fun _ => false)))
    (floor : ∀ q bs, Reach u roots q bs →
      Available u bs (restrictRows rows goal) → L ≤ q) :
    L + 2 ≤ s := by
  classical
  have hconst : Constant (restrictRows rows a) ∨ Constant (restrictRows rows b) := by
    rcases fixed with ⟨_, ha⟩ | ⟨_, hb⟩
    · exact Or.inl ⟨false, ha⟩
    · exact Or.inr ⟨false, hb⟩
  have gateZero : restrictRows rows (comb op a b) = (fun _ => false) := by
    rw [restrict_comb]
    rcases fixed with ⟨hop, ha⟩ | ⟨rfl, hb⟩
    · rcases hop with rfl | rfl <;> rw [ha] <;> funext r <;> simp [comb, combine]
    · rw [hb]
      funext r
      simp [comb, combine]
  have gateCost : cost (restrictRows rows (comb op a b)) = 1 := by
    rw [gateZero]
    simp [cost, Constant]
  have bound := kept_projection_charge rows hd tail nc sup
    (hconst.elim (fun h => Or.inl ⟨rfl, h⟩) (fun h => Or.inr ⟨rfl, h⟩)) floor
  rw [gateCost] at bound
  omega


end PEqualNP.Outside.L_meta_2592.Signed

namespace PEqualNP.Outside.L_meta_2592.Signed.Extended

def firstPairRows (i j : Fin 10) (d : Fin 4) : Row × Row :=
  ([
  (0,0),(0,0),(0,0),(0,0),(64,576),(384,896),(384,896),(64,576),
  (128,640),(96,608),(96,608),(128,640),(128,640),(384,896),(384,896),(128,640),
  (128,640),(192,704),(192,704),(128,640),(128,640),(144,656),(144,656),(128,640),
  (128,640),(68,580),(68,580),(128,640),(128,640),(129,641),(129,641),(128,640),
  (128,640),(136,648),(136,648),(128,640),(128,640),(130,642),(130,642),(128,640),
  (32,160),(544,672),(544,672),(32,160),(0,0),(0,0),(0,0),(0,0),
  (512,640),(544,672),(544,672),(512,640),(512,640),(768,896),(768,896),(512,640),
  (512,640),(96,224),(96,224),(512,640),(512,640),(48,176),(48,176),(512,640),
  (512,640),(516,644),(516,644),(512,640),(512,640),(513,641),(513,641),(512,640),
  (512,640),(520,648),(520,648),(512,640),(512,640),(514,642),(514,642),(512,640),
  (128,160),(768,800),(768,800),(128,160),(256,288),(384,416),(384,416),(256,288),
  (0,0),(0,0),(0,0),(0,0),(128,160),(768,800),(768,800),(128,160),
  (128,160),(192,224),(192,224),(128,160),(128,160),(144,176),(144,176),(128,160),
  (128,160),(260,292),(260,292),(128,160),(128,160),(513,545),(513,545),(128,160),
  (128,160),(136,168),(136,168),(128,160),(128,160),(130,162),(130,162),(128,160),
  (32,288),(544,800),(544,800),(32,288),(32,288),(192,448),(192,448),(32,288),
  (64,320),(544,800),(544,800),(64,320),(0,0),(0,0),(0,0),(0,0),
  (32,288),(192,448),(192,448),(32,288),(32,288),(48,304),(48,304),(32,288),
  (32,288),(36,292),(36,292),(32,288),(32,288),(65,321),(65,321),(32,288),
  (32,288),(520,776),(520,776),(32,288),(32,288),(34,290),(34,290),(32,288),
  (256,320),(544,608),(544,608),(256,320),(512,576),(384,448),(384,448),(512,576),
  (512,576),(544,608),(544,608),(512,576),(512,576),(768,832),(768,832),(512,576),
  (0,0),(0,0),(0,0),(0,0),(512,576),(272,336),(272,336),(512,576),
  (512,576),(516,580),(516,580),(512,576),(512,576),(513,577),(513,577),(512,576),
  (512,576),(520,584),(520,584),(512,576),(512,576),(514,578),(514,578),(512,576),
  (1,17),(544,560),(544,560),(1,17),(512,528),(129,145),(129,145),(512,528),
  (512,528),(544,560),(544,560),(512,528),(512,528),(768,784),(768,784),(512,528),
  (512,528),(65,81),(65,81),(512,528),(0,0),(0,0),(0,0),(0,0),
  (512,528),(516,532),(516,532),(512,528),(512,528),(513,529),(513,529),(512,528),
  (512,528),(520,536),(520,536),(512,528),(512,528),(514,530),(514,530),(512,528),
  (128,132),(520,524),(520,524),(128,132),(8,12),(384,388),(384,388),(8,12),
  (128,132),(40,44),(40,44),(128,132),(128,132),(384,388),(384,388),(128,132),
  (128,132),(192,196),(192,196),(128,132),(128,132),(144,148),(144,148),(128,132),
  (0,0),(0,0),(0,0),(0,0),(128,132),(129,133),(129,133),(128,132),
  (128,132),(520,524),(520,524),(128,132),(128,132),(514,518),(514,518),(128,132),
  (32,33),(544,545),(544,545),(32,33),(32,33),(144,145),(144,145),(32,33),
  (16,17),(544,545),(544,545),(16,17),(32,33),(272,273),(272,273),(32,33),
  (32,33),(96,97),(96,97),(32,33),(32,33),(144,145),(144,145),(32,33),
  (32,33),(36,37),(36,37),(32,33),(0,0),(0,0),(0,0),(0,0),
  (32,33),(40,41),(40,41),(32,33),(32,33),(514,515),(514,515),(32,33),
  (256,264),(768,776),(768,776),(256,264),(256,264),(384,392),(384,392),(256,264),
  (256,264),(48,56),(48,56),(256,264),(16,24),(768,776),(768,776),(16,24),
  (256,264),(80,88),(80,88),(256,264),(256,264),(144,152),(144,152),(256,264),
  (256,264),(516,524),(516,524),(256,264),(256,264),(257,265),(257,265),(256,264),
  (0,0),(0,0),(0,0),(0,0),(256,264),(258,266),(258,266),(256,264),
  (64,66),(516,518),(516,518),(64,66),(64,66),(192,194),(192,194),(64,66),
  (64,66),(96,98),(96,98),(64,66),(64,66),(260,262),(260,262),(64,66),
  (4,6),(192,194),(192,194),(4,6),(64,66),(80,82),(80,82),(64,66),
  (64,66),(516,518),(516,518),(64,66),(64,66),(513,515),(513,515),(64,66),
  (64,66),(72,74),(72,74),(64,66),(0,0),(0,0),(0,0),(0,0)] : List (Row × Row)).getD (40 * i.val + 4 * j.val + d.val) (0,0)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma firstPairChecked : ∀ (i j : Fin 10) (d : Fin 4), i ≠ j →
    let rs := firstPairRows i j d
    bit rs.1 target ≠ bit rs.2 target ∧
    bit rs.1 (bin d.val (pins.getD i.val zero) (pins.getD j.val zero)) =
      bit rs.2 (bin d.val (pins.getD i.val zero) (pins.getD j.val zero)) ∧
    ∀ q : Fin 10, q ≠ i →
      bit rs.1 (pins.getD q.val zero) = bit rs.2 (pins.getD q.val zero) := by
  decide +kernel

lemma pins_as_ofFn : pins = List.ofFn (fun i : Fin 10 => pins.getD i.val zero) := by
  decide +kernel

lemma pin_mem (a : Sig) : a ∈ pins ↔ ∃ i : Fin 10, pins.getD i.val zero = a := by
  conv_lhs => rw [pins_as_ofFn]
  rw [List.mem_ofFn]

lemma first_gate_keeps_left {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat}
    (ha : a ∈ pins) (hb : b ∈ pins) (distinct : a ≠ b) (op : d < 4)
    (raw : ∀ v ∈ U, v ∈ pins) (run : Live true target k (insert (bin d a b) U)) :
    a ∈ U := by
  by_contra na
  obtain ⟨i, rfl⟩ := (pin_mem a).mp ha
  obtain ⟨j, rfl⟩ := (pin_mem b).mp hb
  have ij : i ≠ j := by
    rintro rfl
    exact distinct rfl
  obtain ⟨diff, gateSame, othersSame⟩ := firstPairChecked i j ⟨d, op⟩ ij
  obtain ⟨v, hv, changed⟩ := live_row_difference run diff
  rcases Finset.mem_insert.mp hv with rfl | inU
  · exact changed gateSame
  · obtain ⟨q, eq⟩ := (pin_mem v).mp (raw v inU)
    have qi : q ≠ i := by
      rintro rfl
      exact na (eq.symm ▸ inU)
    exact changed (eq ▸ othersSame q qi)

lemma first_gate_keeps_both {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat}
    (ha : a ∈ pins) (hb : b ∈ pins) (distinct : a ≠ b) (op : d < 4)
    (raw : ∀ v ∈ U, v ∈ pins) (run : Live true target k (insert (bin d a b) U)) :
    a ∈ U ∧ b ∈ U := by
  have hd : allowed true d := Or.inr ⟨rfl, op⟩
  have flipped : flipOp d < 4 := by
    have h := (flip_flip hd).1
    rcases h with h | ⟨_, h⟩ <;> omega
  have tail : Live true target k (insert (bin (flipOp d) b a) U) := by
    rw [← bin_flip hd]
    exact run
  exact ⟨first_gate_keeps_left ha hb distinct op raw run,
    first_gate_keeps_left hb ha (Ne.symm distinct) flipped raw tail⟩

lemma first_gate_keeps_input {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat}
    (ha : a ∈ pins) (hb : b ∈ pins) (distinct : a ≠ b) (op : d < 4)
    (raw : ∀ v ∈ U, v ∈ pins) (run : Live true target k (insert (bin d a b) U)) :
    a ∈ U ∨ b ∈ U :=
  Or.inl (first_gate_keeps_left ha hb distinct op raw run)

end PEqualNP.Outside.L_meta_2592.Signed.Extended

namespace PEqualNP.Outside.L_meta_2592.Signed.Extended

lemma tail_with_retained_inputs {u T k} {U : Finset Sig} {a b : Sig} {d : Nat}
    (distinct : a ≠ b) (ha : a ∈ U) (hb : b ∈ U) (fresh : bin d a b ∉ U)
    (tail : Live u T k (insert (bin d a b) U)) :
    Run u (observe T) k
      (comb d (observe a) (observe b) :: kept true (observe a)
        (kept true (observe b) (((U.erase a).erase b).toList.map observe))) := by
  classical
  let rest := ((U.erase a).erase b).toList
  have nd : (a :: b :: rest).Nodup := by
    simp [rest, distinct]
    exact Finset.nodup_toList _
  have eq : (a :: b :: rest).toFinset = U := by
    ext z
    by_cases za : z = a <;> by_cases zb : z = b <;> simp_all [rest]
  have nd' : (bin d a b :: a :: b :: rest).Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_, nd⟩
    intro member
    exact fresh (eq ▸ List.mem_toFinset.mpr member)
  have run := list_run tail (bin d a b :: a :: b :: rest) nd' (by simp [eq])
  change Run u (observe T) k
    (comb d (observe a) (observe b) :: observe a :: observe b :: rest.map observe)
  simpa only [List.map_cons, obs_bin] using run

end PEqualNP.Outside.L_meta_2592.Signed.Extended

namespace PEqualNP.Outside.L_meta_2592.Signed

open PEqualNP.CircuitLowerBounds

lemma atLeastSeventeen {k S} (run : Extended.Live true Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ Extended.pins) : 17 ≤ k := by
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
    obtain ⟨aKept, bKept⟩ := Extended.first_gate_keeps_both aPin bPin distinct hd4 rawU tail
    have freshU : Extended.bin d a b ∉ U := by
      intro member
      exact fresh (by simp [member])
    have tailRun := Extended.tail_with_retained_inputs distinct aKept bKept freshU tail
    obtain ⟨rows, fixed, same, supplied⟩ := pin_projection a aPin
    have sup : supply true (inputs.map observe)
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
    have op : allowed true d := hd
    have bound := kept_projection_charge rows op tailRun
      (same ▸ observe_proper graph_proper) sup (Or.inl ⟨rfl, fixed⟩)
      (by
        intro q bs reach hit
        apply nineFloor q bs reach
        rwa [same] at hit)
    omega

end PEqualNP.Outside.L_meta_2592.Signed

namespace PEqualNP.Outside.L_meta_2592.Signed

lemma projection_tail_supply {rows : Row → Extended.Row} {U : Finset Extended.Sig}
    {a b : Extended.Sig} (aPin : a ∈ Extended.pins) (bPin : b ∈ Extended.pins)
    (rawU : ∀ z ∈ U, z ∈ Extended.pins)
    (supplied : ∀ z ∈ Extended.pins,
      Available true (inputs.map observe) (restrictRows rows (Extended.observe z))) :
    supply true (inputs.map observe)
      ((Extended.observe a :: Extended.observe b ::
        ((U.erase a).erase b).toList.map Extended.observe).map (restrictRows rows)) := by
  classical
  intro v hv
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
  rcases List.mem_cons.mp hw with rfl | hw
  · exact supplied a aPin
  · rcases List.mem_cons.mp hw with rfl | hw
    · exact supplied b bPin
    · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hw
      exact supplied z (rawU z
        ((Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_toList.mp hz)).2).2))

lemma nonOr_first_lower {k : Nat} {U : Finset Extended.Sig}
    {a b : Extended.Sig} {d : Nat}
    (aPin : a ∈ Extended.pins) (bPin : b ∈ Extended.pins)
    (distinct : a ≠ b) (hd : d < 4) (notOr : d ≠ 1)
    (rawU : ∀ z ∈ U, z ∈ Extended.pins)
    (fresh : Extended.bin d a b ∉ U)
    (tail : Extended.Live true Extended.target k (insert (Extended.bin d a b) U)) :
    18 ≤ k + 1 := by
  classical
  obtain ⟨aKept, bKept⟩ := Extended.first_gate_keeps_both aPin bPin distinct hd rawU tail
  have tailRun := Extended.tail_with_retained_inputs distinct aKept bKept fresh tail
  have alternatives : d = 0 ∨ d = 2 ∨ d = 3 := by omega
  rcases alternatives with rfl | rfl | rfl
  · obtain ⟨rows, fixed, same, supplied⟩ := pin_projection_false a aPin
    have sup := projection_tail_supply aPin bPin rawU supplied
    have gateZero : restrictRows rows (comb 0 (Extended.observe a) (Extended.observe b)) =
        (fun _ => false) := by
      rw [restrict_comb, fixed]
      funext r
      simp [comb, combine]
    have gateCost : cost (restrictRows rows (comb 0 (Extended.observe a) (Extended.observe b))) = 1 := by
      rw [gateZero]
      simp [cost, Constant]
    have bound := kept_projection_charge rows (Or.inr ⟨rfl, hd⟩) tailRun
      (same ▸ observe_proper graph_proper) sup (Or.inl ⟨rfl, ⟨false, fixed⟩⟩)
      (by
        intro q bs reach hit
        apply nineFloor q bs reach
        rwa [same] at hit)
    rw [gateCost] at bound
    omega
  · obtain ⟨rows, fixed, same, supplied⟩ := pin_projection_false a aPin
    have sup := projection_tail_supply aPin bPin rawU supplied
    have gateZero : restrictRows rows (comb 2 (Extended.observe a) (Extended.observe b)) =
        (fun _ => false) := by
      rw [restrict_comb, fixed]
      funext r
      simp [comb, combine]
    have gateCost : cost (restrictRows rows (comb 2 (Extended.observe a) (Extended.observe b))) = 1 := by
      rw [gateZero]
      simp [cost, Constant]
    have bound := kept_projection_charge rows (Or.inr ⟨rfl, hd⟩) tailRun
      (same ▸ observe_proper graph_proper) sup (Or.inl ⟨rfl, ⟨false, fixed⟩⟩)
      (by
        intro q bs reach hit
        apply nineFloor q bs reach
        rwa [same] at hit)
    rw [gateCost] at bound
    omega
  · obtain ⟨rows, fixed, same, supplied⟩ := pin_projection_false b bPin
    have sup := projection_tail_supply aPin bPin rawU supplied
    have gateZero : restrictRows rows (comb 3 (Extended.observe a) (Extended.observe b)) =
        (fun _ => false) := by
      rw [restrict_comb, fixed]
      funext r
      simp [comb, combine]
    have gateCost : cost (restrictRows rows (comb 3 (Extended.observe a) (Extended.observe b))) = 1 := by
      rw [gateZero]
      simp [cost, Constant]
    have bound := kept_projection_charge rows (Or.inr ⟨rfl, hd⟩) tailRun
      (same ▸ observe_proper graph_proper) sup (Or.inr ⟨rfl, ⟨false, fixed⟩⟩)
      (by
        intro q bs reach hit
        apply nineFloor q bs reach
        rwa [same] at hit)
    rw [gateCost] at bound
    omega

end PEqualNP.Outside.L_meta_2592.Signed
