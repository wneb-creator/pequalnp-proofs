import negative_seed_paid

namespace PEqualNP.Outside.L_meta_2592_aux.Stronger.NegativeSeedTransport

open Extended PEqualNP.Outside.L_meta_2592_aux.Subgraphs

def originalSeed : Extended.Sig := Extended.bin 1 (Extended.pins.getD 0 Extended.zero)
  (Extended.pins.getD 1 Extended.zero)

def originalExtra (p : Fin 10) := Extended.bin 2 (Extended.pins.getD p.val Extended.zero) originalSeed

def originalBank (p : Fin 10) := Extended.pins ++ [originalSeed,originalExtra p]

def witness (p : Fin 10) : Extended.Row := ![128,512,128,136,130,129,128,130,144,129] p

def other (p : Fin 10) : Extended.Row := Fin.ofNat 1024 ((witness p).val + 2 ^ vertexPositions p)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma witness_diff : ∀ p : Fin 10,
    Extended.bit (witness p) Extended.target ≠ Extended.bit (other p) Extended.target := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma witness_stable : ∀ p : Fin 10,
    (originalBank p).all (fun a => (Extended.bit (witness p) a == Extended.bit (other p) a) ||
      (a == Extended.pins.getD p.val Extended.zero)) = true := by decide +kernel

lemma pin_needed (p : Fin 10) {k S} (run : Extended.Live true Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ originalBank p) : Extended.pins.getD p.val Extended.zero ∈ S := by
  obtain ⟨a,ha,hd⟩ := Extended.live_row_difference run (witness_diff p)
  have hh := List.all_eq_true.mp (witness_stable p) a (raw a ha)
  simp only [Bool.or_eq_true,beq_iff_eq] at hh
  exact hh.resolve_left hd ▸ ha

lemma lower (p : Fin 10) {k S} (run : Extended.Live true Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ originalBank p) (used : originalExtra p ∈ S) : 16 ≤ k := by
  classical
  have needed := pin_needed p run raw
  let t := pairPerm p p
  let q := t.symm
  have tzero : t 0 = p := pairMap_zero p p
  have ht : ∀ a b, adjacent (t a) (t b) = adjacent a b := pairMap_adjacent p p
  have hqp : q p = 0 := by
    dsimp only [q]
    rw [←tzero,Equiv.symm_apply_apply]
  have hq : ∀ a b, adjacent (q a) (q b) = adjacent a b := by
    intro a b
    simpa only [q,Equiv.apply_symm_apply] using (ht (t.symm a) (t.symm b)).symm
  have seedRename : renameVertices q originalSeed = NegativeSeed.seed (q 0) (q 1) := by
    unfold originalSeed NegativeSeed.seed
    rw [renameVertices_bin]
    exact congrArg₂ (Extended.bin 1) (renameVertices_pin q 0) (renameVertices_pin q 1)
  have extraRename : renameVertices q (originalExtra p) = NegativeSeed.extra (q 0) (q 1) := by
    unfold originalExtra NegativeSeed.extra
    rw [renameVertices_bin,renameVertices_pin q p,seedRename,hqp]
    rfl
  have run' : Extended.Live true Extended.target k (S.image (renameVertices q)) := by
    simpa only [renameVertices_target q hq] using live_renameVertices run q
  have raw' : ∀ a ∈ S.image (renameVertices q), a ∈ NegativeSeed.bank (q 0) (q 1) := by
    intro a ha
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp ha
    have hh := raw v hv
    simp only [originalBank,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hh
    simp only [NegativeSeed.bank,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
    rcases hh with hp | rfl | rfl
    · exact Or.inl (renameVertices_mem_pins q hp)
    · exact Or.inr (Or.inl seedRename)
    · exact Or.inr (Or.inr extraRename)
  have needed' : Extended.pins.getD 0 Extended.zero ∈ S.image (renameVertices q) := by
    refine Finset.mem_image.mpr ⟨Extended.pins.getD p.val Extended.zero,needed,?_⟩
    rw [renameVertices_pin q p,hqp]
    rfl
  have used' : NegativeSeed.extra (q 0) (q 1) ∈ S.image (renameVertices q) :=
    Finset.mem_image.mpr ⟨originalExtra p,used,extraRename⟩
  exact NegativeSeed.lower (q 0) (q 1) run' raw' needed' used'

end PEqualNP.Outside.L_meta_2592_aux.Stronger.NegativeSeedTransport
