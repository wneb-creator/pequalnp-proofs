import PEqualNP.Outside.L_meta_2592
import structural

namespace PEqualNP.Outside.L_meta_2592_aux.Stronger.Extended

open PEqualNP.Outside.L_meta_2592_aux.Subgraphs

def vertexPositions : Fin 10 → Nat := ![9, 7, 5, 8, 6, 4, 2, 0, 3, 1]

def rowOfAssignment (x : Fin 10 → Bool) : Row :=
  Fin.ofNat 1024 (∑ i : Fin 10, if x i then 2 ^ vertexPositions i else 0)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma assign_rowOfAssignment : ∀ x : Fin 10 → Bool, assign (rowOfAssignment x) = x := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rowOfAssignment_assign : ∀ r : Row, rowOfAssignment (assign r) = r := by
  decide +kernel

def permuteRows (p : Equiv.Perm (Fin 10)) : Equiv.Perm Row where
  toFun r := rowOfAssignment (assign r ∘ p)
  invFun r := rowOfAssignment (assign r ∘ p.symm)
  left_inv r := by
    change rowOfAssignment (assign (rowOfAssignment (assign r ∘ p)) ∘ p.symm) = r
    rw [assign_rowOfAssignment]
    have h : (assign r ∘ p) ∘ p.symm = assign r := by funext i; simp
    rw [h, rowOfAssignment_assign]
  right_inv r := by
    change rowOfAssignment (assign (rowOfAssignment (assign r ∘ p.symm)) ∘ p) = r
    rw [assign_rowOfAssignment]
    have h : (assign r ∘ p.symm) ∘ p = assign r := by funext i; simp
    rw [h, rowOfAssignment_assign]

def renameVertices (p : Equiv.Perm (Fin 10)) (a : Sig) : Sig :=
  table fun r => bit (permuteRows p r) a

lemma bit_renameVertices (p : Equiv.Perm (Fin 10)) (a : Sig) (r : Row) :
    bit r (renameVertices p a) = bit (permuteRows p r) a := bit_table _ _

lemma renameVertices_injective (p : Equiv.Perm (Fin 10)) :
    Function.Injective (renameVertices p) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨r, hr⟩ := (permuteRows p).surjective ⟨j, hj⟩
  have he := congrArg (bit r) h
  change bit ⟨j, hj⟩ a = bit ⟨j, hj⟩ b
  rw [bit_renameVertices, bit_renameVertices, hr] at he
  exact he

lemma renameVertices_zero (p : Equiv.Perm (Fin 10)) : renameVertices p zero = zero := by
  apply bit_ext
  intro r
  rw [bit_renameVertices]
  simp [bit, zero]

lemma renameVertices_one (p : Equiv.Perm (Fin 10)) : renameVertices p one = one := by
  apply bit_ext
  intro r
  rw [bit_renameVertices]
  unfold bit one
  simp only [BitVec.getLsbD_allOnes]
  simp

lemma transport_bit_bin (r : Row) (d : Nat) (a b : Sig) : bit r (bin d a b) =
    (if d = 0 then bit r a && bit r b else if d = 1 then bit r a || bit r b else
      if d = 2 then bit r a && !(bit r b) else !(bit r a) && bit r b) := by
  unfold bin
  split_ifs <;> simp [bit]

lemma renameVertices_bin (p : Equiv.Perm (Fin 10)) (d : Nat) (a b : Sig) :
    renameVertices p (bin d a b) = bin d (renameVertices p a) (renameVertices p b) := by
  apply bit_ext
  intro r
  simp only [bit_renameVertices, transport_bit_bin]

lemma renameVertices_pin (p : Equiv.Perm (Fin 10)) (i : Fin 10) :
    renameVertices p (pins.getD i.val zero) = pins.getD (p i).val zero := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change bit ⟨j, hj⟩ (renameVertices p (pins.getD i.val zero)) = bit ⟨j, hj⟩ _
  rw [bit_renameVertices]
  change assign (rowOfAssignment (assign ⟨j, hj⟩ ∘ p)) i = assign ⟨j, hj⟩ (p i)
  rw [assign_rowOfAssignment]
  rfl

lemma f10_eq_edgeFun (x : Fin 10 → Bool) : f10 x = edgeFun x := by
  let es : List (Fin 10 × Fin 10) :=
    [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),
      (5,7),(7,9),(9,6),(6,8),(8,5)]
  have h : (∃ a b : Fin 10, adjacent a b = true ∧ x a = true ∧ x b = true) ↔
      ∃ e ∈ es, x e.1 = true ∧ x e.2 = true := by
    constructor
    · rintro ⟨a, b, hab, ha, hb⟩
      change es.any (fun e => decide ((a = e.1 ∧ b = e.2) ∨ (a = e.2 ∧ b = e.1))) = true at hab
      obtain ⟨e, he, hcase⟩ := List.any_eq_true.mp hab
      simp only [decide_eq_true_eq] at hcase
      rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨e, he, ha, hb⟩
      · exact ⟨e, he, hb, ha⟩
    · rintro ⟨e, he, ha, hb⟩
      refine ⟨e.1, e.2, ?_, ha, hb⟩
      change es.any (fun t => decide ((e.1 = t.1 ∧ e.2 = t.2) ∨ (e.1 = t.2 ∧ e.2 = t.1))) = true
      exact List.any_eq_true.mpr ⟨e, he, by simp⟩
  apply Bool.eq_iff_iff.mpr
  rw [edgeFun, decide_eq_true_eq, h]
  simp [f10, es, Bool.or_eq_true, Bool.and_eq_true, or_assoc]

lemma renameVertices_target (p : Equiv.Perm (Fin 10))
    (hp : ∀ a b, adjacent (p a) (p b) = adjacent a b) :
    renameVertices p target = target := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change bit ⟨j, hj⟩ (renameVertices p target) = bit ⟨j, hj⟩ target
  rw [bit_renameVertices, rowTarget, rowTarget]
  change f10 (assign (rowOfAssignment (assign ⟨j, hj⟩ ∘ p))) = f10 (assign ⟨j, hj⟩)
  rw [assign_rowOfAssignment, f10_eq_edgeFun, f10_eq_edgeFun]
  exact edgeFun_permute p hp _

lemma live_renameVertices {u T k S} (h : Live u T k S) (p : Equiv.Perm (Fin 10)) :
    Live u (renameVertices p T) k (S.image (renameVertices p)) := by
  have inj := renameVertices_injective p
  have pp (v) (h : proper v) : proper (renameVertices p v) :=
    ⟨fun e => h.1 (inj (e.trans (renameVertices_zero p).symm)),
      fun e => h.2 (inj (e.trans (renameVertices_one p).symm))⟩
  induction h using Live.ind with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have fresh : renameVertices p (bin d a b) ∉
        (insert a (insert b U)).image (renameVertices p) := by
      intro hm
      obtain ⟨v, hv, eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert, renameVertices_bin] at fresh ih ⊢
    exact Live.binary hd (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih

lemma renameVertices_mem_pins (p : Equiv.Perm (Fin 10)) {v : Sig} (hv : v ∈ pins) :
    renameVertices p v ∈ pins := by
  have hlist : List.ofFn (fun i : Fin 10 => pins.getD i.val zero) = pins := rfl
  have hv' : v ∈ List.ofFn (fun i : Fin 10 => pins.getD i.val zero) := hlist.symm ▸ hv
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv'
  rw [renameVertices_pin]
  exact hlist ▸ List.mem_ofFn.mpr ⟨p i, rfl⟩

lemma canonicalize_first (d : Fin 4) (a b : Fin 10) (hab : a ≠ b) {k S}
    (run : Live true target k S)
    (raw : ∀ v ∈ S, v ∈ pins ++ [bin d.val (pins.getD a.val zero) (pins.getD b.val zero)]) :
    ∃ (j : Fin 2) (U : Finset Sig), Live true target k U ∧
      ∀ v ∈ U, v ∈ pins ++ [bin d.val (pins.getD 0 zero) (pins.getD (j.val + 1) zero)] := by
  classical
  obtain ⟨p, hzero, hsecond, hp⟩ := normalize_pair a b hab
  let j : Fin 2 := if adjacent a b then 0 else 1
  let q := p.symm
  have hqa : q a = 0 := by
    dsimp [q]
    rw [← hzero, Equiv.symm_apply_apply]
  have hqb : (q b).val = j.val + 1 := by
    dsimp [q]
    rw [← hsecond, Equiv.symm_apply_apply]
    cases h : adjacent a b <;> simp [j, h]
  have hq : ∀ u v, adjacent (q u) (q v) = adjacent u v := by
    intro u v
    simpa only [q, Equiv.apply_symm_apply] using (hp (p.symm u) (p.symm v)).symm
  refine ⟨j, S.image (renameVertices q), ?_, ?_⟩
  · simpa only [renameVertices_target q hq] using live_renameVertices run q
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    have hw' := raw w hw
    simp only [List.mem_append, List.mem_singleton] at hw' ⊢
    rcases hw' with hpin | rfl
    · exact Or.inl (renameVertices_mem_pins q hpin)
    · right
      rw [renameVertices_bin, renameVertices_pin, renameVertices_pin, hqa, hqb]
      rfl

end PEqualNP.Outside.L_meta_2592_aux.Stronger.Extended
