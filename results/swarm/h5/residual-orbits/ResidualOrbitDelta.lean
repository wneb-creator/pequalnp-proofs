import PEqualNP.Outside.L_meta_2373

namespace PEqualNP.Outside.L_meta_2373.Residual.Orbit
def vertices : Fin 8 → Fin 10 → Fin 10 := ![
  ![0,1,2,3,4,5,6,7,8,9],
  ![0,1,2,7,5,4,6,3,9,8],
  ![0,1,6,8,5,4,2,9,3,7],
  ![0,1,6,9,4,5,2,8,7,3],
  ![1,0,4,3,2,6,5,9,8,7],
  ![1,0,4,9,6,2,5,3,7,8],
  ![1,0,5,7,2,6,4,8,9,3],
  ![1,0,5,8,6,2,4,7,3,9]]
def actions : Fin 8 → Fin 9 → Fin 9 := ![
  ![0,1,2,3,4,5,6,7,8],
  ![0,2,1,3,6,7,4,5,8],
  ![0,4,6,8,1,7,2,5,3],
  ![0,6,4,8,2,5,1,7,3],
  ![0,1,6,7,4,8,2,3,5],
  ![0,2,4,5,6,8,1,3,7],
  ![0,6,1,7,2,3,4,8,5],
  ![0,4,2,5,1,3,6,8,7]]
def inverse : Fin 8 → Fin 8 := ![0,1,2,3,4,6,5,7]
def reps : Fin 14 → Nat := ![0,8,40,44,160,168,170,174,424,426,430,442,446,510]
def unpack (r : Fin 1024) (i : Fin 10) : Bool := r.val.testBit i.val

def pack (x : Fin 10 → Bool) : Fin 1024 :=
  ⟨(BitVec.ofBoolListLE (List.ofFn x)).toNat,
    by simpa only [List.length_ofFn] using (BitVec.ofBoolListLE (List.ofFn x)).isLt⟩

lemma unpack_pack (x : Fin 10 → Bool) : unpack (pack x) = x := by
  funext i
  change (BitVec.ofBoolListLE (List.ofFn x)).getLsbD i.val = x i
  rw [BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp only [dite_eq_left i.isLt, Option.getD_some]

lemma unpack_injective : Function.Injective unpack := by
  intro r s h
  apply Fin.ext
  have hb : (BitVec.ofFin r : BitVec 10) = BitVec.ofFin s := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    exact congrFun h ⟨i, hi⟩
  exact congrArg BitVec.toNat hb

def permRow (g : Fin 8) (r : Fin 1024) : Fin 1024 :=
  pack (fun i => unpack r (vertices g i))

lemma unpack_permRow (g : Fin 8) (r : Fin 1024) :
    unpack (permRow g r) = fun i => unpack r (vertices g i) := unpack_pack _

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma tables : (∀ g : Fin 8, Function.Bijective (vertices g)) ∧
    (∀ g : Fin 8, Function.Bijective (actions g)) ∧
    (∀ g : Fin 8, ∀ i : Fin 9, permRow g (rows i) = rows (actions g i)) := by
  decide +kernel

lemma inverse_vertices : ∀ g : Fin 8, ∀ i : Fin 10,
    vertices g (vertices (inverse g) i) = i := by decide +kernel

def graphMinus (x : Fin 10 → Bool) : Bool :=
  (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) ||
  (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) ||
  (x 6 && x 8) || (x 8 && x 5)

def graph (x : Fin 10 → Bool) : Bool := graphMinus x || (x 0 && x 1)

set_option maxHeartbeats 0 in
lemma graph_invariant (g : Fin 8) (x : Fin 10 → Bool) :
    graphMinus (fun i => x (vertices g i)) = graphMinus x ∧
    graph (fun i => x (vertices g i)) = graph x := by
  fin_cases g <;> constructor <;>
    dsimp [graphMinus, graph, vertices] <;> ac_rfl

lemma row_properties (g : Fin 8) (r : Fin 1024) :
    let s := permRow g r
    Fminus s = Fminus r ∧ F s = F r ∧ permRow (inverse g) s = r ∧
      ∀ i : Fin 10, s.val.testBit i.val = r.val.testBit (vertices g i).val := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change graphMinus (unpack (permRow g r)) = graphMinus (unpack r)
    rw [unpack_permRow]
    exact (graph_invariant g (unpack r)).1
  · change graph (unpack (permRow g r)) = graph (unpack r)
    rw [unpack_permRow]
    exact (graph_invariant g (unpack r)).2
  · apply unpack_injective
    funext i
    simp only [unpack_permRow]
    exact congrArg (unpack r) (inverse_vertices g i)
  · intro i
    exact congrFun (unpack_permRow g r) i

def witness (m : Nat) : Fin 14 × Fin 8 :=
  if m = 0 then (0, 0) else
  if m = 8 then (1, 0) else
  if m = 32 then (1, 6) else
  if m = 40 then (2, 0) else
  if m = 44 then (3, 0) else
  if m = 128 then (1, 4) else
  if m = 136 then (2, 1) else
  if m = 138 then (3, 1) else
  if m = 160 then (4, 0) else
  if m = 168 then (5, 0) else
  if m = 170 then (6, 0) else
  if m = 172 then (6, 1) else
  if m = 174 then (7, 0) else
  if m = 256 then (1, 2) else
  if m = 264 then (4, 4) else
  if m = 288 then (2, 3) else
  if m = 296 then (5, 6) else
  if m = 300 then (6, 6) else
  if m = 304 then (3, 3) else
  if m = 312 then (6, 7) else
  if m = 316 then (7, 6) else
  if m = 384 then (2, 2) else
  if m = 392 then (5, 4) else
  if m = 394 then (6, 4) else
  if m = 416 then (5, 2) else
  if m = 424 then (8, 0) else
  if m = 426 then (9, 0) else
  if m = 428 then (9, 1) else
  if m = 430 then (10, 0) else
  if m = 432 then (6, 2) else
  if m = 440 then (9, 2) else
  if m = 442 then (11, 0) else
  if m = 444 then (10, 6) else
  if m = 446 then (12, 0) else
  if m = 448 then (3, 2) else
  if m = 456 then (6, 5) else
  if m = 458 then (7, 4) else
  if m = 480 then (6, 3) else
  if m = 488 then (9, 3) else
  if m = 490 then (10, 4) else
  if m = 492 then (11, 1) else
  if m = 494 then (12, 1) else
  if m = 496 then (7, 2) else
  if m = 504 then (10, 2) else
  if m = 506 then (12, 2) else
  if m = 508 then (12, 3) else
  if m = 510 then (13, 0) else
  (0, 0)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma mask_cover : ∀ m ∈ masks, ∃ k : Fin 14, ∃ g : Fin 8,
    ∀ i : Fin 9, bits m i = bits (reps k) (actions g i) := by
  have h : masks.all (fun m => decide (∀ i : Fin 9,
      bits m i = bits (reps (witness m).1) (actions (witness m).2 i))) = true := by
    decide +kernel
  intro m hm
  exact ⟨(witness m).1, (witness m).2,
    of_decide_eq_true (List.all_eq_true.mp h m hm)⟩

lemma permRow_injective (g : Fin 8) : Function.Injective (permRow g) := by
  intro r s h
  have h' := congrArg (permRow (inverse g)) h
  simpa only [(row_properties g r).2.2.1, (row_properties g s).2.2.1] using h'

lemma target_transport (m : Nat) (k : Fin 14) (g : Fin 8)
    (hbits : ∀ i : Fin 9, bits m i = bits (reps k) (actions g i)) :
    ∀ r : Fin 1024, target m r = target (reps k) (permRow g r) := by
  intro r
  apply Bool.eq_iff_iff.mpr
  simp only [target, decide_eq_true_eq]
  constructor
  · rintro (h | ⟨i, hi, hb⟩)
    · exact Or.inl ((row_properties g r).1.trans h)
    · refine Or.inr ⟨actions g i, ?_, ?_⟩
      · rw [← tables.2.2 g i, hi]
      · rw [← hbits]
        exact hb
  · rintro (h | ⟨j, hj, hb⟩)
    · exact Or.inl ((row_properties g r).1.symm.trans h)
    · obtain ⟨i, hi⟩ := (tables.2.1 g).2 j
      have hr : rows i = r := permRow_injective g (by rw [tables.2.2, hi]; exact hj)
      exact Or.inr ⟨i, hr, by rw [hbits, hi]; exact hb⟩

lemma fourteen_targets (H : Fin 1024 → Bool)
    (hmono : ∀ r s, rowLE r s → H r = true → H s = true)
    (hlower : ∀ r, Fminus r = true → H r = true)
    (hupper : ∀ r, H r = true → F r = true)
    (hzero : H 3 = false) :
    ∃ k : Fin 14, ∃ g : Fin 8,
      H = fun r => target (reps k) (permRow g r) := by
  obtain ⟨m, hm, hH⟩ := classification H hmono hlower hupper hzero
  obtain ⟨k, g, hbits⟩ := mask_cover m hm
  exact ⟨k, g, hH.trans (funext (target_transport m k g hbits))⟩

end PEqualNP.Outside.L_meta_2373.Residual.Orbit
