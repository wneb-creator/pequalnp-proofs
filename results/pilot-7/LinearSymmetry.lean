import MaskSymmetry

namespace PEqualNP.Outside.L_meta_982_aux.Finite.Symmetry.Linear
open Checkpoint

def Check (k : Nat) (pool p q : List Nat) : Bool :=
  decide (p.length = k+k) &&
  p.all (fun j => decide (j < k+k)) && q.all (fun j => decide (j < k+k)) &&
  p.zipIdx.all (fun (s,j) => decide (k ≤ s ↔ k ≤ j)) &&
  decide (q.map (fun j => p.toArray.getD j 0) = List.range (k+k)) &&
  pool.all (fun a => (pool.map (Masked.fast (k+k) p)).contains a)

theorem array_getD (p : List Nat) (j : Nat) : p.toArray.getD j 0 = p.getD j 0 := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem getD_mem {p : List Nat} {j : Nat} (hj : j < p.length) : p.getD j 0 ∈ p := by
  rw [List.getD_eq_getElem p 0 hj]
  exact List.getElem_mem hj

theorem zip_mem {p : List Nat} {j : Nat} (hj : j < p.length) :
    (p.getD j 0,j) ∈ p.zipIdx := by
  rw [List.getD_eq_getElem p 0 hj]
  have hmem := List.getElem_mem (l := p.zipIdx) (by simpa using hj)
  simpa only [List.getElem_zipIdx, Nat.zero_add] using hmem

theorem check_good {k : Nat} {pool p q : List Nat} (hc : Check k pool p q = true) :
    Full.Good k pool p := by
  simp only [Check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨hl,hp⟩,hq⟩,hh⟩,hi⟩,hf⟩ := hc
  have hql : q.length = k+k := by
    have he := congrArg List.length hi
    simpa only [List.length_map, List.length_range] using he
  apply Full.check_good (q := q)
  simp only [Full.Check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  refine ⟨⟨hl, ?_⟩, ?_⟩
  · intro j hj
    have hjp : j < p.length := by omega
    have hjq : j < q.length := by omega
    refine ⟨hp _ (getD_mem hjp), hq _ (getD_mem hjq), ?_, hh _ (zip_mem hjp)⟩
    have he := congrArg (fun l : List Nat => l.getD j 0) hi
    rw [getD_map_lt q (fun j => p.toArray.getD j 0) 0 0 j hjq, range_getD hj,
      array_getD] at he
    exact he
  · have he : Masked.fast (k+k) p = Full.fast (k+k) p := funext (Masked.fast_eq hl)
    rw [← he]
    exact hf

def packedCheck (k pw rw rb n fw fb count : Nat) (pool : List Nat)
    (gs : Array (List Nat)) (q : Nat → List Nat) (rs refs : Array Nat) : Bool :=
  (List.range gs.size).all (fun i => Check k pool (gs.getD i []) (q i)) &&
  recipeCheck pw rw rb n gs.size rs && actionCheck fw fb count (n+1) refs

theorem checked_actions {k pw rw rb n fw fb count : Nat} {pool : List Nat}
    {gs : Array (List Nat)} {rs refs : Array Nat} (q : Nat → List Nat)
    (hc : packedCheck k pw rw rb n fw fb count pool gs q rs refs = true) :
    ∀ p ∈ actions fw fb count refs (group (k+k) pw rw rb n gs rs), Full.Good k pool p := by
  simp only [packedCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  apply actions_preserves
  · exact group_preserves (Full.Good k pool) (k+k) pw rw rb n gs rs (Full.good_id k pool)
      (array_all (xs := gs) (P := Full.Good k pool) [] rfl (fun i => check_good (hc.1.1 i i.2)))
      (fun _ _ hp hq => Full.good_comp hp hq) hc.1.2
  · simpa only [group_size] using hc.2

end PEqualNP.Outside.L_meta_982_aux.Finite.Symmetry.Linear
