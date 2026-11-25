import ReaderRename

namespace PEqualNP.Outside.L_meta_2592.TwoNotSwap
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Automorphisms ReaderDeletion

def swap : Fin 12 → Fin 12 := fun t => if t = 10 then 11 else if t = 11 then 10 else t

def wire (t : Nat) : Nat := if t = 10 then 11 else if t = 11 then 10 else t

lemma rename_eq (t : Nat) : renameWire swap t = wire t := by
  unfold renameWire swap wire
  split_ifs <;> simp_all [Fin.ext_iff]

lemma wire_low (i : Fin 10) : wire i.val = i.val := by
  have hi := i.isLt
  simp [wire,show i.val ≠ 10 by omega,show i.val ≠ 11 by omega]

lemma wire_involutive (t : Nat) : wire (wire t) = t := by
  unfold wire
  split_ifs <;> simp_all

lemma wire_low_iff (i : Fin 10) (t : Nat) : wire t = i.val ↔ t = i.val := by
  constructor
  · intro h
    have h' := congrArg wire h
    simpa only [wire_involutive,wire_low] using h'
  · rintro rfl
    exact wire_low i

lemma wire_ten_iff (t : Nat) : wire t = 10 ↔ t = 11 := by
  unfold wire
  split_ifs <;> simp_all

lemma initial_relation (i j : Fin 10) (x : Fin 10 → Bool) :
    ∀ t, (List.ofFn x ++ [!x j,!x i]).getD (renameWire swap t) false =
      (List.ofFn x ++ [!x i,!x j]).getD t false := by
  intro t
  rw [rename_eq]
  by_cases ht : t < 10
  · have he : wire t = t := wire_low ⟨t,ht⟩
    rw [he,List.getD_append _ _ _ _ (by simpa using ht),
      List.getD_append _ _ _ _ (by simpa using ht)]
  · by_cases h10 : t = 10
    · subst t
      simp [wire,List.getD_eq_getElem?_getD]
    · by_cases h11 : t = 11
      · subst t
        simp [wire,List.getD_eq_getElem?_getD]
      · have h12 : 12 ≤ t := by omega
        have he : wire t = t := by simp [wire,h10,h11]
        rw [he,List.getD_eq_default _ _ (by simp;omega),
          List.getD_eq_default _ _ (by simp;omega)]

lemma prefix_eval (i j : Fin 10) (x : Fin 10 → Bool) :
    ([⟨.not,[i.val]⟩,⟨.not,[j.val]⟩] : List Gate).foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun t => w.getD t false)]) (List.ofFn x) =
      List.ofFn x ++ [!x i,!x j] := by
  have hread (k : Fin 10) : (List.ofFn x).getD k.val false = x k := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn]
    simp
  have hread' (k : Fin 10) (v : Bool) : (List.ofFn x ++ [v]).getD k.val false = x k := by
    rw [List.getD_append _ _ _ _ (by simp)]
    exact hread k
  simp only [List.foldl_cons,List.foldl_nil,List.map_cons,List.map_nil,GateOp.eval,
    hread,hread',List.append_assoc]
  rfl

def switched (i j : Fin 10) (gs : List Gate) (out : Nat) : Circuit :=
  ⟨[⟨.not,[j.val]⟩,⟨.not,[i.val]⟩] ++ gs.map (renameGate swap),renameWire swap out⟩

lemma switched_eval (i j : Fin 10) (gs : List Gate) (out : Nat) (x : Fin 10 → Bool) :
    (switched i j gs out).eval (List.ofFn x) =
      (Circuit.mk ([⟨.not,[i.val]⟩,⟨.not,[j.val]⟩] ++ gs) out).eval (List.ofFn x) := by
  have h := fold_rename_relation swap gs
    (List.ofFn x ++ [!x j,!x i]) (List.ofFn x ++ [!x i,!x j])
    (by simp) (by simp) (initial_relation i j x) out
  simpa only [switched,Circuit.eval,Circuit.wires,List.foldl_append,prefix_eval] using h

lemma switched_size (i j : Fin 10) (gs : List Gate) (out : Nat) :
    (switched i j gs out).size =
      (Circuit.mk ([⟨.not,[i.val]⟩,⟨.not,[j.val]⟩] ++ gs) out).size := by
  simp [switched,Circuit.size]

lemma switched_fanInTwo (i j : Fin 10) (gs : List Gate) (out : Nat)
    (hf : FanInTwo (Circuit.mk ([⟨.not,[i.val]⟩,⟨.not,[j.val]⟩] ++ gs) out)) :
    FanInTwo (switched i j gs out) := by
  intro g hg
  simp only [switched,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with (rfl | rfl) | hg
  · simp
  · simp
  · obtain ⟨g,hmem,rfl⟩ := List.mem_map.mp hg
    have hh := hf g (by simp [hmem])
    simpa [renameGate] using hh

lemma contains_low (i : Fin 10) (xs : List Nat) :
    (xs.map (renameWire swap)).contains i.val = xs.contains i.val := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.contains_iff_mem,List.mem_map,rename_eq]
  constructor
  · rintro ⟨t,ht,he⟩
    exact (wire_low_iff i t).mp he ▸ ht
  · intro h
    exact ⟨i.val,h,wire_low i⟩

lemma contains_ten (xs : List Nat) :
    (xs.map (renameWire swap)).contains 10 = xs.contains 11 := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.contains_iff_mem,List.mem_map,rename_eq]
  constructor
  · rintro ⟨t,ht,he⟩
    exact (wire_ten_iff t).mp he ▸ ht
  · intro h
    exact ⟨11,h,by decide⟩

def readsSecond (j : Fin 10) (g : Gate) : Bool :=
  let xs := match g.op with | .not => g.inputs.take 1 | _ => g.inputs
  xs.contains j.val || xs.contains 11

lemma renamed_reader (j : Fin 10) (g : Gate) :
    readsLiteral j (renameGate swap g) = readsSecond j g := by
  rcases g with ⟨op,xs⟩
  cases op <;> simp only [readsLiteral,readsSecond,renameGate,← List.map_take,
    contains_low,contains_ten]

lemma second_count
    (h15 : ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 p9 15)
    (i j : Fin 10) (gs : List Gate) (out : Nat)
    (hf : FanInTwo (Circuit.mk ([⟨.not,[i.val]⟩,⟨.not,[j.val]⟩,⟨.and,[10,11]⟩] ++ gs) out))
    (hs : (Circuit.mk ([⟨.not,[i.val]⟩,⟨.not,[j.val]⟩,⟨.and,[10,11]⟩] ++ gs) out).size ≤ 19)
    (hc : ∀ x : Fin 10 → Bool,
      (Circuit.mk ([⟨.not,[i.val]⟩,⟨.not,[j.val]⟩,⟨.and,[10,11]⟩] ++ gs) out).eval
        (List.ofFn x) = p10 x) :
    gs.countP (readsSecond j) ≤ 1 := by
  let tail : List Gate := ⟨.and,[10,11]⟩ :: gs
  have hf' := switched_fanInTwo i j tail out hf
  have hs' : (switched i j tail out).size ≤ 19 := by
    rw [switched_size]
    exact hs
  have hc' : ∀ x : Fin 10 → Bool, (switched i j tail out).eval (List.ofFn x) = p10 x := by
    intro x
    rw [switched_eval]
    exact hc x
  have hb := first_not_readers_le_two_any h15 j
    (⟨.not,[i.val]⟩ :: tail.map (renameGate swap)) (renameWire swap out) hf' hs' hc'
  simp only [List.countP_cons,List.countP_map,Function.comp_def,renamed_reader] at hb
  dsimp only [tail] at hb
  have ht : readsSecond j ⟨.and,[10,11]⟩ = true := by simp [readsSecond]
  simp only [List.countP_cons,ht,ite_true] at hb
  change gs.countP (readsSecond j) + 1 + _ ≤ 2 at hb
  omega

lemma second_count_binary
    (h15 : ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 p9 15)
    (i j : Fin 10) (gs : List Gate) (out : Nat)
    (hf : FanInTwo (Circuit.mk ([⟨.not,[i.val]⟩,⟨.not,[j.val]⟩,⟨.and,[10,11]⟩] ++ gs) out))
    (hs : (Circuit.mk ([⟨.not,[i.val]⟩,⟨.not,[j.val]⟩,⟨.and,[10,11]⟩] ++ gs) out).size ≤ 19)
    (hc : ∀ x : Fin 10 → Bool,
      (Circuit.mk ([⟨.not,[i.val]⟩,⟨.not,[j.val]⟩,⟨.and,[10,11]⟩] ++ gs) out).eval
        (List.ofFn x) = p10 x)
    (hn : ∀ g ∈ gs, g.op ≠ .not) :
    gs.countP (fun g => g.inputs.contains j.val || g.inputs.contains 11) ≤ 1 := by
  have h := second_count h15 i j gs out hf hs hc
  have he : gs.countP (readsSecond j) =
      gs.countP (fun g => g.inputs.contains j.val || g.inputs.contains 11) := by
    apply List.countP_congr
    intro g hg
    have hgn := hn g hg
    unfold readsSecond
    cases hgo : g.op <;> simp_all
  rw [← he]
  exact h

end PEqualNP.Outside.L_meta_2592.TwoNotSwap
