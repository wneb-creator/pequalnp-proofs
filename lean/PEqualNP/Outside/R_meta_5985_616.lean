import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 12000 in
set_option maxHeartbeats 6000000 in
theorem PEqualNP.Outside.R_meta_5985_616
    (eliminate : let F := (fun (x : Fin 26 → Bool) => ∃ p l : Fin 13,
        (p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9) ∧
        x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true);
      ∀ C : Circuit, Monotone2 C → C.size ≤ 55 →
      (∀ x, x 0 = false → x 13 = false → (C.eval (List.ofFn x) = true ↔ F x)) →
      ∃ (v : Fin 26) (D : Circuit), v ≠ 0 ∧ v ≠ 13 ∧ Monotone2 D ∧
        D.size + (if v ∈ ([1,3,9,17,23,25] : List (Fin 26)) then 4 else 5) ≤ C.size ∧
        ∀ x : Fin 26 → Bool, x 0 = false → x 13 = false → x v = false →
          D.eval (List.ofFn x) = C.eval (List.ofFn x))
    (representatives : let F := (fun (x : Fin 26 → Bool) => ∃ p l : Fin 13,
        (p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9) ∧
        x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true);
      ∀ (D : Circuit) (v : Fin 26), Monotone2 D → (v=1 ∨ v=2) →
        (∀ x, x 0 = false → x 13 = false → x v = false → (D.eval (List.ofFn x) = true ↔ F x)) →
        (if v=1 then 52 else 51) ≤ D.size) :
    have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → (∀ (x4 : Fin (26 : ℕ) → Bool), x4 (0 : Fin (26 : ℕ)) = Bool.false → x4 (13 : Fin (26 : ℕ)) = Bool.false → (x2.eval (List.ofFn x4) = Bool.true ↔ ∃ (x7 : Fin (13 : ℕ)) (x8 : Fin (13 : ℕ)), x1 x7 x8 ∧ x4 (Fin.castAdd (13 : ℕ) x7) = Bool.true ∧ x4 (Fin.natAdd (13 : ℕ) x8) = Bool.true)) → (56 : ℕ) ≤ x2.size := by
  intro I C mono spec
  by_contra! smallC
  obtain ⟨v,D,hv0,hv13,hm,save,agree⟩ := eliminate C mono (by omega) spec
  let low : Fin 26 → Prop := fun i => i ∈ ([1,3,9,17,23,25] : List (Fin 26))
  let rep (i : Fin 26) : Fin 26 := if low i then 1 else 2
  let table : List (List (Fin 26)) := [
    [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25],
    [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25],
    [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25],
    [0,3,2,1,5,4,6,7,12,9,11,10,8,13,15,14,18,17,16,19,24,22,21,23,20,25],
    [0,1,10,3,2,8,5,12,6,9,4,7,11,13,14,20,15,25,18,22,16,19,21,17,24,23],
    [0,1,6,9,8,2,4,12,10,3,5,7,11,13,18,19,21,25,14,16,22,20,15,17,24,23],
    [0,1,6,3,5,4,2,7,10,9,8,12,11,13,18,16,15,17,14,19,20,22,21,25,24,23],
    [0,1,6,3,8,12,7,2,11,9,5,4,10,13,18,16,20,25,24,19,15,21,22,17,14,23],
    [0,1,8,9,5,4,10,7,2,3,6,11,12,13,18,21,22,17,14,20,19,15,16,23,24,25],
    [0,3,2,9,11,6,4,10,12,1,5,7,8,13,15,19,21,23,16,14,22,24,18,17,20,25],
    [0,1,10,9,4,5,8,7,6,3,2,12,11,13,14,22,21,17,18,20,19,16,15,25,24,23],
    [0,1,11,3,7,5,8,4,6,9,12,2,10,13,24,15,20,17,18,21,16,19,22,25,14,23],
    [0,1,8,3,5,7,11,4,12,9,6,10,2,13,18,20,15,17,24,21,16,22,19,23,14,25],
    [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25],
    [13,25,14,17,19,21,20,22,18,23,15,16,24,0,2,4,7,9,8,10,5,6,11,3,12,1],
    [13,17,14,25,21,19,20,22,24,23,16,15,18,0,4,2,8,9,7,10,12,11,6,3,5,1],
    [13,17,18,25,15,20,19,16,24,23,22,21,14,0,5,8,2,3,7,6,12,11,10,9,4,1],
    [13,17,19,23,24,18,15,14,22,25,20,16,21,0,7,6,11,1,5,2,10,12,8,3,4,9],
    [13,25,18,17,20,15,19,16,14,23,21,22,24,0,8,5,7,3,2,6,4,10,11,9,12,1],
    [13,17,14,23,21,22,15,19,18,25,16,20,24,0,4,10,11,9,5,2,6,8,12,3,7,1],
    [13,17,18,25,22,21,16,19,14,23,15,20,24,0,5,8,12,9,4,6,2,10,11,3,7,1],
    [13,17,18,23,15,16,21,20,14,25,22,19,24,0,5,6,11,3,4,8,10,2,12,9,7,1],
    [13,17,18,23,22,19,20,21,24,25,15,16,14,0,5,6,10,9,7,8,11,12,2,3,4,1],
    [13,17,19,23,20,16,14,15,21,25,24,18,22,0,7,6,10,3,4,2,11,8,12,1,5,9],
    [13,25,18,17,21,22,16,19,24,23,20,15,14,0,8,5,4,9,12,6,7,11,10,3,2,1],
    [13,17,14,23,16,20,19,15,24,25,21,22,18,0,4,10,6,3,7,2,11,12,8,9,5,1]]
  let perm (i j : Fin 26) := (table.getD i.val []).getD j.val 0
  let E (a b : Fin 26) := let p := min a.val b.val; let l := max a.val b.val
                           decide (p < 13 ∧ 13 ≤ l ∧ (p+26-l)%13 ∈ [0,1,3,9])
  have geometric : ∀ i : Fin 26, i ≠ 0 → i ≠ 13 →
      perm i i = rep i ∧ (perm i 0 = 0 ∨ perm i 0 = 13) ∧
      (perm i 13 = 0 ∨ perm i 13 = 13) ∧ (∀ a, ∃ b, perm i b = a) ∧
      ∀ a b, E (perm i a) (perm i b) = E a b := by decide +kernel
  obtain ⟨toRep, at0, at13, onto, preserves⟩ := geometric v hv0 hv13
  let F := fun x : Fin 26 → Bool => ∃ p l, I p l ∧ x (Fin.castAdd 13 p) = true ∧
      x (Fin.natAdd 13 l) = true
  have oriented : ∀ p l : Fin 13, I p l → E (Fin.castAdd 13 p) (Fin.natAdd 13 l) = true := by decide
  have endpoints : ∀ a b, E a b = true → ∃ p l, I p l ∧
      ((a = Fin.castAdd 13 p ∧ b = Fin.natAdd 13 l) ∨
       (b = Fin.castAdd 13 p ∧ a = Fin.natAdd 13 l)) := by decide +kernel
  have edgeForm (x : Fin 26 → Bool) : F x ↔ ∃ a b, E a b = true ∧ x a = true ∧ x b = true := by
    constructor
    · rintro ⟨p,l,hi,hp,hl⟩
      exact ⟨_,_,oriented p l hi,hp,hl⟩
    · rintro ⟨a,b,he,ha,hb⟩
      obtain ⟨p,l,hi,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ := endpoints a b he
      · exact ⟨p,l,hi,ha,hb⟩
      · exact ⟨p,l,hi,hb,ha⟩
  have invariant (x : Fin 26 → Bool) : F (x ∘ perm v) ↔ F x := by
    rw [edgeForm, edgeForm]
    constructor
    · rintro ⟨a,b,h,ha,hb⟩
      exact ⟨_,_,(preserves a b).trans h,ha,hb⟩
    · rintro ⟨a,b,h,ha,hb⟩
      obtain ⟨a',rfl⟩ := onto a
      obtain ⟨b',rfl⟩ := onto b
      exact ⟨_,_,(preserves a' b').symm.trans h,ha,hb⟩
  let σ (w : ℕ) := if h : w < 26 then (perm v ⟨w,h⟩).val else w
  let rg (g : Gate) : Gate := ⟨g.op,g.inputs.map σ⟩
  let B : Circuit := ⟨D.gates.map rg, σ D.output⟩
  have rsize : B.size = D.size := by
    change (D.gates.map rg).length = D.gates.length
    exact List.length_map rg
  have rmono : Monotone2 B := by
    intro g hg
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
    simpa [rg] using hm a ha
  have same (x : Fin 26 → Bool) : B.eval (List.ofFn x) = D.eval (List.ofFn (x ∘ perm v)) := by
    let old := List.ofFn (x ∘ perm v)
    let newIn := List.ofFn x
    have wire (t : List Bool) (w : ℕ) :
        (newIn ++ t).getD (σ w) false = (old ++ t).getD w false := by
      by_cases h : w < 26
      · have hr : σ w < 26 := by simpa only [σ,dite_eq_left h] using (perm v ⟨w,h⟩).isLt
        rw [List.getD_append _ _ _ _ (by simpa only [newIn,List.length_ofFn] using hr),
            List.getD_append _ _ _ _ (by simpa only [old,List.length_ofFn] using h)]
        unfold newIn old
        simp only [List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (show σ w < (List.ofFn x).length by simpa only [List.length_ofFn] using hr),
          List.getElem?_eq_getElem (show w < (List.ofFn (x ∘ perm v)).length by simpa only [List.length_ofFn] using h),
          Option.getD_some,List.getElem_ofFn]
        simp [σ,h]
      · simp only [σ, dite_eq_right h]
        rw [List.getD_append_right _ _ _ _ (by simp [newIn]; omega),
            List.getD_append_right _ _ _ _ (by simp [old]; omega)]
        simp [newIn,old]
    let step (acc : List Bool) (g : Gate) := acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]
    have run (gs : List Gate) (t : List Bool) : ∃ u,
        gs.foldl step (old ++ t) = old ++ u ∧ (gs.map rg).foldl step (newIn ++ t) = newIn ++ u := by
      induction gs generalizing t with
      | nil => exact ⟨t,rfl,rfl⟩
      | cons g gs ih =>
        let z := g.op.eval (g.inputs.map fun i => (old ++ t).getD i false)
        have gate : (rg g).op.eval ((rg g).inputs.map fun i => (newIn ++ t).getD i false) = z := by
          unfold rg z
          rw [List.map_map]
          congr 1
          exact List.map_congr_left fun i _ => wire t i
        obtain ⟨u,hu,hv⟩ := ih (t ++ [z])
        exact ⟨u,by simpa only [List.foldl_cons,step,List.append_assoc,z] using hu,
          by simpa only [List.map_cons,List.foldl_cons,step,gate,List.append_assoc] using hv⟩
    obtain ⟨u,ho,hn⟩ := run D.gates []
    simp only [List.append_nil] at ho hn
    change ((D.gates.map rg).foldl step newIn).getD (σ D.output) false =
      (D.gates.foldl step old).getD D.output false
    rw [ho,hn]
    exact wire u D.output
  have choice : rep v = 1 ∨ rep v = 2 := by unfold rep; split <;> simp
  have bound := representatives B (rep v) rmono choice (by
    intro x h0 h13 hr
    have z0 : (x ∘ perm v) 0 = false := at0.elim (fun h => by simpa [Function.comp,h] using h0)
        (fun h => by simpa [Function.comp,h] using h13)
    have z13 : (x ∘ perm v) 13 = false := at13.elim (fun h => by simpa [Function.comp,h] using h0)
        (fun h => by simpa [Function.comp,h] using h13)
    rw [same,agree _ z0 z13 (by simpa [Function.comp,toRep] using hr)]
    exact (spec _ z0 z13).trans (invariant x))
  rw [rsize] at bound
  by_cases h : low v
  · simp [rep,h] at bound
    change D.size + (if low v then 4 else 5) ≤ C.size at save
    rw [ite_eq_left h] at save
    omega
  · simp [rep,h] at bound
    change D.size + (if low v then 4 else 5) ≤ C.size at save
    rw [ite_eq_right h] at save
    omega
