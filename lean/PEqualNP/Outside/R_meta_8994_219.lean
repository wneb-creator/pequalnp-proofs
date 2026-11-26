import PEqualNP.Defs
import Mathlib.Data.List.GetD
import Mathlib.Tactic.ByContra

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

set_option maxHeartbeats 6000000 in
set_option maxRecDepth 8192 in
theorem PEqualNP.Outside.R_meta_8994_219
    (decompose : ∀ C : Circuit, IsAO2 10 C → C.size ≤ 18 →
      (∀ u : Fin 10, ∃ x : Fin 9 → Bool, C.eval (List.ofFn (u.insertNth false x)) ≠ C.eval (List.ofFn (u.insertNth true x))) →
      ∃ (u : Fin 10) (P Q : Circuit) (c : Bool), IsAO2 9 P ∧ IsAO2 (10 + P.size) Q ∧
        P.size + Q.size ≤ 17 ∧ P.output < 9 + P.size ∧ ∀ (x : Fin 9 → Bool) (z : Bool),
        C.eval (List.ofFn (u.insertNth z x)) = Q.eval (P.wires (List.ofFn x) ++
          [if c then z && P.eval (List.ofFn x) else z || P.eval (List.ofFn x)]))
    (andCase : ∀ (v : Fin 11) (u : Fin 10) (P Q : Circuit), v.val < 4 →
      IsAO2 9 P → IsAO2 (10 + P.size) Q → P.size + Q.size ≤ 17 → 9 ≤ P.output → P.output < 9 + P.size →
      let f := fun (y : Fin 10 → Bool) =>
        let t : Fin 11 → Bool := v.insertNth false y
        ([9,10,15,19,27,32,39,40,52,54,63,64,73,76,86,97] : List ℕ).any (fun e => t (Fin.ofNat 11 (e / 11)) && t (Fin.ofNat 11 (e % 11)))
      (∀ x : Fin 9 → Bool, f (u.insertNth false x) ≠ f (u.insertNth true x) → P.eval (List.ofFn x) = true) →
      ∃ (x : Fin 9 → Bool) (z : Bool), Q.eval (P.wires (List.ofFn x) ++ [z && P.eval (List.ofFn x)]) ≠
        f (u.insertNth z x))
    (orCase : ∀ (v : Fin 11) (u : Fin 10) (P Q : Circuit), v.val < 4 →
      IsAO2 9 P → IsAO2 (10 + P.size) Q → P.size + Q.size ≤ 17 → 9 ≤ P.output → P.output < 9 + P.size →
      let f := fun (y : Fin 10 → Bool) =>
        let t : Fin 11 → Bool := v.insertNth false y
        ([9,10,15,19,27,32,39,40,52,54,63,64,73,76,86,97] : List ℕ).any (fun e => t (Fin.ofNat 11 (e / 11)) && t (Fin.ofNat 11 (e % 11)))
      (∀ x : Fin 9 → Bool, f (u.insertNth false x) ≠ f (u.insertNth true x) → P.eval (List.ofFn x) = false) →
      ∃ (x : Fin 9 → Bool) (z : Bool), Q.eval (P.wires (List.ofFn x) ++ [z || P.eval (List.ofFn x)]) ≠
        f (u.insertNth z x)) :
let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : Fin (11 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), ↑x2 < (4 : ℕ) → PEqualNP.TopForm.IsAO2 (10 : ℕ) x3 → (∀ (x6 : Fin (10 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x3 x6 = PEqualNP.MetaComplexity.NestedCover.graphFun x1 ∅ (x2.insertNth Bool.false x6)) → (19 : ℕ) ≤ x3.size := by
  intro G v C hv legal correct
  by_contra! small
  let edges : List (Fin 11 × Fin 11) := [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
  let edge (x : Fin 11 → Bool) := ([9,10,15,19,27,32,39,40,52,54,63,64,73,76,86,97] : List ℕ).any
    (fun e => x (Fin.ofNat 11 (e / 11)) && x (Fin.ofNat 11 (e % 11)))
  have adj : ∀ a b : Fin 11, G.Adj a b ↔ (a,b) ∈ edges ∨ (b,a) ∈ edges := by decide +kernel
  have graph (x : Fin 11 → Bool) : graphFun G ∅ x = edge x := by
    have val : graphFun G ∅ x = edges.any (fun e => x e.1 && x e.2) := by
      apply Bool.eq_iff_iff.mpr
      delta graphFun
      simp only [Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or,
        decide_eq_true_eq,List.any_eq_true,Bool.and_eq_true]
      constructor
      · rintro ⟨a,b,e,ha,hb⟩
        rcases (adj a b).mp e with h | h
        · exact ⟨(a,b),h,ha,hb⟩
        · exact ⟨(b,a),h,hb,ha⟩
      · rintro ⟨⟨a,b⟩,h,ha,hb⟩
        exact ⟨a,b,(adj a b).mpr (Or.inl h),ha,hb⟩
    exact val.trans (by rfl)
  let f (w : Fin 11) (x : Fin 10 → Bool) := edge (w.insertNth false x)
  let choose (w : Fin 11) (u : Fin 10) (j : Fin 9) (b : Bool) : Fin 9 :=
    Fin.ofNat 9 ((([222222622,620222022,333338333,88330333,444454444,544004444,6,1000000,111111161,601111101,222222522,22022022,222222522,202022022,3,1000,444464444,410404464,111111131,111031101,787777777,108878777,333338333,188330333,444454444,544004444,668666666,280668666,111111161,610111101,222222522,222022022,222222522,212022022,333334333,413300333,4,400000000,1,100000000,787777777,8878777,222222622,620222022,444454444,544004444,111111161,110111101,667666666,610667676,222222522,122022022,222222522,212022022,111111131,111100101,4,400000000,3,300000000,787777777,8878777,222222622,620222022,333338333,188330333,111111161,110111101,222222622,610222022,555855555,185055555,555755555,715055555,111111131,111100101,4,400000000,2,200000000] : List ℕ).getD (20*w.val + 2*u.val + b.toNat) 0 / 10^j.val) % 10)
  let test (w : Fin 11) (u : Fin 10) (j : Fin 9) (b : Bool) (k : Fin 9) :=
    decide (k = choose w u j b) || (b && decide (k = j))
  have tests : ∀ (w : Fin 11), w.val < 4 → ∀ (u : Fin 10) (j : Fin 9) (b : Bool),
      test w u j b j = b ∧ f w (u.insertNth false (test w u j b)) = false ∧
      f w (u.insertNth true (test w u j b)) = true := by decide +kernel
  have val (x : Fin 10 → Bool) : C.eval (List.ofFn x) = f v x :=
    (correct x).trans (graph _)
  have essential (u : Fin 10) : ∃ x : Fin 9 → Bool,
      C.eval (List.ofFn (u.insertNth false x)) ≠ C.eval (List.ofFn (u.insertNth true x)) := by
    obtain ⟨_,no,yes⟩ := tests v hv u 0 false
    exact ⟨_,by rw [val,val,no,yes]; decide⟩
  obtain ⟨u,P,Q,c,pok,qok,cap,prev,decomp⟩ := decompose C legal (by omega) essential
  have sim (x : Fin 9 → Bool) (z : Bool) := (decomp x z).symm.trans (val (u.insertNth z x))
  have openAt (x : Fin 9 → Bool) (h : f v (u.insertNth false x) ≠ f v (u.insertNth true x)) :
      P.eval (List.ofFn x) = c := by
    by_contra ne
    have eq : (if c then false && P.eval (List.ofFn x) else false || P.eval (List.ofFn x)) =
        (if c then true && P.eval (List.ofFn x) else true || P.eval (List.ofFn x)) := by
      cases ec : c <;> cases ep : P.eval (List.ofFn x) <;> first
        | rfl
        | exact False.elim (ne (ep.trans ec.symm))
    exact h ((sim x false).symm.trans ((congrArg (fun b => Q.eval (P.wires (List.ofFn x) ++ [b])) eq).trans (sim x true)))
  have keep (gs : List Gate) (xs : List Bool) (i : ℕ) (hi : i < xs.length) :
      ((Circuit.mk gs 0).wires xs).getD i false = xs.getD i false := by
    induction gs generalizing xs with
    | nil => rfl
    | cons g gs ih =>
      change ((Circuit.mk gs 0).wires (xs ++ [_])).getD i false = _
      rw [ih _ (by simp; omega),List.getD_append _ _ _ _ hi]
  have gate : 9 ≤ P.output := by
    by_contra! lo
    let j : Fin 9 := ⟨P.output,lo⟩
    let x := test v u j (!c)
    obtain ⟨raw,no,yes⟩ := tests v hv u j (!c)
    have pass := openAt x (by rw [no,yes]; decide)
    have projection : P.eval (List.ofFn x) = x j := by
      change ((Circuit.mk P.gates 0).wires (List.ofFn x)).getD P.output false = _
      rw [keep _ _ _ (by simpa only [List.length_ofFn] using lo)]
      rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using lo),List.getElem_ofFn]
    change x j = !c at raw
    have neq := (projection.symm.trans pass).symm.trans raw
    cases c <;> contradiction
  cases hc : c with
  | false =>
    obtain ⟨x,z,h⟩ := orCase v u P Q hv pok qok cap gate prev (fun x hx => (openAt x hx).trans hc)
    exact h (by simpa only [hc,Bool.false_eq_true,ite_false] using sim x z)
  | true =>
    obtain ⟨x,z,h⟩ := andCase v u P Q hv pok qok cap gate prev (fun x hx => (openAt x hx).trans hc)
    exact h (by simpa only [hc,ite_true] using sim x z)
