import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
theorem PEqualNP.Outside.R_meta_17991_17
    (nine : ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) 15)
    (direct : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.eval (List.ofFn fun (x4 : Fin x1) => Bool.false) = Bool.false →       ∀ (x5 x6 : Fin x1),         have x7 : PEqualNP.CircuitLowerBounds.Gate → List ℕ := fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => List.take (bif x7.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x7.inputs;         ∃ (x8 : ℕ), x8 + List.countP (fun (x9 : PEqualNP.CircuitLowerBounds.Gate) => (x7 x9).any fun (x10 : ℕ) => x10 == ↑x5 || x10 == ↑x6) x2.gates ≤ x2.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x9 : Fin x1 → Bool) => x2.eval (List.ofFn (Function.update (Function.update x9 x5 Bool.false) x6 Bool.false))) x8)
    (pinSaved : ∀ (x1 : ℕ) (x2 : (Fin (x1 + (1 : ℕ)) → Bool) → Bool) (x3 : Fin (x1 + (1 : ℕ))) (x4 : Bool) (x5 : ℕ), (∃ (x6 : Fin (x1 + (1 : ℕ)) → Bool), x2 (Function.update x6 x3 !x6 x3) ≠ x2 x6) → (∃ (x7 : Fin (x1 + (1 : ℕ)) → Bool) (x8 : Fin (x1 + (1 : ℕ)) → Bool), x2 (Function.update x7 x3 x4) ≠ x2 (Function.update x8 x3 x4)) → PEqualNP.MetaComplexity.HasCircuitSize (x1 + (1 : ℕ)) x2 (x5 + (1 : ℕ)) → PEqualNP.MetaComplexity.HasCircuitSize (x1 + (1 : ℕ)) (fun (x9 : Fin (x1 + (1 : ℕ)) → Bool) => x2 (Function.update x9 x3 x4)) x5) :
(∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (17 : ℕ) → ∃ (x4 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [x4 (0 : Fin (10 : ℕ)) && x4 (2 : Fin (10 : ℕ)), !(x4 (0 : Fin (10 : ℕ)) && x4 (2 : Fin (10 : ℕ)))]) ≠ (fun (x5 : Fin (10 : ℕ) → Bool) => x5 (0 : Fin (10 : ℕ)) && x5 (1 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (3 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (4 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (0 : Fin (10 : ℕ)) || x5 (0 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (5 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (7 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (9 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (6 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (8 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ))) x4) := by
  have ordinary : ¬ HasCircuitSize 10 (fun x : Fin 10 → Bool =>
      (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
      (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) ||
      (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) 17 := by
    have lLA {α:Type} {l1 l2:List α}:(l1++l2).length=l1.length+l2.length:=List.length_append
    have nAA (a b d:Nat):a+b+d=a+(b+d):=Nat.add_assoc a b d
    have lMMp {α β γ:Type} {g : β->γ} {f : α->β} {l:List α}:(l.map f).map g=l.map (g ∘ f):=List.map_map
    have lGD {α:Type} (l:List α) (d : α) {i:Nat} (h:l.length<=i):l.getD i d=d:=List.getD_eq_default l d h
    let q3 (gs:List Gate) (w:List Bool):List Bool :=
     gs.foldl (fun w g => w++[g.op.eval (g.inputs.map fun i => w.getD i false)]) w
    have zd (gs gs':List Gate) (w:List Bool) :
       q3 (gs++gs') w=q3 gs' (q3 gs w):=by
     simp [q3,List.foldl_append]
    have y1 (gs:List Gate):∀ w:List Bool,
       ∃ t:List Bool,q3 gs w=w++t/\t.length=gs.length:=by
     induction gs with
     | nil => intro w;exact ⟨[],by simp [q3],rfl⟩
     | cons g gs ih =>
       intro w
       obtain ⟨t,ht,hl⟩:=ih (w++[g.op.eval (g.inputs.map fun i => w.getD i false)])
       refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false)::t,?_,by simp [hl]⟩
       have:q3 (g::gs) w
           = q3 gs (w++[g.op.eval (g.inputs.map fun i => w.getD i false)]):=rfl
       rw [this,ht];simp
    have qu (gs:List Gate) (w:List Bool) :
       (q3 gs w).length=w.length+gs.length:=by
     obtain ⟨t,ht,hl⟩:=y1 gs w
     rw [ht];simp [hl]
    let Ok (g:Gate):Prop :=
     g.op ∈ ({GateOp.and,GateOp.or,GateOp.not}:Set GateOp)/\g.inputs.length<=2
    have q8 {α:Type} (L:List α) (S d : α) (j : ℕ) (h:j≠L.length) :
       (L++[S]).getD j d=L.getD j d:=by
     by_cases hj:j < L.length
     . exact List.getD_append _ _ _ _ hj
     . rw [lGD _ _ (by simp;omega),lGD _ _ (by omega)]
    have z0 {α:Type} (L:List α) (S d : α):(L++[S]).getD L.length d=S:=by
     simp
    have truthAnd (xs : List Bool) : GateOp.and.eval xs = xs.all id := rfl
    have truthOr (xs : List Bool) : GateOp.or.eval xs = xs.any id := rfl
    have truthNot (xs : List Bool) : GateOp.not.eval xs = !(xs.headD false) := rfl
    have circuitSize (C : Circuit) : C.size = C.gates.length := rfl
    have circuitEval (C : Circuit) (w : List Bool) :
        C.eval w = (C.wires w).getD C.output false := rfl
    have circuitWires (C : Circuit) (w : List Bool) :
        C.wires w = C.gates.foldl
          (fun a gate => a ++ [gate.op.eval (gate.inputs.map fun i => a.getD i false)]) w := rfl
    let vg (g:Gate):Gate :=
     GateOp.casesOn (motive := fun _ => Gate) g.op g g ⟨.not,g.inputs.take 1⟩ (fun _ => g) g
    have q107 (g:Gate) (F : ℕ->Bool) :
       (vg g).op.eval ((vg g).inputs.map F)=g.op.eval (g.inputs.map F):=by
     obtain ⟨op,inputs⟩:=g
     cases op <;> simp only [vg]
     cases inputs <;> simp [truthAnd, truthOr, truthNot]
    let NOk (g:Gate):Prop:=Ok g/\(g.op=GateOp.not->g.inputs.length<=1)
    have q45 (g:Gate) (h:Ok g):NOk (vg g):=by
     obtain ⟨op,inputs⟩:=g
     obtain ⟨hop,hlen⟩:=h
     rcases hop with h | h | h
     . have:op=GateOp.and:=h
       subst this;exact ⟨⟨Or.inl rfl,hlen⟩,by simp [vg]⟩
     . have:op=GateOp.or:=h
       subst this;exact ⟨⟨Or.inr (Or.inl rfl),hlen⟩,by simp [vg]⟩
     . have:op=GateOp.not:=h
       subst this
       refine ⟨⟨Or.inr (Or.inr rfl),?_⟩,fun _ => ?_⟩ <;> simp [vg]
    have jd (gs:List Gate):∀ w:List Bool,
       q3 (gs.map vg) w=q3 gs w:=by
     induction gs with
     | nil => intro w;rfl
     | cons g gs ih =>
       intro w
       have s1:q3 ((g::gs).map vg) w=q3 (gs.map vg)
           (w++[(vg g).op.eval ((vg g).inputs.map fun i => w.getD i false)]):=rfl
       have s2:q3 (g::gs) w
           = q3 gs (w++[g.op.eval (g.inputs.map fun i => w.getD i false)]):=rfl
       rw [s1,s2,q107,ih]
    let wmap (n m : ℕ) (π:Fin n->Fin m) (w : ℕ) : ℕ :=
     if h:w < n then (π ⟨w,h⟩ : ℕ) else w - n+m
    let jt (n m : ℕ) (π:Fin n->Fin m) (g:Gate):Gate :=
     ⟨g.op,g.inputs.map (wmap n m π)⟩
    let q174 (n m : ℕ) (π:Fin n->Fin m) (C:Circuit):Circuit :=
     ⟨C.gates.map (jt n m π),wmap n m π C.output⟩
    let step (w:List Bool) (g:Gate):List Bool :=
     w++[g.op.eval (g.inputs.map fun i => w.getD i false)]
    let Rel (n m : ℕ) (π:Fin n->Fin m) (W W':List Bool):Prop :=
     n<=W.length/\W'.length+n=W.length+m /\
       ∀ w : ℕ,W'.getD (wmap n m π w) false=W.getD w false
    have q182 (n m : ℕ) (π:Fin n->Fin m) (W W':List Bool) (g:Gate)
       (h:Rel n m π W W'):Rel n m π (step W g) (step W' (jt n m π g)):=by
     obtain ⟨h1,h2,h3⟩:=h
     have hv:(jt n m π g).op.eval
         ((jt n m π g).inputs.map fun i => W'.getD i false)
         = g.op.eval (g.inputs.map fun i => W.getD i false):=by
       simp only [jt,lMMp]
       congr 1
       apply List.map_congr_left
       intro a _
       exact h3 a
     refine ⟨by simp [step];omega,by simp [step];omega,?_⟩
     intro w
     simp only [step,hv]
     rcases Nat.lt_trichotomy w W.length with hw | hw | hw
     . have hlt:wmap n m π w < W'.length:=by
         unfold wmap
         split
         . have:=(π ⟨w,by assumption⟩).2;omega
         . omega
       rw [List.getD_append _ _ _ _ hlt,List.getD_append _ _ _ _ hw]
       exact h3 w
     . have he:wmap n m π w=W'.length:=by
         unfold wmap
         split
         . omega
         . omega
       rw [he,hw,z0,z0]
     . have hge:W'.length+1<=wmap n m π w:=by
         unfold wmap
         split
         . omega
         . omega
       rw [lGD _ _ (by simp;omega),lGD _ _ (by simp;omega)]
    have q184 (n m : ℕ) (π:Fin n->Fin m) (gs:List Gate) :
       ∀ W W':List Bool,Rel n m π W W' ->
         Rel n m π (gs.foldl step W) ((gs.map (jt n m π)).foldl step W'):=by
     induction gs with
     | nil => intro W W' h;exact h
     | cons g gs ih =>
       intro W W' h
       exact ih _ _ (q182 n m π W W' g h)
    have q183 (n m : ℕ) (π:Fin n->Fin m) (x:Fin m->Bool) :
       Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x):=by
     refine ⟨by simp,by simp;omega,?_⟩
     intro w
     unfold wmap
     split
     . rename_i hw
       rw [List.getD_eq_getElem _ _ (by simp),List.getD_eq_getElem _ _ (by simpa using hw)]
       simp
     . rename_i hw
       rw [lGD _ _ (by simp),lGD _ _ (by simp;omega)]
    have yn {n m : ℕ} (π:Fin n->Fin m) (h:(Fin n->Bool)->Bool) (s : ℕ)
       (hc:HasCircuitSize n h s):HasCircuitSize m (fun x => h (x ∘ π)) s:=by
     obtain ⟨C,ok,hsz,hev⟩:=hc
     refine ⟨q174 n m π C,?_,?_,?_⟩
     . intro g hg
       obtain ⟨g0,hg0,rfl⟩:=List.mem_map.1 hg
       exact ⟨(ok g0 hg0).1,by simpa [jt] using (ok g0 hg0).2⟩
     . simpa [q174,circuitSize] using hsz
     . intro x
       show _=h (x ∘ π)
       rw [← hev (x ∘ π)]
       have:=(q184 n m π C.gates _ _ (q183 n m π x)).2.2 C.output
       exact this
    have q134 (n : ℕ) (y:Fin n->Bool) (b:Bool) :
       List.ofFn (Fin.snoc y b:Fin (n+1)->Bool)=List.ofFn y++[b]:=by
     rw [List.ofFn_succ']
     simp
    let BFn (n : ℕ) := (Fin n → Bool) → Bool
    let fix {n : ℕ} (f : BFn n) (p : Fin n) (b : Bool) : BFn n :=
      fun x => f (Function.update x p b)

    let depends {n : ℕ} (f : BFn n) (p : Fin n) : Prop :=
      ∃ x : Fin n → Bool, fix f p (!x p) x ≠ f x

    let nonconstant {n : ℕ} (f : BFn n) : Prop :=
      ∃ x y : Fin n → Bool, f x ≠ f y
    have q70 (n : ℕ) (f:(Fin (n+1)->Bool)->Bool) (p:Fin (n+1)) (b:Bool) (s : ℕ)
       (hdep:∃ x:Fin (n+1)->Bool,f (Function.update x p (!x p))≠f x)
       (hnc:∃ x y:Fin (n+1)->Bool,
         f (Function.update x p b)≠f (Function.update y p b))
       (h:HasCircuitSize (n+1) f s) :
       ∃ s' : ℕ,s'+1<=s /\
         HasCircuitSize (n+1) (fun x => f (Function.update x p b)) s':= by  cases s with
      | succ k => exact ⟨k,by omega,pinSaved n f p b k hdep hnc h⟩
      | zero =>
        obtain ⟨⟨gs,o⟩,_,small,corr⟩ := h
        change gs.length ≤ 0 at small
        have nil : gs = [] := by simpa using small
        subst gs
        have ev (w : Fin (n+1) → Bool) : (List.ofFn w).getD o false = f w := corr w
        by_cases inside : o < n+1
        · let j : Fin (n+1) := ⟨o,inside⟩
          have proj (w : Fin (n+1) → Bool) : f w = w j := by
            rw [←ev, List.getD_eq_getElem _ _ (by simpa using inside)]
            exact List.getElem_ofFn _
          by_cases eq : j = p
          · obtain ⟨x,y,diff⟩ := hnc
            simp [proj,eq] at diff
          · obtain ⟨x,diff⟩ := hdep
            simp [proj,Function.update_of_ne eq] at diff
        · obtain ⟨x,diff⟩ := hdep
          have ef (w : Fin (n+1) → Bool) : f w = false := by
            rw [←ev]; exact List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt inside)
          simp [ef] at diff
    let full (x : Fin 10 → Bool) : Bool :=
      (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)

    let deleted (x : Fin 9 → Bool) : Bool :=
      (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)

    let deleted11 (x : Fin 11 → Bool) : Bool :=
      (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)

    let move (v i : Fin 10) : Fin 10 :=
      (![![9, 6, 8, 3, 4, 7, 1, 5, 2, 0],
        ![4, 9, 7, 5, 0, 3, 6, 2, 8, 1],
        ![0, 4, 9, 6, 1, 5, 3, 7, 8, 2],
        ![0, 1, 6, 9, 4, 5, 2, 8, 7, 3],
        ![6, 1, 2, 7, 9, 8, 0, 3, 5, 4],
        ![4, 3, 2, 1, 0, 9, 8, 7, 6, 5],
        ![0, 4, 3, 2, 1, 5, 9, 8, 7, 6],
        ![0, 1, 6, 8, 5, 4, 2, 9, 3, 7],
        ![0, 1, 2, 7, 5, 4, 6, 3, 9, 8],
        ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9]] : Fin 10 → Fin 10 → Fin 10) v i

    have movesNine : ∀ v, move v 9 = v := by decide +kernel

    have selfInverse : ∀ v i, move v (move v i) = i := by decide +kernel

    have invariant (v : Fin 10) (x : Fin 10 → Bool) :
        full (fun i => x (move v i)) = full x := by
      fin_cases v
      · change ((x 9 && x 6) || (x 6 && x 8) || (x 8 && x 3) || (x 3 && x 4) || (x 4 && x 9) || (x 9 && x 7) || (x 6 && x 1) || (x 8 && x 5) || (x 3 && x 2) || (x 4 && x 0) || (x 7 && x 5) || (x 5 && x 0) || (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 7)) = full x
        unfold full
        ac_rfl
      · change ((x 4 && x 9) || (x 9 && x 7) || (x 7 && x 5) || (x 5 && x 0) || (x 0 && x 4) || (x 4 && x 3) || (x 9 && x 6) || (x 7 && x 2) || (x 5 && x 8) || (x 0 && x 1) || (x 3 && x 2) || (x 2 && x 1) || (x 1 && x 6) || (x 6 && x 8) || (x 8 && x 3)) = full x
        unfold full
        ac_rfl
      · change ((x 0 && x 4) || (x 4 && x 9) || (x 9 && x 6) || (x 6 && x 1) || (x 1 && x 0) || (x 0 && x 5) || (x 4 && x 3) || (x 9 && x 7) || (x 6 && x 8) || (x 1 && x 2) || (x 5 && x 7) || (x 7 && x 2) || (x 2 && x 3) || (x 3 && x 8) || (x 8 && x 5)) = full x
        unfold full
        ac_rfl
      · change ((x 0 && x 1) || (x 1 && x 6) || (x 6 && x 9) || (x 9 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 2) || (x 6 && x 8) || (x 9 && x 7) || (x 4 && x 3) || (x 5 && x 8) || (x 8 && x 3) || (x 3 && x 2) || (x 2 && x 7) || (x 7 && x 5)) = full x
        unfold full
        ac_rfl
      · change ((x 6 && x 1) || (x 1 && x 2) || (x 2 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 1 && x 0) || (x 2 && x 3) || (x 7 && x 5) || (x 9 && x 4) || (x 8 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 5 && x 8)) = full x
        unfold full
        ac_rfl
      · change ((x 4 && x 3) || (x 3 && x 2) || (x 2 && x 1) || (x 1 && x 0) || (x 0 && x 4) || (x 4 && x 9) || (x 3 && x 8) || (x 2 && x 7) || (x 1 && x 6) || (x 0 && x 5) || (x 9 && x 7) || (x 7 && x 5) || (x 5 && x 8) || (x 8 && x 6) || (x 6 && x 9)) = full x
        unfold full
        ac_rfl
      · change ((x 0 && x 4) || (x 4 && x 3) || (x 3 && x 2) || (x 2 && x 1) || (x 1 && x 0) || (x 0 && x 5) || (x 4 && x 9) || (x 3 && x 8) || (x 2 && x 7) || (x 1 && x 6) || (x 5 && x 8) || (x 8 && x 6) || (x 6 && x 9) || (x 9 && x 7) || (x 7 && x 5)) = full x
        unfold full
        ac_rfl
      · change ((x 0 && x 1) || (x 1 && x 6) || (x 6 && x 8) || (x 8 && x 5) || (x 5 && x 0) || (x 0 && x 4) || (x 1 && x 2) || (x 6 && x 9) || (x 8 && x 3) || (x 5 && x 7) || (x 4 && x 9) || (x 9 && x 7) || (x 7 && x 2) || (x 2 && x 3) || (x 3 && x 4)) = full x
        unfold full
        ac_rfl
      · change ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 7) || (x 7 && x 5) || (x 5 && x 0) || (x 0 && x 4) || (x 1 && x 6) || (x 2 && x 3) || (x 7 && x 9) || (x 5 && x 8) || (x 4 && x 3) || (x 3 && x 8) || (x 8 && x 6) || (x 6 && x 9) || (x 9 && x 4)) = full x
        unfold full
        ac_rfl
      · change ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) = full x
        unfold full
        ac_rfl

    let pinNine (x : Fin 9 → Bool) (i : Fin 10) : Bool :=
      if h : i.val < 9 then x ⟨i.val, h⟩ else false

    have deleted_eq (x : Fin 9 → Bool) : full (pinNine x) = deleted x := by
      simp [full, deleted, pinNine]

    have droppedVertex (v : Fin 10) (x : Fin 9 → Bool) :
        full (fun i => pinNine x (move v i)) = deleted x :=
      (invariant v _).trans (deleted_eq _)

    have droppedAt (v : Fin 10) (x : Fin 9 → Bool) :
        pinNine x (move v v) = false := by
      have h := selfInverse v 9
      rw [movesNine] at h
      rw [h]
      rfl

    have pushedPin (v : Fin 10) (x : Fin 9 → Bool) :
        Function.update (x ∘ (fun i : Fin 10 => Fin.ofNat 9 (move v i).val)) v false =
          fun i => pinNine x (move v i) := by
      funext i
      by_cases same : i = v
      · subst i
        rw [Function.update_self, droppedAt]
      · rw [Function.update_of_ne same]
        have hn : move v i ≠ 9 := by
          intro eq
          have hi := selfInverse v i
          rw [eq, movesNine] at hi
          exact same hi.symm
        have lt : (move v i).val < 9 := by
          by_contra! h
          apply hn
          apply Fin.ext
          have h' := (move v i).isLt
          change (move v i).val = 9
          omega
        simp only [Function.comp_apply, pinNine, dite_eq_left lt]
        congr 1
        exact Fin.ext (Nat.mod_eq_of_lt lt)

    have lowerPinned (v : Fin 10)
        (lowerKnown : ¬ HasCircuitSize 9 deleted 15)
        (relabel : ∀ {n m : ℕ} (p : Fin n → Fin m) (f : (Fin n → Bool) → Bool) (s : ℕ),
          HasCircuitSize n f s → HasCircuitSize m (fun x => f (x ∘ p)) s) :
        ¬ HasCircuitSize 10 (fun x => full (Function.update x v false)) 15 := by
      intro small
      have restricted := relabel (fun i : Fin 10 => Fin.ofNat 9 (move v i).val) _ 15 small
      have h : (fun x : Fin 9 → Bool =>
          full (Function.update (x ∘ (fun i : Fin 10 => Fin.ofNat 9 (move v i).val)) v false)) =
          deleted := by
        funext x
        rw [pushedPin, droppedVertex]
      exact lowerKnown (h ▸ restricted)
    let reads (v : Nat) (g : Gate) : Bool := g.inputs.contains v || g.inputs.contains 10

    have wireNine (v : Fin 10) (w : Nat) :
        wmap 10 10 (move v) w = 9 ↔ w = v.val := by
      by_cases hw : w < 10
      · simp only [wmap, dite_eq_left hw]
        constructor
        · intro h
          have e : move v ⟨w, hw⟩ = 9 := Fin.ext h
          have i := selfInverse v ⟨w, hw⟩
          rw [e, movesNine] at i
          exact congrArg Fin.val i.symm
        · rintro rfl
          have e := selfInverse v 9
          rw [movesNine] at e
          exact congrArg Fin.val e
      · simp only [wmap, dite_eq_right hw]
        have := v.isLt
        omega

    have wireTen (v : Fin 10) (w : Nat) :
        wmap 10 10 (move v) w = 10 ↔ w = 10 := by
      by_cases hw : w < 10
      · simp only [wmap, dite_eq_left hw]
        have := (move v ⟨w, hw⟩).isLt
        omega
      · simp only [wmap, dite_eq_right hw]
        omega

    have hitMap (v : Fin 10) (g : Gate) :
        reads 9 (jt 10 10 (move v) g) = reads v.val g := by
      apply Bool.eq_iff_iff.mpr
      simp [reads, jt, List.mem_map, wireNine, wireTen]

    have mapNorm (v : Fin 10) (g : Gate) :
        vg (jt 10 10 (move v) g) = jt 10 10 (move v) (vg g) := by
      rcases g with ⟨op, ws⟩
      cases op <;> simp [vg,jt]

    have sameCount (v : Fin 10) (gs : List Gate) :
        ((gs.map (jt 10 10 (move v))).map vg).countP (reads 9) =
          (gs.map vg).countP (reads v.val) := by
      induction gs with
      | nil => rfl
      | cons g gs ih => simp only [List.map_cons, List.countP_cons, mapNorm, hitMap, ih]

    have canonical (v : Fin 10) (extra : List Nat) (gs : List Gate) (o : Nat)
        (legal : FanInTwo (⟨⟨.not, v.val :: extra⟩ :: gs, o⟩ : Circuit))
        (correct : ∀ x : Fin 10 → Bool,
          (⟨⟨.not, v.val :: extra⟩ :: gs, o⟩ : Circuit).eval (List.ofFn x) = full x) :
        ∃ (extra' : List Nat) (gs' : List Gate) (o' : Nat),
          FanInTwo (⟨⟨.not, 9 :: extra'⟩ :: gs', o'⟩ : Circuit) ∧
          (∀ x : Fin 10 → Bool, (⟨⟨.not, 9 :: extra'⟩ :: gs', o'⟩ : Circuit).eval (List.ofFn x) = full x) ∧
          gs'.length = gs.length ∧ (gs'.map vg).countP (reads 9) = (gs.map vg).countP (reads v.val) := by
      let C : Circuit := ⟨⟨.not, v.val :: extra⟩ :: gs, o⟩
      let f := wmap 10 10 (move v)
      have first : f v.val = 9 := (wireNine v _).mpr rfl
      have shape : q174 10 10 (move v) C =
          ⟨⟨.not, 9 :: extra.map f⟩ :: gs.map (jt 10 10 (move v)), f o⟩ := by
        exact congrArg (fun i : Nat => (⟨⟨.not, i :: extra.map f⟩ :: gs.map (jt 10 10 (move v)), f o⟩ : Circuit)) first
      refine ⟨extra.map f, gs.map (jt 10 10 (move v)), f o, ?_, ?_, by simp, sameCount v gs⟩
      · rw [← shape]
        intro g hg
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
        exact ⟨(legal a ha).1, by simpa [jt] using (legal a ha).2⟩
      · intro x
        rw [← shape]
        have eq := (q184 10 10 (move v) C.gates _ _ (q183 10 10 (move v) x)).2.2 C.output
        exact eq.trans ((correct (x ∘ move v)).trans (invariant v x))
    let tailDeleted (x : Fin 11 → Bool) : Bool :=
      (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
      (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) ||
      (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)

    have size_mono {n s t} {f : BFn n} (h : HasCircuitSize n f s) (hst : s ≤ t) :
        HasCircuitSize n f t := by
      obtain ⟨C, legal, small, eq⟩ := h
      exact ⟨C, legal, small.trans hst, eq⟩

    have pin {n s} {f : BFn (n+1)} (i : Fin (n+1)) (b : Bool)
        (nc : nonconstant (fix f i b)) (small : HasCircuitSize (n+1) f s) :
        HasCircuitSize (n+1) (fix f i b) s := by
      by_cases hd : depends f i
      · obtain ⟨s', h, hs⟩ := q70 n f i b s hd nc small
        exact size_mono hs (by omega)
      · have eq : fix f i b = f := by
          funext x
          by_cases v : b = x i
          · simp [fix, v]
          · have inv : b = !x i := by cases b <;> cases v' : x i <;> simp_all
            by_contra h
            exact hd ⟨x, by simpa [inv] using h⟩
        rwa [eq]

    have pin_pair {n s} {f : BFn (n+1)} (i j : Fin (n+1)) (a b : Bool)
        (hd : depends f i) (nc : nonconstant (fix (fix f i a) j b))
        (small : HasCircuitSize (n+1) f s) :
        ∃ t, t + 1 ≤ s ∧ HasCircuitSize (n+1) (fix (fix f i a) j b) t := by
      obtain ⟨x,y,h⟩ := nc
      have nc1 : nonconstant (fix f i a) :=
        ⟨Function.update x j b, Function.update y j b, h⟩
      obtain ⟨t, saved, restricted⟩ := q70 n f i a s hd nc1 small
      exact ⟨t, saved, pin j b ⟨x,y,h⟩ restricted⟩

    let notRaw (x : Fin 11 → Bool) (i : Fin 10) : Bool :=
      if i = 9 then false else x i.castSucc

    have inputs_eq (x : Fin 11 → Bool) :
        Function.update (Function.update x 10 true) 9 false =
          Fin.snoc (notRaw x) (!(notRaw x 9)) := by
      funext i
      fin_cases i <;> rfl

    have inputs_eq' (x : Fin 11 → Bool) :
        Function.update (Function.update x 9 false) 10 true =
          Fin.snoc (notRaw x) (!(notRaw x 9)) := by
      funext i
      fin_cases i <;> rfl

    have edge_restrict (x : Fin 11 → Bool) : full (notRaw x) = tailDeleted x := by
      simp [full, notRaw, tailDeleted]

    let bits {n : Nat} (mask : Nat) (i : Fin n) : Bool := mask.testBit i.val

    have joint {g : BFn 11}
        (diag : ∀ x : Fin 10 → Bool, g (Fin.snoc x (!(x 9))) = full x) :
        depends g 9 ∨ depends g 10 := by
      by_cases h : g (bits 128) = false
      · left
        refine ⟨bits 128, ?_⟩
        change g (Function.update (bits 128) 9 _) ≠ g (bits 128)
        rw [show Function.update (bits (n:=11) 128) 9 (!(bits 128 (9 : Fin 11))) =
            Fin.snoc (bits (n:=10) 640) (!(bits 640 (9 : Fin 10))) by decide, diag, h]
        decide
      · right
        refine ⟨bits 128, ?_⟩
        change g (Function.update (bits 128) 10 _) ≠ g (bits 128)
        rw [show Function.update (bits (n:=11) 128) 10 (!(bits 128 (10 : Fin 11))) =
            Fin.snoc (bits (n:=10) 128) (!(bits 128 (9 : Fin 10))) by decide, diag]
        exact Ne.symm h

    have cofactor (t : Nat) (small : HasCircuitSize 11 tailDeleted t) : 16 ≤ t := by
      by_contra! h
      have restricted := yn (fun i : Fin 11 => Fin.ofNat 9 i.val) tailDeleted 15
        (size_mono small (by omega))
      exact nine restricted
    have first_not_lower
        (rest : List Nat) (gs : List Gate) (o : Nat)
        (legal : FanInTwo (⟨⟨.not, 9 :: rest⟩ :: gs, o⟩ : Circuit))
        (correct : ∀ x : Fin 10 → Bool,
          (⟨⟨.not, 9 :: rest⟩ :: gs, o⟩ : Circuit).eval (List.ofFn x) = full x) :
        18 ≤ (⟨⟨.not, 9 :: rest⟩ :: gs, o⟩ : Circuit).size := by
      let g : BFn 11 := fun w => (⟨gs,o⟩ : Circuit).eval (List.ofFn w)
      have small : HasCircuitSize 11 g gs.length := by
        exact ⟨⟨gs,o⟩, fun gate hg => legal gate (List.mem_cons_of_mem _ hg), le_rfl,
          fun _ => rfl⟩
      have diag (x : Fin 10 → Bool) : g (Fin.snoc x (!(x 9))) = full x := by
        rw [←correct x]
        change (⟨gs,o⟩ : Circuit).eval (List.ofFn (Fin.snoc x (!(x 9)))) = _
        rw [q134]
        simp [circuitEval, circuitWires, truthAnd, truthOr, truthNot]
      have eq1 : fix (fix g 9 false) 10 true = tailDeleted := by
        funext x
        exact (congrArg g (inputs_eq x)).trans ((diag (notRaw x)).trans (edge_restrict x))
      have eq2 : fix (fix g 10 true) 9 false = tailDeleted := by
        funext x
        exact (congrArg g (inputs_eq' x)).trans ((diag (notRaw x)).trans (edge_restrict x))
      have varies : nonconstant tailDeleted := ⟨bits 0, bits 3, by decide⟩
      have cost : ∃ t, t+1 ≤ gs.length ∧ HasCircuitSize 11 tailDeleted t := by
        rcases joint diag with hd | hd
        · simpa only [eq1] using pin_pair 9 10 false true hd (eq1.symm ▸ varies) small
        · simpa only [eq2] using pin_pair 10 9 true false hd (eq2.symm ▸ varies) small
      obtain ⟨t, saved, smaller⟩ := cost
      have lower := cofactor t smaller
      change 18 ≤ gs.length+1
      omega
    let two (u w i : Fin 10) : Bool := decide (i = u ∨ i = w)

    have distinct_neighbors : ∀ (u v : Fin 10), u ≠ v →
        ∃ w : Fin 10, w ≠ u ∧ w ≠ v ∧ full (two u w) ≠ full (two v w) := by decide +kernel

    let Agree (u v : Nat) (a b : List Bool) : Prop :=
      a.length = b.length ∧ ∀ i, i ≠ u → i ≠ v → a.getD i false = b.getD i false

    have append_same {u v a b c} (ok : Agree u v a b) :
        Agree u v (a ++ [c]) (b ++ [c]) := by
      obtain ⟨len,eq⟩ := ok
      refine ⟨by simp [len], ?_⟩
      intro i hi hj
      by_cases e : i = a.length
      · rw [e, z0, len, z0]
      · rw [q8 _ _ _ _ e, q8 _ _ _ _ (by simpa [len] using e)]
        exact eq i hi hj

    have tails_agree {u v} (tail : List Gate)
        (unused : ∀ g ∈ tail, u ∉ g.inputs ∧ v ∉ g.inputs) {a b} (ok : Agree u v a b) :
        Agree u v (q3 tail a) (q3 tail b) := by
      induction tail generalizing a b with
      | nil => exact ok
      | cons g gs ih =>
        have reads : (g.inputs.map fun i => a.getD i false) = (g.inputs.map fun i => b.getD i false) := by
          apply List.map_congr_left
          intro i h
          exact ok.2 i (fun e => (unused g (.head _)).1 (e ▸ h)) (fun e => (unused g (.head _)).2 (e ▸ h))
        change Agree u v (q3 gs (a ++ [g.op.eval _])) (q3 gs (b ++ [g.op.eval _]))
        rw [reads]
        exact ih (fun z hz => unused z (.tail g hz)) (append_same ok)

    have get_input (x : Fin 10 → Bool) (i : Fin 10) :
        (List.ofFn x).getD i.val false = x i := by
      rw [List.getD_eq_getElem _ _ (by simp)]
      simp only [List.getElem_ofFn]

    have sole_reads_invariant (u v : Fin 10) (op : GateOp) (hop : op = .and ∨ op = .or)
        (tail : List Gate) (unused : ∀ g ∈ tail, u.val ∉ g.inputs ∧ v.val ∉ g.inputs)
        (x y : Fin 10 → Bool) (rest : ∀ i, i ≠ u → i ≠ v → x i = y i)
        (uv : x u = y v) (vu : x v = y u) (o : Nat) (ou : o ≠ u.val) (ov : o ≠ v.val) :
        (⟨⟨op,[u.val,v.val]⟩ :: tail, o⟩ : Circuit).eval (List.ofFn x) =
        (⟨⟨op,[u.val,v.val]⟩ :: tail, o⟩ : Circuit).eval (List.ofFn y) := by
      have raw : Agree u.val v.val (List.ofFn x) (List.ofFn y) := by
        refine ⟨by simp, ?_⟩
        intro i hi hj
        by_cases small : i < 10
        · let j : Fin 10 := ⟨i,small⟩
          rw [show i = j.val from rfl, get_input, get_input]
          exact rest j (fun e => hi (congrArg Fin.val e)) (fun e => hj (congrArg Fin.val e))
        · rw [lGD _ _ (by simp; omega), lGD _ _ (by simp; omega)]
      have gate : op.eval ([u.val,v.val].map fun i => (List.ofFn x).getD i false) =
          op.eval ([u.val,v.val].map fun i => (List.ofFn y).getD i false) := by
        simp only [List.map_cons,List.map_nil,get_input,uv,vu]
        rcases hop with rfl | rfl <;> simp [truthAnd, truthOr, truthNot, Bool.and_comm, Bool.or_comm]
      change (q3 tail ((List.ofFn x) ++ [op.eval _])).getD o false =
          (q3 tail ((List.ofFn y) ++ [op.eval _])).getD o false
      rw [gate]
      exact (tails_agree tail unused (append_same raw)).2 o ou ov

    have requires_tail_use (u v : Fin 10) (hne : u ≠ v) (op : GateOp)
        (hop : op = .and ∨ op = .or) (tail : List Gate) (o : Nat)
        (correct : ∀ x : Fin 10 → Bool,
          (⟨⟨op,[u.val,v.val]⟩ :: tail, o⟩ : Circuit).eval (List.ofFn x) = full x) :
        ∃ g ∈ tail, u.val ∈ g.inputs ∨ v.val ∈ g.inputs := by
      have out : 10 ≤ o := by
        by_contra! h
        let j : Fin 10 := ⟨o,h⟩
        let x := fun i : Fin 10 => i == j
        have hz : ∀ k : Fin 10, full (fun i => i == k) = false := by decide
        obtain ⟨t,wire,_⟩ := y1 (⟨op,[u.val,v.val]⟩ :: tail) (List.ofFn x)
        have hit := correct x
        change (q3 _ (List.ofFn x)).getD o false = full x at hit
        rw [wire, List.getD_append _ _ _ _ (by simp; omega), show o = j.val from rfl,
            get_input, hz j] at hit
        simp [x] at hit
      obtain ⟨w,wu,wv,hdiff⟩ := distinct_neighbors u v hne
      by_contra! none
      have eq := sole_reads_invariant u v op hop tail none (two u w) (two v w)
        (by intro i hi hj; simp [two,hi,hj])
        (by simp [two])
        (by simp [two,hne,hne.symm,wu.symm,wv.symm])
        o (by omega) (by omega)
      rw [correct, correct] at eq
      exact hdiff eq
    let read (x : Fin 10 → Bool) (a : Nat) : Bool := (List.ofFn x).getD a false

    let val (g : Gate) (x : Fin 10 → Bool) : Bool :=
      g.op.eval (g.inputs.map (read x))

    let Simple (g : Gate) : Prop :=
      (∃ b : Bool, ∀ x, val g x = b) ∨ ∃ i : Fin 10, ∀ x, val g x = x i

    let Neg (g : Gate) : Prop :=
      ∃ (i : Fin 10) (extra : List Nat), g = ⟨.not, i.val :: extra⟩

    let Pair (g : Gate) : Prop :=
      ∃ (u v : Fin 10), u ≠ v ∧ (g.op = .and ∨ g.op = .or) ∧ g.inputs = [u.val, v.val]

    have from_input (x : Fin 10 → Bool) {a : Nat} (h : a < 10) :
        read x a = x ⟨a,h⟩ := by
      unfold read
      rw [List.getD_eq_getElem _ _ (by simpa)]
      exact List.getElem_ofFn _

    have from_past (x : Fin 10 → Bool) {a : Nat} (h : ¬ a < 10) :
        read x a = false :=
      List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt h)

    have classify_binary (op : GateOp) (ws : List Nat) (hop : op = .and ∨ op = .or)
        (len : ws.length ≤ 2) : Simple ⟨op,ws⟩ ∨ Pair ⟨op,ws⟩ := by
      cases ws with
      | nil =>
        left; left
        rcases hop with rfl|rfl
        · exact ⟨true, fun _ => rfl⟩
        · exact ⟨false, fun _ => rfl⟩
      | cons a rest =>
        cases rest with
        | nil =>
          left
          by_cases ha : a < 10
          · right; refine ⟨⟨a,ha⟩, ?_⟩; intro x
            rcases hop with rfl|rfl <;> simp [val, truthAnd, truthOr, truthNot, from_input x ha]
          · left; refine ⟨false,?_⟩; intro x
            rcases hop with rfl|rfl <;> simp [val, truthAnd, truthOr, truthNot, from_past x ha]
        | cons b tail =>
          have ht : tail = [] := by simpa using len
          subst tail
          by_cases ha : a < 10
          · by_cases hb : b < 10
            · by_cases eq : a = b
              · subst b; left; right; refine ⟨⟨a,ha⟩,?_⟩; intro x
                rcases hop with rfl|rfl <;> simp [val, truthAnd, truthOr, truthNot, from_input x ha]
              · right; exact ⟨⟨a,ha⟩, ⟨b,hb⟩, fun e => eq (congrArg Fin.val e), hop, rfl⟩
            · left; rcases hop with rfl|rfl
              · left; exact ⟨false, fun x => by simp [val, truthAnd, truthOr, truthNot, from_past x hb]⟩
              · right; exact ⟨⟨a,ha⟩, fun x => by simp [val, truthAnd, truthOr, truthNot, from_input x ha, from_past x hb]⟩
          · by_cases hb : b < 10
            · left; rcases hop with rfl|rfl
              · left; exact ⟨false, fun x => by simp [val, truthAnd, truthOr, truthNot, from_past x ha]⟩
              · right; exact ⟨⟨b,hb⟩, fun x => by simp [val, truthAnd, truthOr, truthNot, from_past x ha, from_input x hb]⟩
            · left; left; refine ⟨false, ?_⟩; intro x
              rcases hop with rfl|rfl <;> simp [val, truthAnd, truthOr, truthNot, from_past x ha, from_past x hb]

    have classify (g : Gate) (legal : g.op ∈ ({.and,.or,.not} : Set GateOp) ∧
        g.inputs.length ≤ 2) : Simple g ∨ Neg g ∨ Pair g := by
      rcases g with ⟨op,ws⟩
      obtain ⟨hop,len⟩ := legal
      change op ∈ ({.and,.or,.not} : Set GateOp) at hop
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      rcases hop with h|h|rfl
      · exact (classify_binary op ws (Or.inl h) len).imp_right Or.inr
      · exact (classify_binary op ws (Or.inr h) len).imp_right Or.inr
      · cases ws with
        | nil => exact Or.inl (Or.inl ⟨true, fun _ => rfl⟩)
        | cons a rest =>
          by_cases ha : a < 10
          · exact Or.inr (Or.inl ⟨⟨a,ha⟩,rest,rfl⟩)
          · exact Or.inl (Or.inl ⟨true, fun x => by simp [val, truthAnd, truthOr, truthNot, from_past x ha]⟩)

    let globBits {n : Nat} (mask : Nat) (i : Fin n) : Bool := mask.testBit i.val

    have widen {n s t} {f : BFn n} (h : HasCircuitSize n f s) (hst : s ≤ t) :
        HasCircuitSize n f t := by
      obtain ⟨C, legal, small, eq⟩ := h
      exact ⟨C,legal,small.trans hst,eq⟩

    have lower17 (smaller : ¬ HasCircuitSize 9 deleted 15) (s : Nat) (hc : HasCircuitSize 10 full s) :
        17 ≤ s := by
      have hd : depends full 9 := ⟨globBits 128, by decide⟩
      have nc : nonconstant (fix full 9 false) := ⟨globBits 0, globBits 3, by decide⟩
      obtain ⟨t, saved, rest⟩ := q70 9 full 9 false s hd nc hc
      have r := yn (fun i : Fin 10 => Fin.ofNat 9 i.val) (fix full 9 false) t rest
      have eq : (fun x : Fin 9 → Bool => fix full 9 false (x ∘ fun i : Fin 10 => Fin.ofNat 9 i.val)) = deleted := by
        funext x
        simp [fix, full, deleted, Function.update]
        rfl
      rw [eq] at r
      by_contra! h
      exact smaller (widen r (by omega))

    have pinGlobal {n s} {f : BFn (n+1)} (i : Fin (n+1)) (b : Bool)
        (nc : nonconstant (fix f i b)) (small : HasCircuitSize (n+1) f s) :
        HasCircuitSize (n+1) (fix f i b) s := by
      by_cases hd : depends f i
      · obtain ⟨t, saved, h⟩ := q70 n f i b s hd nc small
        exact widen h (by omega)
      · have eq : fix f i b = f := by
          funext x
          by_cases hx : b = x i
          · simp [fix, hx]
          · have hb : b = !x i := by cases b <;> cases he : x i <;> simp_all
            by_contra h
            exact hd ⟨x, by simpa [hb] using h⟩
        rwa [eq]

    let tailFun (gs : List Gate) (o : Nat) (w : Fin 11 → Bool) : Bool :=
      (⟨gs,o⟩ : Circuit).eval (List.ofFn w)

    have simple_bound (smaller : ¬ HasCircuitSize 9 deleted 15) (first : Gate)
        (gs : List Gate) (o : Nat) (hs : Simple first)
        (legal : FanInTwo (⟨first :: gs,o⟩ : Circuit))
        (correct : ∀ x : Fin 10 → Bool, (⟨first :: gs,o⟩ : Circuit).eval (List.ofFn x) = full x) :
        18 ≤ gs.length+1 := by
      have small : HasCircuitSize 11 (tailFun gs o) gs.length :=
        ⟨⟨gs,o⟩, fun gate hg => legal gate (List.mem_cons_of_mem _ hg), le_rfl, fun _ => rfl⟩
      have diag (x : Fin 10 → Bool) :
          tailFun gs o (Fin.snoc x (val first x)) = full x := by
        rw [←correct x]; unfold tailFun; rw [q134]; rfl
      have h : HasCircuitSize 10 full gs.length := by
        rcases hs with ⟨b,hb⟩ | ⟨i,hi⟩
        · have eq (x : Fin 10 → Bool) :
              Function.update (x ∘ Fin.snoc id (0 : Fin 10)) 10 b = Fin.snoc x b := by
            funext j
            fin_cases j <;> rfl
          have rep (x : Fin 10 → Bool) :
              fix (tailFun gs o) 10 b (x ∘ Fin.snoc id (0 : Fin 10)) = full x := by
            unfold fix
            rw [eq, ←hb x, diag]
          have nc : nonconstant (fix (tailFun gs o) 10 b) := by
            refine ⟨globBits (n:=10) 0 ∘ Fin.snoc id 0, globBits (n:=10) 3 ∘ Fin.snoc id 0, ?_⟩
            rw [rep,rep]; decide
          have r := yn (Fin.snoc id (0 : Fin 10)) _ gs.length (pinGlobal 10 b nc small)
          rwa [funext rep] at r
        · have r := yn (Fin.snoc id i) _ gs.length small
          have rep (x : Fin 10 → Bool) : tailFun gs o (x ∘ Fin.snoc id i) = full x := by
            have eq : x ∘ Fin.snoc id i = Fin.snoc x (x i) := by
              funext j
              fin_cases j <;> rfl
            rw [eq, ←hi x, diag]
          rwa [funext rep] at r
      have bound := lower17 smaller _ h
      omega

    have assemble
        (smaller : ¬ HasCircuitSize 9 deleted 15)
        (not9 : ∀ (extra : List Nat) (gs : List Gate) (o : Nat),
          FanInTwo (⟨⟨.not, 9 :: extra⟩ :: gs,o⟩ : Circuit) →
          (∀ x : Fin 10 → Bool, (⟨⟨.not, 9 :: extra⟩ :: gs,o⟩ : Circuit).eval (List.ofFn x) = full x) →
          18 ≤ gs.length+1)
        (oneReader : ∀ (v : Fin 10) (C : Circuit), FanInTwo C →
          (∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = full x) → C.size ≤ 17 →
          (C.gates.map vg).countP (fun g => g.inputs.contains v.val) ≤ 1)
        (twin : ∀ (u v : Fin 10), u ≠ v → ∀ (op : GateOp), (op = .and ∨ op = .or) →
          ∀ (gs : List Gate) (o : Nat),
          (∀ x : Fin 10 → Bool,
            (⟨⟨op,[u.val,v.val]⟩ :: gs,o⟩ : Circuit).eval (List.ofFn x) = full x) →
          ∃ g ∈ gs, u.val ∈ g.inputs ∨ v.val ∈ g.inputs) : ¬ HasCircuitSize 10 full 17 := by
      rintro ⟨⟨gates,o⟩, legal, small, correct⟩
      cases gates with
      | nil =>
        have h := lower17 smaller 0 ⟨⟨[],o⟩,legal,le_rfl,correct⟩
        omega
      | cons first gs =>
        have shape := classify first (legal first (by simp))
        change gs.length+1 ≤ 17 at small
        rcases shape with simple | ⟨v,extra,rfl⟩ | ⟨u,v,ne,hop,heq⟩
        · have h := simple_bound smaller first gs o simple legal correct
          omega
        · obtain ⟨extra',gs',o',legal',correct',len,_⟩ :=
            canonical v extra gs o legal correct
          have h := not9 extra' gs' o' legal' correct'
          omega
        · rcases first with ⟨op,ws⟩
          change ws = [u.val,v.val] at heq
          subst ws
          change op = .and ∨ op = .or at hop
          have normalized (x : Fin 10 → Bool) :
              (⟨⟨op,[u.val,v.val]⟩ :: gs.map vg,o⟩ : Circuit).eval (List.ofFn x) = full x := by
            rw [←correct x]
            change (q3 (gs.map vg) _).getD o false = (q3 gs _).getD o false
            rw [jd]
          obtain ⟨g, hg, uses⟩ := twin u v ne op hop (gs.map vg) o normalized
          have count (i : Fin 10) (hit : i.val ∈ g.inputs) (initial : i.val ∈ [u.val,v.val]) :
              False := by
            have nonempty : 0 < (gs.map vg).countP (fun h => h.inputs.contains i.val) :=
              List.countP_pos_iff.mpr ⟨g,hg,by simpa using hit⟩
            have bound := oneReader i ⟨⟨op,[u.val,v.val]⟩ :: gs,o⟩ legal correct small
            have firstHit : (vg ⟨op,[u.val,v.val]⟩).inputs.contains i.val = true := by
              rcases hop with rfl|rfl <;> simpa [vg] using initial
            simp only [List.map_cons, List.countP_cons, firstHit, ↓reduceIte] at bound
            omega
          rcases uses with left|right
          · exact count u left (by simp)
          · exact count v right (by simp)
    have oneReader (v : Fin 10) (C : Circuit) (legal : FanInTwo C)
        (correct : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = full x)
        (small : C.size ≤ 17) : (C.gates.map vg).countP (fun g => g.inputs.contains v.val) ≤ 1 := by
      obtain ⟨s, saved, restricted⟩ := direct 10 C legal ((correct _).trans rfl) v v
      have eq : (fun x : Fin 10 → Bool => C.eval (List.ofFn (Function.update (Function.update x v false) v false))) = (fun x => full (Function.update x v false)) := by
        funext x; rw [correct, Function.update_idem]
      rw [eq] at restricted
      have LB : 16 ≤ s := by
        by_contra! h
        exact (lowerPinned v nine (@yn)) (widen restricted (by omega))
      let predicate (g : Gate) := ((List.take (bif g.op.eval [false] then 1 else 2) g.inputs).any fun w => w == v.val || w == v.val)
      change s + List.countP predicate C.gates ≤ C.size at saved
      have counts : (C.gates.map vg).countP (fun g => g.inputs.contains v.val) = C.gates.countP predicate := by
        rw [List.countP_map]
        apply List.countP_congr
        intro g hg
        obtain ⟨o,ins⟩ := g
        obtain ⟨hop,hlen⟩ := legal _ hg
        change o ∈ ({.and,.or,.not} : Set GateOp) at hop
        change ins.length ≤ 2 at hlen
        rcases hop with hop|hop|hop
        · change o = .and at hop; subst o
          simp [vg,predicate,Function.comp_def,truthAnd, truthOr, truthNot,List.take_of_length_le hlen,List.contains_eq_any_beq]
        · change o = .or at hop; subst o
          simp [vg,predicate,Function.comp_def,truthAnd, truthOr, truthNot,List.take_of_length_le hlen,List.contains_eq_any_beq]
        · change o = .not at hop; subst o
          simp [vg,predicate,Function.comp_def,truthAnd, truthOr, truthNot,List.contains_eq_any_beq]
      omega
    exact assemble nine first_not_lower oneReader requires_tail_use
  have erase : let operands := fun g : Gate => GateOp.casesOn (motive := fun _ => List ℕ) g.op g.inputs g.inputs (g.inputs.take 1) (fun _ => g.inputs) g.inputs
          ∀ (n : ℕ) (C : Circuit), FanInTwo C → C.output ≠ n → C.output ≠ n + 1 →
            (∀ g ∈ C.gates, n ∉ operands g ∧ n+1 ∉ operands g) →
            ∃ D : Circuit, FanInTwo D ∧ D.size ≤ C.size ∧
              ∀ (x : Fin n → Bool) (p q : Bool),
                D.eval (List.ofFn x) = C.eval (List.ofFn x ++ [p,q]) := by
    intro ops n C legal out1 out2 skip
    let down (i : Nat) : Nat := if i < n then i else i - 2
    let project (g : Gate) : Gate := ⟨g.op, (ops g).map down⟩
    let step (w : List Bool) (g : Gate) : List Bool := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have op_eval (g : Gate) (v : Nat → Bool) :
        g.op.eval (g.inputs.map v) = g.op.eval ((ops g).map v) := by
      obtain ⟨o,l⟩ := g
      cases o <;> first | rfl | cases l <;> rfl

    have lookup (u t : List Bool) (a b : Bool) (hu : u.length = n)
        {i : Nat} (ha : i ≠ n) (hb : i ≠ n+1) :
        ((u ++ t).getD (down i) false) = ((u ++ [a,b]) ++ t).getD i false := by
      change (u ++ t).getD (if i < n then i else i - 2) false = _
      by_cases hi : i < n
      · rw [if_pos hi, List.getD_append _ _ _ _ (by omega),
          List.getD_append _ _ _ _ (by simp [hu]; omega), List.getD_append _ _ _ _ (by omega)]
      · have hl : (u ++ [a,b]).length = n+2 := by simp [hu]
        rw [if_neg hi, List.getD_append_right _ _ _ _ (by omega),
          List.getD_append_right _ _ _ _ (by omega), hu, hl]
        congr 1 <;> omega

    have run (gs : List Gate) (u : List Bool) (a b : Bool)
        (hu : u.length = n)
        (skip : ∀ g ∈ gs, ∀ i ∈ ops g, i ≠ n ∧ i ≠ n+1) :
        ∀ t : List Bool, ∃ t' : List Bool,
          (gs.map project).foldl step (u ++ t) = u ++ t' ∧
          gs.foldl step ((u ++ [a,b]) ++ t) = (u ++ [a,b]) ++ t' := by
      induction gs with
      | nil => intro t; exact ⟨t,rfl,rfl⟩
      | cons g gs ih =>
        intro t
        let c := g.op.eval (g.inputs.map fun i => (((u ++ [a,b]) ++ t).getD i false))
        have eq : g.op.eval ((ops g).map fun i => (u ++ t).getD (down i) false) = c := by
          unfold c
          rw [op_eval g (fun i => ((u ++ [a,b]) ++ t).getD i false)]
          congr 1
          exact List.map_congr_left (fun i hi =>
            lookup u t a b hu (skip g (by simp) i hi).1 (skip g (by simp) i hi).2)
        have l : step (u ++ t) (project g) = u ++ (t ++ [c]) := by
          simpa [step,project,List.map_map,Function.comp_def,List.append_assoc] using
            congrArg (fun z => u ++ (t ++ [z])) eq
        have r : step ((u ++ [a,b]) ++ t) g = (u ++ [a,b]) ++ (t ++ [c]) := by
          simp [step,c,List.append_assoc]
        simp only [List.map_cons,List.foldl_cons,l,r]
        exact ih (fun h hh => skip h (by simp [hh])) (t ++ [c])
    refine ⟨⟨C.gates.map project, down C.output⟩, ?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨orig,ho,rfl⟩ := List.mem_map.mp hg
      refine ⟨(legal orig ho).1, ?_⟩
      have h := (legal orig ho).2
      change (List.map down (ops orig)).length ≤ 2
      rw [List.length_map]
      rcases orig with ⟨o,ins⟩
      cases o <;> simp_all [ops]
    · change (C.gates.map project).length ≤ C.gates.length
      simp
    · intro x a b
      have noPins : ∀ g ∈ C.gates, ∀ i ∈ ops g, i ≠ n ∧ i ≠ n+1 := by
        intro g hg i hi
        obtain ⟨p,q⟩ := skip g hg
        exact ⟨fun h => p (h ▸ hi), fun h => q (h ▸ hi)⟩
      obtain ⟨t,l,r⟩ := run C.gates (List.ofFn x) a b (by simp) noPins []
      simp only [List.append_nil] at l r
      change ((C.gates.map project).foldl step _).getD (down C.output) false = (C.gates.foldl step _).getD C.output false
      rw [l,r]
      exact lookup _ _ _ _ (by simp) out1 out2
  have cofactor : let operands := fun g : Gate => GateOp.casesOn (motive := fun _ => List ℕ) g.op g.inputs g.inputs (g.inputs.take 1) (fun _ => g.inputs) g.inputs
          ∀ (C : Circuit) (v : Fin 10) (g h : Gate), FanInTwo C → (v = 0 ∨ v = 2) →
            g ∈ C.gates → h ∈ C.gates → g ≠ h → v.val ∈ operands g →
            (10 ∈ operands h ∨ 11 ∈ operands h) →
            (∀ x : Fin 10 → Bool, x v = false → C.eval (List.ofFn x ++ [x 0 && x 2, !(x 0 && x 2)]) = (fun x : Fin 10 → Bool =>
      (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
      (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) ||
      (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) x) → 18 ≤ C.size := by
    have smaller := nine
    have lLA {α:Type} {l1 l2:List α}:(l1++l2).length=l1.length+l2.length:=List.length_append
    have nAA (a b d:Nat):a+b+d=a+(b+d):=Nat.add_assoc a b d
    have lMMp {α β γ:Type} {g : β->γ} {f : α->β} {l:List α}:(l.map f).map g=l.map (g ∘ f):=List.map_map
    have lGD {α:Type} (l:List α) (d : α) {i:Nat} (h:l.length<=i):l.getD i d=d:=List.getD_eq_default l d h
    let q3 (gs:List Gate) (w:List Bool):List Bool :=
     gs.foldl (fun w g => w++[g.op.eval (g.inputs.map fun i => w.getD i false)]) w
    have zd (gs gs':List Gate) (w:List Bool) :
       q3 (gs++gs') w=q3 gs' (q3 gs w):=by
     simp [q3,List.foldl_append]
    have y1 (gs:List Gate):∀ w:List Bool,
       ∃ t:List Bool,q3 gs w=w++t/\t.length=gs.length:=by
     induction gs with
     | nil => intro w;exact ⟨[],by simp [q3],rfl⟩
     | cons g gs ih =>
       intro w
       obtain ⟨t,ht,hl⟩:=ih (w++[g.op.eval (g.inputs.map fun i => w.getD i false)])
       refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false)::t,?_,by simp [hl]⟩
       have:q3 (g::gs) w
           = q3 gs (w++[g.op.eval (g.inputs.map fun i => w.getD i false)]):=rfl
       rw [this,ht];simp
    have qu (gs:List Gate) (w:List Bool) :
       (q3 gs w).length=w.length+gs.length:=by
     obtain ⟨t,ht,hl⟩:=y1 gs w
     rw [ht];simp [hl]
    let Ok (g:Gate):Prop :=
     g.op ∈ ({GateOp.and,GateOp.or,GateOp.not}:Set GateOp)/\g.inputs.length<=2
    have q8 {α:Type} (L:List α) (S d : α) (j : ℕ) (h:j≠L.length) :
       (L++[S]).getD j d=L.getD j d:=by
     by_cases hj:j < L.length
     . exact List.getD_append _ _ _ _ hj
     . rw [lGD _ _ (by simp;omega),lGD _ _ (by omega)]
    have z0 {α:Type} (L:List α) (S d : α):(L++[S]).getD L.length d=S:=by
     simp
    have truthAnd (xs : List Bool) : GateOp.and.eval xs = xs.all id := rfl
    have truthOr (xs : List Bool) : GateOp.or.eval xs = xs.any id := rfl
    have truthNot (xs : List Bool) : GateOp.not.eval xs = !(xs.headD false) := rfl
    let vg (g : Gate) : Gate :=
      GateOp.casesOn (motive := fun _ => Gate) g.op g g ⟨.not,g.inputs.take 1⟩ (fun _ => g) g
    have q107 (g:Gate) (F : ℕ->Bool) :
       (vg g).op.eval ((vg g).inputs.map F)=g.op.eval (g.inputs.map F):=by
     obtain ⟨op,inputs⟩:=g
     cases op <;> simp only [vg]
     cases inputs <;> simp [truthNot]
    let NOk (g:Gate):Prop:=Ok g/\(g.op=GateOp.not->g.inputs.length<=1)
    have q45 (g:Gate) (h:Ok g):NOk (vg g):=by
     obtain ⟨op,inputs⟩:=g
     obtain ⟨hop,hlen⟩:=h
     rcases hop with h | h | h
     . have:op=GateOp.and:=h
       subst this;exact ⟨⟨Or.inl rfl,hlen⟩,by simp [vg]⟩
     . have:op=GateOp.or:=h
       subst this;exact ⟨⟨Or.inr (Or.inl rfl),hlen⟩,by simp [vg]⟩
     . have:op=GateOp.not:=h
       subst this
       refine ⟨⟨Or.inr (Or.inr rfl),?_⟩,fun _ => ?_⟩ <;> simp [vg]
    have jd (gs:List Gate):∀ w:List Bool,
       q3 (gs.map vg) w=q3 gs w:=by
     induction gs with
     | nil => intro w;rfl
     | cons g gs ih =>
       intro w
       have s1:q3 ((g::gs).map vg) w=q3 (gs.map vg)
           (w++[(vg g).op.eval ((vg g).inputs.map fun i => w.getD i false)]):=rfl
       have s2:q3 (g::gs) w
           = q3 gs (w++[g.op.eval (g.inputs.map fun i => w.getD i false)]):=rfl
       rw [s1,s2,q107,ih]
    let Stat:=Sum Bool ℕ
    let ze (w : List Bool) (s : Stat) : Bool :=
      Sum.casesOn (motive := fun _ => Bool) s (fun b => b) (fun j => w.getD j false)
    let qn (m : ℕ) (s : Stat) : Prop :=
      Sum.casesOn (motive := fun _ => Prop) s (fun _ => True) (fun j => j < m)
    let wr (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
      List.casesOn (motive := fun _ => Option Gate × Stat) ins (none,.inl true) fun a _ =>
        Sum.casesOn (motive := fun _ => Option Gate × Stat) a
          (fun c => (none,.inl (!c))) (fun j => (some ⟨.not,[j]⟩,.inr m))
    let binary (empty : Bool) (pair : Stat → Stat → Option Gate × Stat)
        (ins : List Stat) : Option Gate × Stat :=
      List.casesOn (motive := fun _ => Option Gate × Stat) ins (none,.inl empty) fun a tail =>
        List.casesOn (motive := fun _ => Option Gate × Stat) tail (none,a) fun b rest =>
          List.casesOn (motive := fun _ => Option Gate × Stat) rest (pair a b) (fun _ _ => (none,.inl false))
    let ko (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
      binary true (fun a b => Sum.casesOn (motive := fun _ => Option Gate × Stat) a
        (fun c => Sum.casesOn (motive := fun _ => Option Gate × Stat) b
          (fun d => (none,.inl (c && d))) (fun j => (none,bif c then Sum.inr j else Sum.inl false)))
        (fun j => Sum.casesOn (motive := fun _ => Option Gate × Stat) b
          (fun c => (none,bif c then Sum.inr j else Sum.inl false)) (fun k => (some ⟨.and,[j,k]⟩,.inr m)))) ins
    let ji (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
      binary false (fun a b => Sum.casesOn (motive := fun _ => Option Gate × Stat) a
        (fun c => Sum.casesOn (motive := fun _ => Option Gate × Stat) b
          (fun d => (none,.inl (c || d))) (fun j => (none,bif c then Sum.inl true else Sum.inr j)))
        (fun j => Sum.casesOn (motive := fun _ => Option Gate × Stat) b
          (fun c => (none,bif c then Sum.inl true else Sum.inr j)) (fun k => (some ⟨.or,[j,k]⟩,.inr m)))) ins
    let qg (op:GateOp) (m : ℕ) (ins:List Stat):Option Gate × Stat :=
     GateOp.casesOn (motive := fun _ => Option Gate × Stat) op
       (ko m ins) (ji m ins) (wr m ins) (fun _ => (none,Sum.inl false)) (none,Sum.inl false)
    have q151 (op:GateOp) (m : ℕ) (ins:List Stat) :
       ∀ g ∈ (qg op m ins).1,Ok g:=by
     clear * - op m ins qg Ok wr ko ji
     intro g hg
     cases op <;> simp only [qg] at hg
     . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
         simp_all [ko,binary, Ok]
       subst g
       simp
     . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
         simp_all [ji,binary, Ok]
       subst g
       simp
     . rcases ins with _ | ⟨a,l⟩ <;> (try cases a) <;>
         simp_all [wr, Ok]
       subst g
       simp
     . simp at hg
     . simp at hg
    have jh (op:GateOp) (m : ℕ) (ins:List Stat)
       (hop:op=GateOp.and\/op=GateOp.or\/op=GateOp.not) (hlen:ins.length<=2)
       (hnot:op=GateOp.not->ins.length<=1) (hc:∃ c,Sum.inl c ∈ ins) :
       (qg op m ins).1=none:=by
     clear * - op m ins hop hlen hnot hc qg wr ko ji
     obtain ⟨c,hc⟩:=hc
     rcases hop with rfl | rfl | rfl
     . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨d,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
         simp_all [qg,ko,binary]
     . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨d,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
         simp_all [qg,ji,binary]
     . have:=hnot rfl
       rcases ins with _ | ⟨a,_ | ⟨b,l⟩⟩ <;> (try cases a) <;> simp_all [qg,wr]
    have kn (op:GateOp) (hop:op=GateOp.and\/op=GateOp.or\/op=GateOp.not)
       (w:List Bool) (ins:List Stat) (hlen:ins.length<=2)
       (hv:∀ s ∈ ins,qn w.length s) :
       qn (w.length+(qg op w.length ins).1.toList.length) (qg op w.length ins).2 /\
       ze (q3 (qg op w.length ins).1.toList w) (qg op w.length ins).2
         = op.eval (ins.map (ze w)):=by
     clear * - op hop w ins hlen hv qg wr ko ji qn ze q3 truthAnd truthOr truthNot
     rcases hop with rfl | rfl | rfl
     . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨d,l⟩⟩⟩
       . simp [qg,ko,binary,qn,ze,truthAnd]
       . cases a <;> simp_all [qg,ko,binary,qn,ze,q3]
       . cases a <;> cases b <;> (rename_i c e; cases c) <;> cases e <;>
           simp_all [qg,ko,binary,qn,ze,q3]
       . simp at hlen
     . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨d,l⟩⟩⟩
       . simp [qg,ji,binary,qn,ze,truthOr]
       . cases a <;> simp_all [qg,ji,binary,qn,ze,q3]
       . cases a <;> cases b <;> (rename_i c e; cases c) <;> cases e <;>
           simp_all [qg,ji,binary,qn,ze,q3]
       . simp at hlen
     . rcases ins with _ | ⟨a,l⟩
       . simp [qg,wr,qn,ze,truthNot]
       . cases a <;> simp_all [qg,wr,qn,ze,q3]
    let qa (n : ℕ) (acc:List Stat × List Gate) (g:Gate):List Stat × List Gate :=
     (acc.1++[(qg g.op (n+acc.2.length)
         (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
       acc.2++(qg g.op (n+acc.2.length)
         (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)
    let elim (n : ℕ) (gs:List Gate) (acc:List Stat × List Gate):List Stat × List Gate :=
     gs.foldl (qa n) acc
    have k4 (n : ℕ) (g:Gate) (gs:List Gate) (acc:List Stat × List Gate) :
       elim n (g::gs) acc=elim n gs (qa n acc g):=rfl
    have y2 {α:Type} (o:Option α):o.toList.length<=1:=by
     cases o <;> simp
    have q156 (n : ℕ) (gs:List Gate):∀ acc:List Stat × List Gate,
       (∀ g ∈ acc.2,Ok g)->∀ g ∈ (elim n gs acc).2,Ok g:=by
     induction gs with
     | nil => intro acc h;exact h
     | cons g gs ih =>
       intro acc h
       apply ih (qa n acc g)
       intro g' hg'
       rcases List.mem_append.1 hg' with h1 | h1
       . exact h g' h1
       . exact q151 _ _ _ g' (by simpa using h1)
    have km {m m' : ℕ} (h:m<=m'):∀ s:Stat,qn m s->qn m' s := by
      intro s hs
      cases s with
      | inl c => exact trivial
      | inr j => exact lt_of_lt_of_le hs h
    have jg (w t : List Bool) (s : Stat) (hs : qn w.length s) :
        ze (w ++ t) s = ze w s := by
      cases s with
      | inl c => rfl
      | inr j => exact List.getD_append _ _ _ _ hs
    let Inv (n : ℕ) (y:List Bool) (w:List Bool) (acc:List Stat × List Gate):Prop :=
     acc.1.length=w.length/\∀ i : ℕ,
       qn (n+acc.2.length) (acc.1.getD i (Sum.inl false)) /\
       ze (q3 acc.2 y) (acc.1.getD i (Sum.inl false))=w.getD i false
    have j7 (n : ℕ) (y:List Bool) (hy:y.length=n) (gs:List Gate) :
       ∀ (w:List Bool) (acc:List Stat × List Gate),(∀ g ∈ gs,Ok g)->Inv n y w acc ->
         Inv n y (q3 gs w) (elim n gs acc):=by
     induction gs with
     | nil => intro w acc _ h;exact h
     | cons g gs ih =>
       intro w acc hok h
       apply ih (w++[g.op.eval (g.inputs.map fun i => w.getD i false)]) (qa n acc g)
         (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
       obtain ⟨hl,hi⟩:=h
       set w':=q3 acc.2 y with hw'
       have lw':w'.length=n+acc.2.length:=by rw [hw',qu,hy]
       set ins:=g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
       have hgok:=hok g List.mem_cons_self
       have hs:=kn g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
         (by
           intro s hs
           obtain ⟨a,_,rfl⟩:=List.mem_map.1 hs
           rw [lw'];exact (hi a).1)
       rw [lw'] at hs
       set r:=qg g.op (n+acc.2.length) ins with hr
       have hvals:ins.map (ze w')=g.inputs.map fun i => w.getD i false:=by
         rw [hins,lMMp]
         apply List.map_congr_left
         intro a _
         exact (hi a).2
       have hnew:q3 (acc.2++r.1.toList) y=q3 r.1.toList w':=by
         rw [zd]
       obtain ⟨t,ht,_⟩:=y1 r.1.toList w'
       refine ⟨by simp [qa,hl],?_⟩
       intro i
       show qn (n+(acc.2++r.1.toList).length) ((acc.1++[r.2]).getD i (Sum.inl false)) /\
         ze (q3 (acc.2++r.1.toList) y) ((acc.1++[r.2]).getD i (Sum.inl false))=_
       rw [hnew,lLA,← nAA]
       by_cases hil:i=acc.1.length
       . subst hil
         rw [z0,hl,z0]
         exact ⟨hs.1,by rw [hs.2,hvals]⟩
       . rw [q8 _ _ _ _ hil,q8 _ _ _ _ (by omega)]
         refine ⟨km (by omega) _ (hi i).1,?_⟩
         rw [ht,jg _ _ _ (by rw [lw'];exact (hi i).1)]
         exact (hi i).2
    have vs (n : ℕ) (acc:List Stat × List Gate) (g:Gate) (hg:NOk g) (k : ℕ)
       (hk:k ∈ g.inputs) (c:Bool) (hc:acc.1.getD k (Sum.inl false)=Sum.inl c) :
       (qa n acc g).2.length=acc.2.length:=by
     have hnone:(qg g.op (n+acc.2.length)
         (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1=none:=by
       apply jh
       . exact hg.1.1
       . simpa using hg.1.2
       . intro h;simpa using hg.2 h
       . exact ⟨c,List.mem_map.2 ⟨k,hk,hc⟩⟩
     show (acc.2++(qg g.op (n+acc.2.length)
       (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length=_
     rw [hnone];simp
    let full (x : Fin 10 → Bool) : Bool :=
      (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
    let deleted (x : Fin 9 → Bool) : Bool :=
      (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
    let move (v i : Fin 10) : Fin 10 :=
      if v = 0 then (![9,6,8,3,4,7,1,5,2,0] : Fin 10 → Fin 10) i
      else (![0,4,9,6,1,5,3,7,8,2] : Fin 10 → Fin 10) i
    let pinNine (x : Fin 9 → Bool) (i : Fin 10) : Bool :=
      if h : i.val < 9 then x ⟨i.val, h⟩ else false
    have droppedVertex (v : Fin 10) (hv : v = 0 ∨ v = 2) (y : Fin 9 → Bool) :
        full (fun j => pinNine y (move v j)) = deleted y := by
      rcases hv with rfl | rfl
      · change ((false && y 6) || (y 6 && y 8) || (y 8 && y 3) || (y 3 && y 4) || (y 4 && false) || (false && y 7) || (y 6 && y 1) || (y 8 && y 5) || (y 3 && y 2) || (y 4 && y 0) || (y 7 && y 5) || (y 5 && y 0) || (y 0 && y 1) || (y 1 && y 2) || (y 2 && y 7)) = ((y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 3 && y 4) || (y 4 && y 0) || (y 0 && y 5) || (y 1 && y 6) || (y 2 && y 7) || (y 3 && y 8) || (y 5 && y 7) || (y 6 && y 8) || (y 8 && y 5))
        simp only [Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or]
        ac_rfl
      · change ((y 0 && y 4) || (y 4 && false) || (false && y 6) || (y 6 && y 1) || (y 1 && y 0) || (y 0 && y 5) || (y 4 && y 3) || (false && y 7) || (y 6 && y 8) || (y 1 && y 2) || (y 5 && y 7) || (y 7 && y 2) || (y 2 && y 3) || (y 3 && y 8) || (y 8 && y 5)) = ((y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 3 && y 4) || (y 4 && y 0) || (y 0 && y 5) || (y 1 && y 6) || (y 2 && y 7) || (y 3 && y 8) || (y 5 && y 7) || (y 6 && y 8) || (y 8 && y 5))
        simp only [Bool.and_false, Bool.false_and, Bool.or_false]
        ac_rfl
    have droppedAt (v : Fin 10) (hv : v = 0 ∨ v = 2) (y : Fin 9 → Bool) :
        pinNine y (move v v) = false := by rcases hv with rfl | rfl <;> rfl
    let reads (v : Nat) (g : Gate) : Bool :=
      g.inputs.contains v || g.inputs.contains 10 || g.inputs.contains 11
    let initial (v : Fin 10) : List Stat :=
      List.ofFn (fun j : Fin 10 => if (move v j).val < 9 then Sum.inr (move v j).val else Sum.inl false)
        ++ [.inl false, .inl true]
    have getDOfFn {n : Nat} {α : Type} (f : Fin n → α) (i : Nat) (d : α) (hi : i < n) :
        (List.ofFn f).getD i d = f ⟨i,hi⟩ := by simp [hi]
    have initialInv (v : Fin 10) (y : Fin 9 → Bool) :
        Inv 9 (List.ofFn y) (List.ofFn (fun j => pinNine y (move v j)) ++ [false,true]) (initial v, []) := by
      refine ⟨by simp [initial], ?_⟩
      intro i
      by_cases hi : i < 10
      · simp only [initial]
        rw [List.getD_append _ _ _ _ (by simpa using hi), List.getD_append _ _ _ _ (by simpa using hi)]
        rw [getDOfFn _ _ _ hi, getDOfFn _ _ _ hi]
        by_cases hj : (move v ⟨i,hi⟩).val < 9
        · simp only [ite_eq_left hj, pinNine, dite_eq_left hj]
          exact ⟨hj, getDOfFn y _ false hj⟩
        · simp only [ite_eq_right hj, pinNine, dite_eq_right hj]
          exact ⟨trivial, rfl⟩
      · by_cases hk : i < 12
        · have h : i = 10 ∨ i = 11 := by omega
          rcases h with rfl | rfl <;> exact ⟨trivial, rfl⟩
        · rw [lGD _ _ (by simp [initial]; omega), lGD _ _ (by simp; omega)]
          exact ⟨trivial, rfl⟩
    have counting (v : Fin 10) (gs : List Gate) (acc : List Stat × List Gate)
        (ok : ∀ g ∈ gs, NOk g) (hlen : 11 < acc.1.length)
        (fixed : ∀ k, k = v.val ∨ k = 10 ∨ k = 11 → ∃ b, acc.1.getD k (.inl false) = .inl b) :
        (elim 9 gs acc).2.length + gs.countP (reads v.val) ≤ acc.2.length + gs.length := by
      induction gs generalizing acc with
      | nil => simp [elim]
      | cons g gs ih =>
        have hlen' : 11 < (qa 9 acc g).1.length := by simp [qa]; omega
        have fixed' (k : Nat) (hk : k = v.val ∨ k = 10 ∨ k = 11) :
            ∃ b, (qa 9 acc g).1.getD k (.inl false) = .inl b := by
          obtain ⟨b,hb⟩ := fixed k hk
          refine ⟨b, ?_⟩
          change (acc.1 ++ [_]).getD k _ = _
          rw [q8 _ _ _ _ (by have := v.isLt; rcases hk with rfl | rfl | rfl <;> omega)]
          exact hb
        have bound := ih (qa 9 acc g) (fun u hu => ok u (.tail _ hu)) hlen' fixed'
        rw [k4]
        by_cases hit : reads v.val g = true
        · have mem : v.val ∈ g.inputs ∨ 10 ∈ g.inputs ∨ 11 ∈ g.inputs := by
            simpa [reads, or_assoc] using hit
          have ex : ∃ k ∈ g.inputs, k = v.val ∨ k = 10 ∨ k = 11 := by
            rcases mem with h | h | h
            · exact ⟨v.val,h,Or.inl rfl⟩
            · exact ⟨10,h,Or.inr (Or.inl rfl)⟩
            · exact ⟨11,h,Or.inr (Or.inr rfl)⟩
          obtain ⟨k,hk,hfix⟩ := ex
          obtain ⟨b,hb⟩ := fixed k hfix
          have hh := vs 9 acc g (ok _ (.head _)) k hk b hb
          simp [hit] at bound ⊢
          omega
        · have hh : (qa 9 acc g).2.length ≤ acc.2.length+1 := by
            change (acc.2 ++ (qg _ _ _).1.toList).length ≤ _
            rw [List.length_append]
            exact Nat.add_le_add_left (y2 _) _
          simp [hit] at bound ⊢
          omega
    have consumerBound (v : Fin 10)
        (hv : v = 0 ∨ v = 2) (C : Circuit) (legal : FanInTwo C)
        (correct : ∀ x : Fin 10 → Bool, x v = false → C.eval (List.ofFn x ++ [x 0 && x 2, !(x 0 && x 2)]) = full x) :
        16 + (C.gates.map vg).countP (reads v.val) ≤ C.size := by
      rcases C with ⟨gs,o⟩
      let tail := gs.map vg
      have good : ∀ g ∈ tail, NOk g := by
        intro g hg
        obtain ⟨a,ha,rfl⟩ := List.mem_map.1 hg
        exact q45 a (legal a ha)
      let a := elim 9 tail (initial v, [])
      have vals (y : Fin 9 → Bool) :
          ze (q3 a.2 (List.ofFn y)) (a.1.getD o (.inl false)) = deleted y := by
        let x := fun j => pinNine y (move v j)
        have he : (x 0 && x 2) = false := by
          obtain rfl | rfl := hv
          · simp [x, droppedAt 0 (Or.inl rfl) y]
          · simp [x, droppedAt 2 (Or.inr rfl) y]
        have inv := j7 9 (List.ofFn y) (by simp) tail _ _ (fun g hg => (good g hg).1) (initialInv v y)
        rw [(inv.2 o).2]
        change (q3 (gs.map vg) (List.ofFn x ++ [false,true])).getD o false = _
        rw [jd]
        have hx := correct x (droppedAt v hv y)
        rw [he] at hx
        exact hx.trans (droppedVertex v hv y)
      have size : 16 ≤ a.2.length := by
        cases hs : a.1.getD o (.inl false) with
        | inl c =>
          have first := vals (fun _ => false)
          have last := vals (fun _ => true)
          rw [hs] at first last
          have h : deleted (fun _ => false) ≠ deleted (fun _ => true) := by decide
          exact False.elim (h (first.symm.trans last))
        | inr j =>
          by_contra! h
          apply smaller
          refine ⟨⟨a.2,j⟩, q156 9 tail _ (by simp), by change a.2.length ≤ 15; omega, ?_⟩
          intro y
          have tmp := vals y
          rw [hs] at tmp
          exact tmp
      have fixed (k : Nat) (hk : k = v.val ∨ k = 10 ∨ k = 11) :
          ∃ b, (initial v).getD k (.inl false) = .inl b := by
        rcases hk with rfl | rfl | rfl
        · rcases hv with rfl | rfl <;> exact ⟨false,rfl⟩
        · exact ⟨false,rfl⟩
        · exact ⟨true,rfl⟩
      have count := counting v tail (initial v, []) good (by simp [initial]) fixed
      change a.2.length + tail.countP (reads v.val) ≤ 0 + tail.length at count
      change 16 + tail.countP (reads v.val) ≤ gs.length
      have hl : tail.length = gs.length := by simp [tail]
      omega
    intro operands C v g h legal hv hg hh diff hvread hhelper correct
    let ops := fun g : Gate => GateOp.casesOn (motive := fun _ => List ℕ) g.op g.inputs g.inputs (g.inputs.take 1) (fun _ => g.inputs) g.inputs
    have normOp (g : Gate) : (vg g).inputs = ops g := by obtain ⟨op,is⟩ := g; cases op <;> rfl
    change v.val ∈ ops g at hvread
    change 10 ∈ ops h ∨ 11 ∈ ops h at hhelper
    have hb := consumerBound v hv C legal correct
    let p := fun u : Gate => reads v.val (vg u)
    have pg : p g = true := by simp [p,reads,normOp,hvread]
    have ph : p h = true := by rcases hhelper with e | e <;> simp [p,reads,normOp,e]
    have two (gs : List Gate) (hg : g ∈ gs) (hh : h ∈ gs) : 2 ≤ gs.countP p := by
      induction gs with
      | nil => simp at hg
      | cons a t ih =>
        rcases List.mem_cons.1 hg with rfl | gt
        · have ht := (List.mem_cons.1 hh).resolve_left (Ne.symm diff)
          have hpos : 0 < t.countP p := List.countP_pos_iff.mpr ⟨h,ht,ph⟩
          rw [List.countP_cons_of_pos pg]
          omega
        · rcases List.mem_cons.1 hh with rfl | ht
          · have hpos : 0 < t.countP p := List.countP_pos_iff.mpr ⟨g,gt,pg⟩
            rw [List.countP_cons_of_pos ph]
            omega
          · have both := ih gt ht
            rw [List.countP_cons]
            split <;> omega
    have gt := two C.gates hg hh
    have count : (C.gates.map vg).countP (reads v.val) = C.gates.countP p := by
      exact List.countP_map
    omega
  intro C legal small
  by_contra! correct
  let graph := (fun x : Fin 10 → Bool =>
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) ||
  (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))
  let aug := fun x : Fin 10 → Bool => (List.ofFn x ++ [x 0 && x 2, !(x 0 && x 2)])
  let operands := fun g : Gate => GateOp.casesOn (motive := fun _ => List ℕ) g.op g.inputs g.inputs (g.inputs.take 1) (fun _ => g.inputs) g.inputs
  let bits := fun (m : ℕ) (i : Fin 10) => m.testBit i.val
  let run := fun (gs : List Gate) (a : List Bool) => gs.foldl
    (fun w g => w ++ [g.op.eval (g.inputs.map (fun j => w.getD j false))]) a
  change ∀ x : Fin 10 → Bool, C.eval (aug x) = graph x at correct
  have lengthAug (x : Fin 10 → Bool) : (aug x).length = 12 := by simp [aug]
  have effective (g : Gate) (f : ℕ → Bool) :
      g.op.eval (g.inputs.map f) = g.op.eval ((operands g).map f) := by
    obtain ⟨op,is⟩ := g
    cases op <;> try rfl
    cases is <;> rfl
  have originalInput (gs : List Gate) (a : List Bool) (i : ℕ) (lt : i < a.length) :
      (run gs a).getD i false = a.getD i false := by
    induction gs generalizing a with
    | nil => rfl
    | cons h t ih =>
      change (run t (a ++ [_])).getD i false = _
      rw [ih _ (by simp; omega), List.getD_append _ _ _ _ lt]
  have projection (j : ℕ) (lt : j < 12) (out : C.output = j) (x : Fin 10 → Bool) :
      (aug x).getD j false = graph x := by
    have e := correct x
    change (run C.gates (aug x)).getD C.output false = _ at e
    rw [out,originalInput C.gates (aug x) j (by rw [lengthAug]; exact lt)] at e
    exact e
  have n10 : C.output ≠ 10 := by
    intro e
    exact (by decide : (aug (bits 3)).getD 10 false ≠ graph (bits 3)) (projection 10 (by decide) e _)
  have n11 : C.output ≠ 11 := by
    intro e
    exact (by decide : (aug (bits 0)).getD 11 false ≠ graph (bits 0)) (projection 11 (by decide) e _)
  let agrees := fun (i : ℕ) (a b : List Bool) =>
    a.length = b.length ∧ ∀ j, j ≠ i → a.getD j false = b.getD j false
  have stable (i : ℕ) (gs : List Gate) (avoid : ∀ g ∈ gs, i ∉ operands g)
      (a b : List Bool) (ok : agrees i a b) : agrees i (run gs a) (run gs b) := by
    induction gs generalizing a b with
    | nil => exact ok
    | cons g gs ih =>
      obtain ⟨len,eq⟩ := ok
      have gate : g.op.eval (g.inputs.map (fun j => a.getD j false)) =
          g.op.eval (g.inputs.map (fun j => b.getD j false)) := by
        rw [effective, effective g (fun j => b.getD j false)]
        apply congrArg g.op.eval
        apply List.map_congr_left
        intro j hj
        exact eq j (fun e => avoid _ (.head _) (e ▸ hj))
      change agrees i (run gs (a ++ [g.op.eval _])) (run gs (b ++ [g.op.eval _]))
      rw [gate]
      apply ih (fun z hz => avoid z (.tail g hz))
      refine ⟨by simp [len], ?_⟩
      intro j neq
      by_cases low : j < a.length
      · rw [List.getD_append _ _ _ _ low, List.getD_append _ _ _ _ (by omega)]
        exact eq j neq
      · by_cases atEnd : j = a.length
        · rw [atEnd]
          simp [len]
        · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  let src := fun b : Bool => (if b then 2 else 0 : Fin 10)
  have tests : ∀ b : Bool,
      (aug (bits (2 ^ (src b).val))).getD (src b).val false ≠ graph (bits (2 ^ (src b).val)) ∧
      graph (bits 2) ≠ graph (bits (2 + 2 ^ (src b).val)) ∧
      ∀ j : Fin 12, j.val ≠ (src b).val →
        (aug (bits 2)).getD j.val false = (aug (bits (2 + 2 ^ (src b).val))).getD j.val false := by decide
  have uses (b : Bool) : ∃ g ∈ C.gates, (src b).val ∈ operands g := by
    obtain ⟨different,unequal,rest⟩ := tests b
    have outside : C.output ≠ (src b).val := by
      intro e
      exact different (projection _ (by have := (src b).isLt; omega) e _)
    by_contra! none
    have ok : agrees (src b).val (aug (bits 2)) (aug (bits (2+2^(src b).val))) := by
      refine ⟨(lengthAug _).trans (lengthAug _).symm, ?_⟩
      intro j hj
      by_cases low : j < 12
      · exact rest ⟨j,low⟩ hj
      · rw [List.getD_eq_default _ _ (by rw [lengthAug]; omega), List.getD_eq_default _ _ (by rw [lengthAug]; omega)]
    have value := (stable _ _ none _ _ ok).2 C.output outside
    change C.eval (aug (bits 2)) = C.eval (aug (bits (2+2^(src b).val))) at value
    rw [correct,correct] at value
    exact unequal value
  have noHelpers : ∀ h ∈ C.gates, 10 ∉ operands h ∧ 11 ∉ operands h := by
    intro h hh
    by_contra! bad
    have helper : 10 ∈ operands h ∨ 11 ∈ operands h := by tauto
    have forced (b : Bool) : (src b).val ∈ operands h := by
      obtain ⟨g,hg,raw⟩ := uses b
      by_cases e : g = h
      · simpa only [e] using raw
      · have lb := cofactor C (src b) g h legal (by cases b <;> simp [src]) hg hh e raw helper
          (fun x _ => correct x)
        omega
    have zero : 0 ∈ operands h := forced false
    have two : 2 ∈ operands h := forced true
    have limit : (operands h).length ≤ 2 := by
      have hs := (legal h hh).2
      cases h with
      | mk op is =>
        cases op <;> try exact hs
        simp [operands]
    have three (v : ℕ) (hv : v = 10 ∨ v = 11) (hit : v ∈ operands h) : False := by
      have sub : ({0,2,v} : Finset ℕ) ⊆ (operands h).toFinset := by
        intro k hk
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl | rfl <;> simp_all only [List.mem_toFinset]
      have card := Finset.card_le_card sub
      have lim := (List.toFinset_card_le (operands h)).trans limit
      rcases hv with rfl | rfl <;> norm_num at card <;> omega
    exact helper.elim (three 10 (.inl rfl)) (three 11 (.inr rfl))
  obtain ⟨D,legalD,smallD,eq⟩ := erase 10 C legal n10 n11 noHelpers
  apply ordinary
  exact ⟨D,legalD,smallD.trans small,fun x => (eq x _ _).trans (correct x)⟩
