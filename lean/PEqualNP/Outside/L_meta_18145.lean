import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18145

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.ReadK

def scan {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α) : List α :=
  gs.foldl (fun w g => w ++ [step w g]) w

lemma scan_cons {α : Type} (step : List α → Gate → α) (g : Gate) (gs : List Gate) (w : List α) :
    scan step (g :: gs) w = scan step gs (w ++ [step w g]) := rfl

lemma scan_append {α : Type} (step : List α → Gate → α) (gs hs : List Gate) (w : List α) :
    scan step (gs ++ hs) w = scan step hs (scan step gs w) := by
  simp [scan, List.foldl_append]

lemma scan_length {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α) :
    (scan step gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [scan_cons, ih]
    simp
    omega

lemma scan_prefix {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α)
    (d : α) (i : ℕ) (hi : i < w.length) :
    (scan step gs w).getD i d = w.getD i d := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [scan_cons, ih _ (by simp; omega)]
    exact List.getD_append _ _ _ _ hi

lemma scan_gate {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α)
    (d : α) (j : ℕ) (hj : j < gs.length)
    (hstep : ∀ p p' : List α, (∀ i < w.length + j, p.getD i d = p'.getD i d) →
      step p gs[j] = step p' gs[j]) :
    (scan step gs w).getD (w.length + j) d = step (scan step gs w) gs[j] := by
  let pre := scan step (gs.take j) w
  have hp : pre.length = w.length + j := by
    simp [pre, scan_length, Nat.min_eq_left hj.le]
  have hs : scan step gs w = scan step (gs[j] :: gs.drop (j + 1)) pre := by
    have hsplit := List.take_append_drop j gs
    conv_lhs => rw [← hsplit, scan_append, List.drop_eq_getElem_cons hj]
  have hpre : ∀ i < w.length + j, (scan step gs w).getD i d = pre.getD i d := by
    intro i hi
    rw [hs]
    exact scan_prefix step (gs[j] :: gs.drop (j + 1)) pre d i (by omega)
  have hres : (scan step gs w).getD (w.length + j) d = step pre gs[j] := by
    rw [hs, scan_cons, scan_prefix step (gs.drop (j + 1)) (pre ++ [step pre gs[j]]) d (w.length + j) (by simp [hp])]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    have hsub : w.length + j - pre.length = 0 := by omega
    rw [hsub]
    simp only [List.getD_cons_zero]
  rw [hres]
  exact hstep pre (scan step gs w) (fun i hi => (hpre i hi).symm)

def boolStep (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def linStep (w : List (Bool × Bool)) (g : Gate) : Bool × Bool :=
  let ins := g.inputs.map fun i => w.getD i (false, false)
  match g.op with
  | GateOp.or => (ins.any (·.1), ins.any (·.2))
  | GateOp.and => ins.foldl (fun (acc : Bool × Bool) p =>
        (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (true, false)
  | _ => (false, false)

lemma wires_eq_scan (C : Circuit) (x : List Bool) :
    C.wires x = scan boolStep C.gates x := rfl

lemma linearParts_eq_scan (C : Circuit) (isLine : ℕ → Bool) (x : List Bool) :
    linearParts C isLine x =
      scan linStep C.gates ((x.zipIdx).map fun (b, i) => if isLine i then (false, b) else (b, false)) := rfl

lemma list_eq_two {l : List ℕ} (hl : l.length = 2) : l = [l.getD 0 0, l.getD 1 0] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;> simp at hl ⊢

lemma gateAt_eq_getElem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, hj]

lemma ao2_gate_props {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] ∧
    opnd C j 0 < n + j ∧ opnd C j 1 < n + j := by
  have hmem : C.gates[j] ∈ C.gates := List.getElem_mem hj
  have hop : (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := by
    rw [gateAt_eq_getElem hj]
    exact hAO2.1 C.gates[j] hmem
  have hlen : (gateAt C j).inputs.length = 2 := by
    rw [gateAt_eq_getElem hj]
    exact hAO2.2.2 C.gates[j] hmem
  have hin : (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
    simpa [opnd] using list_eq_two hlen
  have hrb := hAO2.2.1 j hj
  have h0 : opnd C j 0 < n + j := hrb (opnd C j 0) (by rw [hin]; simp)
  have h1 : opnd C j 1 < n + j := hrb (opnd C j 1) (by rw [hin]; simp)
  exact ⟨hop, hin, h0, h1⟩

private abbrev W (n : ℕ) (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  scan boolStep gs (List.ofFn x)

private theorem inputAt {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (W n gs x).getD i false = x ⟨i,hi⟩ := by
  rw [scan_prefix boolStep _ _ _ _ (by simpa using hi),List.getD_eq_getElem _ _ (by simpa using hi),List.getElem_ofFn]

private theorem wireAtGate {n : ℕ} (C : Circuit) (h : IsAO2 n C) (j : ℕ)
    (hj : j < C.gates.length) (x : Fin n → Bool) :
    (W n C.gates x).getD (n+j) false = boolStep (W n C.gates x) C.gates[j] := by
  simpa only [List.length_ofFn] using
    (scan_gate boolStep C.gates (List.ofFn x) false j hj (fun r s he => by
      unfold boolStep
      congr 1
      apply List.map_congr_left
      intro i hi
      apply he
      have := h.2.1 j hj i (by rwa [gateAt_eq_getElem hj])
      simpa using this))

private def readOpt (w : List Bool) (ref : Option ℕ) : Bool :=
  (ref.map fun i => w.getD i false).getD false

private def validRef (lim : ℕ) (ref : Option ℕ) : Prop :=
  ∀ i, ref = some i → i < lim

private theorem optPrefix (w : List Bool) (v : Bool) (ref : Option ℕ) (ok : validRef w.length ref) :
    readOpt (w ++ [v]) ref = readOpt w ref := by
  cases ref with
  | none => rfl
  | some i => exact List.getD_append _ _ _ _ (ok i rfl)

private inductive Action where
  | reuse (ref : Option ℕ)
  | add (g : Gate)

private def Action.ref (lim : ℕ) : Action → Option ℕ
  | .reuse r => r
  | .add _ => some lim

private def Action.newGates : Action → List Gate
  | .reuse _ => []
  | .add g => [g]

private def Action.eval (w : List Bool) : Action → Bool
  | .reuse r => readOpt w r
  | .add g => boolStep w g

private def Action.Well (limit : ℕ) : Action → Prop
  | .reuse r => validRef limit r
  | .add g => (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 ∧
      ∀ i ∈ g.inputs, i < limit

private theorem newGatesSmall (act : Action) : act.newGates.length ≤ 1 := by cases act <;> simp [Action.newGates]

private def pick (op : GateOp) (a b : Option ℕ) : Action :=
  match a, b with
  | some i, some j => .add ⟨op,[i,j]⟩
  | none, v | v, none => .reuse (if op.eval [false,true] then v else none)

private theorem pickSound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (a b : Option ℕ) (w : List Bool) : (pick op a b).eval w =
      op.eval [readOpt w a,readOpt w b] := by
  rcases hop with rfl | rfl <;> cases a <;> cases b <;>
    simp [pick,Action.eval,readOpt,GateOp.eval,boolStep]

private theorem pickWell (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (a b : Option ℕ) (lim : ℕ) (va : validRef lim a) (vb : validRef lim b) :
    (pick op a b).Well lim := by
  rcases hop with rfl | rfl <;> cases a <;> cases b <;>
    simp_all [pick,Action.Well,validRef,GateOp.eval]

private theorem actionApply {n : ℕ} (gs : List Gate) (legal : IsAO2 n (⟨gs,0⟩ : Circuit))
    (act : Action) (well : act.Well (n+gs.length)) :
    IsAO2 n (⟨gs++act.newGates,0⟩ : Circuit) := by
  cases act with
  | reuse r => simpa [Action.newGates] using legal
  | add g =>
    obtain ⟨hop,hlen,back⟩ := well
    refine ⟨?_,?_,?_⟩
    · intro g' hm
      rcases List.mem_append.mp hm with h | h
      · exact legal.1 _ h
      · obtain rfl := List.mem_singleton.mp h
        exact hop
    · intro j hj i hi
      change j < (gs ++ [g]).length at hj
      simp only [List.length_append,List.length_singleton] at hj
      by_cases hlt : j < gs.length
      · have he : gateAt ⟨gs++[g],0⟩ j = gateAt ⟨gs,0⟩ j := by
          rw [gateAt,gateAt,List.getD_append _ _ _ _ hlt]
        exact legal.2.1 j hlt i (he ▸ hi)
      · have heq : j = gs.length := by omega
        subst j
        have he : gateAt ⟨gs++[g],0⟩ gs.length = g := by
          rw [gateAt,List.getD_append_right _ _ _ _ (by simp),Nat.sub_self,List.getD_cons_zero]
        exact back i (he ▸ hi)
    · intro g' hm
      rcases List.mem_append.mp hm with h | h
      · exact legal.2.2 _ h
      · obtain rfl := List.mem_singleton.mp h
        exact hlen

private theorem oldSource (act : Action) (w : List Bool) (ref : Option ℕ)
    (vr : validRef w.length ref) :
    readOpt (scan boolStep act.newGates w) ref = readOpt w ref := by
  cases act with
  | reuse r => rfl
  | add g => exact optPrefix w _ ref vr

private theorem resultSource (act : Action) (w : List Bool) (ok : act.Well w.length) :
    readOpt (scan boolStep act.newGates w) (act.ref w.length) = act.eval w := by
  cases act with
  | reuse r => rfl
  | add g =>
    change (w ++ [boolStep w g]).getD w.length false = boolStep w g
    rw [List.getD_append_right _ _ _ _ (Nat.le_refl _),Nat.sub_self,List.getD_cons_zero]

private theorem refAvailable (act : Action) (lim : ℕ) (hw : act.Well lim) :
    validRef (lim+act.newGates.length) (act.ref lim) := by
  cases act with
  | reuse r => simpa [Action.ref,Action.newGates,Action.Well] using hw
  | add g => simp [Action.ref,Action.newGates,validRef]

private theorem validEnlarge (ref : Option ℕ) {a b : ℕ} (h : a ≤ b) (vr : validRef a ref) : validRef b ref :=
  fun i hi => Nat.lt_of_lt_of_le (vr i hi) h

private abbrev fixed {n : ℕ} (x : Fin n → Bool) (p : Fin n) := Function.update x p false

private structure Prefix (n : ℕ) (C : Circuit) (p : Fin n) (S : Finset ℕ) (j : ℕ) where
  gs : List Gate
  f : ℕ → Option ℕ
  legal : IsAO2 n (⟨gs,0⟩ : Circuit)
  cost : gs.length + (S.filter (· < j)).card ≤ j
  valids : ∀ i < n+j, validRef (n+gs.length) (f i)
  sound : ∀ i < n+j, ∀ x : Fin n → Bool,
    readOpt (W n gs x) (f i) = (W n C.gates (fixed x p)).getD i false

private theorem countFilterStep (S : Finset ℕ) (j : ℕ) :
    (S.filter (· < j+1)).card = (S.filter (· < j)).card + if j ∈ S then 1 else 0 := by
  by_cases hm : j ∈ S
  · have e : S.filter (· < j+1) = insert j (S.filter (· < j)) := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_insert]
      constructor
      · rintro ⟨hi,hl⟩
        by_cases e : i = j
        · exact Or.inl e
        · exact Or.inr ⟨hi,by omega⟩
      · rintro (rfl | ⟨hi,hl⟩)
        · exact ⟨hm,by omega⟩
        · exact ⟨hi,by omega⟩
    rw [e,Finset.card_insert_of_notMem (by simp),ite_eq_left hm]
  · have e : S.filter (· < j+1) = S.filter (· < j) := by
      ext i
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hi,hl⟩
        exact ⟨hi,by have hn : i ≠ j := fun eq => hm (eq ▸ hi); omega⟩
      · rintro ⟨hi,hl⟩; exact ⟨hi,by omega⟩
    rw [e,ite_eq_right hm,Nat.add_zero]

private def Prefix.step {n : ℕ} {C : Circuit} {p : Fin n} {S : Finset ℕ} {j : ℕ}
    (P : Prefix n C p S j) (act : Action) (hw : act.Well (n+P.gs.length))
    (hshort : act.newGates.length + (if j ∈ S then 1 else 0) ≤ 1)
    (ok : ∀ x : Fin n → Bool, act.eval (W n P.gs x) =
      (W n C.gates (fixed x p)).getD (n+j) false) : Prefix n C p S (j+1) := by
  let new := P.gs ++ act.newGates
  let ff (i : ℕ) := if i = n+j then act.ref (n+P.gs.length) else P.f i
  refine ⟨new,ff,actionApply P.gs P.legal act hw,?_,?_,?_⟩
  · have hc := P.cost
    rw [countFilterStep]
    simp only [new,List.length_append]
    omega
  · intro i hi
    by_cases he : i = n+j
    · simpa [ff,new,he,Nat.add_assoc] using refAvailable act (n+P.gs.length) hw
    · change validRef _ (if i = n+j then _ else P.f i)
      rw [ite_eq_right he]
      exact validEnlarge _ (by simp [new]) (P.valids _ (by omega))
  · intro i hi x
    have len : (W n P.gs x).length = n+P.gs.length := by rw [scan_length,List.length_ofFn]
    rw [show W n new x = scan boolStep act.newGates (W n P.gs x) by exact scan_append boolStep _ _ _]
    by_cases he : i = n+j
    · subst i
      simp only [ff,ite_true]
      rw [← len,resultSource _ _ (by rw [len]; exact hw)]
      exact ok x
    · simp only [ff,he,ite_false]
      rw [oldSource _ _ _ (by rw [len]; exact P.valids _ (by omega))]
      exact P.sound _ (by omega) x

private theorem build {n : ℕ} {C : Circuit} (p : Fin n) (S : Finset ℕ)
    (hC : IsAO2 n C)
    (aliases : ∀ j ∈ S, ∃ i < n+j, ∀ x : Fin n → Bool,
      (W n C.gates (fixed x p)).getD (n+j) false = (W n C.gates (fixed x p)).getD i false)
    (j : ℕ) (bound : j ≤ C.gates.length) : Nonempty (Prefix n C p S j) := by
  induction j with
  | zero =>
    refine ⟨⟨[],fun i => if i = p.val then none else some i,by simp [IsAO2,PEqualNP.EdgeOwnership.AndOrOnly,ReadsBack],by simp,?_,?_⟩⟩
    · intro i hi
      by_cases he : i = p.val
      · simp [he,validRef]
      · simpa [he,validRef] using hi
    · intro i hi x
      have hi' : i < n := by simpa using hi
      rw [inputAt C.gates _ i hi']
      by_cases he : i = p.val
      · have hp : (⟨i,hi'⟩ : Fin n) = p := Fin.ext he
        simp [he,readOpt,fixed]
      · have hp : (⟨i,hi'⟩ : Fin n) ≠ p := fun h => he (congrArg Fin.val h)
        simp only [he,ite_false,readOpt,Option.map_some,Option.getD_some]
        rw [inputAt [] x i hi']
        simp [fixed,Function.update_of_ne hp]
  | succ j ih =>
    obtain ⟨P⟩ := ih (by omega)
    have hj : j < C.gates.length := by omega
    by_cases hm : j ∈ S
    · obtain ⟨i,hi,he⟩ := aliases j hm
      refine ⟨P.step (.reuse (P.f i)) (P.valids i hi) (by simp [Action.newGates,hm]) (fun x => ?_)⟩
      exact (P.sound i hi x).trans (he x).symm
    · obtain ⟨hop,hin,ha,hb⟩ := ao2_gate_props hC hj
      let g := gateAt C j
      let a := opnd C j 0
      let b := opnd C j 1
      let act := pick g.op (P.f a) (P.f b)
      refine ⟨P.step act (pickWell _ hop _ _ _ (P.valids a ha) (P.valids b hb)) ?_ (fun x => ?_)⟩
      · simpa [hm] using newGatesSmall act
      · rw [wireAtGate C hC j hj,← gateAt_eq_getElem hj]
        rw [pickSound g.op hop, P.sound a ha, P.sound b hb]
        change g.op.eval [_ , _] = boolStep _ g
        rw [boolStep,show g.inputs = [a,b] from hin]
        rfl

end PEqualNP.Outside.L_meta_18145

theorem PEqualNP.Outside.L_meta_18145 : (∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin x1) (x4 : Finset ℕ),   PEqualNP.TopForm.IsAO2 x1 x2 →     (∀ x6 ∈ x4,         x6 < x2.size ∧           ∃ x8 < x1 + x6,             ∀ (x9 : Fin x1 → Bool),               have x10 : List Bool := x2.wires (List.ofFn (Function.update x9 x3 Bool.false));               x10.getD (x1 + x6) Bool.false = x10.getD x8 Bool.false) →       (∃ (x7 : Fin x1 → Bool) (x8 : Fin x1 → Bool), x2.eval (List.ofFn (Function.update x7 x3 Bool.false)) ≠ x2.eval (List.ofFn (Function.update x8 x3 Bool.false))) → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x8 ∧ x8.size + x4.card ≤ x2.size ∧ ∀ (x9 : Fin x1 → Bool), x8.eval (List.ofFn x9) = x2.eval (List.ofFn (Function.update x9 x3 Bool.false))) := by
  open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_18145 in
  intro n C p S hC hAlias nconst
  obtain ⟨P⟩ := build p S hC (fun j hj => (hAlias j hj).2) C.gates.length (Nat.le_refl _)
  have within : C.output < n + C.gates.length := by
    by_contra! h
    obtain ⟨x,y,hn⟩ := nconst
    have zero (z : Fin n → Bool) : C.eval (List.ofFn (fixed z p)) = false := by
      change (W n C.gates (fixed z p)).getD C.output false = false
      apply List.getD_eq_default
      rwa [scan_length,List.length_ofFn]
    exact hn ((zero x).trans (zero y).symm)
  cases he : P.f C.output with
  | none =>
    obtain ⟨x,y,hn⟩ := nconst
    have zero (z : Fin n → Bool) : C.eval (List.ofFn (fixed z p)) = false := by
      have hz := P.sound C.output within z
      rw [he] at hz
      exact hz.symm
    exact False.elim (hn ((zero x).trans (zero y).symm))
  | some o =>
    have hsize := P.cost
    have hs : S.filter (· < C.gates.length) = S := Finset.filter_true_of_mem (fun _ hi => (hAlias _ hi).1)
    rw [hs] at hsize
    refine ⟨⟨P.gs,o⟩,P.legal,hsize,?_⟩
    intro x
    change (W n P.gs x).getD o false = (W n C.gates (fixed x p)).getD C.output false
    simpa only [he,readOpt,Option.map_some,Option.getD_some] using P.sound C.output within x
