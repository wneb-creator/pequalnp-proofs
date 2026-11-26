import Mathlib
import PEqualNP.Defs

open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover

namespace PEqualNP.Outside.L_meta_17725

def run (gs : List Gate) (v : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) v

theorem extendsInputs (gs : List Gate) (v : List Bool) :
    ∃ z, run gs v = v++z ∧ z.length = gs.length := by
  induction gs generalizing v with
  | nil => exact ⟨[],by simp [run]⟩
  | cons g gs ih =>
    let b := g.op.eval (g.inputs.map fun i => v.getD i false)
    obtain ⟨z,hz,hl⟩ := ih (v++[b])
    exact ⟨b::z,by simpa [run,b,List.append_assoc] using hz,by simp [hl]⟩

theorem old {C D : Circuit} {extra : List Gate} (shape : D.gates=C.gates++extra)
    {n w : ℕ} (hw : w<n+C.size) (x : Fin n → Bool) :
    BlindGate.wireValue D n x w = BlindGate.wireValue C n x w := by
  let xs := List.ofFn x
  let v := run C.gates xs
  obtain ⟨z,hz,len⟩ := extendsInputs C.gates xs
  have vl : v.length = n+C.size := by change (run C.gates xs).length = _; simp [hz,xs,len,Circuit.size]
  obtain ⟨z',he,_⟩ := extendsInputs extra v
  change (run D.gates xs).getD w false = v.getD w false
  rw [shape,show run (C.gates++extra) xs = run extra v from List.foldl_append,he]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_append_left (show w<v.length by omega)]

theorem input (C : Circuit) {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    BlindGate.wireValue C n x i.val = x i := by
  obtain ⟨z,h,_⟩ := extendsInputs C.gates (List.ofFn x)
  change (run C.gates (List.ofFn x)).getD i.val false = _
  rw [h]
  simp [List.getD_eq_getElem?_getD,List.getElem?_append_left (show i.val<(List.ofFn x).length by simp),i.isLt]

def Ext (n : ℕ) (C D : Circuit) (es : List Gate) : Prop :=
  D.gates=C.gates++es ∧ (∀ g ∈ es, g.op=.or) ∧ IsAO2 n D ∧
  ∀ j, C.size≤j → j<D.size → ∃ i : Fin n, ∀ x : Fin n → Bool,
    x i=true → BlindGate.wireValue D n x (n+j)=true

theorem trivialExt {n : ℕ} {C : Circuit} (h : IsAO2 n C) : Ext n C C [] :=
  ⟨by simp,by simp,h,by intro j hj hlt; omega⟩

theorem combine {n : ℕ} {C D E : Circuit} {a b : List Gate} (h : Ext n C D a) (h' : Ext n D E b) :
    Ext n C E (a++b) := by
  refine ⟨by rw [h'.1,h.1,List.append_assoc],?_,h'.2.2.1,?_⟩
  · intro g hg
    exact (List.mem_append.mp hg).elim (h.2.1 g) (h'.2.1 g)
  · intro j low high
    by_cases hj : j < D.size
    · obtain ⟨i,hi⟩ := h.2.2.2 j low hj
      exact ⟨i,fun x hx => (old h'.1 (by omega) x).trans (hi x hx)⟩
    · exact h'.2.2.2 j (by omega) high

def add (C : Circuit) (i w : ℕ) : Circuit := ⟨C.gates++[⟨.or,[i,w]⟩],C.output⟩

theorem addSize (C : Circuit) (i w : ℕ) : (add C i w).size = C.size + 1 := by simp [Circuit.size,add]

theorem addValue (C : Circuit) {n : ℕ} (i : Fin n) (w : ℕ) (x : Fin n → Bool) :
    BlindGate.wireValue (add C i.val w) n x (n+C.size) = (x i || BlindGate.wireValue C n x w) := by
  let v := run C.gates (List.ofFn x)
  obtain ⟨z,h,len⟩ := extendsInputs C.gates (List.ofFn x)
  have hl : v.length = n+C.size := by simp [v,h,len,Circuit.size]
  have raw : v.getD i.val false = x i := input C x i
  change (run (C.gates++[⟨.or,[i.val,w]⟩]) (List.ofFn x)).getD (n+C.size) false = (x i || v.getD w false)
  rw [show run (C.gates++[⟨.or,[i.val,w]⟩]) (List.ofFn x) = run [⟨.or,[i.val,w]⟩] v from List.foldl_append]
  change (v++[GateOp.or.eval [v.getD i.val false,v.getD w false]]).getD (n+C.size) false = _
  rw [←hl,raw]
  suffices ∀ a b : Bool, GateOp.or.eval [a,b] = (a || b) by simpa using this (x i) (v.getD w false)
  decide

theorem addExt {n : ℕ} {C : Circuit} (M : IsAO2 n C) (i : Fin n) {w : ℕ} (bound : w<n+C.size) :
    Ext n C (add C i.val w) [⟨.or,[i.val,w]⟩] := by
  let g : Gate := ⟨.or,[i.val,w]⟩
  let D := add C i.val w
  have size : D.size = C.size+1 := addSize _ _ _
  have model : IsAO2 n D := by
    refine ⟨?_,?_,?_⟩
    · intro a ha
      rcases List.mem_append.mp ha with h | h
      · exact M.1 a h
      · obtain rfl : a=g := List.mem_singleton.mp h
        exact Or.inr rfl
    · intro j hj k hk
      by_cases h : j<C.gates.length
      · have oldg : gateAt D j = gateAt C j := by
          simp [D,add,gateAt,List.getD_eq_getElem?_getD,List.getElem?_append_left h]
        rw [oldg] at hk
        exact M.2.1 j h k hk
      · change j<D.size at hj
        have eqj : j=C.gates.length := by change ¬j<C.size at h; change j=C.size; omega
        subst j
        have last : gateAt D C.gates.length = g := by simp [D,add,gateAt,g]
        rw [last] at hk
        change k ∈ [i.val,w] at hk
        have hi := i.isLt
        rcases List.mem_cons.mp hk with rfl | h
        · omega
        · simpa [List.mem_singleton.mp h,Circuit.size] using bound
    · intro a ha
      rcases List.mem_append.mp ha with h | h
      · exact M.2.2 a h
      · obtain rfl : a=g := List.mem_singleton.mp h
        rfl
  refine ⟨rfl,by simp,model,?_⟩
  intro j lo hi
  change j<D.size at hi
  obtain rfl : j=C.size := by omega
  exact ⟨i,fun x hx => by simp [addValue,hx]⟩

theorem chain {n : ℕ} {C : Circuit} (M : IsAO2 n C) (vs : List (Fin n)) (ne : vs ≠ []) :
    ∃ (D : Circuit) (es : List Gate) (w : ℕ), Ext n C D es ∧ es.length+1=vs.length ∧
      w<n+D.size ∧ (2≤vs.length → n≤w) ∧
      ∀ x : Fin n → Bool, BlindGate.wireValue D n x w = vs.any x := by
  induction vs with
  | nil => contradiction
  | cons v vs ih =>
    by_cases h : vs=[]
    · subst vs
      refine ⟨C,[],v.val,trivialExt M,rfl,?_,by simp,?_⟩
      · have := v.isLt; omega
      · intro x; simpa using input C x v
    · obtain ⟨D,es,w,ext,len,bound,_,calcw⟩ := ih h
      let g : Gate := ⟨.or,[v.val,w]⟩
      have more := addExt ext.2.2.1 v bound
      refine ⟨add D v.val w,es++[g],n+D.size,combine ext more,?_,?_,fun _ => by omega,?_⟩
      · simp only [List.length_append,List.length_cons,List.length_nil]
        omega
      · rw [addSize]; omega
      · intro x; rw [addValue,calcw,List.any_cons]

end PEqualNP.Outside.L_meta_17725

open PEqualNP.Outside.L_meta_17725

theorem PEqualNP.Outside.L_meta_17725 : (∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : List (Fin x1 × List (Fin x1))), PEqualNP.TopForm.IsAO2 x1 x2 → (∀ x5 ∈ x3, (2 : ℕ) ≤ x5.2.length) → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : List (ℕ × ℕ)) (x8 : List PEqualNP.CircuitLowerBounds.Gate), x6.gates = x2.gates ++ x8 ∧ (∀ x9 ∈ x8, x9.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ PEqualNP.TopForm.IsAO2 x1 x6 ∧ x8.length + x3.length ≤ (List.map (fun (x9 : Fin x1 × List (Fin x1)) => x9.2.length) x3).sum ∧ x7.length = x3.length ∧ (∀ x9 ∈ x7, x9.1 < x1 + x6.size ∧ x9.2 < x1 + x6.size ∧ x1 ≤ x9.2) ∧ (∀ (x9 : Fin x1 → Bool), (x7.any fun (x10 : ℕ × ℕ) => PEqualNP.BlindGate.wireValue x6 x1 x9 x10.1 && PEqualNP.BlindGate.wireValue x6 x1 x9 x10.2) = x3.any fun (x10 : Fin x1 × List (Fin x1)) => x9 x10.1 && x10.2.any x9) ∧ ∀ (x9 : ℕ), x2.size ≤ x9 → x9 < x6.size → ∃ (x12 : Fin x1), ∀ (x13 : Fin x1 → Bool), x13 x12 = Bool.true → PEqualNP.BlindGate.wireValue x6 x1 x13 (x1 + x9) = Bool.true) := by
  intro n C gs M wide
  induction gs generalizing C with
  | nil =>
    refine ⟨C,[],[],by simp,by simp,M,by simp,rfl,by simp,by simp,?_⟩
    intro j h h'; omega
  | cons g gs ih =>
    have gw := wide g (List.mem_cons_self ..)
    obtain ⟨D,es,w,h,len,bound,computed,calcw⟩ := chain M g.2 (by intro e; simp [e] at gw)
    have ww : n≤w := computed gw
    obtain ⟨E,L,tail,shape,ors,model,cost,count,ends,targets,pure⟩ :=
      ih D h.2.2.1 (fun g' hm => wide g' (List.mem_cons_of_mem g hm))
    have ext : Ext n D E tail := ⟨shape,ors,model,pure⟩
    have joint := combine h ext
    have sizes : E.size = D.size+tail.length := by simp [Circuit.size,shape]
    let e : ℕ×ℕ := (g.1.val,w)
    refine ⟨E,e::L,es++tail,joint.1,joint.2.1,model,?_,?_,?_,?_,joint.2.2.2⟩
    · simp only [List.length_append,List.length_cons,List.map_cons,List.sum_cons]
      omega
    · simp [count]
    · intro e' he
      rcases List.mem_cons.mp he with h' | h'
      · subst e'
        have hi := g.1.isLt
        exact ⟨by change g.1.val < n+E.size; omega,by change w < n+E.size; omega,ww⟩
      · exact ends e' h'
    · intro x
      simp only [List.any_cons,targets]
      change ((BlindGate.wireValue E n x g.1.val && BlindGate.wireValue E n x w) || _) = _
      rw [input,old shape bound,calcw]
