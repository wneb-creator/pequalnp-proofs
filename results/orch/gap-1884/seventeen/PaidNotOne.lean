import SemanticBudgetExtra

namespace PEqualNP.Outside.L_meta_1884
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def inputMap {n : ℕ} (p : Fin n → Fin n) (w : ℕ) : ℕ :=
  if hw : w<n then (p ⟨w,hw⟩).val else w

def renameGate {n : ℕ} (p : Fin n → Fin n) (g : Gate) : Gate :=
  ⟨g.op,g.inputs.map (inputMap p)⟩

def renameInputs {n : ℕ} (p : Fin n → Fin n) (C : Circuit) : Circuit :=
  ⟨C.gates.map (renameGate p),inputMap p C.output⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma snoc_getD (w : List Bool) (b : Bool) (i : ℕ) :
    (w++[b]).getD i false = if i=w.length then b else w.getD i false := by
  rcases Nat.lt_trichotomy i w.length with hi | hi | hi
  · rw [ite_eq_right (by omega)]
    exact List.getD_append _ _ _ _ hi
  · subst i
    simp [List.getD_eq_getElem?_getD]
  · rw [ite_eq_right (by omega)]
    rw [List.getD_eq_default _ _ (by simp;omega),List.getD_eq_default _ _ (by omega)]

lemma step_relabel {n : ℕ} (p : Fin n → Fin n) (g : Gate)
    (old new : List Bool) (hlen : old.length=new.length) (hn : n≤old.length)
    (hrel : ∀ w,old.getD w false=new.getD (inputMap p w) false) :
    ∀ w,(step old g).getD w false=(step new (renameGate p g)).getD (inputMap p w) false := by
  intro w
  have hev : g.op.eval (g.inputs.map fun i => old.getD i false) =
      (renameGate p g).op.eval ((renameGate p g).inputs.map fun i => new.getD i false) := by
    simp only [renameGate,List.map_map]
    congr 1
    exact List.map_congr_left fun i _ => hrel i
  simp only [step,snoc_getD]
  rw [← hev]
  by_cases hw : w<n
  · have hp : inputMap p w < n := by simp only [inputMap,dite_eq_left hw]; exact (p ⟨w,hw⟩).isLt
    rw [ite_eq_right (by omega),ite_eq_right (by omega)]
    exact hrel w
  · have he : inputMap p w=w := by simp [inputMap,hw]
    rw [he,← hlen]
    split_ifs
    · rfl
    · exact (hrel w).trans (by rw [he])

lemma fold_relabel {n : ℕ} (p : Fin n → Fin n) (gs : List Gate)
    (old new : List Bool) (hlen : old.length=new.length) (hn : n≤old.length)
    (hrel : ∀ w,old.getD w false=new.getD (inputMap p w) false) :
    ∀ w,(gs.foldl step old).getD w false=
      ((gs.map (renameGate p)).foldl step new).getD (inputMap p w) false := by
  induction gs generalizing old new with
  | nil => exact hrel
  | cons g gs ih =>
    simp only [List.foldl_cons,List.map_cons]
    exact ih (step old g) (step new (renameGate p g)) (by simp [step,hlen])
      (by simp [step];omega) (step_relabel p g old new hlen hn hrel)

lemma initial_relabel {n : ℕ} (p : Fin n → Fin n) (x : Fin n → Bool) (b : Bool) :
    ∀ w,(List.ofFn (x ∘ p)++[b]).getD w false=
      (List.ofFn x++[b]).getD (inputMap p w) false := by
  intro w
  by_cases hw : w<n
  · have hp : inputMap p w<n := by simp only [inputMap,dite_eq_left hw]; exact (p ⟨w,hw⟩).isLt
    rw [List.getD_append _ _ _ _ (by simpa using hw),
      List.getD_append _ _ _ _ (by simpa using hp)]
    simp [List.getD_eq_getElem?_getD,inputMap,hw,Function.comp_def]
  · have he : inputMap p w=w := by simp [inputMap,hw]
    rw [he,snoc_getD,snoc_getD]
    simp only [List.length_ofFn]
    split_ifs
    · rfl
    · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hw),
        List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hw)]

lemma renameInputs_eval {n : ℕ} (p : Fin n → Fin n) (C : Circuit) (x : Fin n → Bool) (b : Bool) :
    (renameInputs p C).eval (List.ofFn x++[b])=
      C.eval (List.ofFn (x ∘ p)++[b]) := by
  exact (fold_relabel p C.gates _ _ (by simp) (by simp) (initial_relabel p x b) C.output).symm

lemma renameInputs_size {n : ℕ} (p : Fin n → Fin n) (C : Circuit) :
    (renameInputs p C).size=C.size := by simp [renameInputs,Circuit.size]

lemma renameInputs_fanInTwo {n : ℕ} (p : Fin n → Fin n) (C : Circuit) (hC : FanInTwo C) :
    FanInTwo (renameInputs p C) := by
  intro g hg
  change g ∈ C.gates.map (renameGate p) at hg
  obtain ⟨g0,hg0,he⟩ := List.mem_map.mp hg
  subst g
  obtain ⟨hop,hlen⟩ := hC g0 hg0
  exact ⟨hop,by simpa [renameGate] using hlen⟩

lemma unary_four (h : Bool → Bool) :
    h=(fun _ => false) ∨ h=(fun _ => true) ∨ h=id ∨ h=Bool.not := by
  cases hF : h false <;> cases hT : h true
  · left;funext b;cases b <;> assumption
  · right;right;left;funext b;cases b <;> assumption
  · right;right;right;funext b;cases b <;> assumption
  · right;left;funext b;cases b <;> assumption

lemma four_canonical_cases_suffice {n : ℕ} (a : Fin n) (F : (Fin n → Bool) → Bool) (k : ℕ)
    (hcases : ∀ h : Bool → Bool,
      (h=(fun _ => false) ∨ h=(fun _ => true) ∨ h=id ∨ h=Bool.not) →
      ∀ D : Circuit,FanInTwo D → D.size≤k →
      ∃ x : Fin n → Bool,D.eval (List.ofFn x++[h (x a)])≠F x) :
    ∀ (C : Circuit) (p : Fin n → Fin n) (h : Bool → Bool),
      FanInTwo C → C.size≤k →
      ∃ x : Fin n → Bool,C.eval (List.ofFn (x ∘ p)++[h (x a)])≠F x := by
  intro C p h hC hs
  obtain ⟨x,hx⟩ := hcases h (unary_four h) (renameInputs p C)
    (renameInputs_fanInTwo p C hC) (by simpa [renameInputs_size] using hs)
  exact ⟨x,by simpa only [renameInputs_eval] using hx⟩


def prependNot (C : Circuit) : Circuit := ⟨⟨GateOp.not,[0]⟩::C.gates,C.output⟩

lemma prependNot_eval (C : Circuit) (x : Fin 10 → Bool) :
    (prependNot C).eval (List.ofFn x)=C.eval (List.ofFn x++[!x 0]) := by
  change C.eval (List.ofFn x++[GateOp.not.eval ([0].map fun i => (List.ofFn x).getD i false)]) = _
  congr 1

lemma prependNot_fanInTwo (C : Circuit) (hC : FanInTwo C) : FanInTwo (prependNot C) := by
  intro g hg
  change g ∈ ⟨GateOp.not,[0]⟩::C.gates at hg
  rcases List.mem_cons.mp hg with rfl | hg
  · simp [GateOp.eval]
  · exact hC g hg

lemma prependNot_nonNotCount (C : Circuit) :
    (prependNot C).gates.countP (fun g => !g.op.eval [false])=
      C.gates.countP (fun g => !g.op.eval [false]) := by
  simp [prependNot,GateOp.eval]

def paidNotCount (C : Circuit) : ℕ := C.gates.countP (fun g => g.op.eval [false])

lemma nonNot_add_paidNot (C : Circuit) :
    C.gates.countP (fun g => !g.op.eval [false])+paidNotCount C=C.size := by
  have h (gs : List Gate) :
      gs.countP (fun g => !g.op.eval [false])+gs.countP (fun g => g.op.eval [false])=gs.length := by
    induction gs with
    | nil => rfl
    | cons g gs ih =>
      cases hg : g.op.eval [false] <;> simp [hg,List.countP_cons] <;> omega
  exact h C.gates

lemma paidNotCount_eq (C : Circuit) (hC : FanInTwo C) :
    paidNotCount C=C.gates.countP (fun g => match g.op with | .not => true | _ => false) := by
  apply List.countP_congr
  intro g hg
  have hop := (hC g hg).1
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hop
  rcases hop with h | h | h <;> change g.op=_ at h <;> simp [h,GateOp.eval]

lemma free_not_paid_bound (F : (Fin 10 → Bool) → Bool)
    (lower : ∀ D : Circuit,FanInTwo D → circuitFun 10 D=F →
      16≤D.gates.countP (fun g => !g.op.eval [false]))
    (C : Circuit) (hC : FanInTwo C) (hsize : C.size≤18)
    (hfun : ∀ x : Fin 10 → Bool,C.eval (List.ofFn x++[!x 0])=F x) :
    paidNotCount C≤2 := by
  have hD : circuitFun 10 (prependNot C)=F := by
    funext x
    exact (prependNot_eval C x).trans (hfun x)
  have hl := lower (prependNot C) (prependNot_fanInTwo C hC) hD
  rw [prependNot_nonNotCount] at hl
  have hpartition := nonNot_add_paidNot C
  omega

end PEqualNP.Outside.L_meta_1884

namespace PEqualNP.Outside.L_meta_1884
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
lemma free_not_paid_one_from_lower
    (hfloor : PEqualNP.Outside.L_meta_6581.Lower true
      PEqualNP.Outside.L_meta_6581.inputs PEqualNP.Outside.L_meta_6581.graph 15)
    (C : Circuit) (hC : FanInTwo C) (hsize : C.size≤18)
    (hfun : ∀ x : Fin 10 → Bool,C.eval (List.ofFn x++[!x 0])=
      PEqualNP.Outside.L_meta_6581.Extended.f10 x) :
    C.gates.countP (fun g => match g.op with | .not => true | _ => false)≤1 := by
  have hD : ∀ x : Fin 10 → Bool,(prependNot C).eval (List.ofFn x)=
      PEqualNP.Outside.L_meta_6581.Extended.f10 x := by
    intro x
    exact (prependNot_eval C x).trans (hfun x)
  have hlegal := prependNot_fanInTwo C hC
  have hl := PEqualNP.Outside.L_meta_6581.circuit_nonNot_seventeen1884
    hfloor (prependNot C) hlegal hD
  have countEq : (prependNot C).gates.countP
      (fun g => !PEqualNP.Outside.L_meta_6581.Extended.isNot g)=
      (prependNot C).gates.countP (fun g => !g.op.eval [false]) := by
    apply List.countP_congr
    intro g hg
    obtain ⟨op,ins⟩ := g
    have hop := (hlegal _ hg).1
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hop
    rcases hop with (h | h | h) <;> change op = _ at h <;> subst op <;> rfl
  rw [countEq,prependNot_nonNotCount] at hl
  have hp := nonNot_add_paidNot C
  have hn : paidNotCount C≤1 := by omega
  rwa [paidNotCount_eq C hC] at hn
end PEqualNP.Outside.L_meta_1884
