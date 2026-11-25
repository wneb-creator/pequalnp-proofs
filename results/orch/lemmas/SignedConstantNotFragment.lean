
namespace PEqualNP.Outside.L_meta_2592.Signed.Extended
open PEqualNP.CircuitLowerBounds

def constantNegations : List Gate → List Sig → Prop
  | [], _ => True
  | g :: gs, w => (isNot g = true → gv w g = zero ∨ gv w g = one) ∧
      constantNegations gs (w ++ [gv w g])

lemma constantNegations_mono (gs : List Gate) (w : List Sig)
    (mono : ∀ g ∈ gs, isNot g = false) : constantNegations gs w := by
  induction gs generalizing w with
  | nil => trivial
  | cons g gs ih =>
    refine ⟨?_, ih _ (fun a ha => mono a (by simp [ha]))⟩
    intro hn
    rw [mono g (by simp)] at hn
    contradiction

lemma constantNegations_append (gs hs : List Gate) (w : List Sig) :
    constantNegations (gs ++ hs) w ↔
      constantNegations gs w ∧ constantNegations hs (execute gs w) := by
  induction gs generalizing w with
  | nil => simp [constantNegations, execute]
  | cons g gs ih => simp only [List.cons_append, constantNegations, execute, List.foldl_cons, ih, and_assoc]

lemma gate_rep_constant_not (w : List Sig) (g : Gate)
    (legal : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (constant : isNot g = true → gv w g = zero ∨ gv w g = one) :
    Repr false (w.map (nrm false)) (gv w g) ∨
      (isNot g = false ∧ witness false (w.map (nrm false)) (nrm false (gv w g))) := by
  cases hn : isNot g with
  | false => simpa only [hn] using gate_rep false w g legal (fun _ => hn)
  | true => exact Or.inl (repr_const (constant hn))

lemma extract_constant_not {target} (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (constant : constantNegations gs w)
    (hp : proper target) (hout : target ∈ (execute gs w).map (nrm false)) :
    ∃ k S, k ≤ gs.countP (fun g => !isNot g) ∧ Live false target k S ∧
      ∀ a ∈ S, a ∈ w.map (nrm false) := by
  induction gs generalizing w with
  | nil => exact ⟨0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,S,hk,ht,hs⟩ := ih (w ++ [gv w g]) (fun a ha => legal a (by simp [ha]))
      constant.2 hout
    have rep := gate_rep_constant_not w g (legal g (by simp)) constant.1
    rw [List.map_append] at hs
    have rep' : represented (w.map (nrm false)) (nrm false (gv w g)) ∨
        ((if isNot g then 0 else 1)=1 ∧ witness false (w.map (nrm false)) (nrm false (gv w g))) :=
      rep.imp id (fun h => ⟨by simp [h.1],h.2⟩)
    obtain ⟨l,T,hl,hu,hT⟩ := pull_gate ht rep' hs
    refine ⟨l,T,?_,hu,hT⟩
    rw [List.countP_cons]
    cases hn : isNot g <;> simp [hn] at hl ⊢ <;> omega

end PEqualNP.Outside.L_meta_2592.Signed.Extended
