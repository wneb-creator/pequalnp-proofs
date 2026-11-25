import PEqualNP.Outside.L_meta_2592
namespace PEqualNP.Outside.L_meta_2592.Signed.Extended
open PEqualNP.CircuitLowerBounds
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]
private lemma live_proper {u target k S} (h : Live u target k S) : ∀ a ∈ S, proper a := by
  induction h using Live.ind with
  | stop hp => simpa using hp
  | binary hd ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma get_rep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact repr_const (Or.inl rfl)
  | some a => exact Or.inl (List.mem_map_of_mem (List.mem_of_getElem? h))

private lemma gate_rep (u : Bool) (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → isNot g=false) :
    Repr u (w.map (nrm u)) (gv w g) ∨ (isNot g=false ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have prim (d : Bool) : Repr u (w.map (nrm u)) ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one)) ∨
      witness u (w.map (nrm u)) (nrm u ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one))) := by
    have unit (v : Sig) : prime d v (if d then zero else one) = v := by
      apply bit_ext
      intro i
      cases d <;> simp [bit_prime,bit_zero,bit_one]
    cases l with
    | nil => exact Or.inl (repr_const (by cases d <;> simp))
    | cons i l =>
      cases l with
      | nil =>
        simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
        exact Or.inl (get_rep w i)
      | cons j l =>
        cases l with
        | cons a l => simp at hl
        | nil =>
          simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
          exact prime_rep d (get_rep w i) (get_rep w j)
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id (fun h => ⟨rfl,h⟩)
  · exact (prim true).imp id (fun h => ⟨rfl,h⟩)
  · cases u
    · exact absurd (mono rfl) (by simp [isNot])
    left
    cases l with
    | nil => exact repr_const (Or.inr (by simp [gv,neg_laws]))
    | cons i l => exact repr_neg (get_rep w i)


private lemma pull_gate {u target} {w : List Sig} {z : Sig} {k S c} (h : Live u target k S)
    (hz : represented w z ∨ (c=1 ∧ witness u w z)) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' S', k' ≤ k+c ∧ Live u target k' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | ⟨rfl,d,a,b,hd,ha,hb,pa,pb,hab,eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live u target k (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,Nat.le_refl _,Live.binary hd pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha



end PEqualNP.Outside.L_meta_2592.Signed.Extended

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
