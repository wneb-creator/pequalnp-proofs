import UniqueReader
import SoleReaderFree
import PairLocalization

namespace PEqualNP.Outside.L_meta_1884.TwoRailReaders

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open SoleReader ElimManyCount SoleOrPartner

def seed (x : Fin 10 → Bool) : List Bool := List.ofFn x ++ [!x 0]

def agree (w z : List Bool) : Prop :=
  w.length = z.length ∧ 11 ≤ w.length ∧
    ∀ i,i ≠ 0 → i ≠ 10 → w.getD i false = z.getD i false

lemma append_agree {w z : List Bool} {a b : Bool} (h : agree w z) (hab : a=b) :
    agree (w++[a]) (z++[b]) := by
  have hwlen := h.2.1
  refine ⟨by simp [h.1],by simp;omega,?_⟩
  intro i hi0 hi10
  by_cases hi : i < w.length
  · rw [List.getD_append _ _ _ _ hi,List.getD_append _ _ _ _ (h.1 ▸ hi)]
    exact h.2.2 i hi0 hi10
  · by_cases he : i = w.length
    · subst i
      simpa [List.getD_eq_getElem?_getD,h.1] using hab
    · rw [List.getD_eq_default _ _ (by simp;omega),
        List.getD_eq_default _ _ (by simp [←h.1];omega)]

lemma both_inputs (ins : List Nat) (hlen : ins.length ≤ 2)
    (h0 : 0 ∈ ins) (h10 : 10 ∈ ins) : ins=[0,10] ∨ ins=[10,0] := by
  rcases ins with _ | ⟨a,_ | ⟨b,l⟩⟩
  · simp at h0
  · simp only [List.mem_singleton] at h0 h10
    omega
  · have hl : l=[] := by
      cases l with
      | nil => rfl
      | cons c cs => simp at hlen
    subst l
    simp only [List.mem_cons,List.mem_singleton] at h0 h10
    rcases h0 with h0 | h0 <;> rcases h10 with h10 | h10 <;> simp_all <;> omega

lemma gate_agree (g : Gate) (legal : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧
    g.inputs.length ≤ 2) (trim : g.op=.not → g.inputs.length≤1)
    (coupled : 0 ∈ g.inputs ↔ 10 ∈ g.inputs)
    (w z : List Bool) (h : agree w z)
    (hw : w.getD 10 false = !w.getD 0 false)
    (hz : z.getD 10 false = !z.getD 0 false) :
    g.op.eval (g.inputs.map fun i=>w.getD i false) =
      g.op.eval (g.inputs.map fun i=>z.getD i false) := by
  by_cases h0 : 0 ∈ g.inputs
  · have h10 := coupled.mp h0
    have hins := both_inputs g.inputs legal.2 h0 h10
    have hop : g.op=.and ∨ g.op=.or := by
      have ht : g.op=.and ∨ g.op=.or ∨ g.op=.not := by simpa using legal.1
      rcases ht with ht | ht | ht
      · exact Or.inl ht
      · exact Or.inr ht
      · have hb := trim ht
        rcases hins with he | he <;> simp [he] at hb
    rcases hop with hop | hop <;> rcases hins with hins | hins <;>
      simp only [hop,hins,GateOp.eval,List.map_cons,List.map_nil,List.all_cons,
        List.all_nil,List.any_cons,List.any_nil,id,Bool.and_true,Bool.or_false] <;>
      rw [hw,hz] <;> simp
  · have h10 : 10 ∉ g.inputs := fun hm=>h0 (coupled.mpr hm)
    congr 1
    apply List.map_congr_left
    intro i hi
    exact h.2.2 i (fun he=>h0 (he ▸ hi)) (fun he=>h10 (he ▸ hi))

lemma run_agree (gs : List Gate) (w z : List Bool) (h : agree w z)
    (hw : w.getD 10 false = !w.getD 0 false)
    (hz : z.getD 10 false = !z.getD 0 false)
    (legal : ∀ g ∈ gs,g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (trim : ∀ g ∈ gs,g.op=.not → g.inputs.length≤1)
    (coupled : ∀ g ∈ gs,0 ∈ g.inputs ↔ 10 ∈ g.inputs) :
    agree (run gs w) (run gs z) := by
  induction gs generalizing w z with
  | nil => exact h
  | cons g gs ih =>
    have hwlen := h.2.1
    have hzlen : 11≤z.length := h.1 ▸ hwlen
    apply ih (step w g) (step z g)
    · exact append_agree h (gate_agree g (legal g (by simp)) (trim g (by simp))
        (coupled g (by simp)) w z h hw hz)
    · simpa only [step,List.getD_append _ _ _ _ (show 10<w.length by omega),
        List.getD_append _ _ _ _ (show 0<w.length by omega)] using hw
    · simpa only [step,List.getD_append _ _ _ _ (show 10<z.length by omega),
        List.getD_append _ _ _ _ (show 0<z.length by omega)] using hz
    · exact fun g' hg'=>legal g' (by simp [hg'])
    · exact fun g' hg'=>trim g' (by simp [hg'])
    · exact fun g' hg'=>coupled g' (by simp [hg'])

lemma output_not_positive (C : Circuit)
    (correct : ∀ x : Fin 10 → Bool,C.eval (seed x)=target x) : C.output ≠ 0 := by
  intro hout
  have h := correct (singleton 0)
  change (run C.gates (seed (singleton 0))).getD C.output false = _ at h
  rw [hout,SoleReader.run_input _ _ _ (by simp [seed])] at h
  change true=false at h
  cases h

lemma output_not_negative (C : Circuit)
    (correct : ∀ x : Fin 10 → Bool,C.eval (seed x)=target x) : C.output ≠ 10 := by
  intro hout
  have h := correct (fun _=>false)
  change (run C.gates (seed (fun _=>false))).getD C.output false = _ at h
  rw [hout,SoleReader.run_input _ _ _ (by simp [seed])] at h
  change true=false at h
  cases h

lemma seed_agree : agree (seed (singleton 1)) (seed (pair 0 1)) := by
  refine ⟨rfl,by decide,?_⟩
  intro i hi0 hi10
  by_cases hi : i<11
  · interval_cases i <;> simp_all [seed,SoleOrPartner.singleton,pair,List.getD_eq_getElem?_getD]
  · rw [List.getD_eq_default _ _ (by simp [seed];omega),
      List.getD_eq_default _ _ (by simp [seed];omega)]

lemma coupled_impossible (C : Circuit) (legal : FanInTwo C)
    (trim : ∀ g ∈ C.gates,g.op=.not → g.inputs.length≤1)
    (correct : ∀ x : Fin 10 → Bool,C.eval (seed x)=target x)
    (coupled : ∀ g ∈ C.gates,0 ∈ g.inputs ↔ 10 ∈ g.inputs) : False := by
  have h := run_agree C.gates _ _ seed_agree (by decide) (by decide) legal trim coupled
  have he := h.2.2 C.output (output_not_positive C correct) (output_not_negative C correct)
  change C.eval (seed (singleton 1))=C.eval (seed (pair 0 1)) at he
  rw [correct,correct] at he
  change false=true at he
  cases he

lemma reader_iff (g : Gate) : reads Forced13Compile.rails g = true ↔
    0 ∈ g.inputs ∨ 10 ∈ g.inputs := by
  simp only [reads,List.any_eq_true]
  constructor
  · rintro ⟨i,hi,hr⟩
    have hm : i=0 ∨ i=10 := by simpa [Forced13Compile.rails] using of_decide_eq_true hr
    rcases hm with rfl | rfl
    · exact Or.inl hi
    · exact Or.inr hi
  · intro hr
    rcases hr with hr | hr
    · exact ⟨0,hr,by decide⟩
    · exact ⟨10,hr,by decide⟩

lemma sole_contains (pre post : List Gate) (g : Gate) (k : Nat) (hk : k=0 ∨ k=10)
    (hpre : ∀ g' ∈ pre,reads Forced13Compile.rails g'=false)
    (hpost : ∀ g' ∈ post,reads Forced13Compile.rails g'=false)
    (used : ∃ g' ∈ pre++g::post,k ∈ g'.inputs) : k ∈ g.inputs := by
  obtain ⟨g',hg',hin⟩ := used
  have hr : reads Forced13Compile.rails g'=true := (reader_iff g').mpr (by
    rcases hk with rfl | rfl
    · exact Or.inl hin
    · exact Or.inr hin)
  rcases List.mem_append.mp hg' with hg' | hg'
  · rw [hpre g' hg'] at hr
    cases hr
  · rcases List.mem_cons.mp hg' with rfl | hg'
    · exact hin
    · rw [hpost g' hg'] at hr
      cases hr

theorem at_least_two (C : Circuit) (legal : FanInTwo C)
    (trim : ∀ g ∈ C.gates,g.op=.not → g.inputs.length≤1)
    (correct : ∀ x : Fin 10 → Bool,C.eval (seed x)=target x)
    (used0 : ∃ g ∈ C.gates,0 ∈ g.inputs)
    (used10 : ∃ g ∈ C.gates,10 ∈ g.inputs) :
    2 ≤ C.gates.countP (reads Forced13Compile.rails) := by
  by_contra! hsmall
  have hs : C.gates.countP (reads Forced13Compile.rails) ≤ 1 := by omega
  obtain ⟨g,hg,h0⟩ := used0
  obtain ⟨pre,g,post,he,hr,hpre,hpost⟩ := UniqueReader.split_one
    (reads Forced13Compile.rails) C.gates hs ⟨g,hg,(reader_iff g).mpr (Or.inl h0)⟩
  have h0' : 0 ∈ g.inputs := sole_contains pre post g 0 (Or.inl rfl) hpre hpost
    (by rw [←he];exact ⟨_,hg,h0⟩)
  have h10' : 10 ∈ g.inputs := sole_contains pre post g 10 (Or.inr rfl) hpre hpost
    (by rw [←he];exact used10)
  apply coupled_impossible C legal trim correct
  intro g' hg'
  rw [he] at hg'
  have away (hread : reads Forced13Compile.rails g'=false) :
      0 ∈ g'.inputs ↔ 10 ∈ g'.inputs := by
    constructor <;> intro hin
    · have ht := (reader_iff g').mpr (Or.inl hin)
      rw [hread] at ht
      cases ht
    · have ht := (reader_iff g').mpr (Or.inr hin)
      rw [hread] at ht
      cases ht
  rcases List.mem_append.mp hg' with hg' | hg'
  · exact away (hpre g' hg')
  · rcases List.mem_cons.mp hg' with rfl | hg'
    · exact iff_of_true h0' h10'
    · exact away (hpost g' hg')

end PEqualNP.Outside.L_meta_1884.TwoRailReaders
