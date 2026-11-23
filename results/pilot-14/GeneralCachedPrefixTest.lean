import DynamicBase
namespace PEqualNP.Outside.L_meta_670_aux.Base1007

lemma live_proper {k t S} (h : Live k t S) : ∀ a ∈ S, proper a := by
  induction h with
  | stop =>
      have ht : proper target := by unfold proper target zero one top; decide
      simpa using ht
  | unary ha hf _ ih =>
      simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
      simp only [Finset.forall_mem_insert]
      exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

end PEqualNP.Outside.L_meta_670_aux.Base1007
namespace PEqualNP.Outside.L_meta_670_aux.Projection

open Base1007 PEqualNP.CircuitLowerBounds

lemma prefix_pull_from {p : LiveCheck.Sig → Base1007.Sig}
    (initial : List Base1007.Sig) (gs : List Gate)
    (legal : ∀ g ∈ gs,
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    {q : Nat} {S : Finset LiveCheck.Sig}
    (hcover : ∀ a ∈ S, Base1007.proper (p a) →
      p a ∈ Base1007.execute gs (initial ++ [Base1007.zero, Base1007.one]))
    (hf : Feasible p q S) :
    ∃ m ≤ q + gs.length, ∃ t T, Base1007.Live m t T ∧ T ⊆ initial.toFinset := by
  obtain ⟨m,hm,t,T,hl,hT⟩ := hf
  have hsub : ∀ a ∈ T,
      a ∈ Base1007.execute gs (initial ++ [Base1007.zero, Base1007.one]) := by
    intro a ha
    obtain ⟨b,hb,he⟩ := Finset.mem_image.mp (hT ha)
    subst a
    exact hcover b hb (Base1007.live_proper hl _ ha)
  obtain ⟨m',t',T',hm',hl',hT'⟩ :=
    old_extract_from gs (initial ++ [Base1007.zero, Base1007.one]) legal hl hsub
  refine ⟨m',by omega,t',T',hl',?_⟩
  intro a ha
  have hm := hT' a ha
  have hp := Base1007.live_proper hl' a ha
  apply List.mem_toFinset.mpr
  simpa only [List.mem_append, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, hp.1, hp.2, or_false] using hm

lemma exclude_by_prefix_from {p : LiveCheck.Sig → Base1007.Sig}
    (pt : p LiveCheck.target = Base1007.target)
    (pn : ∀ a, p (LiveCheck.neg a) = Base1007.neg (p a))
    (pb : ∀ d a b, p (LiveCheck.bin d a b) = Base1007.bin d (p a) (p b))
    (initial : List Base1007.Sig) (gs : List Gate)
    (legal : ∀ g ∈ gs,
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    {k t budget : Nat} {S : Finset LiveCheck.Sig}
    (hcover : ∀ a ∈ S, Base1007.proper (p a) →
      p a ∈ Base1007.execute gs (initial ++ [Base1007.zero, Base1007.one]))
    (hbase : ∀ m ≤ budget, ∀ u T, T ⊆ initial.toFinset → ¬ Base1007.Live m u T)
    (hcost : gs.length + k ≤ budget + constantCount p S) :
    ¬ LiveCheck.Live k t S := by
  intro h
  obtain ⟨q,hq,hf⟩ := feasible_count pt pn pb h
  obtain ⟨m,hm,u,T,hl,hT⟩ := prefix_pull_from initial gs legal hcover hf
  exact hbase m (by omega) u T hT hl

end PEqualNP.Outside.L_meta_670_aux.Projection
namespace PEqualNP.Outside.L_meta_670_aux.ProjectionCertificate

open PEqualNP.CircuitLowerBounds
open Projection ProjectionData

def cachedConstant (z : Base1007.Sig) : Bool :=
  z == Base1007.zero || z == Base1007.one

def cachedConstants (ps : List Base1007.Sig) : Nat := ps.countP cachedConstant

def coversCached (gs : List Gate) (ps : List Base1007.Sig) : Bool :=
  let w := Base1007.execute gs prefixInputs
  ps.all fun z => cachedConstant z || w.contains z

def fastCachedCheck (k : Nat) (gs : List Gate) (ps : List Base1007.Sig) : Bool :=
  decide (gs.length + k ≤ 12 + cachedConstants ps) &&
    legalPrefix gs && coversCached gs ps

lemma cachedConstants_map {p : LiveCheck.Sig → Base1007.Sig}
    {v : List LiveCheck.Sig} (hv : v.Nodup) :
    constantCount p v.toFinset = cachedConstants (v.map p) := by
  unfold constantCount constantSignals cachedConstants
  rw [hv.card_eq_countP, List.countP_map]
  congr 1

lemma coversCached_map (i : Fin 3) (gs : List Gate) (v : List LiveCheck.Sig) :
    coversCached gs (v.map (project i)) = coversPrefix i gs v := by
  simp only [coversCached, coversPrefix, cachedConstant, List.all_map,
    Function.comp_def]

lemma fastCachedCheck_eq {i : Fin 3} {k : Nat} {gs : List Gate}
    {v : List LiveCheck.Sig} {ps : List Base1007.Sig}
    (hv : v.Nodup) (hp : ps = v.map (project i)) :
    fastCachedCheck k gs ps = prefixCheck i k gs v := by
  subst ps
  simp only [fastCachedCheck, prefixCheck, coversCached_map,
    cachedConstants_map hv, Bool.and_assoc, Bool.and_comm]

lemma fastCachedCheck_sound {i : Fin 3} {k : Nat} {gs : List Gate}
    {v : List LiveCheck.Sig} {ps : List Base1007.Sig}
    (hbase : ∀ m ≤ 12, ∀ u, ¬ Base1007.Live m u Base1007.raw.toFinset)
    (hv : v.Nodup) (hp : ps = v.map (project i))
    (hc : fastCachedCheck k gs ps = true) :
    ∀ m ≤ k, ∀ t, ¬ LiveCheck.Live m t v.toFinset := by
  rw [fastCachedCheck_eq hv hp] at hc
  exact prefixCheck_sound hbase hc

end PEqualNP.Outside.L_meta_670_aux.ProjectionCertificate
namespace PEqualNP.Outside.L_meta_670_aux.ProjectionCertificate

open PEqualNP.CircuitLowerBounds
open Projection

def coversCachedFrom (initial : List Base1007.Sig) (gs : List Gate)
    (ps : List Base1007.Sig) : Bool :=
  let w := Base1007.execute gs (initial ++ [Base1007.zero, Base1007.one])
  ps.all fun z => cachedConstant z || w.contains z

def fastCachedCheckFrom (initial : List Base1007.Sig) (budget k : Nat)
    (gs : List Gate) (ps : List Base1007.Sig) : Bool :=
  decide (gs.length + k ≤ budget + cachedConstants ps) &&
    legalPrefix gs && coversCachedFrom initial gs ps

lemma coversCachedFrom_sound {p : LiveCheck.Sig → Base1007.Sig}
    {initial : List Base1007.Sig} {gs : List Gate}
    {v : List LiveCheck.Sig} {ps : List Base1007.Sig}
    (hp : ps = v.map p) (hc : coversCachedFrom initial gs ps = true) :
    ∀ a ∈ v.toFinset, Base1007.proper (p a) →
      p a ∈ Base1007.execute gs (initial ++ [Base1007.zero, Base1007.one]) := by
  intro a ha hproper
  have hm : p a ∈ ps := by
    rw [hp]
    exact List.mem_map.mpr ⟨a, List.mem_toFinset.mp ha, rfl⟩
  have hh := List.all_eq_true.mp hc (p a) hm
  simp only [cachedConstant, Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] at hh
  exact hh.resolve_left (by simpa only [Base1007.proper, not_or] using hproper)

lemma fastCachedCheckFrom_sound {p : LiveCheck.Sig → Base1007.Sig}
    (pt : p LiveCheck.target = Base1007.target)
    (pn : ∀ a, p (LiveCheck.neg a) = Base1007.neg (p a))
    (pb : ∀ d a b, p (LiveCheck.bin d a b) = Base1007.bin d (p a) (p b))
    {initial : List Base1007.Sig} {budget k : Nat} {gs : List Gate}
    {v : List LiveCheck.Sig} {ps : List Base1007.Sig}
    (hbase : ∀ m ≤ budget, ∀ u T, T ⊆ initial.toFinset → ¬ Base1007.Live m u T)
    (hv : v.Nodup) (hp : ps = v.map p)
    (hc : fastCachedCheckFrom initial budget k gs ps = true) :
    ∀ m ≤ k, ∀ t, ¬ LiveCheck.Live m t v.toFinset := by
  have hchecks : (gs.length + k ≤ budget + cachedConstants ps ∧
      legalPrefix gs = true) ∧ coversCachedFrom initial gs ps = true := by
    simpa only [fastCachedCheckFrom, Bool.and_eq_true, decide_eq_true_eq] using hc
  have hcount : constantCount p v.toFinset = cachedConstants ps := by
    rw [hp, cachedConstants_map hv]
  intro m hm t
  apply exclude_by_prefix_from pt pn pb initial gs
    (legalPrefix_sound hchecks.1.2) (coversCachedFrom_sound hp hchecks.2) hbase
  omega

end PEqualNP.Outside.L_meta_670_aux.ProjectionCertificate
