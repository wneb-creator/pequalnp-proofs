namespace PEqualNP.Outside.L_meta_670_aux.CheapPrefix

open LiveCheck DynamicLeaf PEqualNP.CircuitLowerBounds

def required (initial ps : List Base1007.Sig) : Nat :=
  ((ps.filter fun z => !(ProjectionCertificate.cachedConstant z) &&
    !(initial.contains z)).eraseDups).length

def precheck (initial : List Base1007.Sig) (budget k : Nat)
    (ps : List Base1007.Sig) : Bool :=
  let available := budget + ProjectionCertificate.cachedConstants ps
  decide (k ≤ available) && decide (required initial ps + k ≤ available)

def wrap (initial : List Base1007.Sig) (budget : Nat) (o : Oracle) : Oracle where
  project := o.project
  mapNeg := o.mapNeg
  mapBin := o.mapBin
  inputs := o.inputs
  check := fun k gs ps => precheck initial budget k ps && o.check k gs ps

lemma wrap_sound (initial : List Base1007.Sig) (budget : Nat) (o : Oracle)
    (hs : o.Sound) : (wrap initial budget o).Sound := by
  intro k t v gs ps hv hp hc
  have hh : precheck initial budget k ps = true ∧ o.check k gs ps = true := by
    simpa only [wrap,Bool.and_eq_true] using hc
  exact @hs k t v gs ps hv hp hh.2

def oracles (q : Fin 12) : Oracle :=
  wrap (ClosedDomains12.initial q) (ProjectionDomains.budget q) (ClosedDomains12.oracles q)

lemma oracles_sound
    (hbase : ∀ q : Fin 12, ∀ m ≤ ProjectionDomains.budget q, ∀ t T,
      T ⊆ (ClosedDomains12.initial q).toFinset → ¬ Base1007.Live m t T)
    (q : Fin 12) : (oracles q).Sound :=
  @wrap_sound _ _ _ (@ClosedDomains12.oracles_sound hbase q)

lemma project_target (q : Fin 12) : (oracles q).project target = Base1007.target :=
  ProjectionDomains.project_target q

lemma cachedRaw_correct (q : Fin 12) (i : Fin 9) :
    CachedProjection.cachedRaw q i = (oracles q).project
      (raw.getD i.val zero) := ClosedDomains12.cachedRaw_correct q i

end PEqualNP.Outside.L_meta_670_aux.CheapPrefix
