namespace PEqualNP.Outside.L_meta_670_aux.Cut12StrictReplay

open LiveCheck

def signal (i : Nat) : Sig := recipeValue sourceSignals (Cut12Data.wireRecipe i)

def state (_ _ j : Nat) : List Sig := (Cut12Data.wireIds j).map signal

def hint (_ _ j : Nat) : Sig → Nat :=
  MetadataStrictEdges.listHint (state 0 0 j) ((Cut12Data.wireIds j).map Cut12Data.wireRecipe)

def count (k t : Nat) : Nat :=
  if 12 ≤ k ∧ k ≤ 15 ∧ t ≤ k-8 then Cut12Data.rowCount else 0

def rawHashes : Nat := 0x4fc52ac86957602c663ac11e237e558d86e5ba381c99b6113a9819b1e7939325c78120

def word (data bits i : Nat) : Nat := (data >>> (bits*i)) &&& (2^bits-1)

def hashSig (a : Sig) : Nat :=
  (((a.1.toNat % 2147483647)*65537+a.2.toNat % 2147483647+317) % 2147483647)^3 % 2147483647

def hashCodes (g : Fin 12) (codes : List Nat) : Nat :=
  (codes.foldl (fun s code => s +
    if code ≤ 9 then word rawHashes 31 (rawSym g (Fin.ofNat 9 (code-1))).val
    else hashSig (recipeValue (rawImage g) code)) 0) % 2147483647

def canonical (h : Sig → Nat) (v : List Sig) : Nat × Fin 12 :=
  let codes := v.map h
  (List.finRange 12).foldl (fun best g =>
    let value := hashCodes g codes
    if value < best.1 then (value,g) else best) (hashCodes 0 codes,0)

def compositionData : Nat := 0x5127390a864b4036281b975a680a4b271539791b5a36042832450189ba6723541098ab76046382b179a5157293a068b486a0b472519397b1a5634082ab8967452301ba9876543210

def lookup (h : Sig → Nat) (k t : Nat) (v : List Sig) : Nat × Fin 12 :=
  let canon := canonical h v
  let stamp := Cut12Data.lookupStamp k t canon.1
  ((stamp-1)/12,
    Fin.ofNat 12 (word compositionData 4 (12*canon.2.val+(stamp-1) % 12)))

lemma rhoCorrect (q : Fin 12) : CachedProjection.cachedRaw q =
    (ClosedDomains12.oracles q).project ∘ FastRecipe.source := by
  funext i
  exact ClosedDomains12.cachedRaw_correct q i

def programs (h : Sig → Nat) (v : List Sig) (q : Fin 12) :
    List PEqualNP.CircuitLowerBounds.Gate × List Nat :=
  AutoContext.programs (ClosedDomains12.oracles q).inputs (CachedProjection.wireMap q) h v
    (FastRecipe.values (ClosedDomains12.oracles q).project (CachedProjection.cachedRaw q) h v)

def initial (k t j : Nat) : DynamicCovered.CheckedContext ClosedDomains12.oracles (state k t j) :=
  ⟨FastRecipe.initial ClosedDomains12.oracles CachedProjection.cachedRaw (hint k t j)
      (state k t j) (programs (hint k t j) (state k t j)),
    FastRecipe.initial_valid ClosedDomains12.oracles CachedProjection.cachedRaw (hint k t j)
      rhoCorrect (state k t j) (programs (hint k t j) (state k t j))⟩

def config (terminal : Nat → Nat → Nat → List Sig → Bool) : MetadataReplay.Config where
  limit := 7
  count := count
  state := state
  enabled := Cut12Data.enabled
  transport := fun h g v => v.map (recipeAction h g)
  lookup := lookup
  terminal := terminal
  edges := MetadataStrictEdges.edges ClosedDomains12.oracles state initial hint

lemma config_valid
    (hsound : ∀ q, (ClosedDomains12.oracles q).Sound)
    (terminal : Nat → Nat → Nat → List Sig → Bool)
    (hterminal : ∀ k t j v, terminal k t j v = true → Impossible k t v) :
    MetadataReplay.Valid (config terminal) := by
  constructor
  · intro h g k t w z hp hz
    exact rotate_recipe_impossible h g hp hz
  · exact hterminal
  · exact MetadataStrictEdges.edges_cut_sound ClosedDomains12.oracles hsound
      (fun q => ProjectionDomains.project_target q) state initial hint

end PEqualNP.Outside.L_meta_670_aux.Cut12StrictReplay
