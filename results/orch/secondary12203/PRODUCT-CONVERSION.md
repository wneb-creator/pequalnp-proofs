Static preparation only; no build has been run for this conversion.

The four custom structures can be eliminated without weakening their data or proof fields. Keep the four existing type names as aliases of Subtype/Sigma, and retain their field API through helpers under the corresponding type namespace. This avoids changing the many downstream statements that use H.owns, H.total, F.inside, and pc.tags.

Suggested representations:

- KWRooms S T: the subtype of relations owns : Sig → Row → Row → Prop satisfying the conjunction total ∧ valid ∧ unique ∧ rect, with exactly the original quantified field propositions.
- FreeRooms S T H: the analogous relation subtype, with its original relaxed total proposition.
- SingleFactor S T: Σ inner : Finset Sig, Σ outer : Finset Sig, Σ pivot : Sig, { pair : KWRooms inner pivot × FreeRooms outer T pivot // inner ∪ outer = S ∧ Disjoint inner outer }.
- PanelProof: Σ arity : Nat, { tags : List PanelTag // panelClosed arity tags }.

Projection helpers can be abbreviations, preserving reducibility. KWRooms.owns is Subtype.val, its four proof projections select the appropriate conjunct; FreeRooms is identical. SingleFactor.inner/outer/pivot select the three Sigma components, inside/outside select the pair in the final subtype, and cover/apart select its proof conjunction. PanelProof.arity/tags/closed select the Sigma/subtype fields.

Provide explicit KWRooms.mk, FreeRooms.mk, and SingleFactor.mk helper functions with the original constructor argument order. This retains the original proof-goal order when changing record refinements to these helper calls.

Constructor inventory in original PR12203 source:

- kwLeaf (line3408): record-style definition; change to KWRooms.mk with the five existing fields.
- kwFork (line3415, refinement3433): replace the record refinement by KWRooms.mk applied to the owns relation and four existing proof holes.
- freeFrom (line3548): record-style definition; change to FreeRooms.mk.
- freeHide (line3555): record-style definition; change to FreeRooms.mk.
- factorOfTree (line3570): record-style definition; change to SingleFactor.mk.
- freeFork (line3584, refinement3602): change record refinement to FreeRooms.mk.
- factorExpand (line3677): its two SingleFactor constructor expressions need explicit SingleFactor.mk calls.
- factorKeep (line3697): its SingleFactor construction needs the same explicit helper.
- panelAt (line4171): the existing flattened three-entry angle constructors should fit the nested Sigma/subtype representation directly; confirm in Lean.

The source has no explicit KWRooms.rec, FreeRooms.rec, SingleFactor.rec, or PanelProof.rec usage. Most downstream proofs use field projections rather than cases on these structures, so the above changes should stay local. Definitional reduction and field-notation elaboration still require validation; this is a plan, not a checked transformation.

The saved noncomputable candidate has6317bytes headroom. Projection/constructor helpers may use most of that, so additional own-identifier shortening may be needed. Do not change the exact final theorem or any certificate data to make space. Full build plus checker are required before this variant is publishable.
