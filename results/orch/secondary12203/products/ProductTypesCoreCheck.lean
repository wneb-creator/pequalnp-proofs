
namespace PEqualNP.Outside.L_meta_670
abbrev Sig := Nat
abbrev Row := Nat
def bit (r : Row) (a : Sig) := a.testBit r
noncomputable def KWRooms (S : List Sig) (T : Sig) :=
  { owns : Sig → Row → Row → Prop //
    (∀ p n, bit p T=true → bit n T=false → ∃ v, owns v p n) ∧
    (∀ {v p n}, owns v p n → v∈S ∧ bit p v=true ∧ bit n v=false) ∧
    (∀ {v w p n}, owns v p n → owns w p n → v=w) ∧
    (∀ {v p n p' n'}, owns v p n' → owns v p' n → owns v p n) }
abbrev KWRooms.owns {S T} (D : KWRooms S T) := D.val
abbrev KWRooms.total {S T} (D : KWRooms S T) :
    ∀ p n, bit p T=true → bit n T=false → ∃ v, D.owns v p n := D.property.1
abbrev KWRooms.valid {S T} (D : KWRooms S T) :
    ∀ {v p n}, D.owns v p n → v∈S ∧ bit p v=true ∧ bit n v=false := D.property.2.1
abbrev KWRooms.unique {S T} (D : KWRooms S T) :
    ∀ {v w p n}, D.owns v p n → D.owns w p n → v=w := D.property.2.2.1
abbrev KWRooms.rect {S T} (D : KWRooms S T) :
    ∀ {v p n p' n'}, D.owns v p n' → D.owns v p' n → D.owns v p n := D.property.2.2.2
noncomputable def KWRooms.mk {S T} (owns : Sig → Row → Row → Prop)
    (total : ∀ p n, bit p T=true → bit n T=false → ∃ v, owns v p n)
    (valid : ∀ {v p n}, owns v p n → v∈S ∧ bit p v=true ∧ bit n v=false)
    (unique : ∀ {v w p n}, owns v p n → owns w p n → v=w)
    (rect : ∀ {v p n p' n'}, owns v p n' → owns v p' n → owns v p n) : KWRooms S T :=
  ⟨owns,total,valid,unique,rect⟩

noncomputable def FreeRooms (S : List Sig) (T H : Sig) :=
  { owns : Sig → Row → Row → Prop //
    (∀ p n, bit p T=true → bit n T=false →
      (bit p H=true ∧ bit n H=false) ∨ ∃ v, owns v p n) ∧
    (∀ {v p n}, owns v p n → v∈S ∧ bit p v=true ∧ bit n v=false) ∧
    (∀ {v w p n}, owns v p n → owns w p n → v=w) ∧
    (∀ {v p n p' n'}, owns v p n' → owns v p' n → owns v p n) }
abbrev FreeRooms.owns {S T H} (D : FreeRooms S T H) := D.val
abbrev FreeRooms.total {S T H} (D : FreeRooms S T H) :
    ∀ p n, bit p T=true → bit n T=false → (bit p H=true ∧ bit n H=false) ∨ ∃ v, D.owns v p n := D.property.1
abbrev FreeRooms.valid {S T H} (D : FreeRooms S T H) :
    ∀ {v p n}, D.owns v p n → v∈S ∧ bit p v=true ∧ bit n v=false := D.property.2.1
abbrev FreeRooms.unique {S T H} (D : FreeRooms S T H) :
    ∀ {v w p n}, D.owns v p n → D.owns w p n → v=w := D.property.2.2.1
abbrev FreeRooms.rect {S T H} (D : FreeRooms S T H) :
    ∀ {v p n p' n'}, D.owns v p n' → D.owns v p' n → D.owns v p n := D.property.2.2.2
noncomputable def FreeRooms.mk {S T H} (owns : Sig → Row → Row → Prop)
    (total : ∀ p n, bit p T=true → bit n T=false → (bit p H=true ∧ bit n H=false) ∨ ∃ v, owns v p n)
    (valid : ∀ {v p n}, owns v p n → v∈S ∧ bit p v=true ∧ bit n v=false)
    (unique : ∀ {v w p n}, owns v p n → owns w p n → v=w)
    (rect : ∀ {v p n p' n'}, owns v p n' → owns v p' n → owns v p n) : FreeRooms S T H :=
  ⟨owns,total,valid,unique,rect⟩

noncomputable def SingleFactor (S : List Sig) (T : Sig) :=
  Σ inner : List Sig, Σ outer : List Sig, Σ pivot : Sig,
    { pair : KWRooms inner pivot × FreeRooms outer T pivot //
      inner ++ outer = S ∧ (∀ v, ¬ (v ∈ inner ∧ v ∈ outer)) }
abbrev SingleFactor.inner {S T} (D : SingleFactor S T) := D.1
abbrev SingleFactor.outer {S T} (D : SingleFactor S T) := D.2.1
abbrev SingleFactor.pivot {S T} (D : SingleFactor S T) := D.2.2.1
abbrev SingleFactor.cover {S T} (D : SingleFactor S T) := D.2.2.2.property.1
abbrev SingleFactor.apart {S T} (D : SingleFactor S T) := D.2.2.2.property.2
abbrev SingleFactor.inside {S T} (D : SingleFactor S T) := D.2.2.2.val.1
abbrev SingleFactor.outside {S T} (D : SingleFactor S T) := D.2.2.2.val.2
noncomputable def SingleFactor.mk {S T} (inner outer : List Sig) (pivot : Sig)
    (cover : inner ++ outer = S) (apart : (∀ v, ¬ (v ∈ inner ∧ v ∈ outer)))
    (inside : KWRooms inner pivot) (outside : FreeRooms outer T pivot) :
    SingleFactor S T := ⟨inner,outer,pivot,⟨(inside,outside),cover,apart⟩⟩

abbrev PanelTag := Nat × Nat × Nat
def onlyWire (S : List Sig) (T v : Sig) (p n : Row) :=
  bit p T=true ∧ bit n T=false ∧ ∀ w∈S, bit p w=true → bit n w=false → w=v
def panelClosed (arity : Nat) (tags : List PanelTag) : Prop :=
  ∀ {S T}, (F : SingleFactor S T) → (w : Nat → Sig) → (p n : Nat → Row) →
    (∀ i<arity, w i∈S) → (∀ i<arity, ∀ j<arity, i≠j → w i≠w j) →
    (∀ t∈tags, onlyWire S T (w t.1) (p t.2.1) (n t.2.2)) → False
noncomputable def PanelProof := Σ arity : Nat, { tags : List PanelTag // panelClosed arity tags }
abbrev PanelProof.arity (p : PanelProof) := p.1
abbrev PanelProof.tags (p : PanelProof) := p.2.val
abbrev PanelProof.closed (p : PanelProof) : panelClosed p.arity p.tags := p.2.property

theorem kwOwns {S T} (owns) (total) (valid) (unique) (rect) :
    (KWRooms.mk (S:=S) (T:=T) owns total valid unique rect).owns = owns := rfl

theorem frOwns {S T H} (owns) (total) (valid) (unique) (rect) :
    (FreeRooms.mk (S:=S) (T:=T) (H:=H) owns total valid unique rect).owns = owns := rfl

theorem sfInner {S T} (inner) (outer) (pivot) (cover) (apart) (inside) (outside) :
    (SingleFactor.mk (S:=S) (T:=T) inner outer pivot cover apart inside outside).inner = inner := rfl

theorem panelArity (n : Nat) (tags : List PanelTag) (h : panelClosed n tags) :
    (show PanelProof from ⟨n,⟨tags,h⟩⟩).arity = n := rfl

end PEqualNP.Outside.L_meta_670
