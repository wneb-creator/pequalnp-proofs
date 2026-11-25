namespace PEqualNP.Outside.L_meta_1886_aux.EndpointOrder

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2592_aux.ConstantSweep
open MapRigidity

def initial (x : Fin 10 → Bool) : List Bool := List.ofFn x ++ [x 0 && x 1]
def low (p : Fin 2) (i : Fin 10) : Bool := decide (i.val = if p.val = 0 then 4 else 2)
def high (p : Fin 2) (i : Fin 10) : Bool := decide (i.val = p.val ∨ i.val = if p.val = 0 then 4 else 2)
def singleton (p : Fin 2) (i : Fin 10) : Bool := decide (i.val = p.val)

lemma initial_length (x : Fin 10 → Bool) : (initial x).length = 11 := by simp [initial]

lemma witness_data : ∀ p : Fin 2,
    (initial (high p)).getD p.val false = true ∧
    (initial (low p)).getD p.val false = false ∧
    edge10 (high p) = true ∧ edge10 (low p) = false ∧
    (initial (singleton p)).getD p.val false = true ∧ edge10 (singleton p) = false ∧
    ∀ i : Fin 11, i.val ≠ p.val →
      (initial (high p)).getD i.val false ≤ (initial (low p)).getD i.val false := by
  decide +kernel

lemma initial_away (p : Fin 2) : awayLE p.val (initial (high p)) (initial (low p)) := by
  intro i hi
  by_cases hlt : i < 11
  · exact (witness_data p).2.2.2.2.2.2 ⟨i,hlt⟩ hi
  · rw [List.getD_eq_default _ _ (by rw [initial_length]; omega),
      List.getD_eq_default _ _ (by rw [initial_length]; omega)]

lemma consumer_distinct (p : Fin 2) (pre suffix : List Gate) (outIdx : Nat)
    (monoPre : ∀ g ∈ pre, g.op = .and ∨ g.op = .or)
    (monoSuffix : ∀ g ∈ suffix, g.op = .and ∨ g.op = .or)
    (computes : ∀ x : Fin 10 → Bool,
      (Circuit.mk (pre ++ ⟨.not,[p.val]⟩ :: suffix) outIdx).eval (initial x) = edge10 x) :
    (∃ g ∈ pre, p.val ∈ g.inputs) ∨
      ∃ g ∈ suffix, p.val ∈ g.inputs ∧ 11 + pre.length ∉ g.inputs := by
  by_cases earlier : ∃ g ∈ pre, p.val ∈ g.inputs
  · exact Or.inl earlier
  right
  by_contra missing
  have absent : ∀ g ∈ pre, p.val ∉ g.inputs := by
    intro g hg hp
    exact earlier ⟨g,hg,hp⟩
  have paired : ∀ g ∈ suffix, p.val ∈ g.inputs → 11 + pre.length ∈ g.inputs := by
    intro g hg hp
    by_contra hz
    exact missing ⟨g,hg,hp,hz⟩
  obtain ⟨highBit,lowBit,highF,lowF,singleBit,singleF,_⟩ := witness_data p
  have outputDifferent : outIdx ≠ p.val := by
    intro eq
    have h := computes (singleton p)
    change (run (pre ++ ⟨.not,[p.val]⟩ :: suffix) (initial (singleton p))).getD outIdx false = _ at h
    rw [eq,run_prefix _ _ _ (by rw [initial_length]; omega),singleBit,singleF] at h
    cases h
  let wh := run pre (initial (high p))
  let wl := run pre (initial (low p))
  have lenH : wh.length = 11 + pre.length := by simp [wh,run_length,initial_length]
  have lenL : wl.length = 11 + pre.length := by simp [wl,run_length,initial_length]
  have len : wh.length = wl.length := by omega
  have hrH : p.val < wh.length := by omega
  have hrL : p.val < wl.length := by omega
  have whr : wh.getD p.val false = true := by
    rw [show wh = run pre (initial (high p)) from rfl,run_prefix _ _ _ (by rw [initial_length]; omega)]
    exact highBit
  have wlr : wl.getD p.val false = false := by
    rw [show wl = run pre (initial (low p)) from rfl,run_prefix _ _ _ (by rw [initial_length]; omega)]
    exact lowBit
  have preOrder : awayLE p.val wh wl := run_away p.val pre monoPre absent
    (by rw [initial_length,initial_length]) (initial_away p)
  have postOrder : awayLE p.val (wh ++ [false]) (wl ++ [true]) :=
    append_away p.val len preOrder (by decide)
  have finalOrder := run_paired p.val (11 + pre.length) suffix monoSuffix paired
    (w := wh ++ [false]) (v := wl ++ [true])
    (by simp [len]) (by simp; omega) (by simp; omega)
    (by rw [List.getD_append _ _ _ _ hrH]; exact whr)
    (by rw [List.getD_append _ _ _ _ hrL]; exact wlr)
    (by rw [←lenH]; exact getD_last wh false false)
    (by rw [←lenL]; exact getD_last wl true false) postOrder
  have notHigh : step wh ⟨.not,[p.val]⟩ = wh ++ [false] := by
    change wh ++ [!(wh.getD p.val false)] = wh ++ [false]
    simp only [whr,Bool.not_true]
  have notLow : step wl ⟨.not,[p.val]⟩ = wl ++ [true] := by
    change wl ++ [!(wl.getD p.val false)] = wl ++ [true]
    simp only [wlr,Bool.not_false]
  have highEq := computes (high p)
  have lowEq := computes (low p)
  change (run (pre ++ ⟨.not,[p.val]⟩ :: suffix) (initial (high p))).getD outIdx false = _ at highEq
  change (run (pre ++ ⟨.not,[p.val]⟩ :: suffix) (initial (low p))).getD outIdx false = _ at lowEq
  rw [run_append] at highEq lowEq
  change (run suffix (step wh ⟨.not,[p.val]⟩)).getD outIdx false = _ at highEq
  change (run suffix (step wl ⟨.not,[p.val]⟩)).getD outIdx false = _ at lowEq
  rw [notHigh,highF] at highEq
  rw [notLow,lowF] at lowEq
  have impossible := finalOrder outIdx outputDifferent
  rw [highEq,lowEq] at impossible
  simp [Bool.le_iff_imp] at impossible

end PEqualNP.Outside.L_meta_1886_aux.EndpointOrder
