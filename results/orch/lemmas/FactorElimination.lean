import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2602_aux.GlobalRewire.Eval

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

-- The wire evaluation and gate monotonicity lemmas are adapted from L_meta_1766.
def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

lemma opMono_eq : OpMono Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

lemma opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

lemma wire_relation {n : ℕ} {C : Circuit} {u : ℕ} {sigma : ℕ → ℕ} {x : Fin n → Bool}
    (R : Bool → Bool → Prop) (reflR : ∀ b, R b b)
    (transR : ∀ {a b c}, R a b → R b c → R a c) (mono : OpMono R)
    (hC : PEqualNP.TopForm.IsAO2 n C) (hs : ∀ r, sigma r < n + u)
    (reads : ∀ r < C.gates.length, n + u ∈ (gateAt C r).inputs →
      R (val C (List.ofFn x) (sigma r)) (val C (List.ofFn x) (n + u))) :
    ∀ i, R (val (PEqualNP.FactorSubst.substReads C n u sigma) (List.ofFn x) i)
      (val C (List.ofFn x) i) := by
  let D := PEqualNP.FactorSubst.substReads C n u sigma
  let z := List.ofFn x
  have hz : z.length = n := by simp [z]
  have len : D.gates.length = C.gates.length := by simp [D, PEqualNP.FactorSubst.substReads]
  change ∀ i, R (val D z i) (val C z i)
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    by_cases hin : i < n
    · rw [val_input hz hin, val_input hz hin]
      exact reflR _
    by_cases hout : n + C.gates.length ≤ i
    · rw [val_ge hz (show n + D.gates.length ≤ i by omega), val_ge hz hout]
      exact reflR _
    let r := i - n
    have hi : i = n + r := by dsimp [r]; omega
    have hr : r < C.gates.length := by omega
    have hd : r < D.gates.length := by omega
    let sub := fun j : ℕ => if j = n + u then sigma r else j
    have atD : gateAt D r = ⟨(gateAt C r).op, (gateAt C r).inputs.map sub⟩ := by
      rw [gateAt_eq hd, gateAt_eq hr]
      simp [D, PEqualNP.FactorSubst.substReads, sub]
    rw [hi, val_gate hz hd, val_gate hz hr, atD, List.map_map]
    apply mono _ (hC.1 _ (gateAt_mem hr))
    intro j hj
    have hjlt := hC.2.1 r hr j hj
    have hsig := hs r
    have hsub : sub j < n + r := by
      dsimp [sub]
      split <;> omega
    simp only [Function.comp_apply, ite_eq_left hsub, ite_eq_left hjlt]
    by_cases he : j = n + u
    · subst j
      simpa only [sub, ite_eq_left rfl] using transR (ih (sigma r) (by omega)) (reads r hr hj)
    · simpa [sub, he] using ih j (by omega)

end PEqualNP.Outside.L_meta_2602_aux.GlobalRewire.Eval

namespace PEqualNP.Outside.L_meta_2602_aux.GlobalRewire

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover Eval

def changeWire (n c : ℕ) (sigma : ℕ → ℕ) (j i : ℕ) : ℕ :=
  if i = n + c then sigma j else i

def ProposedValue (n : ℕ) (C : Circuit) (c : ℕ) (sigma : ℕ → ℕ)
    (x : Fin n → Bool) (j : ℕ) : Bool :=
  (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
    val C (List.ofFn x) (changeWire n c sigma j i))

lemma wire_eq_on_false (n : ℕ) (C : Circuit) (c : ℕ) (sigma : ℕ → ℕ)
    (hC : PEqualNP.TopForm.IsAO2 n C) (hs : ∀ r, sigma r < n + c)
    (x : Fin n → Bool)
    (hgrow : ∀ r < C.gates.length, n + c ∈ (gateAt C r).inputs →
      val C (List.ofFn x) (n + c) = true → val C (List.ofFn x) (sigma r) = true)
    (hfalse : ∀ r < C.gates.length, n + c ∈ (gateAt C r).inputs →
      ProposedValue n C c sigma x r = false) :
    ∀ i, val (PEqualNP.FactorSubst.substReads C n c sigma) (List.ofFn x) i =
      val C (List.ofFn x) i := by
  let D := PEqualNP.FactorSubst.substReads C n c sigma
  let z := List.ofFn x
  have hz : z.length = n := by simp [z]
  have len : D.gates.length = C.gates.length := by simp [D, PEqualNP.FactorSubst.substReads]
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    by_cases hin : i < n
    · rw [val_input hz hin, val_input hz hin]
    by_cases hout : n + C.gates.length ≤ i
    · rw [val_ge hz (show n + D.gates.length ≤ i by omega), val_ge hz hout]
    let r := i - n
    have hi : i = n + r := by dsimp [r]; omega
    have hr : r < C.gates.length := by omega
    have hd : r < D.gates.length := by omega
    let sub := changeWire n c sigma r
    have atD : gateAt D r = ⟨(gateAt C r).op, (gateAt C r).inputs.map sub⟩ := by
      rw [gateAt_eq hd, gateAt_eq hr]
      simp [D, PEqualNP.FactorSubst.substReads, sub, changeWire]
    have small (j : ℕ) (hj : j ∈ (gateAt C r).inputs) : sub j < n + r := by
      have hlt := hC.2.1 r hr j hj
      have hsig := hs r
      dsimp [sub, changeWire]
      split <;> omega
    have left : val D z (n + r) = ProposedValue n C c sigma x r := by
      rw [val_gate hz hd, atD, List.map_map]
      unfold ProposedValue
      apply congrArg (gateAt C r).op.eval
      apply List.map_congr_left
      intro j hj
      simp only [Function.comp_apply, ite_eq_left (small j hj)]
      exact ih (sub j) (by rw [hi]; exact small j hj)
    have right : val C z (n + r) =
        (gateAt C r).op.eval ((gateAt C r).inputs.map (val C z)) := by
      rw [val_gate hz hr]
      apply congrArg (gateAt C r).op.eval
      apply List.map_congr_left
      intro j hj
      exact ite_eq_left (hC.2.1 r hr j hj)
    rw [hi, left, right]
    by_cases read : n + c ∈ (gateAt C r).inputs
    · rw [hfalse r hr read]
      have mono := opMono_imp (gateAt C r).op (hC.1 _ (gateAt_mem hr))
        (gateAt C r).inputs (val C z) (fun j => val C z (sub j))
        (by
          intro j hj
          by_cases eq : j = n + c
          · subst j
            simpa [sub, changeWire] using hgrow r hr read
          · simp [sub, changeWire, eq])
      cases old : (gateAt C r).op.eval ((gateAt C r).inputs.map (val C z)) with
      | false => rfl
      | true =>
        have bad := mono old
        change ProposedValue n C c sigma x r = true at bad
        rw [hfalse r hr read] at bad
        cases bad
    · unfold ProposedValue
      apply congrArg (gateAt C r).op.eval
      apply List.map_congr_left
      intro j hj
      have ne : j ≠ n + c := fun h => read (h ▸ hj)
      simp [changeWire, ne, z]

lemma rewire_computes (n : ℕ) (C : Circuit) (c : ℕ) (sigma : ℕ → ℕ)
    (hC : PEqualNP.TopForm.IsAO2 n C) (hs : ∀ r, sigma r < n + c)
    (F : (Fin n → Bool) → Bool)
    (hF : ∀ x, C.eval (List.ofFn x) = F x)
    (hgrow : ∀ r < C.gates.length, n + c ∈ (gateAt C r).inputs →
      ∀ x : Fin n → Bool, val C (List.ofFn x) (n + c) = true →
        val C (List.ofFn x) (sigma r) = true)
    (hclean : ∀ r < C.gates.length, n + c ∈ (gateAt C r).inputs →
      ∀ x : Fin n → Bool, ProposedValue n C c sigma x r = true → F x = true) :
    ∀ x, (PEqualNP.FactorSubst.substReads C n c sigma).eval (List.ofFn x) = F x := by
  intro x
  cases hf : F x with
  | false =>
    have eq := wire_eq_on_false n C c sigma hC hs x
      (fun r hr mem => hgrow r hr mem x) (by
        intro r hr mem
        cases hp : ProposedValue n C c sigma x r with
        | false => rfl
        | true => have bad := hclean r hr mem x hp; rw [hf] at bad; cases bad)
      C.output
    exact eq.trans (hF x |>.trans hf)
  | true =>
    have mono := wire_relation (n := n) (C := C) (u := c) (sigma := sigma) (x := x)
      (fun a b => b = true → a = true) (fun _ h => h)
      (fun h₁ h₂ v => h₁ (h₂ v))
      (fun op hop l f g h => opMono_imp op hop l g f h) hC hs
      (fun r hr mem => hgrow r hr mem x)
    exact mono C.output (hF x |>.trans hf)

def Proper (n : ℕ) (C : Circuit) : Prop :=
  ∀ j g, C.gates[j]? = some g →
    (g.op = .and ∨ g.op = .or) ∧
      ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < n + j ∧ b < n + j

def DerivativeRules (n : ℕ) (C : Circuit) (v d : ℕ → Bool) : Prop :=
  ∀ j g a b, C.gates[j]? = some g → g.inputs = [a, b] →
    (g.op = .and → d (n + j) = (v a && d b || d a && v b)) ∧
    (g.op = .or → d (n + j) = (d a || d b))

lemma rewire_proper (n : ℕ) (C : Circuit) (c : ℕ) (sigma : ℕ → ℕ)
    (hC : Proper n C) (hs : ∀ r, sigma r < n + c)
    (hne : ∀ j g a b, C.gates[j]? = some g → g.inputs = [a, b] →
      changeWire n c sigma j a ≠ changeWire n c sigma j b) :
    Proper n (PEqualNP.FactorSubst.substReads C n c sigma) := by
  let D := PEqualNP.FactorSubst.substReads C n c sigma
  have len : D.gates.length = C.gates.length := by simp [D, PEqualNP.FactorSubst.substReads]
  intro j gg hgg
  have hjD : j < D.gates.length := List.getElem?_eq_some_iff.mp hgg |>.1
  have hj : j < C.gates.length := by omega
  let g := C.gates[j]
  have hg : C.gates[j]? = some g := List.getElem?_eq_getElem hj
  let sub := changeWire n c sigma j
  have hmap : D.gates[j]? = some ⟨g.op, g.inputs.map sub⟩ := by
    rw [List.getElem?_eq_getElem hjD]
    simp [D, PEqualNP.FactorSubst.substReads, g, sub, changeWire]
  have eg : gg = ⟨g.op, g.inputs.map sub⟩ := Option.some.inj (hgg.symm.trans hmap)
  subst gg
  obtain ⟨hop, a, b, hab, _, ha, hb⟩ := hC j g hg
  refine ⟨hop, sub a, sub b, by simp [hab], hne j g a b hg hab, ?_, ?_⟩
  · have hsig := hs j
    dsimp [sub, changeWire]
    split <;> omega
  · have hsig := hs j
    dsimp [sub, changeWire]
    split <;> omega

lemma rewire_dead (n : ℕ) (C : Circuit) (c : ℕ) (sigma : ℕ → ℕ)
    (hs : ∀ r, sigma r < n + c) :
    ∀ g ∈ (PEqualNP.FactorSubst.substReads C n c sigma).gates, n + c ∉ g.inputs := by
  intro g hg
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
  simp only [PEqualNP.FactorSubst.substReads, List.getElem_mapIdx]
  intro mem
  obtain ⟨i, _, heq⟩ := List.mem_map.mp mem
  split at heq
  · have hsig := hs j
    omega
  · contradiction

lemma rewire_derivative (n : ℕ) (C : Circuit) (c : ℕ) (sigma : ℕ → ℕ)
    (hC : Proper n C) (hA : PEqualNP.TopForm.IsAO2 n C)
    (hs : ∀ r, sigma r < n + c) (x : Fin n → Bool) (d : ℕ → Bool)
    (hd : DerivativeRules n C (val C (List.ofFn x)) d)
    (hval : ∀ j g, C.gates[j]? = some g → n + c ∈ g.inputs →
      val C (List.ofFn x) (sigma j) = val C (List.ofFn x) (n + c))
    (hder : ∀ j g, C.gates[j]? = some g → n + c ∈ g.inputs → d (sigma j) = d (n + c)) :
    DerivativeRules n (PEqualNP.FactorSubst.substReads C n c sigma)
      (val (PEqualNP.FactorSubst.substReads C n c sigma) (List.ofFn x)) d := by
  let D := PEqualNP.FactorSubst.substReads C n c sigma
  have len : D.gates.length = C.gates.length := by simp [D, PEqualNP.FactorSubst.substReads]
  have veq : ∀ i, val D (List.ofFn x) i = val C (List.ofFn x) i := by
    apply wire_relation Eq (fun _ => rfl) (fun h₁ h₂ => h₁.trans h₂) opMono_eq hA hs
    intro j hj mem
    exact hval j (gateAt C j) (by rw [gateAt_eq hj]; exact List.getElem?_eq_getElem hj) mem
  intro j gg aa bb hgg hin
  have hjD : j < D.gates.length := List.getElem?_eq_some_iff.mp hgg |>.1
  have hj : j < C.gates.length := by omega
  let g := C.gates[j]
  have hg : C.gates[j]? = some g := List.getElem?_eq_getElem hj
  let sub := changeWire n c sigma j
  have hmap : D.gates[j]? = some ⟨g.op, g.inputs.map sub⟩ := by
    rw [List.getElem?_eq_getElem hjD]
    simp [D, PEqualNP.FactorSubst.substReads, g, sub, changeWire]
  have eg : gg = ⟨g.op, g.inputs.map sub⟩ := Option.some.inj (hgg.symm.trans hmap)
  obtain ⟨_, a, b, hab, _, _, _⟩ := hC j g hg
  have ins : gg.inputs = [sub a, sub b] := by simp [eg, hab]
  rw [ins] at hin
  have ea : aa = sub a := (List.cons.inj hin).1.symm
  have eb : bb = sub b := (List.cons.inj (List.cons.inj hin).2).1.symm
  subst aa
  subst bb
  have sv (k : ℕ) (hk : k ∈ g.inputs) :
      val D (List.ofFn x) (sub k) = val C (List.ofFn x) k := by
    rw [veq]
    by_cases eq : k = n + c
    · subst k
      simpa [sub, changeWire] using hval j g hg hk
    · simp [sub, changeWire, eq]
  have sd (k : ℕ) (hk : k ∈ g.inputs) : d (sub k) = d k := by
    by_cases eq : k = n + c
    · subst k
      simpa [sub, changeWire] using hder j g hg hk
    · simp [sub, changeWire, eq]
  rw [sv a (by simp [hab]), sv b (by simp [hab]), sd a (by simp [hab]), sd b (by simp [hab])]
  have old := hd j g a b hg hab
  simpa only [eg] using old

lemma and_value (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (c a b : ℕ) (hc : c < C.gates.length) (hop : (gateAt C c).op = .and)
    (hin : (gateAt C c).inputs = [a, b]) (x : Fin n → Bool) :
    val C (List.ofFn x) (n + c) = (val C (List.ofFn x) a && val C (List.ofFn x) b) := by
  have ha := hC.2.1 c hc a (by simp [hin])
  have hb := hC.2.1 c hc b (by simp [hin])
  rw [val_gate (by simp) hc, hop, hin]
  simp [GateOp.eval, ha, hb]

lemma factor_grows (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (c a b s : ℕ) (hc : c < C.gates.length) (hop : (gateAt C c).op = .and)
    (hin : (gateAt C c).inputs = [a, b]) (hs : s = a ∨ s = b) (x : Fin n → Bool) :
    val C (List.ofFn x) (n + c) = true → val C (List.ofFn x) s = true := by
  rw [and_value n C hC c a b hc hop hin x]
  intro h
  rcases hs with rfl | rfl
  · exact (Bool.and_eq_true_iff.mp h).1
  · exact (Bool.and_eq_true_iff.mp h).2

lemma zero_factor_equal (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (c a b s : ℕ) (hc : c < C.gates.length) (hop : (gateAt C c).op = .and)
    (hin : (gateAt C c).inputs = [a, b]) (hs : s = a ∨ s = b) (x : Fin n → Bool)
    (d : ℕ → Bool) (hd : DerivativeRules n C (val C (List.ofFn x)) d)
    (hv : val C (List.ofFn x) s = false) (hds : d s = false) :
    val C (List.ofFn x) s = val C (List.ofFn x) (n + c) ∧ d s = d (n + c) := by
  have hg : C.gates[c]? = some (gateAt C c) := by
    rw [gateAt_eq hc]
    exact List.getElem?_eq_getElem hc
  rw [and_value n C hC c a b hc hop hin x, (hd c _ a b hg hin).1 hop]
  rcases hs with rfl | rfl <;> simp [hv, hds]

end PEqualNP.Outside.L_meta_2602_aux.GlobalRewire
