import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17770_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.ReadK PEqualNP.TopForm
open PEqualNP.ReadTwo (wval)

theorem foldl_snoc_prefix {α β : Type _} (F : List α → β → α) (gs : List β) (init : List α) :
    init <+: gs.foldl (fun R g => R ++ [F R g]) init := by
  induction gs generalizing init with
  | nil => exact List.prefix_refl _
  | cons g gs ih => exact (List.prefix_append init [F init g]).trans (ih _)

theorem foldl_snoc_length {α β : Type _} (F : List α → β → α) (gs : List β) (init : List α) :
    (gs.foldl (fun R g => R ++ [F R g]) init).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp
  | cons g gs ih => simp [ih]; omega

theorem getD_of_prefix {α : Type _} {P L : List α} (h : P <+: L) {i : ℕ} (hi : i < P.length)
    (d : α) : L.getD i d = P.getD i d := by
  obtain ⟨t, rfl⟩ := h
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem foldl_snoc_init {α : Type _} (G : List α → Gate → α) (d : α) (init : List α)
    (gs : List Gate) (i : ℕ) (hi : i < init.length) :
    (gs.foldl (fun R g => R ++ [G (g.inputs.map fun i => R.getD i d) g]) init).getD i d
      = init.getD i d :=
  getD_of_prefix (foldl_snoc_prefix (fun R g => G (g.inputs.map fun i => R.getD i d) g) _ _) hi d

theorem foldl_snoc_beyond {α : Type _} (G : List α → Gate → α) (d : α) (init : List α)
    (gs : List Gate) (i : ℕ) (hi : init.length + gs.length ≤ i) :
    (gs.foldl (fun R g => R ++ [G (g.inputs.map fun i => R.getD i d) g]) init).getD i d = d := by
  apply List.getD_eq_default
  rw [foldl_snoc_length (fun R g => G (g.inputs.map fun i => R.getD i d) g)]
  exact hi

theorem foldl_snoc_gate {α : Type _} (G : List α → Gate → α) (d : α) (init : List α)
    (gs : List Gate) (j : ℕ) (hj : j < gs.length)
    (hrb : ∀ i ∈ gs[j].inputs, i < init.length + j) :
    (gs.foldl (fun R g => R ++ [G (g.inputs.map fun i => R.getD i d) g]) init).getD
        (init.length + j) d
      = G (gs[j].inputs.map fun i =>
          (gs.foldl (fun R g => R ++ [G (g.inputs.map fun i => R.getD i d) g]) init).getD i d)
          gs[j] := by
  have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by simp
  set P := (gs.take j).foldl (fun R g => R ++ [G (g.inputs.map fun i => R.getD i d) g]) init
    with hP
  have hPl : P.length = init.length + j := by
    rw [hP, foldl_snoc_length (fun R g => G (g.inputs.map fun i => R.getD i d) g)]
    simp; omega
  have hpre : (P ++ [G (gs[j].inputs.map fun i => P.getD i d) gs[j]]) <+:
      gs.foldl (fun R g => R ++ [G (g.inputs.map fun i => R.getD i d) g]) init := by
    conv_rhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
    exact foldl_snoc_prefix (fun R g => G (g.inputs.map fun i => R.getD i d) g) _ _
  have hpre2 := (List.prefix_append P _).trans hpre
  rw [getD_of_prefix hpre (by simp; omega)]
  have e1 : (P ++ [G (gs[j].inputs.map fun i => P.getD i d) gs[j]]).getD (init.length + j) d
      = G (gs[j].inputs.map fun i => P.getD i d) gs[j] := by
    rw [← hPl]; simp
  rw [e1]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [getD_of_prefix hpre2 (by rw [hPl]; exact hrb i hi)]

theorem wires_eq (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl
      (fun R g => R ++ [(fun ins (g : Gate) => g.op.eval ins) (g.inputs.map fun i => R.getD i false) g])
      x := rfl

theorem gateAt_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

section Wires
variable (C : Circuit) (n : ℕ)

abbrev W (x : Fin n → Bool) (i : ℕ) : Bool := (C.wires (List.ofFn x)).getD i false

theorem W_input (x : Fin n → Bool) (i : ℕ) (hi : i < n) : W C n x i = x ⟨i, hi⟩ := by
  unfold W
  rw [wires_eq, foldl_snoc_init (fun ins (g : Gate) => g.op.eval ins) false _ _ _ (by simpa using hi)]
  simp [List.getD_eq_getElem?_getD, hi]

theorem W_gate (x : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length)
    (hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j) :
    W C n x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (W C n x)) := by
  unfold W
  rw [gateAt_eq C j hj] at hrb ⊢
  have := foldl_snoc_gate (fun ins (g : Gate) => g.op.eval ins) false (List.ofFn x) C.gates j hj
    (by simpa using hrb)
  simp only [List.length_ofFn] at this
  rw [wires_eq, this]

end Wires

abbrev fixed {n : ℕ} (a : Fin n) (i : Fin n) : Bool := decide (i = a)
def Cst {n : ℕ} (C : Circuit) (a z : Fin n) (i : ℕ) :=
  (scalarMults C n [a.val,z.val] z.val).getD i none

def enabled {n : ℕ} (C : Circuit) (a : Fin n) (u v : ℕ) : Prop :=
  ∃ (j : ℕ) (g : Gate) (w : ℕ), v = n+j ∧ C.gates[j]? = some g ∧
    (g.inputs=[u,w] ∨ g.inputs=[w,u]) ∧ (g.op=.or ∨ g.op=.and ∧ W C n (fixed a) w=true)

abbrev Path {n : ℕ} (C : Circuit) (a z : Fin n) (i : ℕ) :=
  Relation.ReflTransGen (enabled C a) z.val i

def least : Option ℕ → Option ℕ → Option ℕ
  | none,x => x | some u,none => some u | some u,some v => some (min u v)
def plus : Option ℕ → Option ℕ → Option ℕ
  | some u,some v => some (u+v) | _,_ => none
def op (ins : List (Option ℕ)) (g : Gate) : Option ℕ :=
  match g.op with
  | .or => ins.foldl least none
  | .and => ins.foldl plus (some 0)
  | _ => none
def inp {n : ℕ} (a z : Fin n) (i : ℕ) : Option ℕ :=
  if i=z.val then some 1 else if i ∈ [a.val,z.val] then some 0 else none

theorem fold_form {n : ℕ} (C : Circuit) (a z : Fin n) : scalarMults C n [a.val,z.val] z.val =
    C.gates.foldl (fun R g => R ++ [op (g.inputs.map fun i => R.getD i none) g]) ((List.range n).map (inp a z)) := rfl

theorem at_input {n : ℕ} (C : Circuit) (a z : Fin n) (i : ℕ) (hi : i<n) : Cst C a z i = inp a z i := by
  unfold Cst
  rw [fold_form,foldl_snoc_init _ _ _ _ _ (by simpa using hi)]
  simp [List.getD_eq_getElem?_getD,hi]

theorem at_gate {n : ℕ} (C : Circuit) (a z : Fin n) (j : ℕ) (hj : j<C.gates.length)
    (back : ∀ i ∈ (gateAt C j).inputs, i < n+j) :
    Cst C a z (n+j) = op ((gateAt C j).inputs.map (Cst C a z)) (gateAt C j) := by
  unfold Cst
  rw [fold_form,gateAt_eq C j hj]
  have h := foldl_snoc_gate op none ((List.range n).map (inp a z)) C.gates j hj
    (by simpa [gateAt_eq C j hj] using back)
  simpa using h

theorem beyond {n : ℕ} (C : Circuit) (a z : Fin n) (i : ℕ) (hi : n+C.gates.length ≤ i) :
    Cst C a z i = none ∧ W C n (fixed a) i = false := by
  constructor
  · unfold Cst
    rw [fold_form,foldl_snoc_beyond]
    simpa using hi
  · apply List.getD_eq_default
    rw [wires_eq,foldl_snoc_length]
    simpa using hi

theorem binary_g {C : Circuit} {n : ℕ} (ao : IsAO2 n C) (j : ℕ) (hj : j<C.gates.length) :
    ∃ l r, (gateAt C j).inputs=[l,r] ∧ l<n+j ∧ r<n+j ∧
      ((gateAt C j).op=.and ∨ (gateAt C j).op=.or) := by
  have mem : gateAt C j ∈ C.gates := by rw [gateAt_eq C j hj]; exact List.getElem_mem _
  obtain ⟨l,r,eq⟩ := List.length_eq_two.1 (ao.2.2 _ mem)
  exact ⟨l,r,eq,ao.2.1 j hj l (by simp [eq]),ao.2.1 j hj r (by simp [eq]),ao.1 _ mem⟩

theorem binary_cost {n : ℕ} {C : Circuit} {a z : Fin n} (ao : IsAO2 n C)
    {j l r : ℕ} (hj : j<C.gates.length) (es : (gateAt C j).inputs=[l,r]) :
    ((gateAt C j).op=.and → Cst C a z (n+j) = plus (Cst C a z l) (Cst C a z r)) ∧
    ((gateAt C j).op=.or → Cst C a z (n+j) = least (Cst C a z l) (Cst C a z r)) := by
  rw [at_gate C a z j hj (ao.2.1 j hj),es]
  constructor <;> intro h <;> cases h1 : Cst C a z l <;> cases h2 : Cst C a z r <;>
    simp [op,plus,least,h,h1,h2]

theorem zero_val {n : ℕ} (C : Circuit) (a z : Fin n) (az : a ≠ z) (ao : IsAO2 n C) (i : ℕ) :
    Cst C a z i = some 0 ↔ W C n (fixed a) i = true := by
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    by_cases hin : i<n
    · rw [at_input _ _ _ _ hin,W_input _ _ _ _ hin]
      have e : (⟨i,hin⟩ : Fin n) = a ↔ i=a.val := Fin.ext_iff
      have ne : a.val ≠ z.val := fun h => az (Fin.ext h)
      by_cases iz : i=z.val <;> simp_all [inp,fixed,ne.symm]
    · by_cases invalid : n+C.gates.length ≤ i
      · obtain ⟨s,t⟩ := beyond C a z i invalid
        rw [s,t]
        decide
      · obtain ⟨j,rfl⟩ : ∃ j, i=n+j := ⟨i-n,by omega⟩
        have hj : j<C.gates.length := by omega
        obtain ⟨l,r,es,hl,hr,kind⟩ := binary_g ao j hj
        have left := ih l hl; have right := ih r hr
        obtain ⟨ca,co⟩ := binary_cost (a:=a) (z:=z) ao hj es
        rw [W_gate _ _ _ _ hj (ao.2.1 j hj),es]
        rcases kind with h|h
        · rw [ca h,h]
          simp only [List.map_cons,List.map_nil,GateOp.eval,List.all_cons,List.all_nil,id,Bool.and_true,
            Bool.and_eq_true,←left,←right]
          cases Cst C a z l <;> cases Cst C a z r <;> simp [plus]
        · rw [co h,h]
          simp only [List.map_cons,List.map_nil,GateOp.eval,List.any_cons,List.any_nil,id,Bool.or_false,
            Bool.or_eq_true,←left,←right]
          cases Cst C a z l <;> cases Cst C a z r <;> simp [least] <;> omega

theorem edge {n : ℕ} {C : Circuit} {a : Fin n} {j l r : ℕ}
    (hj : j<C.gates.length) (es : (gateAt C j).inputs=[l,r] ∨ (gateAt C j).inputs=[r,l])
    (kind : (gateAt C j).op=.or ∨ (gateAt C j).op=.and ∧ W C n (fixed a) r=true) :
    enabled C a l (n+j) :=
  ⟨j,gateAt C j,r,rfl,by rw [gateAt_eq C j hj,List.getElem?_eq_getElem hj],es,kind⟩

theorem one_path {n : ℕ} (C : Circuit) (a z : Fin n) (az : a≠z) (ao : IsAO2 n C) (i : ℕ)
    (h : Cst C a z i=some 1) : Path C a z i := by
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    by_cases hin : i<n
    · rw [at_input _ _ _ _ hin] at h
      by_cases iz : i=z.val
      · subst i; exact .refl
      · simp [inp,iz] at h
    · by_cases inv : n+C.gates.length ≤ i
      · rw [(beyond C a z i inv).1] at h
        contradiction
      · obtain ⟨j,rfl⟩ : ∃ j, i=n+j := ⟨i-n,by omega⟩
        have hj : j<C.gates.length := by omega
        obtain ⟨l,r,es,hl,hr,kind⟩ := binary_g ao j hj
        obtain ⟨ca,co⟩ := binary_cost (a:=a) (z:=z) ao hj es
        rcases kind with ha|ho
        · have parts : (Cst C a z l=some 1 ∧ Cst C a z r=some 0) ∨
              (Cst C a z l=some 0 ∧ Cst C a z r=some 1) := by
            rw [ca ha] at h
            cases x : Cst C a z l <;> cases y : Cst C a z r <;> simp_all [plus] <;> omega
          rcases parts with ⟨one,zero⟩ | ⟨zero,one⟩
          · exact (ih l hl one).tail (edge hj (Or.inl es) (Or.inr ⟨ha,(zero_val C a z az ao r).1 zero⟩))
          · exact (ih r hr one).tail (edge hj (Or.inr es) (Or.inr ⟨ha,(zero_val C a z az ao l).1 zero⟩))
        · have parts : Cst C a z l=some 1 ∨ Cst C a z r=some 1 := by
            rw [co ho] at h
            cases x : Cst C a z l <;> cases y : Cst C a z r <;> simp_all [least] <;> omega
          rcases parts with one|one
          · exact (ih l hl one).tail (edge hj (Or.inl es) (Or.inl ho))
          · exact (ih r hr one).tail (edge hj (Or.inr es) (Or.inl ho))

theorem cheap_path {n : ℕ} (C : Circuit) (a z : Fin n) (az : a≠z) (ao : IsAO2 n C) {i : ℕ}
    (path : Path C a z i) : Cst C a z i=some 0 ∨ Cst C a z i=some 1 := by
  induction path with
  | refl => right; rw [at_input _ _ _ _ z.isLt]; simp [inp]
  | @tail u v _ step ih =>
    obtain ⟨j,g,r,rfl,hit,es,kind⟩ := step
    have hj : j<C.gates.length := (List.getElem?_eq_some_iff.mp hit).choose
    have hg : gateAt C j=g := by rw [gateAt_eq C j hj]; exact (List.getElem?_eq_some_iff.mp hit).choose_spec
    simp only [←hg] at es kind
    rcases es with es|es <;> obtain ⟨ca,co⟩ := binary_cost (a:=a) (z:=z) ao hj es <;>
      rcases kind with h|⟨h,zero⟩
    · rw [co h]; rcases ih with hu|hu <;> cases Cst C a z r <;> simp [least,hu] <;> omega
    · rw [ca h,(zero_val C a z az ao r).2 zero]; rcases ih with hu|hu <;> simp [plus,hu]
    · rw [co h]; rcases ih with hu|hu <;> cases Cst C a z r <;> simp [least,hu] <;> omega
    · rw [ca h,(zero_val C a z az ao r).2 zero]; rcases ih with hu|hu <;> simp [plus,hu]

theorem iff_one {n : ℕ} (C : Circuit) (a z : Fin n) (az : a≠z) (ao : IsAO2 n C)
    (i : ℕ) (off : W C n (fixed a) i = false) :
    Path C a z i ↔ Cst C a z i = some 1 := by
  refine ⟨fun h => (cheap_path C a z az ao h).resolve_left ?_,one_path C a z az ao i⟩
  intro zero
  have on := (zero_val C a z az ao i).1 zero
  rw [off] at on
  contradiction

theorem support_ext (C : Circuit) (n : ℕ) (S T : List ℕ) (v : ℕ)
    (members : ∀ i, i ∈ S ↔ i ∈ T) : scalarMults C n S v = scalarMults C n T v := by
  unfold scalarMults
  congr 1
  apply List.map_congr_left
  intro i hi
  simp only [members i]

theorem bridge (n : ℕ) (C : Circuit) (a b : Fin n) (S : List ℕ)
    (ao : IsAO2 n C) (ab : a ≠ b) (members : ∀ i : ℕ, i ∈ S ↔ i=a.val ∨ i=b.val)
    (one : (scalarMults C n S b.val).getD C.output none = some 1) :
    Relation.ReflTransGen (fun u w : ℕ => ∃ (j : ℕ) (g : Gate) (v : ℕ),
      w=n+j ∧ C.gates[j]?=some g ∧ (g.inputs=[u,v] ∨ g.inputs=[v,u]) ∧
      (g.op=.or ∨ g.op=.and ∧ (C.wires (List.ofFn fun x : Fin n => decide (x=a))).getD v false=true))
      b.val C.output := by
  apply one_path C a b ab ao C.output
  have eq := support_ext C n S [a.val,b.val] b.val (fun i => by simpa using members i)
  rw [eq] at one
  exact one

theorem exact_child : ∀ (n : ℕ) (C : Circuit) (a b : Fin n) (S : List ℕ),
     IsAO2 n C → a ≠ b → (∀ i : ℕ, i ∈ S ↔ i=a.val ∨ i=b.val) →
     (scalarMults C n S b.val).getD C.output none = some 1 →
     Relation.ReflTransGen (fun u w : ℕ => ∃ (j : ℕ) (g : Gate) (q : ℕ), w = n+j ∧ C.gates[j]? = some g ∧
      (g.inputs = [u,q] ∨ g.inputs = [q,u]) ∧
      (g.op = GateOp.or ∨ g.op = GateOp.and ∧ wval C (fun i => decide (i=a)) q = true)) b.val C.output := bridge

end PEqualNP.Outside.L_meta_17770_aux

theorem PEqualNP.Outside.L_meta_17770 : (∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : Fin x1) (x5 : List ℕ), PEqualNP.TopForm.IsAO2 x1 x2 → x3 ≠ x4 → (∀ (x8 : ℕ), x8 ∈ x5 ↔ x8 = ↑x3 ∨ x8 = ↑x4) → (PEqualNP.ReadK.scalarMults x2 x1 x5 ↑x4).getD x2.output Option.none = Option.some (1 : ℕ) → Relation.ReflTransGen (fun (x10 x11 : ℕ) => ∃ (x12 : ℕ) (x13 : PEqualNP.CircuitLowerBounds.Gate) (x14 : ℕ), x11 = x1 + x12 ∧ x2.gates[x12]? = Option.some x13 ∧ (x13.inputs = [x10, x14] ∨ x13.inputs = [x14, x10]) ∧ (x13.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ x13.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.ReadTwo.wval x2 (fun (x15 : Fin x1) => Decidable.decide (x15 = x3)) x14 = Bool.true)) (↑x4) x2.output) := by
  exact PEqualNP.Outside.L_meta_17770_aux.exact_child
