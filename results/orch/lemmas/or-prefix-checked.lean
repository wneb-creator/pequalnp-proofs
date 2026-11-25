import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_1884.OrPrefix
open PEqualNP.CircuitLowerBounds

def width (p : Fin 4 → Bool) : ℕ :=
  (if p 1 then 1 else 0)+(if p 2 then 1 else 0)+(if p 3 then 1 else 0)

lemma width_and_left : ∀ p q : Fin 4 → Bool,
    width (fun i => p i && q i) ≤ width p := by decide +kernel
lemma width_and_right : ∀ p q : Fin 4 → Bool,
    width (fun i => p i && q i) ≤ width q := by decide +kernel
lemma width_or : ∀ p q : Fin 4 → Bool,
    width (fun i => p i || q i) ≤ width p + width q := by decide +kernel

def narrow (s : Fin 4 → List Bool) (b : ℕ) : Prop :=
  ∀ j, (s 0).getD j false=false → width (fun i => (s i).getD j false)≤b

def stp (s : List Bool) (g : Gate) : List Bool :=
  s ++ [g.op.eval (g.inputs.map fun j => s.getD j false)]
def orFlag (g : Gate) : Bool :=
  match g.op with | GateOp.or => true | _ => false

lemma output_narrow (s : Fin 4 → List Bool) (b : ℕ) (h : narrow s b)
    (g : Gate) (hop : g.op=GateOp.and ∨ g.op=GateOp.or)
    (harity : g.inputs.length≤2)
    (hz : g.op.eval (g.inputs.map fun j => (s 0).getD j false)=false) :
    width (fun i => g.op.eval (g.inputs.map fun j => (s i).getD j false)) ≤
      if orFlag g then b+b else b := by
  rcases g with ⟨op,ls⟩
  change op=GateOp.and ∨ op=GateOp.or at hop
  change ls.length≤2 at harity
  rcases hop with hop | hop <;> subst op
  · cases ls with
    | nil => simp [GateOp.eval] at hz
    | cons a ls =>
      cases ls with
      | nil => simpa [GateOp.eval,orFlag] using h a (by simpa [GateOp.eval] using hz)
      | cons c ls =>
        cases ls with
        | cons d ls => simp at harity
        | nil =>
          have hz' : (s 0).getD a false=false ∨ (s 0).getD c false=false := by
            have hzz : ((s 0).getD a false && (s 0).getD c false)=false := by
              simpa only [GateOp.eval,List.map_cons,List.map_nil,List.all_cons,List.all_nil,Bool.and_true,id_eq] using hz
            cases ha : (s 0).getD a false with
            | false => exact Or.inl rfl
            | true => exact Or.inr (by simpa only [ha,Bool.true_and] using hzz)
          rcases hz' with ha | hc
          · simpa [GateOp.eval,orFlag] using (width_and_left (fun i => (s i).getD a false) (fun i => (s i).getD c false)).trans (h a ha)
          · simpa [GateOp.eval,orFlag] using (width_and_right (fun i => (s i).getD a false) (fun i => (s i).getD c false)).trans (h c hc)
  · cases ls with
    | nil => simp [GateOp.eval,width,orFlag]
    | cons a ls =>
      cases ls with
      | nil =>
        have hh := h a (by simpa [GateOp.eval] using hz)
        simpa [GateOp.eval,orFlag] using (show width (fun i => (s i).getD a false)≤b+b by omega)
      | cons c ls =>
        cases ls with
        | cons d ls => simp at harity
        | nil =>
          have hz' : (s 0).getD a false=false ∧ (s 0).getD c false=false := by
            simpa [GateOp.eval,Bool.or_eq_false_iff] using hz
          have hh := width_or (fun i => (s i).getD a false) (fun i => (s i).getD c false)
          have ha := h a hz'.1
          have hc := h c hz'.2
          simpa [GateOp.eval,orFlag] using (show width (fun i => (s i).getD a false ||
            (s i).getD c false)≤b+b by omega)

lemma step_narrow (s : Fin 4 → List Bool) (n b : ℕ) (hlen : ∀ i,(s i).length=n)
    (h : narrow s b) (g : Gate) (hop : g.op=GateOp.and ∨ g.op=GateOp.or)
    (harity : g.inputs.length≤2) :
    narrow (fun i => stp (s i) g) (if orFlag g then b+b else b) := by
  intro j hj
  by_cases hlt : j<n
  · have he : ∀ i,(stp (s i) g).getD j false=(s i).getD j false := by
      intro i
      have hlti : j<(s i).length := by rw [hlen i];exact hlt
      simp only [stp,List.getD_eq_getElem?_getD,List.getElem?_append_left hlti]
    simp only [he] at hj ⊢
    have hb := h j hj
    split <;> omega
  · by_cases heq : j=n
    · subst j
      have he : ∀ i,(stp (s i) g).getD n false=
          g.op.eval (g.inputs.map fun k => (s i).getD k false) := by
        intro i
        rw [←hlen i]
        simp [stp,List.getD_eq_getElem?_getD]
      simp only [he] at hj ⊢
      exact output_narrow s b h g hop harity hj
    · have he : ∀ i,(stp (s i) g).getD j false=false := by
        intro i
        apply List.getD_eq_default
        simp [stp,hlen]
        omega
      have hefun : (fun i => (stp (s i) g).getD j false)=(fun _ : Fin 4 => false) := funext he
      change width (fun i => (stp (s i) g).getD j false)≤_
      rw [hefun]
      simp [width]

lemma fold_narrow (gs : List Gate) (s : Fin 4 → List Bool) (n b : ℕ)
    (hlen : ∀ i,(s i).length=n) (h : narrow s b)
    (hop : ∀g∈gs,g.op=GateOp.and ∨ g.op=GateOp.or)
    (harity : ∀g∈gs,g.inputs.length≤2) :
    narrow (fun i => gs.foldl stp (s i)) (b*2^(gs.countP orFlag)) := by
  induction gs generalizing s n b with
  | nil => simpa using h
  | cons g gs ih =>
    have hn := step_narrow s n b hlen h g (hop _ (by simp)) (harity _ (by simp))
    have hh := ih (fun i => stp (s i) g) (n+1) (if orFlag g then b+b else b)
      (by intro i;simp [stp,hlen]) hn
      (by intro t ht;exact hop _ (by simp [ht]))
      (by intro t ht;exact harity _ (by simp [ht]))
    simp only [List.foldl_cons,List.countP_cons]
    convert hh using 1
    cases ho : orFlag g <;> simp [ho,pow_succ,Nat.mul_add,Nat.add_mul]
    ring

lemma three_probe_or_bound (C : Circuit) (s : Fin 4 → List Bool) (n : ℕ)
    (hlen : ∀i,(s i).length=n) (hin : narrow s 1)
    (hop : ∀g∈C.gates,g.op=GateOp.and ∨ g.op=GateOp.or)
    (harity : ∀g∈C.gates,g.inputs.length≤2)
    (hzero : C.eval (s 0)=false)
    (hprobes : C.eval (s 1)=true ∧ C.eval (s 2)=true ∧ C.eval (s 3)=true) :
    2≤C.gates.countP orFlag := by
  have hh := fold_narrow C.gates s n 1 hlen hin hop harity C.output hzero
  have he : width (fun i => C.eval (s i))=3 := by simp [width,hprobes]
  change width (fun i => C.eval (s i))≤1*2^(C.gates.countP orFlag) at hh
  rw [he] at hh
  by_contra hn
  have hc : C.gates.countP orFlag=0 ∨ C.gates.countP orFlag=1 := by omega
  rcases hc with hc | hc <;> simp [hc] at hh
end PEqualNP.Outside.L_meta_1884.OrPrefix
