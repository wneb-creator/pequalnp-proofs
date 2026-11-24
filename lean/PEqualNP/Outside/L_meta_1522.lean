import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1522_aux

open PEqualNP.CircuitLowerBounds

abbrev Fn (n : ℕ) := (Fin n → Bool) → Bool

def zero {n : ℕ} : Fn n := fun _ => false

def build {n : ℕ} (ws : List (Fn n)) (g : Gate) : Fn n :=
  fun x => g.op.eval (g.inputs.map fun i => (ws.getD i zero) x)

def step {n : ℕ} (ws : List (Fn n)) (g : Gate) := ws ++ [build ws g]

def inputs (n : ℕ) : List (Fn n) := List.ofFn fun i : Fin n => fun x => x i

lemma evalRead {n : ℕ} (ws : List (Fn n)) (i : ℕ) (x : Fin n → Bool) :
    (ws.getD i zero) x = (ws.map (fun f => f x)).getD i false := by
  simp [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? <;> rfl

lemma simulate {n : ℕ} (gs : List Gate) (ws : List (Fn n)) (x : Fin n → Bool) :
    (gs.foldl step ws).map (fun f => f x) =
      (Circuit.wires ⟨gs,0⟩ (ws.map (fun f => f x))) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons,Circuit.wires,List.foldl_cons] at *
    rw [ih]
    congr 1
    simp [step,build,evalRead]

lemma circuitRead {n : ℕ} (gs : List Gate) (i : ℕ) (x : Fin n → Bool) :
    ((gs.foldl step (inputs n)).getD i zero) x = Circuit.eval ⟨gs,i⟩ (List.ofFn x) := by
  rw [evalRead,simulate]
  simp [Circuit.eval,inputs,List.map_ofFn,Function.comp_def,Circuit.wires]

lemma readMember {n : ℕ} (ws : List (Fn n)) (i : ℕ) (P : Fn n → Prop)
    (no : ¬ P zero) (yes : P (ws.getD i zero)) : ws.getD i zero ∈ ws := by
  by_cases h : i < ws.length
  · rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h]
    exact List.getElem_mem h
  · rw [List.getD_eq_default _ _ (by omega)] at yes
    exact (no yes).elim

abbrev Pattern := Bool × Bool × Bool × Bool

def countP (p : Pattern) : ℕ := p.2.1.toNat + p.2.2.1.toNat + p.2.2.2.toNat

def good (t : ℕ) (p : Pattern) : Prop := p.1 = false ∧ t ≤ countP p
def exactP (t : ℕ) (p : Pattern) : Prop := p.1 = false ∧ countP p = t

def combineP (op : Bool → Bool → Bool) (a b : Pattern) : Pattern :=
  (op a.1 b.1, op a.2.1 b.2.1, op a.2.2.1 b.2.2.1, op a.2.2.2 b.2.2.2)

instance (t) (p) : Decidable (good t p) := by unfold good; infer_instance
instance (t) (p) : Decidable (exactP t p) := by unfold exactP; infer_instance

set_option maxRecDepth 4000 in
theorem binary : ∀ t ∈ [2,3], ∀ a b : Pattern,
    (good t (combineP Bool.and a b) → good t a ∨ good t b) ∧
    (good t (combineP Bool.or a b) → good t a ∨ good t b ∨ exactP t (combineP Bool.or a b)) := by
  simp only [List.mem_cons, forall_eq_or_imp]
  decide +kernel

abbrev X := Fin 13 → Bool
def atPoint (i : Fin 13) : X := fun v => decide (v = i)
def pat (off : X) (f : Fn 13) : Pattern := (f off, f (atPoint 0), f (atPoint 1), f (atPoint 3))

theorem source (off : X) (ws : List (Fn 13)) (g : Gate) (t : ℕ) (ht : t ∈ [2,3])
    (op : g.op = .and ∨ g.op = .or) (arity : g.inputs.length ≤ 2)
    (yes : good t (pat off (build ws g))) :
    (∃ i, good t (pat off (ws.getD i zero))) ∨ (g.op = .or ∧ exactP t (pat off (build ws g))) := by
  obtain ⟨kind,pins⟩ := g
  cases pins with
  | nil =>
    rcases op with rfl | rfl <;> simp [pat,build,GateOp.eval,good,countP] at yes
    simp at ht
    omega
  | cons a tail =>
    cases tail with
    | nil =>
      left
      refine ⟨a, ?_⟩
      rcases op with rfl | rfl <;> simpa [build,GateOp.eval,pat] using yes
    | cons b tail =>
      cases tail with
      | cons c tail => simp at arity
      | nil =>
        let pa := pat off (ws.getD a zero)
        let pb := pat off (ws.getD b zero)
        obtain ⟨hA,hO⟩ := binary t ht pa pb
        rcases op with rfl | rfl
        · rcases hA (by simpa [pa,pb,pat,build,GateOp.eval,combineP] using yes) with h | h
          · exact Or.inl ⟨a,h⟩
          · exact Or.inl ⟨b,h⟩
        · rcases hO (by simpa [pa,pb,pat,build,GateOp.eval,combineP] using yes) with h | h | h
          · exact Or.inl ⟨a,h⟩
          · exact Or.inl ⟨b,h⟩
          · exact Or.inr ⟨rfl, by simpa [pa,pb,pat,build,GateOp.eval,combineP] using h⟩

def wires (gs : List Gate) : List (Fn 13) := gs.foldl step (inputs 13)

theorem lengthRun {n : ℕ} (gs : List Gate) (ws : List (Fn n)) :
    (gs.foldl step ws).length = ws.length + gs.length := by
  induction gs generalizing ws with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons,ih,step]; omega

theorem wireLen (gs : List Gate) : (wires gs).length = 13 + gs.length := by
  simp [wires,lengthRun,inputs]

theorem keep (ws : List (Fn 13)) (f : Fn 13) (i : ℕ) (hi : i < ws.length) :
    (ws ++ [f]).getD i zero = ws.getD i zero := by simp [List.getD,List.getElem?_append,hi]

def found (off : X) (t : ℕ) (gs : List Gate) : Prop :=
  ∃ k : Fin gs.length, (gs.get k).op = .or ∧ exactP t (pat off ((wires gs).getD (13+k.val) zero))

theorem findGate (off : X) (t : ℕ) (ht : t ∈ [2,3]) (gs : List Gate)
    (legal : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (seed : ∀ i : Fin 13, ¬ good t (pat off (fun x => x i))) :
    ∀ f ∈ wires gs, good t (pat off f) → found off t gs := by
  have nozero : ¬ good t (pat off zero) := by
    simp [good,pat,zero,countP]
    simp at ht
    omega
  induction gs using List.reverseRecOn with
  | nil =>
    intro f hf
    change f ∈ List.ofFn (fun i : Fin 13 => fun x : X => x i) at hf
    obtain ⟨i,rfl⟩ := ((List.mem_ofFn' _ _).mp hf)
    exact fun h => (seed i h).elim
  | append_singleton gs g ih =>
    let ws := wires gs
    let fnew := build ws g
    have expand : wires (gs ++ [g]) = ws ++ [fnew] := by simp [wires,ws,fnew,step,List.foldl_append]
    have lift : found off t gs → found off t (gs ++ [g]) := by
      rintro ⟨k,hop,hk⟩
      refine ⟨⟨k.val,by simp⟩, ?_, ?_⟩
      · simpa [List.get_eq_getElem, List.getElem_append, k.isLt] using hop
      · change exactP t (pat off ((wires (gs ++ [g])).getD (13+k.val) zero))
        rw [expand,keep _ _ _ (by dsimp [ws]; rw [wireLen]; omega)]
        exact hk
    have old : ∀ f ∈ ws, good t (pat off f) → found off t (gs ++ [g]) :=
      fun f hf h => lift (ih (fun a ha => legal _ (by simp [ha])) f hf h)
    intro f hf h
    rw [expand] at hf
    rcases List.mem_append.mp hf with hf | hf
    · exact old f hf h
    · have eq : f = fnew := by simpa using hf
      subst f
      have hg := legal g (by simp)
      rcases source off ws g t ht hg.1 hg.2 h with ⟨i,hi⟩ | ⟨hop,hex⟩
      · exact old _ (readMember ws i (fun f => good t (pat off f)) nozero hi) hi
      · refine ⟨⟨gs.length,by simp⟩, ?_, ?_⟩
        · simpa [List.get_eq_getElem] using hop
        · change exactP t (pat off ((wires (gs ++ [g])).getD (13+gs.length) zero))
          rw [expand, ← wireLen gs]
          simpa [ws,List.getD] using hex

theorem counts (off : X) (f : Fn 13) :
    (({0,1,3} : Finset (Fin 13)).filter (fun a => f (atPoint a) = true)).card =
    countP (pat off f) := by
  cases h0 : f (atPoint 0) <;> cases h1 : f (atPoint 1) <;> cases h3 : f (atPoint 3) <;>
    simp [Finset.filter_insert,Finset.filter_singleton,pat,countP,h0,h1,h3]

theorem allThree (off : X) (f : Fn 13) (h : countP (pat off f) = 3) :
    ∀ a ∈ ({0,1,3} : Finset (Fin 13)), f (atPoint a) = true := by
  cases h0 : f (atPoint 0) <;> cases h1 : f (atPoint 1) <;> cases h3 : f (atPoint 3) <;>
    simp_all [countP,pat]

end PEqualNP.Outside.L_meta_1522_aux

open PEqualNP.Outside.L_meta_1522_aux in
theorem PEqualNP.Outside.L_meta_1522 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false →
    (∀ a ∈ ({0, 1, 3} : Finset (Fin 13)), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn (fun v : Fin 13 => decide (v = a))) = true) →
    ∃ B1 B2 : Fin gates.length, B1 ≠ B2 ∧
      (gates.get B1).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (gates.get B2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (B1 : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (B2 : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false ∧
      (({0, 1, 3} : Finset (Fin 13)).filter (fun a => PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (B1 : ℕ)⟩
        (List.ofFn (fun v : Fin 13 => decide (v = a))) = true)).card = 2 ∧
      (∀ a ∈ ({0, 1, 3} : Finset (Fin 13)), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (B2 : ℕ)⟩
        (List.ofFn (fun v : Fin 13 => decide (v = a))) = true) := by
  intro L _ gs out legal offFalse hit
  let off : X := fun v => decide (v ∉ L 0)
  let f := (wires gs).getD out zero
  have read (i : ℕ) (x : X) := circuitRead gs i x
  have ho : f off = false := (read out off).trans offFalse
  have hh (a : Fin 13) (ha : a ∈ ({0,1,3} : Finset (Fin 13))) :
      f (atPoint a) = true := (read out _).trans (hit a ha)
  have hc : countP (pat off f) = 3 := by
    simp [countP,pat,hh 0 (by decide),hh 1 (by decide),hh 3 (by decide)]
  have each (t : ℕ) (ht : t ∈ [2,3]) : found off t gs := by
    have seed (i : Fin 13) : ¬ good t (pat off (fun x => x i)) := by
      have cap : ∀ b : Fin 13, (atPoint 0 b).toNat + (atPoint 1 b).toNat +
          (atPoint 3 b).toNat ≤ 1 := by decide +kernel
      intro hg
      have lo := hg.2
      change t ≤ (atPoint 0 i).toNat + (atPoint 1 i).toNat + (atPoint 3 i).toNat at lo
      specialize cap i
      simp at ht
      omega
    have yes : good t (pat off f) := ⟨ho, by rw [hc]; simp at ht; omega⟩
    have nz : ¬ good t (pat off zero) := by
      simp [good,pat,zero,countP]
      simp at ht
      omega
    exact findGate off t ht gs legal seed f (readMember (wires gs) out (fun v => good t (pat off v)) nz yes) yes
  obtain ⟨i,hi,oi,ci⟩ := each 2 (by decide)
  obtain ⟨j,hj,oj,cj⟩ := each 3 (by decide)
  refine ⟨i,j,?_,hi,hj,?_,?_,?_,?_⟩
  · rintro rfl
    omega
  · exact (read (13+i.val) off).symm.trans oi
  · exact (read (13+j.val) off).symm.trans oj
  · rw [← ci, ← counts]
    congr 1
    apply Finset.filter_congr
    intro a _
    exact (congrArg (fun b => b = true) (read (13+i.val) (atPoint a))).symm.to_iff
  · intro a ha
    exact (read _ (atPoint a)).symm.trans (allThree _ _ cj a ha)
