import DynamicClosedTest

namespace PEqualNP.Outside.L_meta_670_aux.FastRecipe

structure Algebra (α : Type) where
  zero : α
  neg : α → α
  bin : Bool → α → α → α

def step {α : Type} (A : Algebra α) (rho : Fin 9 → α) (op : Nat) (w : List α) : List α :=
  if op ≤ 9 then rho (Fin.ofNat 9 (op-1)) :: w
  else match w with
  | [] => []
  | a :: tail =>
    if op = 10 then A.neg a :: tail
    else match tail with
    | [] => []
    | b :: rest => A.bin (decide (op = 12)) a b :: rest

def run {α : Type} (A : Algebra α) (rho : Fin 9 → α) : Nat → Nat → List α → List α
  | 0, _, w => w
  | fuel+1, code, w => if code = 0 then w else
    run A rho fuel (code >>> 4) (step A rho (code &&& 15) w)

def value {α : Type} (A : Algebra α) (rho : Fin 9 → α) (code : Nat) : α :=
  (run A rho 31 code []).headD A.zero

lemma step_map {α β : Type} (A : Algebra α) (B : Algebra β) (p : α → β)
    (hn : ∀ a, p (A.neg a) = B.neg (p a))
    (hb : ∀ d a b, p (A.bin d a b) = B.bin d (p a) (p b))
    (rho : Fin 9 → α) (op : Nat) (w : List α) :
    (step A rho op w).map p = step B (p ∘ rho) op (w.map p) := by
  unfold step
  by_cases h : op ≤ 9
  · simp [h, Function.comp_def]
  · simp only [ite_eq_right h]
    cases w with
    | nil => rfl
    | cons a w =>
      by_cases hi : op = 10
      · simp [hi,hn]
      · simp only [ite_eq_right hi,List.map_cons]
        cases w <;> simp [hb]

lemma run_map {α β : Type} (A : Algebra α) (B : Algebra β) (p : α → β)
    (hn : ∀ a, p (A.neg a) = B.neg (p a))
    (hb : ∀ d a b, p (A.bin d a b) = B.bin d (p a) (p b))
    (rho : Fin 9 → α) (fuel code : Nat) (w : List α) :
    (run A rho fuel code w).map p = run B (p ∘ rho) fuel code (w.map p) := by
  induction fuel generalizing code w with
  | zero => rfl
  | succ fuel ih =>
    by_cases h : code = 0 <;> simp only [run,h,ite_true,ite_false]
    rw [ih,step_map A B p hn hb]

lemma value_map {α β : Type} (A : Algebra α) (B : Algebra β) (p : α → β)
    (hz : p A.zero = B.zero)
    (hn : ∀ a, p (A.neg a) = B.neg (p a))
    (hb : ∀ d a b, p (A.bin d a b) = B.bin d (p a) (p b))
    (rho : Fin 9 → α) (code : Nat) :
    value B (p ∘ rho) code = p (value A rho code) := by
  have h := run_map A B p hn hb rho 31 code []
  simp only [List.map_nil] at h
  unfold value
  rw [← h]
  cases run A rho 31 code [] <;> simp [hz]

def newAlgebra : Algebra LiveCheck.Sig := ⟨LiveCheck.zero,LiveCheck.neg,LiveCheck.bin⟩
def oldAlgebra : Algebra Base1007.Sig := ⟨Base1007.zero,Base1007.neg,Base1007.bin⟩
def source (i : Fin 9) : LiveCheck.Sig := LiveCheck.raw.getD i.val LiveCheck.zero

def project (p : LiveCheck.Sig → Base1007.Sig) (rho : Fin 9 → Base1007.Sig)
    (hint : LiveCheck.Sig → Nat) (a : LiveCheck.Sig) : Base1007.Sig :=
  let code := hint a
  if value newAlgebra source code == a then value oldAlgebra rho code else p a

lemma project_eq (p : LiveCheck.Sig → Base1007.Sig) (rho : Fin 9 → Base1007.Sig)
    (hint : LiveCheck.Sig → Nat) (hz : p LiveCheck.zero = Base1007.zero)
    (hn : ∀ a, p (LiveCheck.neg a) = Base1007.neg (p a))
    (hb : ∀ d a b, p (LiveCheck.bin d a b) = Base1007.bin d (p a) (p b))
    (hr : rho = p ∘ source) : project p rho hint = p := by
  funext a
  simp only [project]
  split
  · rename_i h
    rw [hr,value_map newAlgebra oldAlgebra p hz hn hb,beq_iff_eq.mp h]
  · rfl

def values (p : LiveCheck.Sig → Base1007.Sig) (rho : Fin 9 → Base1007.Sig)
    (hint : LiveCheck.Sig → Nat) (v : List LiveCheck.Sig) : List Base1007.Sig :=
  v.map (project p rho hint)

lemma values_eq (p : LiveCheck.Sig → Base1007.Sig) (rho : Fin 9 → Base1007.Sig)
    (hint : LiveCheck.Sig → Nat) (hz : p LiveCheck.zero = Base1007.zero)
    (hn : ∀ a, p (LiveCheck.neg a) = Base1007.neg (p a))
    (hb : ∀ d a b, p (LiveCheck.bin d a b) = Base1007.bin d (p a) (p b))
    (hr : rho = p ∘ source) (v : List LiveCheck.Sig) : values p rho hint v = v.map p := by
  rw [values,project_eq p rho hint hz hn hb hr]

lemma oracle_zero (o : DynamicLeaf.Oracle) : o.project LiveCheck.zero = Base1007.zero := by
  have h := o.mapBin false LiveCheck.zero (LiveCheck.neg LiveCheck.zero)
  rw [o.mapNeg] at h
  have hn : LiveCheck.bin false LiveCheck.zero (LiveCheck.neg LiveCheck.zero) = LiveCheck.zero := by
    rfl
  rw [hn] at h
  rw [h]
  rcases he : o.project LiveCheck.zero with ⟨a,b⟩
  simp [Base1007.bin,Base1007.neg,Base1007.zero]

def initial {n : Nat} (oracles : Fin n → DynamicLeaf.Oracle)
    (rho : Fin n → Fin 9 → Base1007.Sig) (hint : LiveCheck.Sig → Nat)
    (v : List LiveCheck.Sig)
    (programs : Fin n → List PEqualNP.CircuitLowerBounds.Gate × List Nat) : DynamicLeaf.Context n :=
  fun i => ⟨(programs i).1,(programs i).2,values (oracles i).project (rho i) hint v⟩

lemma initial_valid {n : Nat} (oracles : Fin n → DynamicLeaf.Oracle)
    (rho : Fin n → Fin 9 → Base1007.Sig) (hint : LiveCheck.Sig → Nat)
    (hr : ∀ i, rho i = (oracles i).project ∘ source)
    (v : List LiveCheck.Sig)
    (programs : Fin n → List PEqualNP.CircuitLowerBounds.Gate × List Nat) :
    DynamicLeaf.Valid oracles v (initial oracles rho hint v programs) := by
  intro i
  exact values_eq (oracles i).project (rho i) hint (oracle_zero (oracles i))
    (oracles i).mapNeg (oracles i).mapBin (hr i) v

end PEqualNP.Outside.L_meta_670_aux.FastRecipe

namespace PEqualNP.Outside.L_meta_670_aux.FastRecipe

def leafCheck {n : Nat} (oracles : Fin n → DynamicLeaf.Oracle)
    (rho : Fin n → Fin 9 → Base1007.Sig) (hint : LiveCheck.Sig → Nat)
    (k t : Nat) (v : List LiveCheck.Sig)
    (programs : Fin n → List PEqualNP.CircuitLowerBounds.Gate × List Nat) : Bool :=
  decide v.Nodup && !(DynamicLeaf.search oracles k t v (initial oracles rho hint v programs))

lemma leafCheck_sound {n : Nat} (oracles : Fin n → DynamicLeaf.Oracle)
    (hsound : ∀ i, (oracles i).Sound)
    (rho : Fin n → Fin 9 → Base1007.Sig) (hint : LiveCheck.Sig → Nat)
    (hr : ∀ i, rho i = (oracles i).project ∘ source)
    {k t : Nat} {v : List LiveCheck.Sig}
    {programs : Fin n → List PEqualNP.CircuitLowerBounds.Gate × List Nat}
    (hc : leafCheck oracles rho hint k t v programs = true) : LiveCheck.Impossible k t v := by
  have hh := Bool.and_eq_true_iff.mp hc
  apply DynamicLeaf.search_sound oracles hsound k t v (initial oracles rho hint v programs)
    (of_decide_eq_true hh.1) (initial_valid oracles rho hint hr v programs)
  cases hs : DynamicLeaf.search oracles k t v (initial oracles rho hint v programs) with
  | false => rfl
  | true =>
    have hbad : False := by
      simpa only [hs,Bool.not_true,Bool.false_eq_true] using hh.2
    exact hbad.elim

end PEqualNP.Outside.L_meta_670_aux.FastRecipe
