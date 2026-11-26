import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18191_aux

open PEqualNP.CircuitLowerBounds

abbrev Count := Option ℕ

def least (a b : Count) : Count :=
  match a, b with
  | none, b => b
  | some a, none => some a
  | some a, some b => some (min a b)

def add (a b : Count) : Count :=
  match a, b with
  | some a, some b => some (a + b)
  | _, _ => none

def value (r : List Count) (g : Gate) : Count :=
  let xs := g.inputs.map fun i => r.getD i none
  match g.op with
  | .or => xs.foldl least none
  | .and => xs.foldl add (some 0)
  | _ => none

def step (r : List Count) (g : Gate) := r ++ [value r g]

theorem preserve (gs : List Gate) (r : List Count) (i : ℕ) (hi : i < r.length) :
    (gs.foldl step r).getD i none = r.getD i none := by
  induction gs generalizing r with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (step r g) (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

theorem at_gate (gs : List Gate) (r : List Count) (i : ℕ) (g : Gate) (a b : ℕ)
    (h : gs[i]? = some g) (ins : g.inputs = [a,b])
    (ha : a < r.length+i) (hb : b < r.length+i) :
    let w := gs.foldl step r
    w.getD (r.length+i) none = value w g := by
  induction gs generalizing r i with
  | nil => simp at h
  | cons f fs ih =>
    cases i with
    | zero =>
      have eq : f = g := by simpa using h
      subst f
      simp only [Nat.add_zero] at ha hb ⊢
      rw [List.foldl_cons]
      have len : (step r g).length = r.length+1 := by simp [step]
      rw [preserve fs (step r g) _ (by omega)]
      have va : (fs.foldl step (step r g)).getD a none = r.getD a none :=
        (preserve fs _ _ (by omega)).trans (List.getD_append _ _ _ _ ha)
      have vb : (fs.foldl step (step r g)).getD b none = r.getD b none :=
        (preserve fs _ _ (by omega)).trans (List.getD_append _ _ _ _ hb)
      have last : (step r g).getD r.length none = value r g := by simp [step, List.getD_eq_getElem?_getD]
      rw [last]
      simp only [value, ins, List.map_cons, List.map_nil, va, vb]
    | succ i =>
      have h' : fs[i]? = some g := by simpa using h
      have len : (step r f).length + i = r.length + (i+1) := by simp [step]; omega
      simpa only [List.foldl_cons,len] using ih (step r f) i h' (len ▸ ha) (len ▸ hb)

def cap (a : Count) : ℕ := min 2 (a.getD 2)

theorem cap_and (a b : Count) : cap (add (add (some 0) a) b) ≤ cap a + cap b := by
  cases a <;> cases b <;> simp [cap,add] <;> omega

theorem cap_or (a b : Count) : cap (least (least none a) b) ≤ min (cap a) (cap b) := by
  cases a <;> cases b <;> simp [cap,least] <;> omega

def initial (v : ℕ) : List Count :=
  (List.range 25).map fun i => if i = v then some 1 else if i ∈ ([0,7] : List ℕ) then some 0 else none

theorem initial_read (v i : ℕ) (hi : i < 25) :
    (initial v).getD i none = (if i = v then some 1 else if i ∈ ([0,7] : List ℕ) then some 0 else none) := by
  simp [initial,List.getD_eq_getElem?_getD,hi]

end PEqualNP.Outside.L_meta_18191_aux

open PEqualNP.Outside.L_meta_18191_aux PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_18191 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (25 : ℕ) + x2 ∧ x6 < (25 : ℕ) + x2) → (∀ x3 ∈ [(0 : ℕ), (7 : ℕ)], (2 : ℕ) ≤ ((PEqualNP.ReadK.scalarMults x1 (25 : ℕ) [(0 : ℕ), (7 : ℕ)] x3).getD x1.output Option.none).getD (2 : ℕ)) → ∀ (x4 : Bool), ∃ (x5 : ℕ → ℕ), x5 (if x4 = Bool.true then (0 : ℕ) else (7 : ℕ)) = (0 : ℕ) ∧ x5 (if x4 = Bool.true then (7 : ℕ) else (0 : ℕ)) ≤ (1 : ℕ) ∧ (∀ x6 < (25 : ℕ), x6 ≠ (0 : ℕ) → x6 ≠ (7 : ℕ) → x5 x6 = (2 : ℕ)) ∧ (2 : ℕ) ≤ x5 x1.output ∧ ∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate) (x8 x9 : ℕ), x1.gates[x6]? = Option.some x7 → x7.inputs = [x8, x9] → (x7.op = PEqualNP.CircuitLowerBounds.GateOp.and → x5 ((25 : ℕ) + x6) ≤ x5 x8 + x5 x9) ∧ (x7.op = PEqualNP.CircuitLowerBounds.GateOp.or → x5 ((25 : ℕ) + x6) ≤ Min.min (x5 x8) (x5 x9)) := by
  intro C hg hout side
  let v : ℕ := if side = true then 7 else 0
  let w := C.gates.foldl step (initial v)
  have calcEq : w = PEqualNP.ReadK.scalarMults C 25 [0,7] v := rfl
  have len : (initial v).length = 25 := by simp [initial]
  have inp (i : ℕ) (hi : i < 25) : w.getD i none =
      (if i = v then some 1 else if i ∈ ([0,7] : List ℕ) then some 0 else none) :=
    (preserve C.gates (initial v) i (len ▸ hi)).trans (initial_read v i hi)
  refine ⟨fun i => cap (w.getD i none), ?_, ?_, ?_, ?_, ?_⟩
  · change cap (w.getD (if side = true then 0 else 7) none) = 0
    rw [inp _ (by cases side <;> decide)]
    cases side <;> decide
  · change cap (w.getD (if side = true then 7 else 0) none) ≤ 1
    rw [inp _ (by cases side <;> decide)]
    cases side <;> decide
  · intro i hi h0 h7
    have hv : i ≠ v := by cases side <;> simp_all [v]
    change cap (w.getD i none) = 2
    rw [inp i hi]
    simp [hv, h0, h7, cap]
  · have hv : v ∈ ([0,7] : List ℕ) := by cases side <;> decide
    have hh := hout v hv
    change 2 ≤ cap (w.getD C.output none)
    rw [cap,calcEq]
    exact le_min (by decide) hh
  · intro i g a b hi ins
    obtain ⟨_, s, t, he, _, hs, ht⟩ := hg i g hi
    have pair : s = a ∧ t = b := by simpa using he.symm.trans ins
    obtain ⟨rfl,rfl⟩ := pair
    have hw := at_gate C.gates (initial v) i g s t hi ins (by simpa [len] using hs) (by simpa [len] using ht)
    change w.getD ((initial v).length+i) none = value w g at hw
    rw [len] at hw
    constructor
    · intro op
      simp only [hw, value, ins, List.map_cons, List.map_nil, op, List.foldl_cons, List.foldl_nil]
      exact cap_and _ _
    · intro op
      simp only [hw, value, ins, List.map_cons, List.map_nil, op, List.foldl_cons, List.foldl_nil]
      exact cap_or _ _
