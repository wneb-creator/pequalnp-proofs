import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Tree.Basic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3821_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def capGate (n : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (fun i => min i n)⟩

def capGates (n : ℕ) : List Gate → List Gate
  | [] => []
  | g :: gs => capGate n g :: capGates (n + 1) gs

def capCircuit (n : ℕ) (C : Circuit) : Circuit :=
  ⟨capGates n C.gates, min C.output (n + C.gates.length)⟩

lemma getD_min_length (w : List Bool) (i : ℕ) :
    w.getD (min i w.length) false = w.getD i false := by
  by_cases h : i < w.length
  · rw [Nat.min_eq_left (Nat.le_of_lt h)]
  · rw [Nat.min_eq_right (Nat.le_of_not_gt h)]
    rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]

lemma capGate_eval (w : List Bool) (g : Gate) :
    (capGate w.length g).op.eval
      ((capGate w.length g).inputs.map (fun i => w.getD i false)) =
    g.op.eval (g.inputs.map (fun i => w.getD i false)) := by
  simp only [capGate, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  exact getD_min_length w i

lemma capGates_length (n : ℕ) (gs : List Gate) :
    (capGates n gs).length = gs.length := by
  induction gs generalizing n with
  | nil => rfl
  | cons g gs ih => simp only [capGates, List.length_cons, ih]

lemma capGates_wires (gs : List Gate) (w : List Bool) :
    (capGates w.length gs).foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]) w =
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]) w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [capGates, List.foldl_cons, capGate_eval]
    have hn : (w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]).length =
        w.length + 1 := by simp
    rw [← hn]
    exact ih _

lemma capCircuit_wires (n : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n) :
    (capCircuit n C).wires x = C.wires x := by
  subst n
  exact capGates_wires C.gates x

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  obtain ⟨gs, o⟩ := C
  unfold Circuit.wires
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih]
    simp only [List.length_append, List.length_singleton]
    omega

lemma capCircuit_eval (n : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n) :
    (capCircuit n C).eval x = C.eval x := by
  unfold Circuit.eval
  rw [capCircuit_wires n C x hx]
  change (C.wires x).getD (min C.output (n + C.gates.length)) false =
    (C.wires x).getD C.output false
  rw [← hx, ← wires_length]
  exact getD_min_length _ _

lemma capCircuit_size (n : ℕ) (C : Circuit) :
    (capCircuit n C).size = C.size :=
  capGates_length n C.gates

lemma capGates_legal (n : ℕ) (gs : List Gate)
    (h : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2) :
    ∀ g ∈ capGates n gs,
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
        g.inputs.length ≤ 2 := by
  induction gs generalizing n with
  | nil => simp [capGates]
  | cons g gs ih =>
    intro g' hg'
    rcases List.mem_cons.mp hg' with rfl | hg'
    · simpa [capGate] using h g List.mem_cons_self
    · exact ih (n + 1) (fun g hg => h g (List.mem_cons_of_mem _ hg)) g' hg'

lemma capCircuit_legal (n : ℕ) (C : Circuit) (h : FanInTwo C) :
    FanInTwo (capCircuit n C) :=
  capGates_legal n C.gates h

lemma capGates_inputs_bound (n : ℕ) (gs : List Gate) :
    ∀ g ∈ capGates n gs, ∀ i ∈ g.inputs, i ≤ n + gs.length := by
  induction gs generalizing n with
  | nil => simp [capGates]
  | cons g gs ih =>
    intro g' hg' i hi
    rcases List.mem_cons.mp hg' with rfl | hg'
    · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi
      have := Nat.min_le_right j n
      simp only [List.length_cons]
      omega
    · have := ih (n + 1) g' hg' i hi
      simp only [List.length_cons]
      omega

lemma capCircuit_bounded (n s : ℕ) (C : Circuit) (h : C.size ≤ s) :
    (capCircuit n C).output ≤ n + s ∧
    ∀ g ∈ (capCircuit n C).gates, ∀ i ∈ g.inputs, i ≤ n + s := by
  have hs : C.gates.length ≤ s := h
  constructor
  · exact le_trans (Nat.min_le_right _ _) (Nat.add_le_add_left hs n)
  · intro g hg i hi
    exact le_trans (capGates_inputs_bound n C.gates g hg i hi)
      (Nat.add_le_add_left hs n)

lemma capCircuit_read (n : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n)
    (i : ℕ) :
    ((capCircuit n C).wires x).getD (min i (n + C.size)) false =
      (C.wires x).getD i false := by
  rw [capCircuit_wires n C x hx]
  change (C.wires x).getD (min i (n + C.gates.length)) false = _
  rw [← hx, ← wires_length]
  exact getD_min_length _ _

lemma bounded_pair (n s : ℕ) (C : Circuit) (a b : ℕ) (legal : FanInTwo C)
    (budget : C.size ≤ s) :
    ∃ (D : Circuit) (a' b' : ℕ),
      FanInTwo D ∧ D.size = C.size ∧ D.output ≤ n + s ∧
      (∀ g ∈ D.gates, ∀ i ∈ g.inputs, i ≤ n + s) ∧
      a' ≤ n + s ∧ b' ≤ n + s ∧
      ∀ x : List Bool, x.length = n →
        (D.wires x).getD a' false = (C.wires x).getD a false ∧
        (D.wires x).getD b' false = (C.wires x).getD b false := by
  refine ⟨capCircuit n C, min a (n + C.size), min b (n + C.size),
    capCircuit_legal n C legal, capCircuit_size n C,
    (capCircuit_bounded n s C budget).1, (capCircuit_bounded n s C budget).2,
    ?_, ?_, ?_⟩
  · exact le_trans (Nat.min_le_right _ _) (Nat.add_le_add_left budget n)
  · exact le_trans (Nat.min_le_right _ _) (Nat.add_le_add_left budget n)
  · intro x hx
    exact ⟨capCircuit_read n C x hx a, capCircuit_read n C x hx b⟩

def gateChoices (bound : ℕ) : List Gate :=
  [GateOp.and, GateOp.or, GateOp.not].flatMap fun op =>
    ⟨op, []⟩ :: ((List.range (bound + 1)).map (fun a => ⟨op, [a]⟩) ++
      (List.range (bound + 1)).flatMap fun a =>
        (List.range (bound + 1)).map (fun b => ⟨op, [a, b]⟩))

lemma mem_gateChoices (bound : ℕ) (g : Gate)
    (legal : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (arity : g.inputs.length ≤ 2) (bounded : ∀ i ∈ g.inputs, i ≤ bound) :
    g ∈ gateChoices bound := by
  obtain ⟨op, inputs⟩ := g
  have hop : op ∈ [GateOp.and, GateOp.or, GateOp.not] := by
    simpa using legal
  simp only [gateChoices, List.mem_flatMap]
  refine ⟨op, hop, ?_⟩
  match inputs with
  | [] => exact List.mem_cons_self
  | [a] =>
    apply List.mem_cons_of_mem
    apply List.mem_append_left
    apply List.mem_map.mpr
    exact ⟨a, List.mem_range.mpr (by have := bounded a (by simp); omega), rfl⟩
  | [a, b] =>
    apply List.mem_cons_of_mem
    apply List.mem_append_right
    apply List.mem_flatMap.mpr
    refine ⟨a, List.mem_range.mpr (by have := bounded a (by simp); omega), ?_⟩
    apply List.mem_map.mpr
    exact ⟨b, List.mem_range.mpr (by have := bounded b (by simp); omega), rfl⟩
  | a :: b :: c :: rest => simp only [List.length_cons] at arity; omega

lemma gateChoices_length (bound : ℕ) :
    (gateChoices bound).length = 3 * (1 + (bound + 1) + (bound + 1) ^ 2) := by
  simp [gateChoices, List.length_flatMap, pow_two, Nat.mul_add, Nat.add_mul]
  omega

def padCircuit (s : ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates ++ List.replicate (s - C.size) ⟨GateOp.or, []⟩, C.output⟩

lemma fold_padding (k : ℕ) (w : List Bool) :
    (List.replicate k (⟨GateOp.or, []⟩ : Gate)).foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]) w =
      w ++ List.replicate k false := by
  induction k generalizing w with
  | zero => simp
  | succ k ih =>
    simp only [List.replicate_succ, List.foldl_cons]
    change (List.replicate k (⟨GateOp.or, []⟩ : Gate)).foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))])
      (w ++ [false]) = _
    rw [ih]
    simp only [List.append_assoc, List.singleton_append]

lemma padCircuit_wires (s : ℕ) (C : Circuit) (x : List Bool) :
    (padCircuit s C).wires x = C.wires x ++ List.replicate (s - C.size) false := by
  unfold Circuit.wires padCircuit
  rw [List.foldl_append, fold_padding]

lemma getD_append_false (w : List Bool) (k i : ℕ) :
    (w ++ List.replicate k false).getD i false = w.getD i false := by
  by_cases h : i < w.length
  · exact List.getD_append _ _ _ _ h
  · rw [List.getD_append_right _ _ _ _ (by omega),
      List.getD_eq_default w false (by omega : w.length ≤ i)]
    simp [List.getD_eq_getElem?_getD]

lemma padCircuit_read (s : ℕ) (C : Circuit) (x : List Bool) (i : ℕ) :
    ((padCircuit s C).wires x).getD i false = (C.wires x).getD i false := by
  rw [padCircuit_wires]
  exact getD_append_false _ _ _

lemma padCircuit_size (s : ℕ) (C : Circuit) (h : C.size ≤ s) :
    (padCircuit s C).size = s := by
  have : C.gates.length ≤ s := h
  simp only [padCircuit, Circuit.size, List.length_append, List.length_replicate]
  omega

lemma padCircuit_legal (s : ℕ) (C : Circuit) (h : FanInTwo C) :
    FanInTwo (padCircuit s C) := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact h g hg
  · have heq := (List.mem_replicate.mp hg).2
    subst g
    simp

lemma fixed_bounded_pair (n s : ℕ) (C : Circuit) (a b : ℕ) (legal : FanInTwo C)
    (budget : C.size ≤ s) :
    ∃ (D : Circuit) (a' b' : ℕ),
      FanInTwo D ∧ D.size = s ∧ D.output ≤ n + s ∧
      (∀ g ∈ D.gates, g ∈ gateChoices (n + s)) ∧
      a' ≤ n + s ∧ b' ≤ n + s ∧
      ∀ x : List Bool, x.length = n →
        (D.wires x).getD a' false = (C.wires x).getD a false ∧
        (D.wires x).getD b' false = (C.wires x).getD b false := by
  have hsize := padCircuit_size s C budget
  obtain ⟨D, a', b', hD, hlen, hout, hbound, ha, hb, heval⟩ :=
    bounded_pair n s (padCircuit s C) a b (padCircuit_legal s C legal) (by omega)
  refine ⟨D, a', b', hD, hlen.trans hsize, hout, ?_, ha, hb, ?_⟩
  · intro g hg
    exact mem_gateChoices (n + s) g (hD g hg).1 (hD g hg).2 (hbound g hg)
  · intro x hx
    exact ⟨((heval x hx).1).trans (padCircuit_read s C x a),
      ((heval x hx).2).trans (padCircuit_read s C x b)⟩

lemma gateChoices_inputs_bound (bound : ℕ) (g : Gate) (hg : g ∈ gateChoices bound) :
    ∀ i ∈ g.inputs, i ≤ bound := by
  obtain ⟨op, _, hg⟩ := List.mem_flatMap.mp hg
  rcases List.mem_cons.mp hg with rfl | hg
  · simp
  · rcases List.mem_append.mp hg with hg | hg
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
      intro i hi
      have hi' : i = a := List.mem_singleton.mp hi
      subst i
      have := List.mem_range.mp ha
      omega
    · obtain ⟨a, ha, hg⟩ := List.mem_flatMap.mp hg
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hg
      intro i hi
      have ha' := List.mem_range.mp ha
      have hb' := List.mem_range.mp hb
      rcases List.mem_cons.mp hi with rfl | hi
      · omega
      · have hi' : i = b := List.mem_singleton.mp hi
        omega

lemma wire_true_lt (n : ℕ) (C : Circuit) (i : ℕ)
    (h : ∃ x : Fin n → Bool, (C.wires (List.ofFn x)).getD i false = true) :
    i < n + C.size := by
  obtain ⟨x, hx⟩ := h
  by_contra hi
  have hlen : (C.wires (List.ofFn x)).length ≤ i := by
    rw [wires_length, List.length_ofFn]
    change n + C.size ≤ i
    omega
  rw [List.getD_eq_default _ _ hlen] at hx
  contradiction

lemma finite_source_pair (n s : ℕ) (C : Circuit) (a b : ℕ) (legal : FanInTwo C)
    (budget : C.size ≤ s)
    (ha : ∃ x : Fin n → Bool, (C.wires (List.ofFn x)).getD a false = true)
    (hb : ∃ x : Fin n → Bool, (C.wires (List.ofFn x)).getD b false = true) :
    ∃ (D : Circuit) (a' b' : Fin (n + s)),
      D.output = 0 ∧ FanInTwo D ∧ D.size = s ∧
      (∀ g ∈ D.gates, ∀ i ∈ g.inputs, i ≤ n + s) ∧
      ∀ x : Fin n → Bool,
        (D.wires (List.ofFn x)).getD a'.val false =
          (C.wires (List.ofFn x)).getD a false ∧
        (D.wires (List.ofFn x)).getD b'.val false =
          (C.wires (List.ofFn x)).getD b false := by
  obtain ⟨D, a', b', hD, hsize, _, hchoices, _, _, heval⟩ :=
    fixed_bounded_pair n s C a b legal budget
  have ha' : a' < n + s := by
    rw [← hsize]
    apply wire_true_lt
    obtain ⟨x, hx⟩ := ha
    exact ⟨x, ((heval _ (by simp)).1).trans hx⟩
  have hb' : b' < n + s := by
    rw [← hsize]
    apply wire_true_lt
    obtain ⟨x, hx⟩ := hb
    exact ⟨x, ((heval _ (by simp)).2).trans hx⟩
  refine ⟨⟨D.gates, 0⟩, ⟨a', ha'⟩, ⟨b', hb'⟩, rfl, hD, hsize, ?_, ?_⟩
  · intro g hg
    exact gateChoices_inputs_bound (n + s) g (hchoices g hg)
  · intro x
    exact heval _ (by simp)

namespace KernelLrat

noncomputable section Replay

def neg (l : Nat) : Nat :=
  match Nat.beq (Nat.mod l (nat_lit 2)) (nat_lit 0) with
  | true => Nat.add l (nat_lit 1)
  | false => Nat.sub l (nat_lit 1)

def bit (T l : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight T l) (nat_lit 1)) (nat_lit 1)

def setBit (T u : Nat) : Nat := Nat.lor T (Nat.shiftLeft (nat_lit 1) u)

lemma bit_eq_testBit (T l : Nat) : bit T l = T.testBit l := by
  have h : Nat.land (Nat.shiftRight T l) 1 = (T >>> l) % 2 := Nat.and_one_is_mod _
  unfold bit
  rw [h, Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow, Bool.eq_iff_iff,
    decide_eq_true_eq]
  exact ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl _⟩

lemma bit_setBit (T u l : Nat) : bit (setBit T u) l = (bit T l || decide (u = l)) := by
  have h : setBit T u = T ||| (1 <<< u) := rfl
  rw [h, bit_eq_testBit, bit_eq_testBit, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]

def litVal (a : Nat → Bool) (l : Nat) : Bool := a (l / 2) == (l % 2 == 0)

def ClauseSat (a : Nat → Bool) (c : List Nat) : Prop := ∃ l ∈ c, litVal a l = true

def FormulaSat (F : List (List Nat)) : Prop := ∃ a : Nat → Bool, ∀ c ∈ F, ClauseSat a c

lemma litVal_neg (a : Nat → Bool) (l : Nat) : litVal a (neg l) = !litVal a l := by
  have hn : neg l = if l % 2 = 0 then l + 1 else l - 1 := by
    unfold neg
    cases hb : Nat.beq (Nat.mod l 2) 0 with
    | false =>
      have h1 : ¬ (l % 2 = 0) := Nat.ne_of_beq_eq_false hb
      rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]; rfl
    | true =>
      have h1 : l % 2 = 0 := Nat.eq_of_beq_eq_true hb
      rw [ite_eq_left_of_eq_true _ _ (eq_true h1)]
  rw [hn]
  unfold litVal
  by_cases h : l % 2 = 0
  · have h1 : (l + 1) / 2 = l / 2 := by omega
    have h2 : (l + 1) % 2 = 1 := by omega
    rw [ite_eq_left_of_eq_true _ _ (eq_true h), h1, h2, h]
    cases a (l / 2) <;> rfl
  · have h1 : (l - 1) / 2 = l / 2 := by omega
    have h2 : (l - 1) % 2 = 0 := by omega
    have h3 : l % 2 = 1 := by omega
    rw [ite_eq_right_of_eq_false _ _ (eq_false h), h1, h2, h3]
    cases a (l / 2) <;> rfl

abbrev Trie := BinaryTree (Option Nat)

namespace Trie

def get (t : Trie) : Nat → Option Nat :=
  BinaryTree.rec (motive := fun _ => Nat → Option Nat) (fun _ => none)
    (fun v _ _ ihl ihr k =>
      Bool.rec
        (Bool.rec (ihr (Nat.sub (Nat.div k (nat_lit 2)) (nat_lit 1))) (ihl (Nat.div k (nat_lit 2)))
          (Nat.beq (Nat.mod k (nat_lit 2)) (nat_lit 1)))
        v (Nat.beq k (nat_lit 0))) t

def root (t : Trie) : Option Nat := BinaryTree.rec (motive := fun _ => Option Nat) none (fun v _ _ _ _ => v) t
def left (t : Trie) : Trie := BinaryTree.rec (motive := fun _ => Trie) .nil (fun _ l _ _ _ => l) t
def right (t : Trie) : Trie := BinaryTree.rec (motive := fun _ => Trie) .nil (fun _ _ r _ _ => r) t

def set (fuel : Nat) : Trie → Nat → Option Nat → Trie :=
  Nat.rec (motive := fun _ => Trie → Nat → Option Nat → Trie) (fun t _ _ => t)
    (fun _ ih t k o =>
      Bool.rec
        (Bool.rec (.node t.root t.left (ih t.right (Nat.sub (Nat.div k (nat_lit 2)) (nat_lit 1)) o))
          (.node t.root (ih t.left (Nat.div k (nat_lit 2)) o) t.right)
          (Nat.beq (Nat.mod k (nat_lit 2)) (nat_lit 1)))
        (.node o t.left t.right) (Nat.beq k (nat_lit 0))) fuel

def All (P : Nat → Prop) : Trie → Prop
  | .nil => True
  | .node v l r => (∀ c, v = some c → P c) ∧ All P l ∧ All P r

lemma All.get {P : Nat → Prop} :
    ∀ {t : Trie} {k : Nat} {c : Nat}, All P t → (Trie.get t) k = some c → P c
  | .nil, _, _, _, h => by simp [Trie.get] at h
  | .node v l r, k, c, ⟨hv, hl, hr⟩, h => by
    change Bool.rec (Bool.rec ((Trie.get r) _) ((Trie.get l) _) _) v _ = some c at h
    cases h0 : Nat.beq k 0
    · rw [h0] at h
      cases h1 : Nat.beq (Nat.mod k 2) 1
      · rw [h1] at h; exact All.get hr h
      · rw [h1] at h; exact All.get hl h
    · rw [h0] at h; exact hv c h

lemma All.root {P : Nat → Prop} {t : Trie} (h : All P t) :
    ∀ c, t.root = some c → P c := by
  cases t with
  | nil => intro c hc; cases hc
  | node v l r => exact h.1

lemma All.left {P : Nat → Prop} {t : Trie} (h : All P t) : All P t.left := by
  cases t with
  | nil => trivial
  | node v l r => exact h.2.1

lemma All.right {P : Nat → Prop} {t : Trie} (h : All P t) : All P t.right := by
  cases t with
  | nil => trivial
  | node v l r => exact h.2.2

lemma All.set {P : Nat → Prop} :
    ∀ (fuel : Nat) {t : Trie} (k : Nat) {o : Option Nat},
      All P t → (∀ c, o = some c → P c) → All P (Trie.set fuel t k o)
  | 0, _, _, _, ht, _ => ht
  | fuel + 1, t, k, o, ht, ho => by
    change All P (Bool.rec (Bool.rec (.node t.root t.left (Trie.set fuel t.right _ o))
      (.node t.root (Trie.set fuel t.left _ o) t.right) _) (.node o t.left t.right) _)
    cases h0 : Nat.beq k 0
    · cases h1 : Nat.beq (Nat.mod k 2) 1
      · exact ⟨ht.root, ht.left, All.set fuel _ ht.right ho⟩
      · exact ⟨ht.root, All.set fuel _ ht.left ho, ht.right⟩
    · exact ⟨ho, ht.left, ht.right⟩

end Trie

lemma bit_land (x y l : Nat) : bit (Nat.land x y) l = (bit x l && bit y l) := by
  rw [bit_eq_testBit, bit_eq_testBit, bit_eq_testBit]
  exact Nat.testBit_and x y l

lemma bit_xor (x y l : Nat) : bit (Nat.xor x y) l = (bit x l ^^ bit y l) := by
  rw [bit_eq_testBit, bit_eq_testBit, bit_eq_testBit]
  exact Nat.testBit_xor x y l

lemma bit_zero (l : Nat) : bit 0 l = false := by
  rw [bit_eq_testBit]; exact Nat.zero_testBit l

lemma bit_pow (u l : Nat) : bit (Nat.shiftLeft 1 u) l = decide (u = l) := by
  have h : Nat.shiftLeft 1 u = 1 <<< u := rfl
  rw [bit_eq_testBit, h, Nat.one_shiftLeft, Nat.testBit_two_pow]

def mask : List Nat → Nat
  | [] => 0
  | l :: ls => setBit (mask ls) l

lemma bit_mask : ∀ (c : List Nat) (l : Nat), bit (mask c) l = true ↔ l ∈ c
  | [], l => by simp [mask, bit_zero]
  | x :: xs, l => by
    rw [mask, bit_setBit, Bool.or_eq_true, bit_mask xs l, decide_eq_true_eq, List.mem_cons]
    exact ⟨fun h => h.elim Or.inr (fun h => Or.inl h.symm),
      fun h => h.elim (fun h => Or.inr h.symm) Or.inl⟩

abbrev Cont := Trie → Nat → Bool → Nat → Nat → Nat → Bool

def stepRead (k : Cont) (db : Trie) (id C F P x : Nat) : Bool :=
  Bool.rec
    (Bool.rec (k db id false (setBit C x) F P) (k db id true C C 0) (Nat.beq x (nat_lit 0)))
    (k db (Nat.succ x) false C F P)
    (Nat.beq id (nat_lit 0))

def stepUnit (k : Cont) (db : Trie) (id C F P x : Nat) : Bool :=
  Bool.rec false (k db id true C (setBit F (neg x)) 0) (Nat.beq P (Nat.shiftLeft (nat_lit 1) x))

def stepClause (k : Cont) (db : Trie) (id C F D : Nat) : Bool :=
  Bool.rec (k db id true C F (Nat.xor D (Nat.land D F)))
    (Bool.rec (k (db.set 64 (Nat.sub id (nat_lit 1)) (some C)) 0 false 0 0 0) true
      (Nat.beq C (nat_lit 0)))
    (Nat.beq (Nat.xor D (Nat.land D F)) (nat_lit 0))

def stepHint (k : Cont) (db : Trie) (id C F x : Nat) : Bool :=
  Option.rec false (stepClause k db id C F) ((Trie.get db) x)

def tokenStep (k : Cont) (x : Nat) : Cont := fun db id mode C F P =>
  Bool.rec (stepRead k db id C F P x)
    (Bool.rec (stepUnit k db id C F P x) (stepHint k db id C F x) (Nat.beq P (nat_lit 0)))
    mode

def stop : Cont := fun _ _ _ _ _ _ => false

def runS (e : Cont) (toks : List Nat) : Cont :=
  List.rec (motive := fun _ => Cont) e (fun x _ k => tokenStep k x) toks

def runWord (W M fuel w : Nat) (k : Cont) : Cont :=
  Nat.rec (motive := fun _ => Nat → Cont) (fun _ => k)
    (fun _ ih w =>
      Bool.rec (tokenStep (ih (Nat.shiftRight w W)) (Nat.land w M)) k (Nat.beq w (nat_lit 1)))
    fuel w

def fuelW : Nat := 1024

def runW (e : Cont) (W : Nat) (words : List Nat) : Cont :=
  List.rec (motive := fun _ => Cont) e
    (fun w _ k => runWord W (Nat.sub (Nat.shiftLeft (nat_lit 1) W) (nat_lit 1)) fuelW w k) words

def entryIn (db : Trie) (e : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun q lits _ =>
      Option.rec false (fun D => Nat.beq D (mask lits)) ((Trie.get db) (Nat.sub q (nat_lit 1)))) e

def verify (B : List (List Nat)) : Cont := fun db _ _ _ _ _ =>
  List.rec (motive := fun _ => Bool) true (fun e _ ih => Bool.rec false ih (entryIn db e)) B

def loadF : List (List Nat) → List Nat → Trie → Trie
  | [], _, t => t
  | _ :: _, [], t => t
  | c :: cs, q :: qs, t =>
    loadF cs qs (Bool.rec (t.set 64 (Nat.sub q 1) (some (mask c))) t (Nat.beq q 0))

def loadB : List (List Nat) → Trie → Trie
  | [], t => t
  | [] :: es, t => loadB es t
  | (q :: lits) :: es, t => loadB es (t.set 64 (Nat.sub q 1) (some (mask lits)))

def check (F : List (List Nat)) (fk : List Nat) (toks : List Nat) : Bool :=
  runS stop toks (loadF F fk .nil) 0 false 0 0 0

def checkW (F : List (List Nat)) (fk : List Nat) (W : Nat) (words : List Nat) : Bool :=
  runW stop W words (loadF F fk .nil) 0 false 0 0 0

def checkFirst (F : List (List Nat)) (fk : List Nat) (W : Nat) (words : List Nat)
    (B : List (List Nat)) : Bool :=
  runW (verify B) W words (loadF F fk .nil) 0 false 0 0 0

def checkSeg (B : List (List Nat)) (W : Nat) (words : List Nat) (B' : List (List Nat)) : Bool :=
  runW (verify B') W words (loadB B .nil) 0 false 0 0 0

def checkLast (B : List (List Nat)) (W : Nat) (words : List Nat) : Bool :=
  runW stop W words (loadB B .nil) 0 false 0 0 0

section Soundness

variable (a : Nat → Bool)

def MaskSat (m : Nat) : Prop := ∃ l, bit m l = true ∧ litVal a l = true

def BitsFalse (F : Nat) : Prop := ∀ l, bit F l = true → litVal a l = false

def EntriesSat (B : List (List Nat)) : Prop := ∀ e ∈ B, ClauseSat a e.tail

def HintInv (C F P : Nat) : Prop :=
  (∀ x, bit C x = true → litVal a x = false) →
    BitsFalse a F ∧ (P = 0 ∨ ∃ w, bit P w = true ∧ litVal a w = true)

lemma witness_U {F D : Nat} (hF : BitsFalse a F) (hD : MaskSat a D) :
    ∃ w, bit (Nat.xor D (Nat.land D F)) w = true ∧ litVal a w = true := by
  obtain ⟨w, hwD, hwv⟩ := hD
  have hwF : bit F w = false := by
    cases hb : bit F w
    · rfl
    · rw [hF w hb] at hwv; exact absurd hwv (by simp)
  exact ⟨w, by rw [bit_xor, bit_land, hwD, hwF]; rfl, hwv⟩

def Good (Q : Prop) (k : Cont) : Prop :=
  ∀ db id mode C F P, db.All (MaskSat a) → (mode = true → HintInv a C F P) →
    k db id mode C F P = true → Q

lemma stop_good (Q : Prop) : Good a Q stop := by
  intro _ _ _ _ _ _ _ _ h
  exact absurd h (by simp [stop])

lemma tokenStep_good {Q : Prop} {k : Cont} (hk : Good a Q k) (x : Nat) :
    Good a Q (tokenStep k x) := by
  intro db id mode C F P hdb hinv h
  change Bool.rec (stepRead k db id C F P x)
    (Bool.rec (stepUnit k db id C F P x) (stepHint k db id C F x) (Nat.beq P 0)) mode = true at h
  cases mode with
  | false =>
    change Bool.rec
      (Bool.rec (k db id false (setBit C x) F P) (k db id true C C 0) (Nat.beq x 0))
      (k db (Nat.succ x) false C F P) (Nat.beq id 0) = true at h
    cases hi : Nat.beq id 0
    · rw [hi] at h
      cases hx : Nat.beq x 0
      · rw [hx] at h
        exact hk db id false _ F P hdb (by simp) h
      · rw [hx] at h
        exact hk db id true C C 0 hdb (fun _ hC => ⟨hC, Or.inl rfl⟩) h
    · rw [hi] at h
      exact hk db _ false C F P hdb (by simp) h
  | true =>
    have hinv := hinv rfl
    cases hP : Nat.beq P 0
    ·
      rw [hP] at h
      change Bool.rec false (k db id true C (setBit F (neg x)) 0)
        (Nat.beq P (Nat.shiftLeft 1 x)) = true at h
      cases hu : Nat.beq P (Nat.shiftLeft 1 x)
      · rw [hu] at h; exact absurd h (by simp)
      · rw [hu] at h
        refine hk db id true C _ 0 hdb (fun _ hC => ⟨?_, Or.inl rfl⟩) h
        obtain ⟨hF, hPw⟩ := hinv hC
        rcases hPw with hP0 | ⟨w, hw, hwv⟩
        · rw [hP0] at hP; exact absurd hP (by simp)
        · rw [Nat.eq_of_beq_eq_true hu, bit_pow, decide_eq_true_eq] at hw
          subst hw
          intro l hl
          rw [bit_setBit, Bool.or_eq_true, decide_eq_true_eq] at hl
          rcases hl with hl | rfl
          · exact hF l hl
          · rw [litVal_neg, hwv]; rfl
    ·
      rw [hP] at h
      change Option.rec false (stepClause k db id C F) ((Trie.get db) x) = true at h
      cases hg : (Trie.get db) x with
      | none => rw [hg] at h; exact absurd h (by simp)
      | some D =>
        rw [hg] at h
        have hD : MaskSat a D := Trie.All.get hdb hg
        change Bool.rec (k db id true C F (Nat.xor D (Nat.land D F)))
          (Bool.rec (k (db.set 64 (Nat.sub id 1) (some C)) 0 false 0 0 0) true
            (Nat.beq C 0))
          (Nat.beq (Nat.xor D (Nat.land D F)) 0) = true at h
        cases hU : Nat.beq (Nat.xor D (Nat.land D F)) 0
        · rw [hU] at h
          refine hk db id true C F _ hdb (fun _ hC => ⟨(hinv hC).1, Or.inr ?_⟩) h
          exact witness_U a (hinv hC).1 hD
        · rw [hU] at h

          have hCsat : MaskSat a C := by
            apply Classical.byContradiction
            intro hn
            have hC : ∀ y, bit C y = true → litVal a y = false := by
              intro y hy
              cases hv : litVal a y
              · rfl
              · exact absurd ⟨y, hy, hv⟩ hn
            obtain ⟨w, hw, _⟩ := witness_U a (hinv hC).1 hD
            rw [Nat.eq_of_beq_eq_true hU, bit_zero] at hw
            exact absurd hw (by simp)
          cases hC0 : Nat.beq C 0
          · rw [hC0] at h
            exact hk _ _ false 0 0 0
              (Trie.All.set 64 _ hdb (fun c hc => by cases hc; exact hCsat)) (by simp) h
          · obtain ⟨w, hw, _⟩ := hCsat
            rw [Nat.eq_of_beq_eq_true hC0, bit_zero] at hw
            exact absurd hw (by simp)

lemma runS_good {Q : Prop} {e : Cont} (he : Good a Q e) :
    ∀ toks : List Nat, Good a Q (runS e toks)
  | [] => he
  | x :: xs => tokenStep_good a (runS_good he xs) x

lemma runWord_good {Q : Prop} (W M : Nat) {k : Cont} (hk : Good a Q k) :
    ∀ fuel w, Good a Q (runWord W M fuel w k)
  | 0, _ => hk
  | fuel + 1, w => by
    change Good a Q (Bool.rec (tokenStep (runWord W M fuel (Nat.shiftRight w W) k)
      (Nat.land w M)) k (Nat.beq w 1))
    cases Nat.beq w 1
    · exact tokenStep_good a (runWord_good W M hk fuel _) _
    · exact hk

lemma runW_good {Q : Prop} {e : Cont} (he : Good a Q e) (W : Nat) :
    ∀ words : List Nat, Good a Q (runW e W words)
  | [] => he
  | w :: ws => by
    have h := runWord_good a W (Nat.sub (Nat.shiftLeft 1 W) 1) (runW_good he W ws) fuelW w
    exact h

lemma clauseSat_of_maskSat {c : List Nat} (h : MaskSat a (mask c)) : ClauseSat a c := by
  obtain ⟨l, hl, hv⟩ := h
  exact ⟨l, (bit_mask c l).mp hl, hv⟩

lemma maskSat_of_clauseSat {c : List Nat} (h : ClauseSat a c) : MaskSat a (mask c) := by
  obtain ⟨l, hl, hv⟩ := h
  exact ⟨l, (bit_mask c l).mpr hl, hv⟩

lemma verify_good (B : List (List Nat)) : Good a (EntriesSat a B) (verify B) := by
  intro db _ _ _ _ _ hdb _ h
  induction B with
  | nil => intro e he; simp at he
  | cons e es ih =>
    change Bool.rec false (List.rec (motive := fun _ => Bool) true
      (fun e _ ih => Bool.rec false ih (entryIn db e)) es) (entryIn db e) = true at h
    cases he : entryIn db e
    · rw [he] at h; exact absurd h (by simp)
    · rw [he] at h
      intro e' he'
      rcases List.mem_cons.mp he' with rfl | he'
      · cases e' with
        | nil => simp [entryIn] at he
        | cons q lits =>
          change Option.rec false (fun D => Nat.beq D (mask lits)) ((Trie.get db) (Nat.sub q 1)) = true
            at he
          cases hg : (Trie.get db) (Nat.sub q 1) with
          | none => rw [hg] at he; exact absurd he (by simp)
          | some D =>
            rw [hg] at he
            have hD := Trie.All.get hdb hg
            rw [Nat.eq_of_beq_eq_true he] at hD
            exact clauseSat_of_maskSat a hD
      · exact ih h e' he'

lemma loadF_all : ∀ (F : List (List Nat)) (fk : List Nat) {t : Trie}, t.All (MaskSat a) →
    (∀ c ∈ F, ClauseSat a c) → (loadF F fk t).All (MaskSat a)
  | [], _, _, ht, _ => ht
  | _ :: _, [], _, ht, _ => ht
  | c :: cs, q :: qs, t, ht, hF => by
    unfold loadF
    apply loadF_all cs qs _ (fun c' hc' => hF c' (List.mem_cons_of_mem _ hc'))
    cases Nat.beq q 0
    · exact Trie.All.set 64 _ ht (fun c' hc' => by
        cases hc'; exact maskSat_of_clauseSat a (hF c List.mem_cons_self))
    · exact ht

lemma loadB_all : ∀ (B : List (List Nat)) {t : Trie}, t.All (MaskSat a) →
    EntriesSat a B → (loadB B t).All (MaskSat a)
  | [], _, ht, _ => ht
  | [] :: es, _, ht, hB => loadB_all es ht (fun e he => hB e (List.mem_cons_of_mem _ he))
  | (q :: lits) :: es, t, ht, hB => by
    unfold loadB
    apply loadB_all es _ (fun e he => hB e (List.mem_cons_of_mem _ he))
    exact Trie.All.set 64 _ ht (fun c' hc' => by
      cases hc'; exact maskSat_of_clauseSat a (hB _ List.mem_cons_self))

end Soundness

lemma check_sound (F : List (List Nat)) (fk toks : List Nat) (h : check F fk toks = true) :
    ¬ FormulaSat F := by
  rintro ⟨a, ha⟩
  exact runS_good a (stop_good a False) toks _ _ false 0 0 0
    (loadF_all a F fk (t := .nil) trivial ha) (by simp) h

lemma checkW_sound (F : List (List Nat)) (fk : List Nat) (W : Nat) (words : List Nat)
    (h : checkW F fk W words = true) : ¬ FormulaSat F := by
  rintro ⟨a, ha⟩
  exact runW_good a (stop_good a False) W words _ _ false 0 0 0
    (loadF_all a F fk (t := .nil) trivial ha) (by simp) h

lemma checkFirst_sound (F : List (List Nat)) (fk : List Nat) (W : Nat) (words : List Nat)
    (B : List (List Nat)) (h : checkFirst F fk W words B = true) :
    ∀ a, (∀ c ∈ F, ClauseSat a c) → EntriesSat a B := fun a ha =>
  runW_good a (verify_good a B) W words _ _ false 0 0 0
    (loadF_all a F fk (t := .nil) trivial ha) (by simp) h

lemma checkSeg_sound (B : List (List Nat)) (W : Nat) (words : List Nat) (B' : List (List Nat))
    (h : checkSeg B W words B' = true) : ∀ a, EntriesSat a B → EntriesSat a B' := fun a hB =>
  runW_good a (verify_good a B') W words _ _ false 0 0 0
    (loadB_all a B (t := .nil) trivial hB) (by simp) h

lemma checkLast_sound (B : List (List Nat)) (W : Nat) (words : List Nat)
    (h : checkLast B W words = true) : ∀ a, EntriesSat a B → False := fun a hB =>
  runW_good a (stop_good a False) W words _ _ false 0 0 0
    (loadB_all a B (t := .nil) trivial hB) (by simp) h

def unpackWord (W M fuel w : Nat) (rest : List Nat) : List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => rest)
    (fun _ ih w => Bool.rec (Nat.land w M :: ih (Nat.shiftRight w W)) rest (Nat.beq w (nat_lit 1)))
    fuel w

def unpack (W : Nat) (words : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) []
    (fun w _ ih => unpackWord W (Nat.sub (Nat.shiftLeft (nat_lit 1) W) (nat_lit 1)) 1024 w ih)
    words

def decodeF (toks : List Nat) : List (List Nat) :=
  List.rec (motive := fun _ => List (List Nat)) []
    (fun x _ acc =>
      Bool.rec (List.rec (motive := fun _ => List (List Nat)) [[x]] (fun c cs _ => (x :: c) :: cs) acc)
        ([] :: acc) (Nat.beq x (nat_lit 0)))
    toks

end Replay

end KernelLrat

end PEqualNP.Outside.L_meta_3821_aux
