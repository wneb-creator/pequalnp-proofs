import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2732_aux.Packed

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma getD_le {w v : List Bool} (h : List.Forall₂ (fun a b => a ≤ b) w v) (i : ℕ) :
    w.getD i false ≤ v.getD i false := by
  induction h generalizing i with
  | nil => simp
  | cons hab _ ih =>
    cases i with
    | zero => simpa using hab
    | succ i => simpa using ih i

lemma bool_le {a b : Bool} : a ≤ b ↔ (a = true → b = true) := by
  cases a <;> cases b <;> decide

lemma gate_le (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) {w v : List Bool}
    (h : List.Forall₂ (fun a b => a ≤ b) w v) :
    g.op.eval (g.inputs.map fun i => w.getD i false) ≤
      g.op.eval (g.inputs.map fun i => v.getD i false) := by
  rw [bool_le]
  rcases hg with hg | hg
  · rw [hg]
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
    intro hx x hx2
    obtain ⟨i, hi, rfl⟩ := hx2
    exact bool_le.mp (getD_le h i) (hx _ ⟨i, hi, rfl⟩)
  · rw [hg]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨x, ⟨i, hi, rfl⟩, hx⟩
    exact ⟨_, ⟨i, hi, rfl⟩, bool_le.mp (getD_le h i) hx⟩

lemma fold_le (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ w v : List Bool, List.Forall₂ (fun a b => a ≤ b) w v →
      List.Forall₂ (fun a b => a ≤ b) (gs.foldl step w) (gs.foldl step v) := by
  induction gs with
  | nil => intro w v h; simpa using h
  | cons g gs ih =>
    intro w v h
    simp only [List.foldl_cons]
    apply ih (fun g2 hg2 => hgs g2 (List.mem_cons_of_mem _ hg2))
    exact List.rel_append h (List.Forall₂.cons (gate_le g (hgs g List.mem_cons_self) h) List.Forall₂.nil)

lemma mono (n : ℕ) (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) (o : ℕ) :
    (gs.foldl step (List.ofFn x)).getD o false ≤ (gs.foldl step (List.ofFn y)).getD o false := by
  have h0 : List.Forall₂ (fun a b => a ≤ b) (List.ofFn x) (List.ofFn y) := by
    rw [List.forall₂_iff_get]
    refine ⟨by simp only [List.length_ofFn], fun i h1 h2 => ?_⟩
    simp only [List.get_eq_getElem, List.getElem_ofFn]
    exact bool_le.mpr (hxy _)
  exact getD_le (fold_le gs hgs _ _ h0) o


def nums : List ℕ := [95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752]

def edges : List (ℕ × ℕ) := [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]

def cols : List ℕ := [127, 244, 314, 432, 541, 660, 792, 1102, 1220, 1290, 1548, 2087, 2212, 2338, 2565, 3078, 3716, 4179, 4304, 4370, 4625, 5008, 5186, 6147, 7426, 8297, 8416, 8488, 8713, 9288, 9992, 10273, 10656, 12353, 13504, 14849, 16256]

def chk (m : ℕ) : Bool :=
  edges.any (fun e => m.testBit e.1 && m.testBit e.2) ||
    (List.range 37).any (fun j => m &&& cols.getD j 0 == m)

lemma chk_all2 : ∀ a < 128, ∀ b < 128, chk (a * 128 + b) = true := by decide +kernel

lemma chk_all : ∀ m < 16384, chk m = true := by
  intro m hm
  have h := chk_all2 (m / 128) (by omega) (m % 128) (by omega)
  rwa [Nat.div_add_mod' m 128] at h

lemma edges_lt : ∀ e ∈ edges, e.1 < 14 ∧ e.2 < 14 := by decide

lemma col_eq : ∀ j < 37, List.ofFn (fun i : Fin 14 => (cols.getD j 0).testBit i.val) =
    nums.map (fun n => n.testBit (21 + j)) ∧ Nat.testBit 2097151 (21 + j) = false := by
  decide +kernel

lemma edge_eq : ∀ u v : Fin 14, (u.val, v.val) ∈ edges → ∃ k : ℕ, k < 21 ∧
    nums.map (fun n => n.testBit k) = List.ofFn (fun i : Fin 14 => decide (i = u ∨ i = v)) ∧
      Nat.testBit 2097151 k = true := by
  decide +kernel


def X2 : List ℕ → ℕ → List ℕ := fun L x => L ++ [if x < 4096 then L.getD (x % 64) 0 &&& L.getD (x / 64 % 64) 0 else L.getD (x % 64) 0 ||| L.getD (x / 64 % 64) 0]

def X3 : ℕ → Gate := fun x => { op := if x < 4096 then GateOp.and else GateOp.or, inputs := [x % 64, x / 64 % 64] }

lemma getD_tb (L : List ℕ) (k i : ℕ) :
    (L.map (fun n => n.testBit k)).getD i false = (L.getD i 0).testBit k := by
  rw [show false = (0 : ℕ).testBit k from (Nat.zero_testBit k).symm, List.getD_map]

lemma sim (k : ℕ) : ∀ (xs L : List ℕ),
    (xs.foldl X2 L).map (fun n => n.testBit k) = (xs.map X3).foldl step (L.map (fun n => n.testBit k)) := by
  intro xs
  induction xs with
  | nil => intro L; rfl
  | cons x xs ih =>
    intro L
    simp only [List.foldl_cons, List.map_cons]
    rw [ih]
    congr 1
    unfold X2 step X3
    rw [List.map_append]
    congr 1
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true, getD_tb]
    by_cases h : x < 4096 <;> simp [h, GateOp.eval, Nat.testBit_and, Nat.testBit_or]

lemma ev (xs : List ℕ) (k : ℕ) :
    Circuit.eval ⟨xs.map X3, 13 + xs.length⟩ (nums.map (fun n => n.testBit k)) =
      ((xs.foldl X2 nums).getD (13 + xs.length) 0).testBit k := by
  show ((xs.map X3).foldl step (nums.map (fun n => n.testBit k))).getD (13 + xs.length) false = _
  rw [← sim k xs nums, getD_tb]

lemma key (gs : List Gate) (out : ℕ) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hk : ∀ (x3 : ℕ), Circuit.eval ⟨gs, out⟩ (nums.map (fun n => n.testBit x3)) = Nat.testBit 2097151 x3)
    (x : Fin 14 → Bool) :
    Circuit.eval ⟨gs, out⟩ (List.ofFn x) = true ↔
      ∃ (u v : Fin 14), (u.val, v.val) ∈ edges ∧ x u = true ∧ x v = true := by
  have hm : ∀ y z : Fin 14 → Bool, (∀ i, y i = true → z i = true) →
      Circuit.eval ⟨gs, out⟩ (List.ofFn y) = true →
      Circuit.eval ⟨gs, out⟩ (List.ofFn z) = true := by
    intro y z h hy
    exact bool_le.mp (mono 14 gs hgs y z h out) hy
  constructor
  · intro hx
    have hlt : Nat.ofBits x < 16384 := Nat.ofBits_lt_two_pow x
    have hc := chk_all _ hlt
    have hb : ∀ (i : ℕ) (h : i < 14), (Nat.ofBits x).testBit i = x ⟨i, h⟩ :=
      fun i h => Nat.testBit_ofBits_lt x i h
    simp only [chk, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, List.mem_range,
      beq_iff_eq] at hc
    rcases hc with ⟨e, he, h1, h2⟩ | ⟨j, hj, hjm⟩
    · obtain ⟨l1, l2⟩ := edges_lt e he
      refine ⟨⟨e.1, l1⟩, ⟨e.2, l2⟩, he, ?_, ?_⟩
      · rw [← hb e.1 l1]; exact h1
      · rw [← hb e.2 l2]; exact h2
    · exfalso
      obtain ⟨c1, c2⟩ := col_eq j hj
      have h3 := hm x (fun i : Fin 14 => (cols.getD j 0).testBit i.val) (by
        intro i hi
        have h4 : (Nat.ofBits x &&& cols.getD j 0).testBit i.val = true := by
          rw [hjm, hb i.val i.isLt]; exact hi
        rw [Nat.testBit_and] at h4
        simp only [Bool.and_eq_true] at h4
        exact h4.2) hx
      rw [c1] at h3
      have h5 : Circuit.eval ⟨gs, out⟩ (nums.map (fun n => n.testBit (21 + j))) =
          Nat.testBit 2097151 (21 + j) := hk (21 + j)
      rw [h3, c2] at h5
      exact Bool.false_ne_true h5.symm
  · rintro ⟨u, v, huv, hu, hv⟩
    obtain ⟨k, _, e1, e2⟩ := edge_eq u v huv
    have h5 : Circuit.eval ⟨gs, out⟩ (nums.map (fun n => n.testBit k)) =
        Nat.testBit 2097151 k := hk k
    rw [e1, e2] at h5
    refine hm _ x ?_ h5
    intro i hi
    simp only [decide_eq_true_eq] at hi
    rcases hi with rfl | rfl
    · exact hu
    · exact hv


lemma decode (xs : List ℕ)
    (hout : (xs.foldl X2 nums).getD (13 + xs.length) 0 = 2097151)
    (x : Fin 14 → Bool) :
    Circuit.eval ⟨xs.map X3, 13 + xs.length⟩ (List.ofFn x) =
      decide (∃ u v : Fin 14, (u.val, v.val) ∈ edges ∧ x u = true ∧ x v = true) := by
  have hgs : ∀ g ∈ xs.map X3, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hg
    by_cases h : a < 4096 <;> simp [X3, h]
  have hk : ∀ k : ℕ, Circuit.eval ⟨xs.map X3, 13 + xs.length⟩ (nums.map (fun n => n.testBit k)) =
      Nat.testBit 2097151 k := by
    intro k
    rw [ev, hout]
  rw [Bool.eq_iff_iff, key _ _ hgs hk x, decide_eq_true_iff]

end PEqualNP.Outside.L_meta_2732_aux.Packed
