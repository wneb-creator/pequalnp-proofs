import ReaderDeletion
import TwoCenterRepair

namespace PEqualNP.Outside.L_meta_2448_aux.RepairAssembly

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2448_aux.ReaderDeletion

def fourGates (m a b c d out : ℕ) : List Gate :=
  [⟨GateOp.and, [c, b]⟩, ⟨GateOp.and, [d, a]⟩,
    ⟨GateOp.or, [m, m + 1]⟩,
    ⟨GateOp.or, [if out < m then out else m + 4, m + 2]⟩]

lemma getD_snoc_lt (w : List Bool) (b : Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ [b]).getD i false = w.getD i false := List.getD_append _ _ _ _ hi

lemma four_eval (w : List Bool) (a b c d out : ℕ)
    (ha : a < w.length) (hb : b < w.length)
    (hc : c < w.length) (hd : d < w.length) :
    (wiresFrom (fourGates w.length a b c d out) w).getD (w.length + 3) false =
      (w.getD out false || ((w.getD c false && w.getD b false) ||
        (w.getD d false && w.getD a false))) := by
  let u := w.getD c false && w.getD b false
  let v := w.getD d false && w.getD a false
  let w1 := w ++ [u]
  let w2 := w1 ++ [v]
  let w3 := w2 ++ [u || v]
  have hw1 : w1.length = w.length + 1 := by simp [w1]
  have hw2 : w2.length = w.length + 2 := by simp [w2, hw1]
  have hw3 : w3.length = w.length + 3 := by simp [w3, hw2]
  have wa : w1.getD a false = w.getD a false := getD_snoc_lt _ _ _ ha
  have wd : w1.getD d false = w.getD d false := getD_snoc_lt _ _ _ hd
  have wu : w2.getD w.length false = u := by
    rw [show w2 = w1 ++ [v] from rfl, getD_snoc_lt _ _ _ (by omega)]
    exact getD_snoc_eq w u false
  have wv : w2.getD (w.length + 1) false = v := by
    rw [← hw1]
    exact getD_snoc_eq w1 v false
  have wh : w3.getD (w.length + 2) false = (u || v) := by
    rw [← hw2]
    exact getD_snoc_eq w2 (u || v) false
  have wr : w3.getD (if out < w.length then out else w.length + 4) false =
      w.getD out false := by
    by_cases ho : out < w.length
    · simp only [ho, ↓reduceIte]
      rw [show w3 = w2 ++ [u || v] from rfl, getD_snoc_lt _ _ _ (by omega)]
      rw [show w2 = w1 ++ [v] from rfl, getD_snoc_lt _ _ _ (by omega)]
      exact getD_snoc_lt _ _ _ ho
    · simp only [ho, ↓reduceIte]
      rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  have hwires : wiresFrom (fourGates w.length a b c d out) w =
      w3 ++ [w.getD out false || (u || v)] := by
    change wiresFrom [⟨GateOp.and, [c, b]⟩, ⟨GateOp.and, [d, a]⟩,
      ⟨GateOp.or, [w.length, w.length + 1]⟩,
      ⟨GateOp.or, [if out < w.length then out else w.length + 4, w.length + 2]⟩] w = _
    simp only [wiresFrom, List.foldl_cons, List.foldl_nil, GateOp.eval,
      List.map_cons, List.map_nil, List.all_cons, List.all_nil, List.any_cons,
      List.any_nil, id_eq, Bool.and_true, Bool.or_false]
    rw [wd, wa]
    change (w2 ++ [w2.getD w.length false || w2.getD (w.length + 1) false]) ++ [_] = _
    rw [wu, wv]
    change w3 ++ [w3.getD (if out < w.length then out else w.length + 4) false ||
      w3.getD (w.length + 2) false] = _
    rw [wr, wh]
  rw [hwires, ← hw3, getD_snoc_eq]

def attach (n : ℕ) (D : Circuit) (a b c d : ℕ) : Circuit :=
  ⟨D.gates ++ fourGates (n + D.size) a b c d D.output, n + D.size + 3⟩

lemma attach_size (n : ℕ) (D : Circuit) (a b c d : ℕ) :
    (attach n D a b c d).size = D.size + 4 := by
  simp [attach, Circuit.size, fourGates]

lemma attach_mono (n : ℕ) (D : Circuit) (a b c d : ℕ) (hD : Monotone2 D) :
    Monotone2 (attach n D a b c d) := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact hD g hg
  · simp only [fourGates, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> simp

theorem attach_eval (n : ℕ) (D : Circuit) (a b c d : ℕ)
    (ha : a < n + D.size) (hb : b < n + D.size)
    (hc : c < n + D.size) (hd : d < n + D.size) (x : Fin n → Bool) :
    (attach n D a b c d).eval (List.ofFn x) =
      (D.eval (List.ofFn x) ||
        (((D.wires (List.ofFn x)).getD c false && (D.wires (List.ofFn x)).getD b false) ||
          ((D.wires (List.ofFn x)).getD d false && (D.wires (List.ofFn x)).getD a false))) := by
  have hl : (wiresFrom D.gates (List.ofFn x)).length = n + D.size := by
    simp [length_wiresFrom, Circuit.size]
  change (wiresFrom (D.gates ++ fourGates (n + D.size) a b c d D.output)
    (List.ofFn x)).getD (n + D.size + 3) false = _
  rw [wiresFrom_append, ← hl]
  exact four_eval _ a b c d D.output (by omega) (by omega) (by omega) (by omega)

lemma elim_preserves_prefix (n : ℕ) (gs : List Gate) :
    ∀ acc : List Stat × List Gate, ∃ tail, (elim n gs acc).2 = acc.2 ++ tail := by
  induction gs with
  | nil => intro acc; exact ⟨[], (List.append_nil _).symm⟩
  | cons g gs ih =>
    intro acc
    obtain ⟨tail, ht⟩ := ih (elimStep n acc g)
    refine ⟨(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList ++ tail, ?_⟩
    change (elim n gs (elimStep n acc g)).2 = _
    rw [ht]
    exact List.append_assoc _ _ _

theorem deletion_with_prefix (n : ℕ) (pre post : List Gate) (out : ℕ)
    (hpre : ∀ g ∈ pre, MonoGate g) (hpost : ∀ g ∈ post, MonoGate g)
    (hzero : forcedEval n pre post out (fun _ => false) = false) :
    ∃ D : Circuit, Monotone2 D ∧
      D.size + readerCount (n + pre.length) post + 1 ≤ pre.length + 1 + post.length ∧
      (∃ tail, D.gates = pre ++ tail) ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = forcedEval n pre post out x := by
  let acc := lowered n pre post
  have hM : ∀ g ∈ acc.2, MonoGate g := elim_mono n post (seed n pre) hpost hpre
  have hlen := lowered_size n pre post hpost
  have hp : ∃ tail, acc.2 = pre ++ tail := elim_preserves_prefix n post (seed n pre)
  have hval := lowered_correct n pre post out hpost
  cases hs : acc.1.getD out (Sum.inl false) with
  | inl b =>
    have hb : b = false := by
      have h := (hval (fun _ => false)).2
      change (acc.1.getD out (Sum.inl false)).val _ = _ at h
      rw [hs] at h
      exact h.trans hzero
    subst b
    refine ⟨⟨acc.2, n + acc.2.length⟩, hM, hlen, hp, ?_⟩
    intro x
    have h := (hval x).2
    change (acc.1.getD out (Sum.inl false)).val _ = _ at h
    rw [hs] at h
    change (wiresFrom acc.2 (List.ofFn x)).getD (n + acc.2.length) false = _
    rw [List.getD_eq_default _ _ (by rw [length_wiresFrom, List.length_ofFn])]
    exact h
  | inr w =>
    refine ⟨⟨acc.2, w⟩, hM, hlen, hp, ?_⟩
    intro x
    have h := (hval x).2
    change (acc.1.getD out (Sum.inl false)).val _ = _ at h
    rw [hs] at h
    exact h

lemma prefix_wire (n : ℕ) (D : Circuit) (pre tail : List Gate)
    (hD : D.gates = pre ++ tail) (i : ℕ) (hi : i < n + pre.length)
    (x : Fin n → Bool) :
    (D.wires (List.ofFn x)).getD i false =
      (wiresFrom pre (List.ofFn x)).getD i false := by
  change (wiresFrom D.gates (List.ofFn x)).getD i false = _
  rw [hD, wiresFrom_append]
  exact getD_wiresFrom tail _ i (by simpa [length_wiresFrom] using hi)

theorem repair_circuit (n : ℕ) (C : Circuit) (pre post : List Gate) (g : Gate)
    (a b c d : ℕ) (hC : C.gates = pre ++ g :: post) (hmono : Monotone2 C)
    (ha : a < n + pre.length) (hb : b < n + pre.length)
    (hc : c < n + pre.length) (hd : d < n + pre.length)
    (hzero : forcedEval n pre post C.output (fun _ => false) = false)
    (hrepair : ∀ x : Fin n → Bool, C.eval (List.ofFn x) =
      (forcedEval n pre post C.output x ||
        (((wiresFrom pre (List.ofFn x)).getD c false &&
          (wiresFrom pre (List.ofFn x)).getD b false) ||
         ((wiresFrom pre (List.ofFn x)).getD d false &&
          (wiresFrom pre (List.ofFn x)).getD a false)))) :
    ∃ E : Circuit, Monotone2 E ∧
      E.size + readerCount (n + pre.length) post ≤ C.size + 3 ∧
      ∀ x : Fin n → Bool, E.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  have hpre : ∀ h ∈ pre, MonoGate h := by
    intro h hh
    exact hmono h (hC ▸ List.mem_append_left _ hh)
  have hpost : ∀ h ∈ post, MonoGate h := by
    intro h hh
    exact hmono h (hC ▸ List.mem_append_right _ (List.mem_cons_of_mem _ hh))
  obtain ⟨D, hD, hsize, ⟨tail, htail⟩, heval⟩ :=
    deletion_with_prefix n pre post C.output hpre hpost hzero
  have hp : pre.length ≤ D.size := by simp [Circuit.size, htail]
  have hlen : C.size = pre.length + 1 + post.length := by
    simp [Circuit.size, hC]
    omega
  refine ⟨attach n D a b c d, attach_mono n D a b c d hD, ?_, ?_⟩
  · rw [attach_size]
    omega
  · intro x
    rw [attach_eval n D a b c d (by omega) (by omega) (by omega) (by omega), heval x]
    rw [prefix_wire n D pre tail htail c hc x, prefix_wire n D pre tail htail b hb x,
      prefix_wire n D pre tail htail d hd x, prefix_wire n D pre tail htail a ha x]
    exact (hrepair x).symm

end PEqualNP.Outside.L_meta_2448_aux.RepairAssembly
