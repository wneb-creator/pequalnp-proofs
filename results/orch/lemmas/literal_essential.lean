import PEqualNP.Outside.L_meta_3451

namespace PEqualNP.Outside.L_meta_3451

open CircuitLowerBounds MetaComplexity NestedCover

def lcSingleton {n : ℕ} (i : Fin n) (k : Fin n) : Bool := decide (k = i)

lemma lcLiteralEval {n : ℕ} (pre : List Gate) (i : Fin n) (z : Fin n → Bool) :
    GateOp.or.eval ([i.val].map fun k => (pre.foldl decStep (List.ofFn z)).getD k false) = z i := by
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
  rw [lcRead _ _ _ (by simpa using i.isLt)]
  exact lcGetDOfFn z i

lemma lcLiteralEssential (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (pre post : List Gate) (g : Gate) (hsplit : C.gates = pre ++ g :: post)
    (hmono : Monotone2 C) (hreads : ReadsBack (N + N) C)
    (hfun : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
    (i : Fin (N + N))
    (hsingle : (C.wires (List.ofFn (lcSingleton i))).getD (N + N + pre.length) false = true)
    (hcritical : ∀ p l : Fin N, I p l →
      circuitFun (N + N) (lcKill C pre post) (lcPair N p l) = false → lcPair N p l i = true) :
    ∃ D : Circuit, lcOutputImproves N I C D ∧
      (∀ k, k ≠ pre.length → gateAt D k = gateAt C k) ∧
      (gateAt D pre.length).op = GateOp.or := by
  let r : Gate := ⟨GateOp.or, [i.val]⟩
  let D : Circuit := ⟨pre ++ r :: post, C.output⟩
  refine ⟨D, ?_, mdReplacementShape C pre post g r hsplit, ?_⟩
  · apply lcReplacementOutput N I C pre post g r hsplit hmono hreads hfun (Or.inr rfl)
    · simp [r]
    · intro k hk
      simp only [r, List.mem_singleton] at hk
      subst k
      have hi := i.isLt
      omega
    · intro z hz
      change GateOp.or.eval _ = true at hz
      rw [lcLiteralEval] at hz
      rw [← lcCircuitGate (N + N) C pre post g hsplit]
      apply decWireMono (N + N) C hmono (lcSingleton i) z ?_ (N + N + pre.length) hsingle
      intro k hk
      have hki : k = i := of_decide_eq_true hk
      simpa only [hki] using hz
    · intro p l hpl
      by_cases he : circuitFun (N + N) (lcKill C pre post) (lcPair N p l) = false
      · have hnew := hcritical p l hpl he
        have hold := lcEssentialAccepted N I C pre post g hsplit hfun p l hpl he
        have heq : r.op.eval (r.inputs.map fun k =>
            (pre.foldl decStep (List.ofFn (lcPair N p l))).getD k false) =
            g.op.eval (g.inputs.map fun k =>
              (pre.foldl decStep (List.ofFn (lcPair N p l))).getD k false) := by
          change GateOp.or.eval _ = _
          rw [lcLiteralEval, hnew, ← lcCircuitGate (N + N) C pre post g hsplit, hold]
        have hw := lcReplaceEq (N + N) C pre post g r hsplit (lcPair N p l) heq
        have hout := congrArg (fun w : List Bool => w.getD C.output false) hw
        exact hout.trans ((hfun _).mpr
          ⟨p, l, hpl, (lcPairTrue N p l).1, (lcPairTrue N p l).2⟩)
      · have hz := Bool.eq_true_of_ne_false he
        exact lcKillBelow (N + N) C pre post r
          (fun a ha => (hmono a (by rw [hsplit]; simp [ha])).1) _ C.output hz
  · simp [gateAt, D, r]

end PEqualNP.Outside.L_meta_3451
