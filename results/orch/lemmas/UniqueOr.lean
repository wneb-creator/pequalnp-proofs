import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9502

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def orRun : List Gate → List Bool → List Bool
  | [], w => w
  | g :: gs, w => orRun gs (w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))])

lemma orRun_fold (gs : List Gate) (w : List Bool) :
    orRun gs w = gs.foldl
      (fun v g => v ++ [g.op.eval (g.inputs.map (fun i => v.getD i false))]) w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih => simpa only [orRun, List.foldl_cons] using ih _

lemma orRun_length (gs : List Gate) (w : List Bool) :
    (orRun gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [orRun]
  | cons g gs ih => simp [orRun, ih, Nat.add_comm, Nat.add_left_comm]

lemma orRun_append (gs hs : List Gate) (w : List Bool) :
    orRun (gs ++ hs) w = orRun hs (orRun gs w) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih => simpa only [List.cons_append, orRun] using ih _

def orExcept (i : Nat) (x y : List Bool) : Prop :=
  ∀ k, k ≠ i → x.getD k false = true → y.getD k false = true

lemma orGet_snoc (w : List Bool) (v : Bool) (k : Nat) :
    (w ++ [v]).getD k false = if k = w.length then v else w.getD k false := by
  split_ifs with h
  · subst h; simp
  · rcases Nat.lt_or_gt_of_ne h with h | h
    · exact List.getD_append _ _ _ _ h
    · rw [List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by omega)]

lemma orExcept_snoc {i : Nat} {x y : List Bool} {a b : Bool}
    (hlen : x.length = y.length) (hxy : orExcept i x y) (hab : a = true → b = true) :
    orExcept i (x ++ [a]) (y ++ [b]) := by
  intro k hk hx
  rw [orGet_snoc] at hx ⊢
  rw [← hlen]
  by_cases he : k = x.length
  · simp only [he, ite_true] at hx ⊢
    exact hab hx
  · simp only [he, ite_false] at hx ⊢
    exact hxy k hk hx

lemma orGate_mono (g : Gate) (x y : List Bool)
    (hop : g.op = .and ∨ g.op = .or)
    (hxy : ∀ k ∈ g.inputs, x.getD k false = true → y.getD k false = true) :
    g.op.eval (g.inputs.map (fun i => x.getD i false)) = true →
      g.op.eval (g.inputs.map (fun i => y.getD i false)) = true := by
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_map, Function.comp_apply, id_eq,
      List.all_eq_true]
    intro h k hk
    exact hxy k hk (h k hk)
  · simp only [hop, GateOp.eval, List.any_map, Function.comp_apply, id_eq,
      List.any_eq_true]
    rintro ⟨k, hk, hx⟩
    exact ⟨k, hk, hxy k hk hx⟩

lemma orRun_except (gs : List Gate) (i : Nat) (x y : List Bool)
    (hops : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (havoid : ∀ g ∈ gs, i ∉ g.inputs) (hlen : x.length = y.length)
    (hxy : orExcept i x y) : orExcept i (orRun gs x) (orRun gs y) := by
  induction gs generalizing x y with
  | nil => exact hxy
  | cons g gs ih =>
    apply ih
    · exact fun g hg => hops g (by simp [hg])
    · exact fun g hg => havoid g (by simp [hg])
    · simp [hlen]
    · apply orExcept_snoc hlen hxy
      apply orGate_mono g x y (hops g (by simp))
      intro k hk hx
      exact hxy k (fun h => havoid g (by simp) (h ▸ hk)) hx

lemma unique_or_repair (pre post : List Gate) (i p out : Nat) (x y : List Bool)
    (hops : ∀ g ∈ pre ++ post, g.op = .and ∨ g.op = .or)
    (havoid : ∀ g ∈ pre ++ post, i ∉ g.inputs)
    (hlen : x.length = y.length) (hxy : orExcept i x y)
    (hp : (orRun pre y).getD p false = true) (hout : out ≠ i) :
    (Circuit.mk (pre ++ [⟨.or, [i, p]⟩] ++ post) out).eval x = true →
      (Circuit.mk (pre ++ [⟨.or, [i, p]⟩] ++ post) out).eval y = true := by
  have hpre : orExcept i (orRun pre x) (orRun pre y) :=
    orRun_except pre i x y
      (fun g hg => hops g (List.mem_append_left _ hg))
      (fun g hg => havoid g (List.mem_append_left _ hg)) hlen hxy
  have hlen' : (orRun pre x).length = (orRun pre y).length := by
    simp [orRun_length, hlen]
  have hmid : orExcept i
      (orRun [⟨.or, [i, p]⟩] (orRun pre x))
      (orRun [⟨.or, [i, p]⟩] (orRun pre y)) := by
    apply orExcept_snoc hlen' hpre
    intro _
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
      List.any_nil, id_eq, hp, Bool.or_false, Bool.or_true]
  have hfinal := orRun_except post i _ _
    (fun g hg => hops g (List.mem_append_right _ hg))
    (fun g hg => havoid g (List.mem_append_right _ hg))
    (by simp [orRun_length, hlen]) hmid
  have heval (w : List Bool) :
      (Circuit.mk (pre ++ [⟨.or, [i, p]⟩] ++ post) out).eval w =
        (orRun post (orRun [⟨.or, [i, p]⟩] (orRun pre w))).getD out false := by
    simp only [Circuit.eval, Circuit.wires, ← orRun_fold, orRun_append]
  rw [heval, heval]
  exact hfinal out hout

lemma orRun_mono (gs : List Gate) (x y : List Bool)
    (hops : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (hlen : x.length = y.length)
    (hxy : ∀ k, x.getD k false = true → y.getD k false = true) :
    ∀ k, (orRun gs x).getD k false = true → (orRun gs y).getD k false = true := by
  induction gs generalizing x y with
  | nil => exact hxy
  | cons g gs ih =>
    apply ih
    · exact fun g hg => hops g (by simp [hg])
    · simp [hlen]
    · intro k hk
      have hstep : orExcept (k + 1)
          (x ++ [g.op.eval (g.inputs.map (fun i => x.getD i false))])
          (y ++ [g.op.eval (g.inputs.map (fun i => y.getD i false))]) :=
        orExcept_snoc hlen (fun j _ => hxy j)
          (orGate_mono g x y (hops g (by simp)) (fun j _ => hxy j))
      exact hstep k (by omega) hk

def orInput (N : Nat) (S : Finset Nat) : List Bool :=
  List.ofFn (fun k : Fin N => decide (k.val ∈ S))

lemma orInput_getD (N : Nat) (S : Finset Nat) (k : Nat) :
    (orInput N S).getD k false = decide (k < N ∧ k ∈ S) := by
  by_cases h : k < N
  · simp [orInput, List.getD, h]
  · simp [orInput, List.getD, h]

lemma orInput_mono (N : Nat) (S T : Finset Nat) (hST : S ⊆ T) :
    ∀ k, (orInput N S).getD k false = true → (orInput N T).getD k false = true := by
  intro k hk
  simp only [orInput_getD, decide_eq_true_eq] at hk ⊢
  exact ⟨hk.1, hST hk.2⟩

lemma orInput_pair_except (N i j c : Nat) :
    orExcept i (orInput N {i, c}) (orInput N {j, c}) := by
  intro k hki hk
  simp only [orInput_getD, decide_eq_true_eq] at hk ⊢
  refine ⟨hk.1, ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk ⊢
  exact Or.inr (hk.2.resolve_left hki)

lemma unique_or_pair_transfer (pre post : List Gate) (N i p out j c : Nat)
    (hops : ∀ g ∈ pre ++ post, g.op = .and ∨ g.op = .or)
    (havoid : ∀ g ∈ pre ++ post, i ∉ g.inputs)
    (hp : (orRun pre (orInput N {j})).getD p false = true) (hout : out ≠ i) :
    (Circuit.mk (pre ++ [⟨.or, [i, p]⟩] ++ post) out).eval (orInput N {i, c}) = true →
      (Circuit.mk (pre ++ [⟨.or, [i, p]⟩] ++ post) out).eval (orInput N {j, c}) = true := by
  apply unique_or_repair pre post i p out _ _ hops havoid
    (by simp [orInput]) (orInput_pair_except N i j c) _ hout
  apply orRun_mono pre _ _
    (fun g hg => hops g (List.mem_append_left _ hg)) (by simp [orInput])
    (orInput_mono N {j} {j, c} (by simp)) p hp

lemma unique_or_single_transfer (pre post : List Gate) (N i p out c : Nat)
    (hops : ∀ g ∈ pre ++ post, g.op = .and ∨ g.op = .or)
    (havoid : ∀ g ∈ pre ++ post, i ∉ g.inputs)
    (hp : (orRun pre (orInput N {c})).getD p false = true) (hout : out ≠ i) :
    (Circuit.mk (pre ++ [⟨.or, [i, p]⟩] ++ post) out).eval (orInput N {i, c}) = true →
      (Circuit.mk (pre ++ [⟨.or, [i, p]⟩] ++ post) out).eval (orInput N {c}) = true := by
  simpa only [Finset.pair_eq_singleton] using
    unique_or_pair_transfer pre post N i p out c c hops havoid hp hout

lemma unique_or_partner_false (pre post : List Gate) (N i p out c : Nat)
    (hops : ∀ g ∈ pre ++ post, g.op = .and ∨ g.op = .or)
    (havoid : ∀ g ∈ pre ++ post, i ∉ g.inputs) (hout : out ≠ i)
    (hedge : (Circuit.mk (pre ++ [⟨.or, [i, p]⟩] ++ post) out).eval
      (orInput N {i, c}) = true)
    (hsingle : (Circuit.mk (pre ++ [⟨.or, [i, p]⟩] ++ post) out).eval
      (orInput N {c}) = false) :
    (orRun pre (orInput N {c})).getD p false = false := by
  cases hp : (orRun pre (orInput N {c})).getD p false with
  | false => rfl
  | true =>
    have h := unique_or_single_transfer pre post N i p out c hops havoid hp hout hedge
    simp only [hsingle, Bool.false_eq_true] at h

end PEqualNP.Outside.L_meta_9502
