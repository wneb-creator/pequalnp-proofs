import ReaderDeletion

namespace PEqualNP.Outside.L_meta_2448_aux.ReaderDeletionCount

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2448_aux.ReaderDeletion

def step (g : Gate) (w : List Bool) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def weight (op : GateOp) (b : Bool) : Nat :=
  match op with
  | GateOp.and => if b then 1 else 0
  | _ => 0

def contribution (g : Gate) (w : List Bool) : Nat :=
  weight g.op (g.op.eval (g.inputs.map fun i => w.getD i false))

def count : List Gate → List Bool → Nat
  | [], _ => 0
  | g :: gs, w => contribution g w + count gs (step g w)

lemma count_append (pre post : List Gate) (w : List Bool) :
    count (pre ++ post) w = count pre w + count post (wiresFrom pre w) := by
  induction pre generalizing w with
  | nil => simp [count, wiresFrom]
  | cons g gs ih =>
    simp [count, wiresFrom, step, ih, Nat.add_assoc]

lemma simplify_count_le (op : GateOp) (m : Nat) (ins : List Stat) (w : List Bool)
    (hop : op = GateOp.and ∨ op = GateOp.or) :
    count (simplify op m ins).1.toList w ≤
      weight op (op.eval (ins.map (Stat.val w))) := by
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;>
      (try cases a) <;> (try cases b) <;>
      simp [simplify, simpAnd, count, contribution, weight, Stat.val, GateOp.eval]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;>
      (try cases a) <;> (try cases b) <;>
      simp [simplify, simpOr, count, contribution, weight, Stat.val, GateOp.eval]

lemma elim_step_count_le (n : Nat) (y w : List Bool)
    (acc : List Stat × List Gate) (g : Gate)
    (hmono : MonoGate g) (hinv : Inv n y w acc) :
    count (elimStep n acc g).2 y ≤ count acc.2 y + contribution g w := by
  change count (acc.2 ++ _) y ≤ _
  rw [count_append]
  apply Nat.add_le_add_left
  have h := simplify_count_le g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
    (wiresFrom acc.2 y) hmono.1
  have hv : (g.inputs.map fun i => acc.1.getD i (Sum.inl false)).map
      (Stat.val (wiresFrom acc.2 y)) = g.inputs.map fun i => w.getD i false := by
    rw [List.map_map]
    apply List.map_congr_left
    intro i _
    exact (hinv.2 i).2
  rw [hv] at h
  exact h

theorem elim_count_le (n : Nat) (y : List Bool) (hy : y.length = n)
    (gs : List Gate) : ∀ (w : List Bool) (acc : List Stat × List Gate),
    (∀ g ∈ gs, MonoGate g) → Inv n y w acc →
    count (elim n gs acc).2 y ≤ count acc.2 y + count gs w := by
  induction gs with
  | nil => intro w acc _ _; simp [elim, count]
  | cons g gs ih =>
    intro w acc hmono hinv
    have hg := hmono g List.mem_cons_self
    have hinv' : Inv n y (step g w) (elimStep n acc g) := by
      have h := inv_elim n y hy [g] w acc
        (by
          intro q hq
          have he : q = g := List.mem_singleton.mp hq
          subst q
          exact (mono_nok g hg).1) hinv
      simpa [wiresFrom, elim, step] using h
    have htail := ih (step g w) (elimStep n acc g)
      (fun q hq => hmono q (List.mem_cons_of_mem _ hq)) hinv'
    have hstep := elim_step_count_le n y w acc g hg hinv
    change count (elim n gs (elimStep n acc g)).2 y ≤ _
    change _ ≤ count acc.2 y + (contribution g w + count gs (step g w))
    omega

theorem lowered_count_le (n : Nat) (pre post : List Gate)
    (hmono : ∀ g ∈ post, MonoGate g) (x : Fin n → Bool) :
    count (lowered n pre post).2 (List.ofFn x) ≤
      count pre (List.ofFn x) +
        count post (wiresFrom pre (List.ofFn x) ++ [false]) := by
  exact elim_count_le n (List.ofFn x) (by simp) post _ (seed n pre) hmono
    (seed_inv n pre x)

def Below (w w' : List Bool) : Prop :=
  ∀ i, w.getD i false = true → w'.getD i false = true

lemma gate_mono (g : Gate) (hmono : MonoGate g) (w w' : List Bool)
    (hbelow : Below w w') :
    g.op.eval (g.inputs.map fun i => w.getD i false) = true →
      g.op.eval (g.inputs.map fun i => w'.getD i false) = true := by
  rcases hmono.1 with ha | ho
  · rw [ha]
    intro h
    have h' : ∀ i ∈ g.inputs, w.getD i false = true := by
      simpa [GateOp.eval] using h
    simpa [GateOp.eval] using (fun i hi => hbelow i (h' i hi))
  · rw [ho]
    intro h
    have h' : ∃ i ∈ g.inputs, w.getD i false = true := by
      simpa [GateOp.eval] using h
    obtain ⟨i, hi, hv⟩ := h'
    simpa [GateOp.eval] using (show ∃ i ∈ g.inputs, w'.getD i false = true from
      ⟨i, hi, hbelow i hv⟩)

lemma step_below (g : Gate) (hmono : MonoGate g) (w w' : List Bool)
    (hlen : w.length = w'.length) (hbelow : Below w w') :
    Below (step g w) (step g w') := by
  intro i hi
  by_cases he : i = w.length
  · subst i
    change (w ++ [_]).getD w.length false = true at hi
    rw [getD_snoc_eq] at hi
    change (w' ++ [_]).getD w.length false = true
    rw [hlen, getD_snoc_eq]
    exact gate_mono g hmono w w' hbelow hi
  · change (w ++ [_]).getD i false = true at hi
    rw [getD_snoc_ne _ _ _ _ he] at hi
    change (w' ++ [_]).getD i false = true
    rw [getD_snoc_ne _ _ _ _ (by omega)]
    exact hbelow i hi

lemma contribution_mono (g : Gate) (hmono : MonoGate g) (w w' : List Bool)
    (hbelow : Below w w') : contribution g w ≤ contribution g w' := by
  cases hv : g.op.eval (g.inputs.map fun i => w.getD i false) with
  | false =>
    unfold contribution
    rw [hv]
    cases g.op <;> simp [weight]
  | true =>
    have hv' := gate_mono g hmono w w' hbelow hv
    unfold contribution
    rw [hv, hv']

theorem count_mono (gs : List Gate) (hmono : ∀ g ∈ gs, MonoGate g)
    (w w' : List Bool) (hlen : w.length = w'.length) (hbelow : Below w w') :
    count gs w ≤ count gs w' := by
  induction gs generalizing w w' with
  | nil => simp [count]
  | cons g gs ih =>
    have hg := hmono g List.mem_cons_self
    have ht := ih (fun q hq => hmono q (List.mem_cons_of_mem _ hq))
      (step g w) (step g w') (by simpa [step] using hlen)
      (step_below g hg w w' hlen hbelow)
    exact Nat.add_le_add (contribution_mono g hg w w' hbelow) ht

theorem lowered_count_plus_removed_le (n : Nat) (pre post : List Gate) (g : Gate)
    (hpost : ∀ q ∈ post, MonoGate q) (x : Fin n → Bool) :
    count (lowered n pre post).2 (List.ofFn x) +
      contribution g (wiresFrom pre (List.ofFn x)) ≤
      count (pre ++ g :: post) (List.ofFn x) := by
  let w := wiresFrom pre (List.ofFn x)
  have hlow := lowered_count_le n pre post hpost x
  have hb : Below (w ++ [false]) (step g w) := by
    intro i hi
    by_cases he : i = w.length
    · subst i
      rw [getD_snoc_eq] at hi
      contradiction
    · rw [getD_snoc_ne _ _ _ _ he] at hi
      change (w ++ [_]).getD i false = true
      rw [getD_snoc_ne _ _ _ _ he]
      exact hi
  have ht := count_mono post hpost (w ++ [false]) (step g w)
    (by simp [step]) hb
  rw [count_append]
  change count (lowered n pre post).2 (List.ofFn x) + contribution g w ≤
    count pre (List.ofFn x) + (contribution g w + count post (step g w))
  change count (lowered n pre post).2 (List.ofFn x) ≤
    count pre (List.ofFn x) + count post (w ++ [false]) at hlow
  omega

theorem weighted_lowered_count_le {I : Type} (s : Finset I) (n : Nat)
    (pre post : List Gate) (g : Gate) (hpost : ∀ q ∈ post, MonoGate q)
    (inputs : I → Fin n → Bool) :
    (∑ i ∈ s, count (lowered n pre post).2 (List.ofFn (inputs i))) +
      (∑ i ∈ s, contribution g (wiresFrom pre (List.ofFn (inputs i)))) ≤
      ∑ i ∈ s, count (pre ++ g :: post) (List.ofFn (inputs i)) := by
  have h := Finset.sum_le_sum (s := s) (fun i _ =>
    lowered_count_plus_removed_le n pre post g hpost (inputs i))
  simpa only [Finset.sum_add_distrib] using h

theorem weighted_lowered_count_lt {I : Type} (s : Finset I) (n : Nat)
    (pre post : List Gate) (g : Gate) (hpost : ∀ q ∈ post, MonoGate q)
    (inputs : I → Fin n → Bool) (a : I) (ha : a ∈ s)
    (hg : contribution g (wiresFrom pre (List.ofFn (inputs a))) = 1) :
    (∑ i ∈ s, count (lowered n pre post).2 (List.ofFn (inputs i))) <
      ∑ i ∈ s, count (pre ++ g :: post) (List.ofFn (inputs i)) := by
  have h := weighted_lowered_count_le s n pre post g hpost inputs
  have hp : contribution g (wiresFrom pre (List.ofFn (inputs a))) ≤
      ∑ i ∈ s, contribution g (wiresFrom pre (List.ofFn (inputs i))) :=
    Finset.single_le_sum (f := fun i => contribution g (wiresFrom pre (List.ofFn (inputs i))))
      (fun _ _ => Nat.zero_le _) ha
  rw [hg] at hp
  omega

end PEqualNP.Outside.L_meta_2448_aux.ReaderDeletionCount
