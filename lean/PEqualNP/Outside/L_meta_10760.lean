import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10760

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

lemma compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

lemma live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

lemma live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

lemma first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

variable {width : Nat}

def ops (x y : BitVec width) : List (BitVec width) :=
  [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]

abbrev basicOps (a b : BitVec width) : Finset (BitVec width) := (ops a b).toFinset

open PEqualNP.CircuitLowerBounds

def holds (av : Finset (BitVec width)) (z : (BitVec width)) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

lemma holds_insert {av : Finset (BitVec width)} {z a : (BitVec width)} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

lemma holds_not {av : Finset (BitVec width)} {z : (BitVec width)} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset (BitVec width)) (z : (BitVec width)) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

lemma reachable_not {av : Finset (BitVec width)} {z : (BitVec width)} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 5000 in
lemma and_reach {av : Finset (BitVec width)} {x y : (BitVec width)} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : (BitVec width)) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : (BitVec width)) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · have he : (~~~(0 : BitVec width)) &&& y = y := by
      apply BitVec.eq_of_getLsbD_eq
      intro i
      simp
    rw [he]
    exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : (BitVec width)) = 0 from BitVec.and_zero]; exact .inl const
  · have he : x &&& ~~~(0 : BitVec width) = x := by
      apply BitVec.eq_of_getLsbD_eq
      intro i
      simp
    rw [he]
    exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : (BitVec width)) (hw : w ∈ basicOps a b) (z : (BitVec width)) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

lemma or_reach {av : Finset (BitVec width)} {x y : (BitVec width)} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin width) (z : (BitVec width)) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma read_bit (w : List (BitVec width)) (i : ℕ) (k : Fin width) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List (BitVec width)) (g : Gate) : (BitVec width) := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

lemma evalAnd (xs : List Bool) : GateOp.and.eval xs = xs.all id := rfl
lemma evalOr (xs : List Bool) : GateOp.or.eval xs = xs.any id := rfl
lemma evalNot (xs : List Bool) : GateOp.not.eval xs = !(xs.headD false) := rfl

set_option maxRecDepth 5000 in
lemma action_spec (w : List (BitVec width)) (g : Gate) (hg : legal g) (k : Fin width) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> try simp at cap
  all_goals have bit0 : (0 : (BitVec width))[k.val] = false := by change (0 : BitVec width)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, evalAnd, evalOr, evalNot, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      BitVec.getElem_zero,bit0,Bool.not_false] <;> rfl

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

lemma available_read {av : Finset (BitVec width)} {w : List (BitVec width)} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
lemma gate_reach (w : List (BitVec width)) (av : Finset (BitVec width)) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> try simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;> simp only [isBinary,Bool.false_eq_true,ite_false,ite_true,
    action,List.head?_nil,List.head?_cons,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,
    Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
    show ∀ x : (BitVec width), x ||| (0 : (BitVec width)) = x from fun x => BitVec.or_zero,
    show ∀ x : (BitVec width), x &&& ~~~0 = x from fun x => by simp]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 4000 in
lemma compile {goal : BitVec width} (nonzero : goal ≠ 0) (nonones : goal ≠ ~~~0) (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List (BitVec width)) (av : Finset (BitVec width)) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k goal) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim (nonzero zero)
    · exact False.elim (nonones ones)
    · exact ⟨t, .inl eq.symm, ht⟩
    · exact ⟨t, .inr (by rw [eq, BitVec.not_not]), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k goal := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset (BitVec width)) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu|hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg,Bool.false_eq_true,ite_false] at stepClass
      simpa [binaryCost,neg] using cont av hw stepClass
    · simp only [neg,ite_true] at stepClass
      have len : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩

lemma bound_from_samples {inputCount budget : Nat} {goal : BitVec width}
    (nonzero : goal ≠ 0) (nonones : goal ≠ ~~~0)
    (target : (Fin inputCount → Bool) → Bool) (ins : List (BitVec width))
    (roots : Finset (BitVec width)) (represented : ∀ u ∈ ins, holds roots u)
    (inputLength : ins.length = inputCount)
    (row : ∀ j : Fin width,
      target (fun i => (ins.getD i.val 0)[j.val]) = goal[j.val])
    (rejection : ∀ z, z = goal ∨ z = ~~~goal →
      ¬ build basicOps z budget roots)
    (gs : List Gate) (out : Nat) (legalGates : ∀ g ∈ gs, legal g)
    (computes : ∀ x : Fin inputCount → Bool,
      Circuit.eval ⟨gs, out⟩ (List.ofFn x) = target x) :
    budget < binaryCost gs := by
  by_contra! low
  have evaluate (k : Fin width) :
      (gs.foldl step (ins.map (bit k))).getD out false = bit k goal := by
    let x (i : Fin inputCount) : Bool := bit k (ins.getD i.val 0)
    have same : List.ofFn x = ins.map (bit k) := by
      apply List.ext_getElem
      · simp [inputLength]
      · intro i hi hj
        have hlt : i < ins.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x,
          List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs, out⟩ (ins.map (bit k)) = bit k goal
    rw [← same, computes]
    exact row k
  obtain ⟨z, hz, run⟩ := compile nonzero nonones gs out legalGates ins roots
    represented evaluate
  have lift {a b : Nat} (h : a ≤ b) (hr : build basicOps z a roots) :
      build basicOps z b roots := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact rejection z hz (lift low run)

lemma replace_from_samples {inputCount replacementSize : Nat} {goal : BitVec width}
    (nonzero : goal ≠ 0) (nonones : goal ≠ ~~~0)
    (target : (Fin inputCount → Bool) → Bool) (ins : List (BitVec width))
    (roots : Finset (BitVec width)) (represented : ∀ u ∈ ins, holds roots u)
    (inputLength : ins.length = inputCount)
    (row : ∀ j : Fin width,
      target (fun i => (ins.getD i.val 0)[j.val]) = goal[j.val])
    (rejection : ∀ z, z = goal ∨ z = ~~~goal →
      ¬ build basicOps z (replacementSize - 2) roots)
    (upper : ∃ (gs : List Gate) (out : Nat),
      (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs.length = replacementSize ∧
      ∀ x : Fin inputCount → Bool, Circuit.eval ⟨gs, out⟩ (List.ofFn x) = target x)
    (gs : List Gate) (out : Nat) (legalGates : ∀ g ∈ gs, legal g)
    (computes : ∀ x : Fin inputCount → Bool,
      Circuit.eval ⟨gs, out⟩ (List.ofFn x) = target x) :
    ∃ (ds : List Gate) (newOut : Nat),
      (∀ g ∈ ds, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      ds.length ≤ gs.length ∧
      ∀ x : Fin inputCount → Bool, Circuit.eval ⟨ds, newOut⟩ (List.ofFn x) = target x := by
  by_cases present : ∃ g ∈ gs, g.op = .not
  · obtain ⟨g, member, op⟩ := present
    have cut : binaryCost gs < gs.length :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr
        ⟨g, member, by simp [isBinary, op]⟩
    have lower := bound_from_samples nonzero nonones target ins roots represented inputLength row rejection
      gs out legalGates computes
    obtain ⟨ds, newOut, ok, size, evaluates⟩ := upper
    exact ⟨ds, newOut, ok, by omega, evaluates⟩
  · refine ⟨gs, out, ?_, le_rfl, computes⟩
    intro g member
    obtain ⟨op, arity⟩ := legalGates g member
    exact ⟨op.elim Or.inl (fun h => h.elim Or.inr
      (fun eq => (present ⟨g, member, eq⟩).elim)), arity⟩

end PEqualNP.Outside.L_meta_10760


namespace PEqualNP.Outside.L_meta_10760

open PEqualNP.CircuitLowerBounds

def edgeFunction (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 2) || (x 1 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 2 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 5 && x 6)

def monotoneWitness : List Gate :=
  [
    ⟨GateOp.or, [0, 2]⟩,
    ⟨GateOp.or, [3, 5]⟩,
    ⟨GateOp.or, [7, 8]⟩,
    ⟨GateOp.and, [6, 9]⟩,
    ⟨GateOp.or, [1, 5]⟩,
    ⟨GateOp.and, [3, 11]⟩,
    ⟨GateOp.or, [0, 1]⟩,
    ⟨GateOp.or, [4, 5]⟩,
    ⟨GateOp.and, [13, 14]⟩,
    ⟨GateOp.or, [0, 4]⟩,
    ⟨GateOp.and, [2, 16]⟩,
    ⟨GateOp.or, [10, 12]⟩,
    ⟨GateOp.or, [15, 17]⟩,
    ⟨GateOp.or, [18, 19]⟩
  ]

lemma witness_size : monotoneWitness.length = 14 := rfl

lemma witness_allowed : ∀ g ∈ monotoneWitness,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  simp [monotoneWitness]

set_option maxHeartbeats 2000000 in
lemma witness_eval : ∀ x : Fin 7 → Bool,
    Circuit.eval ⟨monotoneWitness, 20⟩ (List.ofFn x) = edgeFunction x := by
  decide +kernel

set_option maxHeartbeats 2000000 in
lemma edgeFunction_posted : ∀ x : Fin 7 → Bool,
    decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) = edgeFunction x := by
  decide +kernel


def pairInput (i j : Fin 7) : Fin 7 → Bool :=
  fun k => decide (k = i ∨ k = j)

set_option maxHeartbeats 8000000 in
lemma positive_pair : ∀ x : Fin 7 → Bool, edgeFunction x = true →
    ∃ i j : Fin 7, i ≠ j ∧ pairInput i j ≤ x ∧ edgeFunction (pairInput i j) = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
lemma negative_pair : ∀ x : Fin 7 → Bool, edgeFunction x = false →
    ∃ i j : Fin 7, i ≠ j ∧ x ≤ pairInput i j ∧ edgeFunction (pairInput i j) = false := by
  decide +kernel

lemma pair_table_suffices (g : (Fin 7 → Bool) → Bool) (hg : Monotone g)
    (hpair : ∀ i j : Fin 7, i ≠ j → g (pairInput i j) = edgeFunction (pairInput i j)) :
    ∀ x : Fin 7 → Bool, g x = edgeFunction x := by
  intro x
  cases hx : edgeFunction x with
  | false =>
    obtain ⟨i, j, hij, hle, hf⟩ := negative_pair x hx
    have h := hg hle
    rw [hpair i j hij, hf] at h
    exact Bool.eq_false_of_le_false h
  | true =>
    obtain ⟨i, j, hij, hle, hf⟩ := positive_pair x hx
    have h := hg hle
    rw [hpair i j hij, hf] at h
    exact Bool.eq_true_of_true_le h

end PEqualNP.Outside.L_meta_10760

namespace PEqualNP.Outside.L_meta_10760

open PEqualNP.CircuitLowerBounds

def sampleInputs : List (BitVec 128) := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000, 0xffffffffffffffff0000000000000000]

def sampleGoal : BitVec 128 := 0xfffffffffffefffafffeffeefefeeca0

def signedRoots : Finset (BitVec 128) := (sampleInputs.map (fun w => ~~~w)).toFinset

lemma sample_represented : ∀ u ∈ sampleInputs, holds signedRoots u := by
  intro u hu
  refine Or.inr (Or.inr ⟨~~~u, ?_, Or.inr ?_⟩)
  · exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨u, hu, rfl⟩)
  · exact BitVec.not_not.symm

set_option maxHeartbeats 2000000 in
lemma sample_rows : ∀ j : Fin 128,
    edgeFunction (fun i => (sampleInputs.getD i.val 0)[j.val]) = sampleGoal[j.val] := by
  decide +kernel

set_option maxHeartbeats 2000000 in
lemma gap_of_rejection
    (reject : ∀ z, z = sampleGoal ∨ z = ~~~sampleGoal →
      ¬ build basicOps z 12 signedRoots) :
∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o hg _ hf
  obtain ⟨ds, out, ok, len, ev⟩ := replace_from_samples
    (replacementSize := 14) (goal := sampleGoal)
    (by decide +kernel) (by decide +kernel) edgeFunction sampleInputs signedRoots
    sample_represented rfl sample_rows reject
    ⟨monotoneWitness, 20, witness_allowed, witness_size, witness_eval⟩
    gates o hg (fun x => (hf x).trans (edgeFunction_posted x))
  exact ⟨ds, out, ok, len, fun x => (ev x).trans (edgeFunction_posted x).symm⟩

end PEqualNP.Outside.L_meta_10760


namespace PEqualNP.Outside.L_meta_10760

def firstRoot (i : Fin 7) : BitVec 128 := ~~~(sampleInputs.getD i.val 0)

def firstOp (i j : Fin 7) (o : Fin 4) : BitVec 128 :=
  (ops (firstRoot i) (firstRoot j)).getD o.val 0

def collisionData : List Nat := [0, 0, 0, 0, 775, 517, 517, 775, 517, 2065, 2065, 517, 1549, 517, 517, 1549, 2065, 517, 517, 2065, 4129, 517, 517, 4129, 8257, 517, 517, 8257, 1163, 1034, 1034, 1163, 0, 0, 0, 0, 1550, 1034, 1034, 1550, 1034, 2066, 2066, 1034, 2066, 1034, 1034, 2066, 4130, 1034, 1034, 4130, 10322, 1034, 1034, 10322, 133, 2068, 2068, 133, 391, 133, 133, 391, 0, 0, 0, 0, 1165, 133, 133, 1165, 2068, 133, 133, 2068, 6196, 133, 133, 6196, 8260, 133, 133, 8260, 395, 266, 266, 395, 266, 4136, 4136, 266, 782, 266, 266, 782, 0, 0, 0, 0, 6200, 266, 266, 6200, 4136, 266, 266, 4136, 8264, 266, 266, 8264, 145, 274, 274, 145, 274, 145, 145, 274, 532, 145, 145, 532, 1177, 145, 145, 1177, 0, 0, 0, 0, 4660, 145, 145, 4660, 8530, 145, 145, 8530, 161, 290, 290, 161, 290, 161, 161, 290, 806, 161, 161, 806, 1064, 161, 161, 1064, 3128, 161, 161, 3128, 0, 0, 0, 0, 8288, 161, 161, 8288, 193, 580, 580, 193, 451, 193, 193, 451, 580, 193, 193, 580, 1096, 193, 193, 1096, 3160, 193, 193, 3160, 4192, 193, 193, 4192, 0, 0, 0, 0]

def collisionPos (i j : Fin 7) (o : Fin 4) : Fin 128 :=
  ⟨(collisionData.getD ((i.val * 7 + j.val) * 4 + o.val) 0) % 128, Nat.mod_lt _ (by decide)⟩

def collisionNeg (i j : Fin 7) (o : Fin 4) : Fin 128 :=
  ⟨(collisionData.getD ((i.val * 7 + j.val) * 4 + o.val) 0 / 128) % 128, Nat.mod_lt _ (by decide)⟩

set_option maxHeartbeats 8000000 in
lemma first_collision : ∀ i j : Fin 7, ∀ o : Fin 4, i ≠ j →
    sampleGoal[(collisionPos i j o).val] ≠ sampleGoal[(collisionNeg i j o).val] ∧
    (firstOp i j o)[(collisionPos i j o).val] = (firstOp i j o)[(collisionNeg i j o).val] ∧
    ∀ k : Fin 7, k ≠ i →
      (firstRoot k)[(collisionPos i j o).val] = (firstRoot k)[(collisionNeg i j o).val] := by
  decide +kernel

lemma first_roots_eq : signedRoots = Finset.univ.image firstRoot := by
  decide +kernel

lemma first_mem {u : BitVec 128} (hu : u ∈ signedRoots) : ∃ i : Fin 7, u = firstRoot i := by
  rw [first_roots_eq] at hu
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hu
  exact ⟨i, hi.symm⟩

lemma first_op_mem {i j : Fin 7} {z : BitVec 128}
    (hz : z ∈ basicOps (firstRoot i) (firstRoot j)) : ∃ o : Fin 4, z = firstOp i j o := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩

lemma first_bit_congr {width : Nat} {a b z : BitVec width} (i j : Fin width)
    (hz : z ∈ basicOps a b) (ha : a[i.val] = a[j.val]) (hb : b[i.val] = b[j.val]) :
    z[i.val] = z[j.val] := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not, ha, hb]

lemma first_live_separates {width : Nat} {goal : BitVec width} {k : Nat}
    {s : Finset (BitVec width)} (i j : Fin width) (hd : goal[i.val] ≠ goal[j.val])
    (hl : live basicOps goal k s) : ∃ w ∈ s, w[i.val] ≠ w[j.val] := by
  apply live_separates (fun w => w[i.val] ≠ w[j.val]) hd _ hl
  intro a b z hz hne
  by_contra hn
  simp only [not_or, not_not] at hn
  exact hne (first_bit_congr i j hz hn.1 hn.2)

lemma first_drop_collision {a b z : BitVec 128}
    (ha : a ∈ signedRoots) (hb : b ∈ signedRoots) (hne : a ≠ b)
    (hz : z ∈ basicOps a b) :
    ∃ i j : Fin 128, sampleGoal[i.val] ≠ sampleGoal[j.val] ∧
      ∀ w ∈ insert z (signedRoots.erase a), w[i.val] = w[j.val] := by
  obtain ⟨i, rfl⟩ := first_mem ha
  obtain ⟨j, rfl⟩ := first_mem hb
  obtain ⟨o, rfl⟩ := first_op_mem hz
  obtain ⟨hg, ho, hw⟩ := first_collision i j o (fun h => hne (congrArg firstRoot h))
  refine ⟨collisionPos i j o, collisionNeg i j o, hg, ?_⟩
  intro w hmem
  rcases Finset.mem_insert.mp hmem with rfl | hmem
  · exact ho
  · obtain ⟨hneq, hroot⟩ := Finset.mem_erase.mp hmem
    obtain ⟨k, rfl⟩ := first_mem hroot
    exact hw k (fun h => hneq (congrArg firstRoot h))

def essentialPos (i : Fin 7) : Fin 128 :=
  ⟨(([5, 10, 5, 10, 17, 33, 65] : List Nat).getD i.val 0) % 128, Nat.mod_lt _ (by decide)⟩

def essentialNeg (i : Fin 7) : Fin 128 :=
  ⟨(([4, 8, 1, 2, 1, 1, 1] : List Nat).getD i.val 0) % 128, Nat.mod_lt _ (by decide)⟩

lemma first_essential : ∀ i : Fin 7,
    sampleGoal[(essentialPos i).val] ≠ sampleGoal[(essentialNeg i).val] ∧
    ∀ j : Fin 7, j ≠ i →
      (firstRoot j)[(essentialPos i).val] = (firstRoot j)[(essentialNeg i).val] := by
  decide +kernel

lemma first_goal_diff {goal : BitVec 128} (hgoal : goal = sampleGoal ∨ goal = ~~~sampleGoal)
    {i j : Fin 128} (hd : sampleGoal[i.val] ≠ sampleGoal[j.val]) : goal[i.val] ≠ goal[j.val] := by
  rcases hgoal with rfl | rfl
  · exact hd
  · intro h
    apply hd
    have hh := congrArg Bool.not h
    simpa only [BitVec.getElem_not, Bool.not_not] using hh

lemma firstRootsComplete {goal : BitVec 128} {k : Nat} {s : Finset (BitVec 128)}
    (hgoal : goal = sampleGoal ∨ goal = ~~~sampleGoal)
    (hsub : s ⊆ signedRoots) (hl : live basicOps goal k s) : s = signedRoots := by
  apply Finset.Subset.antisymm hsub
  intro a ha
  obtain ⟨i, rfl⟩ := first_mem ha
  by_contra hn
  obtain ⟨hd, hw⟩ := first_essential i
  obtain ⟨w, hws, hne⟩ := first_live_separates (essentialPos i) (essentialNeg i)
    (first_goal_diff hgoal hd) hl
  obtain ⟨j, rfl⟩ := first_mem (hsub hws)
  exact hne (hw j (fun h => hn (by simpa [h] using hws)))

lemma first_keeps_left {goal a b z : BitVec 128} {k : Nat} {rest : Finset (BitVec 128)}
    (hgoal : goal = sampleGoal ∨ goal = ~~~sampleGoal)
    (ha : a ∈ signedRoots) (hb : b ∈ signedRoots) (hne : a ≠ b)
    (hz : z ∈ basicOps a b) (hsub : rest ⊆ signedRoots)
    (hl : live basicOps goal k (insert z rest)) : a ∈ rest := by
  by_contra haout
  obtain ⟨i, j, hd, hc⟩ := first_drop_collision ha hb hne hz
  obtain ⟨w, hw, hbad⟩ := first_live_separates i j (first_goal_diff hgoal hd) hl
  apply hbad
  apply hc
  rcases Finset.mem_insert.mp hw with rfl | hw
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun h => haout (h ▸ hw), hsub hw⟩)

lemma first_ops_comm (a b : BitVec 128) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false,
    BitVec.and_comm, BitVec.or_comm]
  tauto

lemma first_rest_complete {goal a b z : BitVec 128} {k : Nat} {rest : Finset (BitVec 128)}
    (hgoal : goal = sampleGoal ∨ goal = ~~~sampleGoal)
    (ha : a ∈ signedRoots) (hb : b ∈ signedRoots) (hne : a ≠ b)
    (hz : z ∈ basicOps a b) (hs : signedRoots = insert a (insert b rest))
    (hl : live basicOps goal k (insert z rest)) : rest = signedRoots := by
  have hsub : rest ⊆ signedRoots := by
    intro w hw
    rw [hs]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hw)
  have hleft := first_keeps_left hgoal ha hb hne hz hsub hl
  have hright := first_keeps_left hgoal hb ha hne.symm
    (by simpa only [first_ops_comm] using hz) hsub hl
  rw [Finset.insert_eq_of_mem hright, Finset.insert_eq_of_mem hleft] at hs
  exact hs.symm

lemma first_roots_card : signedRoots.card = 7 := by decide +kernel

lemma first_split_live {goal : BitVec 128} {k : Nat}
    (hgoal : goal = sampleGoal ∨ goal = ~~~sampleGoal)
    (hl : live basicOps goal (k + 1) signedRoots) :
    ∃ a ∈ signedRoots, ∃ b ∈ signedRoots, a ≠ b ∧
      ∃ z ∈ basicOps a b, z ∉ signedRoots ∧ live basicOps goal k (insert z signedRoots) := by
  rcases first_live hl with hs | ⟨a, ha, b, hb, hne, z, hz, hout, rest, hs, ht⟩
  · have hc := first_roots_card
    rw [hs, Finset.card_singleton] at hc
    omega
  · have hrest := first_rest_complete hgoal ha hb hne hz hs ht
    rw [hrest] at ht
    exact ⟨a, ha, b, hb, hne, z, hz, hout, ht⟩

lemma first_split_build {goal : BitVec 128} {k : Nat}
    (hgoal : goal = sampleGoal ∨ goal = ~~~sampleGoal)
    (hb : build basicOps goal (k + 1) signedRoots) :
    ∃ a ∈ signedRoots, ∃ b ∈ signedRoots, a ≠ b ∧
      ∃ z ∈ basicOps a b, z ∉ signedRoots ∧ live basicOps goal k (insert z signedRoots) := by
  obtain ⟨s, hs, hl⟩ := compress hb
  have he := firstRootsComplete hgoal hs hl
  rw [he] at hl
  exact first_split_live hgoal hl

lemma rejection_from_first {goal : BitVec 128} {k : Nat}
    (hgoal : goal = sampleGoal ∨ goal = ~~~sampleGoal)
    (reject : ∀ a ∈ signedRoots, ∀ b ∈ signedRoots, a ≠ b →
      ∀ z ∈ basicOps a b, z ∉ signedRoots → ¬ live basicOps goal k (insert z signedRoots)) :
    ¬ build basicOps goal (k + 1) signedRoots := by
  intro hb
  obtain ⟨a, ha, b, hb, hne, z, hz, hout, hl⟩ := first_split_build hgoal hb
  exact reject a ha b hb hne z hz hout hl

lemma rejection_from_indexed {goal : BitVec 128} {k : Nat}
    (hgoal : goal = sampleGoal ∨ goal = ~~~sampleGoal)
    (reject : ∀ i j : Fin 7, j < i → ∀ o : Fin 4,
      ¬ live basicOps goal k (insert (firstOp i j o) signedRoots)) :
    ¬ build basicOps goal (k + 1) signedRoots := by
  apply rejection_from_first hgoal
  intro a ha b hb hne z hz _
  obtain ⟨i, rfl⟩ := first_mem ha
  obtain ⟨j, rfl⟩ := first_mem hb
  have hij : i ≠ j := fun h => hne (congrArg firstRoot h)
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hz' : z ∈ basicOps (firstRoot j) (firstRoot i) := by
      rwa [first_ops_comm]
    obtain ⟨o, rfl⟩ := first_op_mem hz'
    exact reject j i hij o
  · obtain ⟨o, rfl⟩ := first_op_mem hz
    exact reject i j hji o

lemma first_ops_zero {width : Nat} {a b z : BitVec width} (i : Fin width)
    (hz : z ∈ basicOps a b) (ha : a[i.val] = false) (hb : b[i.val] = false) :
    z[i.val] = false := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not, ha, hb,
      Bool.false_and, Bool.false_or]

lemma first_build_zero {width : Nat} {goal : BitVec width} (i : Fin width)
    (k : Nat) (s : Finset (BitVec width)) (hs : ∀ w ∈ s, w[i.val] = false)
    (hb : build basicOps goal k s) : goal[i.val] = false := by
  induction k generalizing s with
  | zero => exact hs goal hb
  | succ k ih =>
    rcases hb with skip | ⟨a, ha, b, hb, _, z, hz, tail⟩
    · exact ih s hs skip
    · apply ih (insert z s) _ tail
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact first_ops_zero i hz (hs a ha) (hs b hb)
      · exact hs w hw

lemma first_roots_zero : ∀ w ∈ signedRoots, w[127] = false := by
  intro w hw
  obtain ⟨i, rfl⟩ := first_mem hw
  have all : ∀ j : Fin 7, (firstRoot j)[127] = false := by decide +kernel
  exact all i

lemma reject_positive_goal (k : Nat) : ¬ build basicOps sampleGoal k signedRoots := by
  intro hb
  have hz := first_build_zero (goal := sampleGoal) ⟨127, by decide⟩ k signedRoots first_roots_zero hb
  have ho : sampleGoal[127] = true := by decide +kernel
  exact Bool.noConfusion (ho.symm.trans hz)

lemma rejection_from_84
    (reject : ∀ i j : Fin 7, j < i → ∀ o : Fin 4,
      ¬ live basicOps (~~~sampleGoal) 11 (insert (firstOp i j o) signedRoots)) :
    ∀ z, z = sampleGoal ∨ z = ~~~sampleGoal → ¬ build basicOps z 12 signedRoots := by
  intro z hz
  rcases hz with rfl | rfl
  · exact reject_positive_goal 12
  · exact rejection_from_indexed (Or.inr rfl) reject

end PEqualNP.Outside.L_meta_10760

namespace PEqualNP.Outside.L_meta_10760

open PEqualNP.CircuitLowerBounds

def canonical64 (w : BitVec 64) : BitVec 64 :=
  if w.toNat ≤ (~~~w).toNat then w else ~~~w

def sampleInputs64 : List (BitVec 64) := [0x844a844a8952aaa, 0x1089308931264ccc, 0x2111c111c23870f0, 0x421e021e03c07f00, 0x83e003e003ff8000, 0xfc0003fffc000000, 0xfffffc0000000000]

def sampleGoal64 : BitVec 64 := 0xffdfebdfbbbf6ca0

def signedRoots64 : Finset (BitVec 64) := (sampleInputs64.map canonical64).toFinset

lemma sample_represented64 : ∀ u ∈ sampleInputs64, holds signedRoots64 u := by
  intro u hu
  refine Or.inr (Or.inr ⟨canonical64 u,
    List.mem_toFinset.mpr (List.mem_map.mpr ⟨u, hu, rfl⟩), ?_⟩)
  unfold canonical64
  split
  · exact Or.inl rfl
  · exact Or.inr BitVec.not_not.symm

set_option maxHeartbeats 2000000 in
lemma sample_rows64 : ∀ j : Fin 64,
    edgeFunction (fun i => (sampleInputs64.getD i.val 0)[j.val]) = sampleGoal64[j.val] := by
  decide +kernel

set_option maxHeartbeats 2000000 in
lemma gap_of_rejection64
    (reject : ∀ z, z = sampleGoal64 ∨ z = ~~~sampleGoal64 →
      ¬ build basicOps z 12 signedRoots64) :
∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o hg _ hf
  obtain ⟨ds, out, ok, len, ev⟩ := replace_from_samples
    (replacementSize := 14) (goal := sampleGoal64)
    (by decide +kernel) (by decide +kernel) edgeFunction sampleInputs64 signedRoots64
    sample_represented64 rfl sample_rows64 reject
    ⟨monotoneWitness, 20, witness_allowed, witness_size, witness_eval⟩
    gates o hg (fun x => (hf x).trans (edgeFunction_posted x))
  exact ⟨ds, out, ok, len, fun x => (ev x).trans (edgeFunction_posted x).symm⟩

end PEqualNP.Outside.L_meta_10760


namespace PEqualNP.Outside.L_meta_10760.S64

def firstRoot (i : Fin 7) : BitVec 64 :=
  min (sampleInputs64.getD i.val 0) (~~~(sampleInputs64.getD i.val 0))

def firstOp (i j : Fin 7) (o : Fin 4) : BitVec 64 :=
  (ops (firstRoot i) (firstRoot j)).getD o.val 0

def collisionData : List Nat := [0, 0, 0, 0, 261, 391, 391, 261, 976, 261, 261, 976, 261, 781, 781, 261, 976, 261, 261, 976, 1691, 261, 261, 1691, 2731, 261, 261, 2731, 522, 587, 587, 522, 0, 0, 0, 0, 522, 782, 782, 522, 977, 522, 522, 977, 977, 522, 522, 977, 1692, 522, 522, 1692, 3447, 522, 522, 3447, 979, 69, 69, 979, 69, 199, 199, 69, 0, 0, 0, 0, 69, 589, 589, 69, 979, 69, 69, 979, 2408, 69, 69, 2408, 2734, 69, 69, 2734, 138, 203, 203, 138, 1697, 138, 138, 1697, 138, 398, 398, 138, 0, 0, 0, 0, 2409, 138, 138, 2409, 1697, 138, 138, 1697, 2737, 138, 138, 2737, 145, 80, 80, 145, 80, 145, 145, 80, 80, 275, 275, 80, 80, 599, 599, 80, 0, 0, 0, 0, 1960, 80, 80, 1960, 2871, 80, 80, 2871, 156, 91, 91, 156, 91, 156, 156, 91, 91, 416, 416, 91, 91, 545, 545, 91, 1449, 91, 91, 1449, 0, 0, 0, 0, 2746, 91, 91, 2746, 302, 107, 107, 302, 107, 237, 237, 107, 107, 302, 302, 107, 107, 561, 561, 107, 1465, 107, 107, 1465, 1722, 107, 107, 1722, 0, 0, 0, 0]

def collisionPos (i j : Fin 7) (o : Fin 4) : Fin 64 :=
  ⟨(collisionData.getD ((i.val * 7 + j.val) * 4 + o.val) 0) % 64, Nat.mod_lt _ (by decide)⟩

def collisionNeg (i j : Fin 7) (o : Fin 4) : Fin 64 :=
  ⟨(collisionData.getD ((i.val * 7 + j.val) * 4 + o.val) 0 / 64) % 64, Nat.mod_lt _ (by decide)⟩

set_option maxHeartbeats 8000000 in
lemma first_collision : ∀ i j : Fin 7, ∀ o : Fin 4, i ≠ j →
    sampleGoal64[(collisionPos i j o).val] ≠ sampleGoal64[(collisionNeg i j o).val] ∧
    (firstOp i j o)[(collisionPos i j o).val] = (firstOp i j o)[(collisionNeg i j o).val] ∧
    ∀ k : Fin 7, k ≠ i →
      (firstRoot k)[(collisionPos i j o).val] = (firstRoot k)[(collisionNeg i j o).val] := by
  decide +kernel

lemma first_roots_eq : signedRoots64 = Finset.univ.image firstRoot := by
  decide +kernel

lemma first_mem {u : BitVec 64} (hu : u ∈ signedRoots64) : ∃ i : Fin 7, u = firstRoot i := by
  rw [first_roots_eq] at hu
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hu
  exact ⟨i, hi.symm⟩

lemma first_op_mem {i j : Fin 7} {z : BitVec 64}
    (hz : z ∈ basicOps (firstRoot i) (firstRoot j)) : ∃ o : Fin 4, z = firstOp i j o := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩

lemma first_bit_congr {width : Nat} {a b z : BitVec width} (i j : Fin width)
    (hz : z ∈ basicOps a b) (ha : a[i.val] = a[j.val]) (hb : b[i.val] = b[j.val]) :
    z[i.val] = z[j.val] := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not, ha, hb]

lemma first_live_separates {width : Nat} {goal : BitVec width} {k : Nat}
    {s : Finset (BitVec width)} (i j : Fin width) (hd : goal[i.val] ≠ goal[j.val])
    (hl : live basicOps goal k s) : ∃ w ∈ s, w[i.val] ≠ w[j.val] := by
  apply live_separates (fun w => w[i.val] ≠ w[j.val]) hd _ hl
  intro a b z hz hne
  by_contra hn
  simp only [not_or, not_not] at hn
  exact hne (first_bit_congr i j hz hn.1 hn.2)

lemma first_drop_collision {a b z : BitVec 64}
    (ha : a ∈ signedRoots64) (hb : b ∈ signedRoots64) (hne : a ≠ b)
    (hz : z ∈ basicOps a b) :
    ∃ i j : Fin 64, sampleGoal64[i.val] ≠ sampleGoal64[j.val] ∧
      ∀ w ∈ insert z (signedRoots64.erase a), w[i.val] = w[j.val] := by
  obtain ⟨i, rfl⟩ := first_mem ha
  obtain ⟨j, rfl⟩ := first_mem hb
  obtain ⟨o, rfl⟩ := first_op_mem hz
  obtain ⟨hg, ho, hw⟩ := first_collision i j o (fun h => hne (congrArg firstRoot h))
  refine ⟨collisionPos i j o, collisionNeg i j o, hg, ?_⟩
  intro w hmem
  rcases Finset.mem_insert.mp hmem with rfl | hmem
  · exact ho
  · obtain ⟨hneq, hroot⟩ := Finset.mem_erase.mp hmem
    obtain ⟨k, rfl⟩ := first_mem hroot
    exact hw k (fun h => hneq (congrArg firstRoot h))

def essentialPos (i : Fin 7) : Fin 64 :=
  ⟨(([5, 10, 5, 10, 16, 27, 43] : List Nat).getD i.val 0) % 64, Nat.mod_lt _ (by decide)⟩

def essentialNeg (i : Fin 7) : Fin 64 :=
  ⟨(([4, 8, 1, 2, 1, 1, 1] : List Nat).getD i.val 0) % 64, Nat.mod_lt _ (by decide)⟩

lemma first_essential : ∀ i : Fin 7,
    sampleGoal64[(essentialPos i).val] ≠ sampleGoal64[(essentialNeg i).val] ∧
    ∀ j : Fin 7, j ≠ i →
      (firstRoot j)[(essentialPos i).val] = (firstRoot j)[(essentialNeg i).val] := by
  decide +kernel

lemma first_goal_diff {goal : BitVec 64} (hgoal : goal = sampleGoal64 ∨ goal = ~~~sampleGoal64)
    {i j : Fin 64} (hd : sampleGoal64[i.val] ≠ sampleGoal64[j.val]) : goal[i.val] ≠ goal[j.val] := by
  rcases hgoal with rfl | rfl
  · exact hd
  · intro h
    apply hd
    have hh := congrArg Bool.not h
    simpa only [BitVec.getElem_not, Bool.not_not] using hh

lemma firstRootsComplete {goal : BitVec 64} {k : Nat} {s : Finset (BitVec 64)}
    (hgoal : goal = sampleGoal64 ∨ goal = ~~~sampleGoal64)
    (hsub : s ⊆ signedRoots64) (hl : live basicOps goal k s) : s = signedRoots64 := by
  apply Finset.Subset.antisymm hsub
  intro a ha
  obtain ⟨i, rfl⟩ := first_mem ha
  by_contra hn
  obtain ⟨hd, hw⟩ := first_essential i
  obtain ⟨w, hws, hne⟩ := first_live_separates (essentialPos i) (essentialNeg i)
    (first_goal_diff hgoal hd) hl
  obtain ⟨j, rfl⟩ := first_mem (hsub hws)
  exact hne (hw j (fun h => hn (by simpa [h] using hws)))

lemma first_keeps_left {goal a b z : BitVec 64} {k : Nat} {rest : Finset (BitVec 64)}
    (hgoal : goal = sampleGoal64 ∨ goal = ~~~sampleGoal64)
    (ha : a ∈ signedRoots64) (hb : b ∈ signedRoots64) (hne : a ≠ b)
    (hz : z ∈ basicOps a b) (hsub : rest ⊆ signedRoots64)
    (hl : live basicOps goal k (insert z rest)) : a ∈ rest := by
  by_contra haout
  obtain ⟨i, j, hd, hc⟩ := first_drop_collision ha hb hne hz
  obtain ⟨w, hw, hbad⟩ := first_live_separates i j (first_goal_diff hgoal hd) hl
  apply hbad
  apply hc
  rcases Finset.mem_insert.mp hw with rfl | hw
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun h => haout (h ▸ hw), hsub hw⟩)

lemma first_ops_comm (a b : BitVec 64) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false,
    BitVec.and_comm, BitVec.or_comm]
  tauto

lemma first_rest_complete {goal a b z : BitVec 64} {k : Nat} {rest : Finset (BitVec 64)}
    (hgoal : goal = sampleGoal64 ∨ goal = ~~~sampleGoal64)
    (ha : a ∈ signedRoots64) (hb : b ∈ signedRoots64) (hne : a ≠ b)
    (hz : z ∈ basicOps a b) (hs : signedRoots64 = insert a (insert b rest))
    (hl : live basicOps goal k (insert z rest)) : rest = signedRoots64 := by
  have hsub : rest ⊆ signedRoots64 := by
    intro w hw
    rw [hs]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hw)
  have hleft := first_keeps_left hgoal ha hb hne hz hsub hl
  have hright := first_keeps_left hgoal hb ha hne.symm
    (by simpa only [first_ops_comm] using hz) hsub hl
  rw [Finset.insert_eq_of_mem hright, Finset.insert_eq_of_mem hleft] at hs
  exact hs.symm

lemma first_roots_card : signedRoots64.card = 7 := by decide +kernel

lemma first_split_live {goal : BitVec 64} {k : Nat}
    (hgoal : goal = sampleGoal64 ∨ goal = ~~~sampleGoal64)
    (hl : live basicOps goal (k + 1) signedRoots64) :
    ∃ a ∈ signedRoots64, ∃ b ∈ signedRoots64, a ≠ b ∧
      ∃ z ∈ basicOps a b, z ∉ signedRoots64 ∧ live basicOps goal k (insert z signedRoots64) := by
  rcases first_live hl with hs | ⟨a, ha, b, hb, hne, z, hz, hout, rest, hs, ht⟩
  · have hc := first_roots_card
    rw [hs, Finset.card_singleton] at hc
    omega
  · have hrest := first_rest_complete hgoal ha hb hne hz hs ht
    rw [hrest] at ht
    exact ⟨a, ha, b, hb, hne, z, hz, hout, ht⟩

lemma first_split_build {goal : BitVec 64} {k : Nat}
    (hgoal : goal = sampleGoal64 ∨ goal = ~~~sampleGoal64)
    (hb : build basicOps goal (k + 1) signedRoots64) :
    ∃ a ∈ signedRoots64, ∃ b ∈ signedRoots64, a ≠ b ∧
      ∃ z ∈ basicOps a b, z ∉ signedRoots64 ∧ live basicOps goal k (insert z signedRoots64) := by
  obtain ⟨s, hs, hl⟩ := compress hb
  have he := firstRootsComplete hgoal hs hl
  rw [he] at hl
  exact first_split_live hgoal hl

lemma rejection_from_first {goal : BitVec 64} {k : Nat}
    (hgoal : goal = sampleGoal64 ∨ goal = ~~~sampleGoal64)
    (reject : ∀ a ∈ signedRoots64, ∀ b ∈ signedRoots64, a ≠ b →
      ∀ z ∈ basicOps a b, z ∉ signedRoots64 → ¬ live basicOps goal k (insert z signedRoots64)) :
    ¬ build basicOps goal (k + 1) signedRoots64 := by
  intro hb
  obtain ⟨a, ha, b, hb, hne, z, hz, hout, hl⟩ := first_split_build hgoal hb
  exact reject a ha b hb hne z hz hout hl

lemma rejection_from_indexed {goal : BitVec 64} {k : Nat}
    (hgoal : goal = sampleGoal64 ∨ goal = ~~~sampleGoal64)
    (reject : ∀ i j : Fin 7, j < i → ∀ o : Fin 4,
      ¬ live basicOps goal k (insert (firstOp i j o) signedRoots64)) :
    ¬ build basicOps goal (k + 1) signedRoots64 := by
  apply rejection_from_first hgoal
  intro a ha b hb hne z hz _
  obtain ⟨i, rfl⟩ := first_mem ha
  obtain ⟨j, rfl⟩ := first_mem hb
  have hij : i ≠ j := fun h => hne (congrArg firstRoot h)
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hz' : z ∈ basicOps (firstRoot j) (firstRoot i) := by
      rwa [first_ops_comm]
    obtain ⟨o, rfl⟩ := first_op_mem hz'
    exact reject j i hij o
  · obtain ⟨o, rfl⟩ := first_op_mem hz
    exact reject i j hji o

lemma first_ops_zero {width : Nat} {a b z : BitVec width} (i : Fin width)
    (hz : z ∈ basicOps a b) (ha : a[i.val] = false) (hb : b[i.val] = false) :
    z[i.val] = false := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not, ha, hb,
      Bool.false_and, Bool.false_or]

lemma first_build_zero {width : Nat} {goal : BitVec width} (i : Fin width)
    (k : Nat) (s : Finset (BitVec width)) (hs : ∀ w ∈ s, w[i.val] = false)
    (hb : build basicOps goal k s) : goal[i.val] = false := by
  induction k generalizing s with
  | zero => exact hs goal hb
  | succ k ih =>
    rcases hb with skip | ⟨a, ha, b, hb, _, z, hz, tail⟩
    · exact ih s hs skip
    · apply ih (insert z s) _ tail
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact first_ops_zero i hz (hs a ha) (hs b hb)
      · exact hs w hw

lemma first_roots_zero : ∀ w ∈ signedRoots64, w[63] = false := by
  intro w hw
  obtain ⟨i, rfl⟩ := first_mem hw
  have all : ∀ j : Fin 7, (firstRoot j)[63] = false := by decide +kernel
  exact all i

lemma reject_positive_goal (k : Nat) : ¬ build basicOps sampleGoal64 k signedRoots64 := by
  intro hb
  have hz := first_build_zero (goal := sampleGoal64) ⟨63, by decide⟩ k signedRoots64 first_roots_zero hb
  have ho : sampleGoal64[63] = true := by decide +kernel
  exact Bool.noConfusion (ho.symm.trans hz)

lemma rejection_from_84_64
    (reject : ∀ i j : Fin 7, j < i → ∀ o : Fin 4,
      ¬ live basicOps (~~~sampleGoal64) 11 (insert (firstOp i j o) signedRoots64)) :
    ∀ z, z = sampleGoal64 ∨ z = ~~~sampleGoal64 → ¬ build basicOps z 12 signedRoots64 := by
  intro z hz
  rcases hz with rfl | rfl
  · exact reject_positive_goal 12
  · exact rejection_from_indexed (Or.inr rfl) reject

end PEqualNP.Outside.L_meta_10760.S64
