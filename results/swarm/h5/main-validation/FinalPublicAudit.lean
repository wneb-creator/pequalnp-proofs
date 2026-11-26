import PEqualNP.Outside.L_meta_2373

set_option pp.fullNames true

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_2373

example : ∀ (gs gs' : List Gate) (w : List Bool),
  wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := @PEqualNP.Outside.L_meta_2373.wiresFrom_append

#check @PEqualNP.Outside.L_meta_2373.wiresFrom_append
#print axioms PEqualNP.Outside.L_meta_2373.wiresFrom_append

example : ∀ (gs : List Gate),
  ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := @PEqualNP.Outside.L_meta_2373.wiresFrom_prefix

#check @PEqualNP.Outside.L_meta_2373.wiresFrom_prefix
#print axioms PEqualNP.Outside.L_meta_2373.wiresFrom_prefix

example : ∀ (gs : List Gate) (w : List Bool),
  (wiresFrom gs w).length = w.length + gs.length := @PEqualNP.Outside.L_meta_2373.length_wiresFrom

#check @PEqualNP.Outside.L_meta_2373.length_wiresFrom
#print axioms PEqualNP.Outside.L_meta_2373.length_wiresFrom

example : ∀ (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length),
  (wiresFrom gs w).getD i false = w.getD i false := @PEqualNP.Outside.L_meta_2373.getD_wiresFrom

#check @PEqualNP.Outside.L_meta_2373.getD_wiresFrom
#print axioms PEqualNP.Outside.L_meta_2373.getD_wiresFrom

example : ∀ {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length),
  (L ++ [S]).getD j d = L.getD j d := @PEqualNP.Outside.L_meta_2373.getD_snoc_ne

#check @PEqualNP.Outside.L_meta_2373.getD_snoc_ne
#print axioms PEqualNP.Outside.L_meta_2373.getD_snoc_ne

example : ∀ {α : Type} (L : List α) (S d : α),
  (L ++ [S]).getD L.length d = S := @PEqualNP.Outside.L_meta_2373.getD_snoc_eq

#check @PEqualNP.Outside.L_meta_2373.getD_snoc_eq
#print axioms PEqualNP.Outside.L_meta_2373.getD_snoc_eq

example : ∀ (op : GateOp) (m : ℕ) (ins : List Stat),
  ∀ g ∈ (simplify op m ins).1, Ok g := @PEqualNP.Outside.L_meta_2373.simplify_ok

#check @PEqualNP.Outside.L_meta_2373.simplify_ok
#print axioms PEqualNP.Outside.L_meta_2373.simplify_ok

example : ∀ (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins),
  (simplify op m ins).1 = none := @PEqualNP.Outside.L_meta_2373.simplify_count

#check @PEqualNP.Outside.L_meta_2373.simplify_count
#print axioms PEqualNP.Outside.L_meta_2373.simplify_count

example : ∀ (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length),
  ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := @PEqualNP.Outside.L_meta_2373.simplify_sound

#check @PEqualNP.Outside.L_meta_2373.simplify_sound
#print axioms PEqualNP.Outside.L_meta_2373.simplify_sound

example : ∀ {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k),
  (L ++ [S]).getD k d = S := @PEqualNP.Outside.L_meta_2373.getD_snoc_len

#check @PEqualNP.Outside.L_meta_2373.getD_snoc_len
#print axioms PEqualNP.Outside.L_meta_2373.getD_snoc_len

example : ∀ {α : Type} (o : Option α),
  o.toList.length ≤ 1 := @PEqualNP.Outside.L_meta_2373.toList_length_le

#check @PEqualNP.Outside.L_meta_2373.toList_length_le
#print axioms PEqualNP.Outside.L_meta_2373.toList_length_le

example : ∀ (n : ℕ) (gs : List Gate),
  ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := @PEqualNP.Outside.L_meta_2373.elim_ok

#check @PEqualNP.Outside.L_meta_2373.elim_ok
#print axioms PEqualNP.Outside.L_meta_2373.elim_ok

example : ∀ (n : ℕ) (gs : List Gate),
  ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := @PEqualNP.Outside.L_meta_2373.elim_len

#check @PEqualNP.Outside.L_meta_2373.elim_len
#print axioms PEqualNP.Outside.L_meta_2373.elim_len

example : ∀ {m m' : ℕ} (h : m ≤ m'),
  ∀ s : Stat, s.Valid m → s.Valid m' := @PEqualNP.Outside.L_meta_2373.Stat.valid_mono

#check @PEqualNP.Outside.L_meta_2373.Stat.valid_mono
#print axioms PEqualNP.Outside.L_meta_2373.Stat.valid_mono

example : ∀ (w t : List Bool),
  ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w := @PEqualNP.Outside.L_meta_2373.Stat.val_append

#check @PEqualNP.Outside.L_meta_2373.Stat.val_append
#print axioms PEqualNP.Outside.L_meta_2373.Stat.val_append

example : ∀ (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate),
  ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := @PEqualNP.Outside.L_meta_2373.inv_elim

#check @PEqualNP.Outside.L_meta_2373.inv_elim
#print axioms PEqualNP.Outside.L_meta_2373.inv_elim

example : ∀ (g : Gate) (F : ℕ → Bool),
  (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := @PEqualNP.Outside.L_meta_2373.normGate_eval

#check @PEqualNP.Outside.L_meta_2373.normGate_eval
#print axioms PEqualNP.Outside.L_meta_2373.normGate_eval

example : ∀ (g : Gate) (h : Ok g),
  NOk (normGate g) := @PEqualNP.Outside.L_meta_2373.normGate_nok

#check @PEqualNP.Outside.L_meta_2373.normGate_nok
#print axioms PEqualNP.Outside.L_meta_2373.normGate_nok

example : ∀ (gs : List Gate),
  ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := @PEqualNP.Outside.L_meta_2373.wiresFrom_norm

#check @PEqualNP.Outside.L_meta_2373.wiresFrom_norm
#print axioms PEqualNP.Outside.L_meta_2373.wiresFrom_norm

example : ∀ (n : ℕ) (b : Bool) (y : Fin n → Bool),
  Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := @PEqualNP.Outside.L_meta_2373.inv_init

#check @PEqualNP.Outside.L_meta_2373.inv_init
#print axioms PEqualNP.Outside.L_meta_2373.inv_init

example : ∀ (n : ℕ) (y : Fin n → Bool) (b : Bool),
  List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := @PEqualNP.Outside.L_meta_2373.ofFn_snoc

#check @PEqualNP.Outside.L_meta_2373.ofFn_snoc
#print axioms PEqualNP.Outside.L_meta_2373.ofFn_snoc

example : ∀ (n k : ℕ) (gs : List Gate),
  ∀ acc : List Stat × List Gate,
      (∀ g ∈ gs, NOk g) → k < acc.1.length →
      (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
      (elim n gs acc).2.length + readerCount k gs ≤ acc.2.length + gs.length := @PEqualNP.Outside.L_meta_2373.elim_len_readers

#check @PEqualNP.Outside.L_meta_2373.elim_len_readers
#print axioms PEqualNP.Outside.L_meta_2373.elim_len_readers

example : ∀ (n : ℕ) (b : Bool) (C : Circuit)
    (hC : FanInTwo C)
    (hnc : ∃ y y' : Fin n → Bool,
      C.eval (List.ofFn (Fin.snoc y b)) ≠ C.eval (List.ofFn (Fin.snoc y' b))),
  ∃ E : Circuit, FanInTwo E ∧
      E.size + readerCount n (C.gates.map normGate) ≤ C.size ∧
      ∀ y : Fin n → Bool, E.eval (List.ofFn y) = C.eval (List.ofFn (Fin.snoc y b)) := @PEqualNP.Outside.L_meta_2373.fix_last_counted

#check @PEqualNP.Outside.L_meta_2373.fix_last_counted
#print axioms PEqualNP.Outside.L_meta_2373.fix_last_counted

example : ∀ (n q s : ℕ) (b : Bool) (C : Circuit)
    (hC : FanInTwo C) (hsize : C.size ≤ s)
    (hnc : ∃ y y' : Fin n → Bool,
      C.eval (List.ofFn (Fin.snoc y b)) ≠ C.eval (List.ofFn (Fin.snoc y' b)))
    (hlower : ∀ E : Circuit, FanInTwo E →
      (∀ y : Fin n → Bool, E.eval (List.ofFn y) = C.eval (List.ofFn (Fin.snoc y b))) →
      q ≤ E.size),
  q + readerCount n (C.gates.map normGate) ≤ s := @PEqualNP.Outside.L_meta_2373.readers_le_of_cofactor_lower

#check @PEqualNP.Outside.L_meta_2373.readers_le_of_cofactor_lower
#print axioms PEqualNP.Outside.L_meta_2373.readers_le_of_cofactor_lower

example : ∀ (n : ℕ) (K : Finset ℕ) (gs : List Gate),
  ∀ acc : List Stat × List Gate,
      (∀ g ∈ gs, NOk g) →
      (∀ k ∈ K, k < acc.1.length ∧ ∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
      (elim n gs acc).2.length + setReaderCount K gs ≤ acc.2.length + gs.length := @PEqualNP.Outside.L_meta_2373.elim_len_setReaders

#check @PEqualNP.Outside.L_meta_2373.elim_len_setReaders
#print axioms PEqualNP.Outside.L_meta_2373.elim_len_setReaders

example : ∀ (n k : ℕ) (d : Stat) (gs : List Gate),
  ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := @PEqualNP.Outside.L_meta_2373.elim_getD

#check @PEqualNP.Outside.L_meta_2373.elim_getD
#print axioms PEqualNP.Outside.L_meta_2373.elim_getD

example : ∀ (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate),
  (elim n gs acc).1.length = acc.1.length + gs.length := @PEqualNP.Outside.L_meta_2373.elim_status_length

#check @PEqualNP.Outside.L_meta_2373.elim_status_length
#print axioms PEqualNP.Outside.L_meta_2373.elim_status_length

example : ∀ (m : ℕ) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hz : Sum.inl false ∈ ins),
  simplify GateOp.and m ins = (none, Sum.inl false) := @PEqualNP.Outside.L_meta_2373.simplify_and_false

#check @PEqualNP.Outside.L_meta_2373.simplify_and_false
#print axioms PEqualNP.Outside.L_meta_2373.simplify_and_false

example : ∀ (n k : ℕ) (pre post : List Gate) (g : Gate)
    (acc : List Stat × List Gate)
    (hok : ∀ h ∈ pre ++ g :: post, NOk h)
    (hk : k < acc.1.length) (hz : acc.1.getD k (Sum.inl false) = Sum.inl false)
    (hg : g.op = GateOp.and) (hread : k ∈ g.inputs),
  (elim n (pre ++ g :: post) acc).2.length + readerCount k pre + 1 +
        setReaderCount {k, acc.1.length + pre.length} post ≤
      acc.2.length + (pre ++ g :: post).length := @PEqualNP.Outside.L_meta_2373.elim_and_reader_bound

#check @PEqualNP.Outside.L_meta_2373.elim_and_reader_bound
#print axioms PEqualNP.Outside.L_meta_2373.elim_and_reader_bound

example : ∀ (k : ℕ) (xs ys : List Gate),
  readerCount k (xs ++ ys) = readerCount k xs + readerCount k ys := @PEqualNP.Outside.L_meta_2373.readerCount_append

#check @PEqualNP.Outside.L_meta_2373.readerCount_append
#print axioms PEqualNP.Outside.L_meta_2373.readerCount_append

example : ∀ (k l : ℕ) (g : Gate) (gs : List Gate),
  setReaderCount {k, l} (g :: gs) =
      (if k ∈ g.inputs ∨ l ∈ g.inputs then 1 else 0) + setReaderCount {k, l} gs := @PEqualNP.Outside.L_meta_2373.setReaderCount_pair_cons

#check @PEqualNP.Outside.L_meta_2373.setReaderCount_pair_cons
#print axioms PEqualNP.Outside.L_meta_2373.setReaderCount_pair_cons

example : ∀ (k l : ℕ) (gs : List Gate),
  readerCount k gs ≤ setReaderCount {k, l} gs := @PEqualNP.Outside.L_meta_2373.setReaderCount_pair_ge

#check @PEqualNP.Outside.L_meta_2373.setReaderCount_pair_ge
#print axioms PEqualNP.Outside.L_meta_2373.setReaderCount_pair_ge

example : ∀ (k l : ℕ) (gs : List Gate)
    (hx : ∃ g ∈ gs, l ∈ g.inputs ∧ k ∉ g.inputs),
  readerCount k gs + 1 ≤ setReaderCount {k, l} gs := @PEqualNP.Outside.L_meta_2373.setReaderCount_pair_extra

#check @PEqualNP.Outside.L_meta_2373.setReaderCount_pair_extra
#print axioms PEqualNP.Outside.L_meta_2373.setReaderCount_pair_extra

example : ∀ (n k : ℕ) (pre post : List Gate) (g : Gate)
    (acc : List Stat × List Gate)
    (hok : ∀ h ∈ pre ++ g :: post, NOk h)
    (hk : k < acc.1.length) (hz : acc.1.getD k (Sum.inl false) = Sum.inl false)
    (hg : g.op = GateOp.and) (hread : k ∈ g.inputs)
    (hconsumer : ∃ h ∈ post, acc.1.length + pre.length ∈ h.inputs ∧ k ∉ h.inputs),
  (elim n (pre ++ g :: post) acc).2.length +
        readerCount k (pre ++ g :: post) + 1 ≤
      acc.2.length + (pre ++ g :: post).length := @PEqualNP.Outside.L_meta_2373.elim_and_extra_saving

#check @PEqualNP.Outside.L_meta_2373.elim_and_extra_saving
#print axioms PEqualNP.Outside.L_meta_2373.elim_and_extra_saving

example : ∀ (n q : ℕ) (b : Bool) (C : Circuit)
    (hC : FanInTwo C)
    (hnc : ∃ y y' : Fin n → Bool,
      C.eval (List.ofFn (Fin.snoc y b)) ≠ C.eval (List.ofFn (Fin.snoc y' b)))
    (hbudget : (elim n (C.gates.map normGate) (initStats n b, [])).2.length + q ≤ C.size),
  ∃ E : Circuit, FanInTwo E ∧ E.size + q ≤ C.size ∧
      ∀ y : Fin n → Bool, E.eval (List.ofFn y) = C.eval (List.ofFn (Fin.snoc y b)) := @PEqualNP.Outside.L_meta_2373.fix_last_with_savings

#check @PEqualNP.Outside.L_meta_2373.fix_last_with_savings
#print axioms PEqualNP.Outside.L_meta_2373.fix_last_with_savings

example : ∀ (n : ℕ) (C : Circuit) (pre post : List Gate) (g : Gate)
    (hC : FanInTwo C)
    (hnc : ∃ y y' : Fin n → Bool,
      C.eval (List.ofFn (Fin.snoc y false)) ≠ C.eval (List.ofFn (Fin.snoc y' false)))
    (hgs : C.gates.map normGate = pre ++ g :: post)
    (hg : g.op = GateOp.and) (hread : n ∈ g.inputs)
    (hconsumer : ∃ h ∈ post, n + 1 + pre.length ∈ h.inputs ∧ n ∉ h.inputs),
  ∃ E : Circuit, FanInTwo E ∧
      E.size + readerCount n (C.gates.map normGate) + 1 ≤ C.size ∧
      ∀ y : Fin n → Bool, E.eval (List.ofFn y) = C.eval (List.ofFn (Fin.snoc y false)) := @PEqualNP.Outside.L_meta_2373.fix_false_and_extra

#check @PEqualNP.Outside.L_meta_2373.fix_false_and_extra
#print axioms PEqualNP.Outside.L_meta_2373.fix_false_and_extra

example : ∀ (n q s : ℕ) (C : Circuit)
    (pre post : List Gate) (g : Gate)
    (hC : FanInTwo C) (hsize : C.size ≤ s)
    (hnc : ∃ y y' : Fin n → Bool,
      C.eval (List.ofFn (Fin.snoc y false)) ≠ C.eval (List.ofFn (Fin.snoc y' false)))
    (hlower : ∀ E : Circuit, FanInTwo E →
      (∀ y : Fin n → Bool, E.eval (List.ofFn y) = C.eval (List.ofFn (Fin.snoc y false))) →
      q ≤ E.size)
    (hgs : C.gates.map normGate = pre ++ g :: post)
    (hg : g.op = GateOp.and) (hread : n ∈ g.inputs)
    (hconsumer : ∃ h ∈ post, n + 1 + pre.length ∈ h.inputs ∧ n ∉ h.inputs),
  q + readerCount n (C.gates.map normGate) + 1 ≤ s := @PEqualNP.Outside.L_meta_2373.and_readers_le_of_cofactor_lower

#check @PEqualNP.Outside.L_meta_2373.and_readers_le_of_cofactor_lower
#print axioms PEqualNP.Outside.L_meta_2373.and_readers_le_of_cofactor_lower

end PEqualNP.Outside.L_meta_2373

namespace PEqualNP.Outside.L_meta_2373.Consumer

example : ∀ (l : List ℕ) (v w : ℕ) (hvw : v ≠ w)
    (hl : l.length ≤ 2) (hv : v ∈ l) (hw : w ∈ l),
  l = [v, w] ∨ l = [w, v] := @PEqualNP.Outside.L_meta_2373.Consumer.two_inputs_of_distinct

#check @PEqualNP.Outside.L_meta_2373.Consumer.two_inputs_of_distinct
#print axioms PEqualNP.Outside.L_meta_2373.Consumer.two_inputs_of_distinct

example : ∀ {A : Type} (F : A → ℕ → Bool) (g : Gate) (v w : ℕ)
    (hop : g.op = GateOp.and) (hv : v ∈ g.inputs)
    (heval : ∀ a, F a w = g.op.eval (g.inputs.map (F a))),
  ∀ a, F a w = true → F a v = true := @PEqualNP.Outside.L_meta_2373.Consumer.and_value_implies_input

#check @PEqualNP.Outside.L_meta_2373.Consumer.and_value_implies_input
#print axioms PEqualNP.Outside.L_meta_2373.Consumer.and_value_implies_input

example : ∀ {A : Type} (F : A → ℕ → Bool) (g : Gate) (v w out : ℕ)
    (hvw : v ≠ w) (hv : v ∈ g.inputs) (hw : w ∈ g.inputs)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hlen : g.inputs.length ≤ 2) (hnot : g.op = GateOp.not → g.inputs.length ≤ 1)
    (heval : ∀ a, F a out = g.op.eval (g.inputs.map (F a)))
    (himp : ∀ a, F a w = true → F a v = true),
  (∀ a, F a out = F a w) ∨ (∀ a, F a out = F a v) := @PEqualNP.Outside.L_meta_2373.Consumer.consumer_absorbs

#check @PEqualNP.Outside.L_meta_2373.Consumer.consumer_absorbs
#print axioms PEqualNP.Outside.L_meta_2373.Consumer.consumer_absorbs

example : ∀ {A : Type} (F : A → ℕ → Bool)
    (source consumer : Gate) (n v p q : ℕ) (hv : v < n) (hpq : p < q)
    (hsource : source.op = GateOp.and) (hsourcev : v ∈ source.inputs)
    (hread : n + p ∈ consumer.inputs)
    (hop : consumer.op = GateOp.and ∨ consumer.op = GateOp.or ∨ consumer.op = GateOp.not)
    (hlen : consumer.inputs.length ≤ 2)
    (hnot : consumer.op = GateOp.not → consumer.inputs.length ≤ 1)
    (hsourceval : ∀ a, F a (n + p) = source.op.eval (source.inputs.map (F a)))
    (hconsumerval : ∀ a, F a (n + q) = consumer.op.eval (consumer.inputs.map (F a)))
    (hnoalias : ∀ j, j < n + q → ¬ ∀ a, F a (n + q) = F a j),
  v ∉ consumer.inputs := @PEqualNP.Outside.L_meta_2373.Consumer.consumer_avoids_raw_input

#check @PEqualNP.Outside.L_meta_2373.Consumer.consumer_avoids_raw_input
#print axioms PEqualNP.Outside.L_meta_2373.Consumer.consumer_avoids_raw_input

example : ∀ {A : Type} (F : A → ℕ → Bool)
    (gs : List Gate) (n v p : ℕ) (source : Gate) (hv : v < n)
    (hsource : gs[p]? = some source) (hsourceop : source.op = GateOp.and)
    (hsourcev : v ∈ source.inputs)
    (hnormal : ∀ (q : ℕ) (g : Gate), gs[q]? = some g →
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2 ∧ (g.op = GateOp.not → g.inputs.length ≤ 1))
    (hvalues : ∀ (q : ℕ) (g : Gate), gs[q]? = some g →
      ∀ a, F a (n + q) = g.op.eval (g.inputs.map (F a)))
    (hnoalias : ∀ q, q < gs.length → ∀ j, j < n + q →
      ¬ ∀ a, F a (n + q) = F a j)
    (hlive : ∃ q, p < q ∧ ∃ g, gs[q]? = some g ∧ n + p ∈ g.inputs),
  ∃ q g, p < q ∧ gs[q]? = some g ∧ n + p ∈ g.inputs ∧ v ∉ g.inputs := @PEqualNP.Outside.L_meta_2373.Consumer.live_consumer_avoids_raw_input

#check @PEqualNP.Outside.L_meta_2373.Consumer.live_consumer_avoids_raw_input
#print axioms PEqualNP.Outside.L_meta_2373.Consumer.live_consumer_avoids_raw_input

end PEqualNP.Outside.L_meta_2373.Consumer

namespace PEqualNP.Outside.L_meta_2373.InputRename

example : ∀ {n : ℕ} (s : Equiv.Perm (Fin n)) {i : ℕ} (hi : n ≤ i),
  wire s i = i := @PEqualNP.Outside.L_meta_2373.InputRename.wire_ge

#check @PEqualNP.Outside.L_meta_2373.InputRename.wire_ge
#print axioms PEqualNP.Outside.L_meta_2373.InputRename.wire_ge

example : ∀ {n : ℕ} (s : Equiv.Perm (Fin n)) {i j : ℕ}
    (hj : n ≤ j) (hne : i ≠ j),
  wire s i ≠ j := @PEqualNP.Outside.L_meta_2373.InputRename.wire_ne_ge

#check @PEqualNP.Outside.L_meta_2373.InputRename.wire_ne_ge
#print axioms PEqualNP.Outside.L_meta_2373.InputRename.wire_ne_ge

example : ∀ {n : ℕ} (s : Equiv.Perm (Fin n)) (gs : List Gate),
  ∀ w w' : List Bool, w'.length = w.length → n ≤ w.length →
      (∀ i, w'.getD (wire s i) false = w.getD i false) →
      ∀ i, (wiresFrom (gs.map (gate s)) w').getD (wire s i) false =
        (wiresFrom gs w).getD i false := @PEqualNP.Outside.L_meta_2373.InputRename.wires_relation

#check @PEqualNP.Outside.L_meta_2373.InputRename.wires_relation
#print axioms PEqualNP.Outside.L_meta_2373.InputRename.wires_relation

example : ∀ {n : ℕ} (s : Equiv.Perm (Fin n)) (C : Circuit) (x : Fin n → Bool),
  (circuit s C).eval (List.ofFn (x ∘ s.symm)) = C.eval (List.ofFn x) := @PEqualNP.Outside.L_meta_2373.InputRename.eval

#check @PEqualNP.Outside.L_meta_2373.InputRename.eval
#print axioms PEqualNP.Outside.L_meta_2373.InputRename.eval

example : ∀ {n : ℕ} (s : Equiv.Perm (Fin n)) (C : Circuit),
  (circuit s C).size = C.size := @PEqualNP.Outside.L_meta_2373.InputRename.size

#check @PEqualNP.Outside.L_meta_2373.InputRename.size
#print axioms PEqualNP.Outside.L_meta_2373.InputRename.size

example : ∀ {n : ℕ} (s : Equiv.Perm (Fin n)) (C : Circuit) (hC : FanInTwo C),
  FanInTwo (circuit s C) := @PEqualNP.Outside.L_meta_2373.InputRename.fanInTwo

#check @PEqualNP.Outside.L_meta_2373.InputRename.fanInTwo
#print axioms PEqualNP.Outside.L_meta_2373.InputRename.fanInTwo

example : ∀ {n : ℕ} (s : Equiv.Perm (Fin n)) (i : Fin n) (k : ℕ),
  wire s k = i ↔ k = (s.symm i : ℕ) := @PEqualNP.Outside.L_meta_2373.InputRename.wire_preimage

#check @PEqualNP.Outside.L_meta_2373.InputRename.wire_preimage
#print axioms PEqualNP.Outside.L_meta_2373.InputRename.wire_preimage

example : ∀ {n : ℕ} (s : Equiv.Perm (Fin n)) (g : Gate),
  normGate (gate s g) = gate s (normGate g) := @PEqualNP.Outside.L_meta_2373.InputRename.norm_gate

#check @PEqualNP.Outside.L_meta_2373.InputRename.norm_gate
#print axioms PEqualNP.Outside.L_meta_2373.InputRename.norm_gate

example : ∀ {n : ℕ} (s : Equiv.Perm (Fin n)) (i : Fin n) (gs : List Gate),
  readerCount i (gs.map (gate s)) = readerCount (s.symm i) gs := @PEqualNP.Outside.L_meta_2373.InputRename.readerCount_map

#check @PEqualNP.Outside.L_meta_2373.InputRename.readerCount_map
#print axioms PEqualNP.Outside.L_meta_2373.InputRename.readerCount_map

example : ∀ {n : ℕ} (s : Equiv.Perm (Fin n)) (i : Fin n) (C : Circuit),
  readerCount i ((circuit s C).gates.map normGate) =
      readerCount (s.symm i) (C.gates.map normGate) := @PEqualNP.Outside.L_meta_2373.InputRename.effective_readers

#check @PEqualNP.Outside.L_meta_2373.InputRename.effective_readers
#print axioms PEqualNP.Outside.L_meta_2373.InputRename.effective_readers

example : ∀ {n : ℕ} (s : Equiv.Perm (Fin n)) (C : Circuit) (y : Fin n → Bool),
  (circuit s C).eval (List.ofFn y) = C.eval (List.ofFn (y ∘ s)) := @PEqualNP.Outside.L_meta_2373.InputRename.eval_relabel

#check @PEqualNP.Outside.L_meta_2373.InputRename.eval_relabel
#print axioms PEqualNP.Outside.L_meta_2373.InputRename.eval_relabel

end PEqualNP.Outside.L_meta_2373.InputRename

namespace PEqualNP.Outside.L_meta_2373

example : ∀ (n : ℕ) (v : Fin (n + 1)) (b : Bool) (C : Circuit)
    (hC : FanInTwo C)
    (hnc : ∃ y y' : Fin n → Bool,
      C.eval (List.ofFn (Fin.snoc y b ∘ Equiv.swap v (Fin.last n))) ≠
        C.eval (List.ofFn (Fin.snoc y' b ∘ Equiv.swap v (Fin.last n)))),
  ∃ E : Circuit, FanInTwo E ∧
      E.size + readerCount v (C.gates.map normGate) ≤ C.size ∧
      ∀ y : Fin n → Bool, E.eval (List.ofFn y) =
        C.eval (List.ofFn (Fin.snoc y b ∘ Equiv.swap v (Fin.last n))) := @PEqualNP.Outside.L_meta_2373.fix_input_counted

#check @PEqualNP.Outside.L_meta_2373.fix_input_counted
#print axioms PEqualNP.Outside.L_meta_2373.fix_input_counted

example : ∀ (n q s : ℕ) (v : Fin (n + 1)) (b : Bool)
    (C : Circuit) (hC : FanInTwo C) (hsize : C.size ≤ s)
    (hnc : ∃ y y' : Fin n → Bool,
      C.eval (List.ofFn (Fin.snoc y b ∘ Equiv.swap v (Fin.last n))) ≠
        C.eval (List.ofFn (Fin.snoc y' b ∘ Equiv.swap v (Fin.last n))))
    (hlower : ∀ E : Circuit, FanInTwo E →
      (∀ y : Fin n → Bool, E.eval (List.ofFn y) =
        C.eval (List.ofFn (Fin.snoc y b ∘ Equiv.swap v (Fin.last n)))) → q ≤ E.size),
  q + readerCount v (C.gates.map normGate) ≤ s := @PEqualNP.Outside.L_meta_2373.input_readers_le_of_cofactor_lower

#check @PEqualNP.Outside.L_meta_2373.input_readers_le_of_cofactor_lower
#print axioms PEqualNP.Outside.L_meta_2373.input_readers_le_of_cofactor_lower

end PEqualNP.Outside.L_meta_2373

namespace PEqualNP.Outside.L_meta_2373.Graph2373

example : ∀ v : Fin 10, Function.Bijective (table v) ∧
    table v v = Fin.last 9 := @PEqualNP.Outside.L_meta_2373.Graph2373.table_properties

#check @PEqualNP.Outside.L_meta_2373.Graph2373.table_properties
#print axioms PEqualNP.Outside.L_meta_2373.Graph2373.table_properties

example : ∀ (v : Fin 10),
  symmetry v v = Fin.last 9 := @PEqualNP.Outside.L_meta_2373.Graph2373.symmetry_at

#check @PEqualNP.Outside.L_meta_2373.Graph2373.symmetry_at
#print axioms PEqualNP.Outside.L_meta_2373.Graph2373.symmetry_at

example : ∀ (v : Fin 10) (x : Fin 10 → Bool),
    f (x ∘ table v) = f x := @PEqualNP.Outside.L_meta_2373.Graph2373.table_invariant

#check @PEqualNP.Outside.L_meta_2373.Graph2373.table_invariant
#print axioms PEqualNP.Outside.L_meta_2373.Graph2373.table_invariant

example : ∀ (v : Fin 10) (x : Fin 10 → Bool),
  f (x ∘ symmetry v) = f x := @PEqualNP.Outside.L_meta_2373.Graph2373.symmetry_invariant

#check @PEqualNP.Outside.L_meta_2373.Graph2373.symmetry_invariant
#print axioms PEqualNP.Outside.L_meta_2373.Graph2373.symmetry_invariant

example : ∀ (v : Fin 10),
  fromZero v 0 = v := @PEqualNP.Outside.L_meta_2373.Graph2373.fromZero_at

#check @PEqualNP.Outside.L_meta_2373.Graph2373.fromZero_at
#print axioms PEqualNP.Outside.L_meta_2373.Graph2373.fromZero_at

example : ∀ (v : Fin 10) (x : Fin 10 → Bool),
  f (x ∘ fromZero v) = f x := @PEqualNP.Outside.L_meta_2373.Graph2373.fromZero_invariant

#check @PEqualNP.Outside.L_meta_2373.Graph2373.fromZero_invariant
#print axioms PEqualNP.Outside.L_meta_2373.Graph2373.fromZero_invariant

end PEqualNP.Outside.L_meta_2373.Graph2373

namespace PEqualNP.Outside.L_meta_2373.Cofactors

example : ∀ (C : Circuit) (h : FanInTwo C) (correct : ∀ x, C.eval (List.ofFn x) = fn3819 x),
  11 ≤ C.gates.countP (fun g => !isNot g) := @PEqualNP.Outside.L_meta_2373.Cofactors.bound3819_nonNot

#check @PEqualNP.Outside.L_meta_2373.Cofactors.bound3819_nonNot
#print axioms PEqualNP.Outside.L_meta_2373.Cofactors.bound3819_nonNot

example : ∀ (C : Circuit) (h : FanInTwo C)
   (correct : ∀ x, C.eval (List.ofFn x) = fn3819 x),
  11 ≤ C.size := @PEqualNP.Outside.L_meta_2373.Cofactors.bound3819

#check @PEqualNP.Outside.L_meta_2373.Cofactors.bound3819
#print axioms PEqualNP.Outside.L_meta_2373.Cofactors.bound3819

example : ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) 15 := @PEqualNP.Outside.L_meta_2373.Cofactors.zero_lower

#check @PEqualNP.Outside.L_meta_2373.Cofactors.zero_lower
#print axioms PEqualNP.Outside.L_meta_2373.Cofactors.zero_lower

end PEqualNP.Outside.L_meta_2373.Cofactors

namespace PEqualNP.Outside.L_meta_2373.Graph2373

example : ∀ (y : Fin 9 → Bool),
  f (Fin.snoc y false) = fzero y := @PEqualNP.Outside.L_meta_2373.Graph2373.last_zero

#check @PEqualNP.Outside.L_meta_2373.Graph2373.last_zero
#print axioms PEqualNP.Outside.L_meta_2373.Graph2373.last_zero

example : ∀ (C : Circuit)
    (correct : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = f x),
  ∃ y y' : Fin 9 → Bool,
      C.eval (List.ofFn (Fin.snoc y false)) ≠ C.eval (List.ofFn (Fin.snoc y' false)) := @PEqualNP.Outside.L_meta_2373.Graph2373.last_zero_nonconstant

#check @PEqualNP.Outside.L_meta_2373.Graph2373.last_zero_nonconstant
#print axioms PEqualNP.Outside.L_meta_2373.Graph2373.last_zero_nonconstant

example : ∀ (C : Circuit) (hC : FanInTwo C)
    (correct : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = fzero x),
  16 ≤ C.size := @PEqualNP.Outside.L_meta_2373.Graph2373.zero_lower_correct

#check @PEqualNP.Outside.L_meta_2373.Graph2373.zero_lower_correct
#print axioms PEqualNP.Outside.L_meta_2373.Graph2373.zero_lower_correct

example : ∀ (C : Circuit) (hC : FanInTwo C) (hsize : C.size ≤ 19)
    (correct : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = f x),
  readerCount 9 (C.gates.map normGate) ≤ 3 := @PEqualNP.Outside.L_meta_2373.Graph2373.last_reader_bound

#check @PEqualNP.Outside.L_meta_2373.Graph2373.last_reader_bound
#print axioms PEqualNP.Outside.L_meta_2373.Graph2373.last_reader_bound

example : ∀ (C : Circuit) (hC : FanInTwo C) (hsize : C.size ≤ 19)
    (correct : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = f x) (v : Fin 10),
  readerCount v (C.gates.map normGate) ≤ 3 := @PEqualNP.Outside.L_meta_2373.Graph2373.all_input_readers_bound

#check @PEqualNP.Outside.L_meta_2373.Graph2373.all_input_readers_bound
#print axioms PEqualNP.Outside.L_meta_2373.Graph2373.all_input_readers_bound

example : ∀ (C : Circuit) (hC : FanInTwo C) (hsize : C.size ≤ 19)
    (correct : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = f x)
    (pre post : List Gate) (g : Gate) (hgs : C.gates.map normGate = pre ++ g :: post)
    (hg : g.op = GateOp.and) (hread : 9 ∈ g.inputs)
    (hconsumer : ∃ h ∈ post, 10 + pre.length ∈ h.inputs ∧ 9 ∉ h.inputs),
  readerCount 9 (C.gates.map normGate) ≤ 2 := @PEqualNP.Outside.L_meta_2373.Graph2373.last_and_reader_bound

#check @PEqualNP.Outside.L_meta_2373.Graph2373.last_and_reader_bound
#print axioms PEqualNP.Outside.L_meta_2373.Graph2373.last_and_reader_bound

end PEqualNP.Outside.L_meta_2373.Graph2373

namespace PEqualNP.Outside.L_meta_2373.Residual

example : 
  ∀ r : Fin 1024,
   F r = true → Fminus r = false → ∃ i : Fin 9, rows i = r := @PEqualNP.Outside.L_meta_2373.Residual.exceptions

#check @PEqualNP.Outside.L_meta_2373.Residual.exceptions
#print axioms PEqualNP.Outside.L_meta_2373.Residual.exceptions

example : 
  ∀ fill : Fin 9 → Bool,
   admissible fill → fill ∈ masks.map bits := @PEqualNP.Outside.L_meta_2373.Residual.finite_classification

#check @PEqualNP.Outside.L_meta_2373.Residual.finite_classification
#print axioms PEqualNP.Outside.L_meta_2373.Residual.finite_classification

example : 
  masks.length = 47 := @PEqualNP.Outside.L_meta_2373.Residual.masks_length

#check @PEqualNP.Outside.L_meta_2373.Residual.masks_length
#print axioms PEqualNP.Outside.L_meta_2373.Residual.masks_length

example : 
  masks.Nodup := @PEqualNP.Outside.L_meta_2373.Residual.masks_nodup

#check @PEqualNP.Outside.L_meta_2373.Residual.masks_nodup
#print axioms PEqualNP.Outside.L_meta_2373.Residual.masks_nodup

example : ∀ (H : Fin 1024 → Bool)
   (hmono : ∀ r s, rowLE r s → H r = true → H s = true)
   (hlower : ∀ r, Fminus r = true → H r = true)
   (hupper : ∀ r, H r = true → F r = true)
   (hzero : H 3 = false),
  ∃ m ∈ masks, H = target m := @PEqualNP.Outside.L_meta_2373.Residual.classification

#check @PEqualNP.Outside.L_meta_2373.Residual.classification
#print axioms PEqualNP.Outside.L_meta_2373.Residual.classification

end PEqualNP.Outside.L_meta_2373.Residual
