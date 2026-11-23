import Mathlib
import PEqualNP.Defs

namespace CircuitCertificate

open PEqualNP.MetaComplexity

abbrev Record := ℕ × Bool
abbrev GateValues := Bool × Bool × Bool

def sameValue (a b : Record) : Prop := a.1 = b.1 → a.2 = b.2

def ordered (a b : Record) : Prop := a.1 ≤ b.1 ∧ sameValue a b

def agrees (rows : List Record) : Prop :=
  ∀ a ∈ rows, ∀ b ∈ rows, sameValue a b

lemma ordered_trans (a b c : Record) : ordered a b → ordered b c → ordered a c := by
  intro hab hbc
  refine ⟨hab.1.trans hbc.1, ?_⟩
  intro hac
  have habkey : a.1 = b.1 := Nat.le_antisymm hab.1 (by simpa [hac] using hbc.1)
  have hbckey : b.1 = c.1 := habkey.symm.trans hac
  exact (hab.2 habkey).trans (hbc.2 hbckey)

lemma pairwise_agrees (rows : List Record) (h : rows.Pairwise sameValue) : agrees rows := by
  induction rows with
  | nil => simp [agrees]
  | cons a rows ih =>
    rw [List.pairwise_cons] at h
    intro x hx y hy hxy
    rcases List.mem_cons.mp hx with hxa | hxt
    · subst x
      rcases List.mem_cons.mp hy with hya | hyt
      · subst y; rfl
      · exact h.1 y hyt hxy
    · rcases List.mem_cons.mp hy with hya | hyt
      · subst y
        exact (h.1 x hxt hxy.symm).symm
      · exact ih h.2 x hxt y hyt hxy

lemma adjacent_scan_sound (rows : List Record) (h : rows.IsChain ordered) : agrees rows := by
  let : IsTrans Record ordered := ⟨ordered_trans⟩
  have hp : rows.Pairwise ordered := List.isChain_iff_pairwise.mp h
  exact pairwise_agrees rows (hp.imp fun h => h.2)

lemma agrees_perm (a b : List Record) (h : a.Perm b) : agrees a ↔ agrees b := by
  constructor
  · intro ha x hx y hy
    exact ha x (h.mem_iff.mpr hx) y (h.mem_iff.mpr hy)
  · intro hb x hx y hy
    exact hb x (h.mem_iff.mp hx) y (h.mem_iff.mp hy)

lemma agrees_sublist (rows sub : List Record) (h : agrees rows)
    (hs : ∀ r ∈ sub, r ∈ rows) : agrees sub := by
  intro a ha b hb
  exact h a (hs a ha) b (hs b hb)

def sources (values : List Bool) : List Record :=
  (List.range values.length).map (fun i => (i, values.getD i false)) ++ [(values.length, false)]

def key (total available index : ℕ) : ℕ := if index < available then index else total

def read (values : List Bool) (available index : ℕ) : Bool :=
  if index < available then values.getD index false else false

lemma source_read (values : List Bool) (available index : ℕ) (h : available ≤ values.length) :
    (key values.length available index, read values available index) ∈ sources values := by
  by_cases hi : index < available
  · simp only [key, read, ite_eq_left hi, sources, List.mem_append]
    left
    apply List.mem_map.mpr
    exact ⟨index, List.mem_range.mpr (hi.trans_le h), rfl⟩
  · simp [key, read, hi, sources]

lemma read_prefix (input tail : List Bool) (index : ℕ) :
    read (input ++ tail) input.length index = input.getD index false := by
  by_cases hi : index < input.length
  · simp only [read, ite_eq_left hi]
    exact List.getD_append input tail false index hi
  · simp [read, hi]

def references (total available : ℕ) : List BinaryGate → List GateValues → List Record
  | g :: gs, v :: vs =>
      (key total available g.left, v.1) ::
      (key total available g.right, v.2.1) :: references total (available + 1) gs vs
  | _, _ => []

def outputs (cert : List GateValues) : List Bool := cert.map fun v => v.2.2

def gateRules : List BinaryGate → List GateValues → Prop
  | [], [] => True
  | g :: gs, v :: vs => v.2.2 = g.op v.1 v.2.1 ∧ gateRules gs vs
  | _, _ => False

lemma gateRules_length (gates : List BinaryGate) (cert : List GateValues)
    (h : gateRules gates cert) : gates.length = cert.length := by
  induction gates generalizing cert with
  | nil => cases cert <;> simp_all [gateRules]
  | cons g gs ih =>
    cases cert with
    | nil => simp [gateRules] at h
    | cons v vs => exact congrArg (· + 1) (ih vs h.2)

lemma references_length (gates : List BinaryGate) (cert : List GateValues)
    (total available : ℕ) (h : gates.length = cert.length) :
    (references total available gates cert).length = 2 * gates.length := by
  induction gates generalizing cert available with
  | nil => cases cert <;> simp_all [references]
  | cons g gs ih =>
    cases cert with
    | nil => simp at h
    | cons v vs => simp only [List.length_cons, Nat.add_right_cancel_iff] at h
                   simp [references, ih vs (available + 1) h]
                   omega

def run (gates : List BinaryGate) (input : List Bool) : List Bool :=
  gates.foldl (fun w g => w ++ [g.op (w.getD g.left false) (w.getD g.right false)]) input

lemma reference_value (all : List Bool) (available index : ℕ) (claimed : Bool)
    (rows : List Record) (hbound : available ≤ all.length)
    (h : agrees (sources all ++ rows))
    (hm : (key all.length available index, claimed) ∈ rows) :
    claimed = read all available index := by
  exact h _ (List.mem_append.mpr (Or.inr hm)) _
    (List.mem_append.mpr (Or.inl (source_read all available index hbound))) rfl

lemma run_sound (gates : List BinaryGate) (cert : List GateValues) (input : List Bool)
    (hg : gateRules gates cert)
    (h : agrees (sources (input ++ outputs cert) ++
      references (input ++ outputs cert).length input.length gates cert)) :
    run gates input = input ++ outputs cert := by
  induction gates generalizing cert input with
  | nil =>
    cases cert with
    | nil => simp [run, outputs]
    | cons v vs => simp [gateRules] at hg
  | cons g gs ih =>
    cases cert with
    | nil => simp [gateRules] at hg
    | cons v vs =>
      obtain ⟨hv, hgs⟩ := hg
      have hleft := reference_value (input ++ outputs (v :: vs)) input.length g.left v.1
        (references (input ++ outputs (v :: vs)).length input.length (g :: gs) (v :: vs))
        (by simp) h (by simp [references])
      have hright := reference_value (input ++ outputs (v :: vs)) input.length g.right v.2.1
        (references (input ++ outputs (v :: vs)).length input.length (g :: gs) (v :: vs))
        (by simp) h (by simp [references])
      rw [read_prefix] at hleft hright
      have heval : g.op (input.getD g.left false) (input.getD g.right false) = v.2.2 := by
        rw [← hleft, ← hright, hv]
      have htail : agrees (sources ((input ++ [v.2.2]) ++ outputs vs) ++
          references ((input ++ [v.2.2]) ++ outputs vs).length (input ++ [v.2.2]).length gs vs) := by
        apply agrees_sublist _ _ h
        intro r hr
        simp only [outputs, List.map_cons, List.append_assoc, List.singleton_append,
          List.length_append, List.length_singleton] at hr ⊢
        simp only [references, List.mem_append, List.mem_cons] at hr ⊢
        rcases hr with hr | hr
        · exact Or.inl hr
        · exact Or.inr (Or.inr (Or.inr hr))
      change run gs (input ++ [g.op (input.getD g.left false) (input.getD g.right false)]) = _
      rw [heval, ih vs (input ++ [v.2.2]) hgs htail]
      simp [outputs, List.append_assoc]

def records (C : BinaryCircuit) (input : List Bool) (cert : List GateValues) (answer : Bool) :
    List Record :=
  let all := input ++ outputs cert
  sources all ++ references all.length input.length C.gates cert ++
    [(key all.length all.length C.output, answer)]

lemma sorted_certificate_sound (C : BinaryCircuit) (input : List Bool)
    (cert : List GateValues) (answer : Bool) (sorted : List Record)
    (hg : gateRules C.gates cert) (hp : (records C input cert answer).Perm sorted)
    (hs : sorted.IsChain ordered) : answer = C.eval input := by
  have h := (agrees_perm _ _ hp).mpr (adjacent_scan_sound sorted hs)
  have hr : agrees (sources (input ++ outputs cert) ++
      references (input ++ outputs cert).length input.length C.gates cert) := by
    apply agrees_sublist _ _ h
    intro r hr
    exact List.mem_append.mpr (Or.inl hr)
  have heval := run_sound C.gates cert input hg hr
  have hout : answer = read (input ++ outputs cert) (input ++ outputs cert).length C.output := by
    apply reference_value _ _ _ answer
      (references (input ++ outputs cert).length input.length C.gates cert ++
        [(key (input ++ outputs cert).length (input ++ outputs cert).length C.output, answer)])
      (le_refl _) ?_ (by simp)
    simpa [records, List.append_assoc] using h
  have hread : read (input ++ outputs cert) (input ++ outputs cert).length C.output =
      (input ++ outputs cert).getD C.output false := by
    simpa using read_prefix (input ++ outputs cert) [] C.output
  rw [hread] at hout
  change answer = (run C.gates input).getD C.output false
  rw [heval]
  exact hout

lemma record_count (C : BinaryCircuit) (input : List Bool) (cert : List GateValues) (answer : Bool)
    (hg : gateRules C.gates cert) :
    (records C input cert answer).length = input.length + 3 * C.size + 2 := by
  have hlen := gateRules_length C.gates cert hg
  simp [records, sources, outputs, references_length C.gates cert _ _ hlen,
    BinaryCircuit.size]
  omega

def computedCert : List BinaryGate → List Bool → List GateValues
  | [], _ => []
  | g :: gs, input =>
      let left := input.getD g.left false
      let right := input.getD g.right false
      let value := g.op left right
      (left, right, value) :: computedCert gs (input ++ [value])

lemma computed_rules (gates : List BinaryGate) (input : List Bool) :
    gateRules gates (computedCert gates input) := by
  induction gates generalizing input with
  | nil => trivial
  | cons g gs ih => exact ⟨rfl, ih _⟩

lemma computed_wires (gates : List BinaryGate) (input : List Bool) :
    run gates input = input ++ outputs (computedCert gates input) := by
  induction gates generalizing input with
  | nil => simp [run, outputs, computedCert]
  | cons g gs ih =>
    change run gs (input ++ [g.op (input.getD g.left false) (input.getD g.right false)]) = _
    rw [ih]
    simp [computedCert, outputs, List.append_assoc]

lemma read_key (all : List Bool) (available index : ℕ) :
    read all available index = all.getD (key all.length available index) false := by
  by_cases h : index < available <;> simp [read, key, h]

lemma computed_references (gates : List BinaryGate) (input : List Bool) :
    ∀ r ∈ references (run gates input).length input.length gates (computedCert gates input),
      r.2 = (run gates input).getD r.1 false := by
  induction gates generalizing input with
  | nil => simp [references]
  | cons g gs ih =>
    intro r hr
    simp only [computedCert, references, List.mem_cons] at hr
    rcases hr with rfl | rfl | hr
    · change input.getD g.left false =
        (run (g :: gs) input).getD (key (run (g :: gs) input).length input.length g.left) false
      rw [computed_wires]
      exact (read_prefix input _ g.left).symm.trans (read_key _ _ _)
    · change input.getD g.right false =
        (run (g :: gs) input).getD (key (run (g :: gs) input).length input.length g.right) false
      rw [computed_wires]
      exact (read_prefix input _ g.right).symm.trans (read_key _ _ _)
    · apply ih (input ++ [g.op (input.getD g.left false) (input.getD g.right false)]) r
      simpa [run] using hr

lemma source_value (all : List Bool) : ∀ r ∈ sources all, r.2 = all.getD r.1 false := by
  intro r hr
  rcases List.mem_append.mp hr with h | h
  · obtain ⟨i, _, rfl⟩ := List.mem_map.mp h
    rfl
  · obtain rfl := List.mem_singleton.mp h
    simp

lemma computed_records_agree (C : BinaryCircuit) (input : List Bool) :
    agrees (records C input (computedCert C.gates input) (C.eval input)) := by
  have hv : ∀ r ∈ records C input (computedCert C.gates input) (C.eval input),
      r.2 = (run C.gates input).getD r.1 false := by
    intro r hr
    simp only [records, ← computed_wires] at hr
    rcases List.mem_append.mp hr with hr | hr
    · rcases List.mem_append.mp hr with hr | hr
      · exact source_value _ r hr
      · exact computed_references _ _ r hr
    · obtain rfl := List.mem_singleton.mp hr
      change (run C.gates input).getD C.output false =
        (run C.gates input).getD (key (run C.gates input).length (run C.gates input).length C.output)
          false
      have hread : read (run C.gates input) (run C.gates input).length C.output =
          (run C.gates input).getD C.output false := by
        simpa using read_prefix (run C.gates input) [] C.output
      exact hread.symm.trans (read_key _ _ _)
  intro a ha b hb he
  exact (hv a ha).trans (by rw [he]; exact (hv b hb).symm)

lemma ordered_of_key_order (rows : List Record)
    (hkeys : rows.Pairwise (fun a b => a.1 ≤ b.1)) (ha : agrees rows) :
    rows.Pairwise ordered := by
  induction rows with
  | nil => exact List.Pairwise.nil
  | cons a rows ih =>
    rw [List.pairwise_cons] at hkeys ⊢
    refine ⟨?_, ih hkeys.2 ?_⟩
    · intro b hb
      exact ⟨hkeys.1 b hb, ha a (by simp) b (by simp [hb])⟩
    · apply agrees_sublist _ _ ha
      intro b hb
      simp [hb]

def sortRecords (rows : List Record) : List Record :=
  rows.mergeSort (fun a b => a.1 ≤ b.1)

lemma sortRecords_perm (rows : List Record) : rows.Perm (sortRecords rows) :=
  (List.mergeSort_perm _ _).symm

lemma sorted_certificate_complete (C : BinaryCircuit) (input : List Bool) :
    ∃ cert sorted, gateRules C.gates cert ∧
      (records C input cert (C.eval input)).Perm sorted ∧ sorted.IsChain ordered := by
  let cert := computedCert C.gates input
  let rows := records C input cert (C.eval input)
  refine ⟨cert, sortRecords rows, computed_rules _ _, sortRecords_perm _, ?_⟩
  let : IsTrans Record ordered := ⟨ordered_trans⟩
  apply List.isChain_iff_pairwise.mpr
  apply ordered_of_key_order
  · let : IsTrans Record (fun a b => a.1 ≤ b.1) := ⟨fun _ _ _ => Nat.le_trans⟩
    let : Std.Total (fun a b : Record => a.1 ≤ b.1) := ⟨fun _ _ => Nat.le_total _ _⟩
    exact List.pairwise_mergeSort' _ rows
  · exact (agrees_perm _ _ (sortRecords_perm rows)).mp (computed_records_agree C input)

lemma sorted_certificate_iff (C : BinaryCircuit) (input : List Bool) (answer : Bool) :
    (∃ cert sorted, gateRules C.gates cert ∧
      (records C input cert answer).Perm sorted ∧ sorted.IsChain ordered) ↔ answer = C.eval input := by
  constructor
  · rintro ⟨cert, sorted, hg, hp, hs⟩
    exact sorted_certificate_sound C input cert answer sorted hg hp hs
  · rintro rfl
    exact sorted_certificate_complete C input

lemma key_le (total available index : ℕ) (h : available ≤ total) :
    key total available index ≤ total := by
  by_cases hi : index < available
  · simpa [key, hi] using hi.le.trans h
  · simp [key, hi]

lemma references_bound (gates : List BinaryGate) (cert : List GateValues)
    (total available : ℕ) (h : available + gates.length ≤ total) :
    ∀ r ∈ references total available gates cert, r.1 ≤ total := by
  induction gates generalizing cert available with
  | nil => simp [references]
  | cons g gs ih =>
    cases cert with
    | nil => simp [references]
    | cons v vs =>
      intro r hr
      simp only [references, List.mem_cons] at hr
      rcases hr with rfl | rfl | hr
      · exact key_le _ _ _ (by simpa using (Nat.le_add_right available (g :: gs).length).trans h)
      · exact key_le _ _ _ (by simpa using (Nat.le_add_right available (g :: gs).length).trans h)
      · exact ih vs (available + 1) (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h) r hr

lemma sources_bound (all : List Bool) : ∀ r ∈ sources all, r.1 ≤ all.length := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
    exact (List.mem_range.mp hi).le
  · obtain rfl := List.mem_singleton.mp hr
    rfl

lemma records_bound (C : BinaryCircuit) (input : List Bool) (cert : List GateValues) (answer : Bool)
    (hg : gateRules C.gates cert) :
    ∀ r ∈ records C input cert answer, r.1 ≤ input.length + C.size := by
  have hlen := gateRules_length C.gates cert hg
  have htotal : (input ++ outputs cert).length = input.length + C.size := by
    simp [outputs, BinaryCircuit.size, hlen]
  intro r hr
  simp only [records, List.mem_append, List.mem_singleton] at hr
  rcases hr with (hr | hr) | rfl
  · rw [← htotal]
    exact sources_bound _ r hr
  · rw [← htotal]
    exact references_bound C.gates cert _ input.length (by simp [outputs, hlen]) r hr
  · exact (key_le _ _ _ (le_refl _)).trans_eq htotal

end CircuitCertificate
