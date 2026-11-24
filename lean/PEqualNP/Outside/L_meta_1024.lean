import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1024_aux

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl step (List.ofFn x)).getD i false

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_cons]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma val_nil {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    val [] x i = if h : i < n then x ⟨i, h⟩ else false := by
  unfold val
  by_cases h : i < n <;> simp [List.getD_eq_getElem?_getD, h]

lemma val_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (i : ℕ) :
    val (gs ++ [g]) x i =
      if i = n + gs.length then g.op.eval (g.inputs.map fun j => val gs x j)
      else val gs x i := by
  unfold val
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, step]
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rcases lt_trichotomy i (n + gs.length) with h | h | h
  · rw [ite_eq_right (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  · rw [ite_eq_left h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hl, h]
  · rw [ite_eq_right (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

lemma val_input {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : Fin n) :
    val gs x i.val = x i := by
  induction gs using List.reverseRecOn with
  | nil => simp [val_nil, i.isLt]
  | append_singleton gs g ih =>
    rw [val_snoc, ite_eq_right (by omega)]
    exact ih

lemma val_beyond {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ)
    (hi : n + gs.length ≤ i) : val gs x i = false := by
  unfold val
  rw [List.getD_eq_default]
  simpa [fold_length] using hi

def line (w : Fin 13) : Finset (Fin 13) :=
  ({0, 1, 3, 9} : Finset (Fin 13)).image (fun u => u + w)

def target (w : Fin 13) (x : Fin 13 → Bool) : Bool :=
  decide (∃ p ∈ line w, x p = true)

def row (r : Fin 13) (p : Fin 13) : Bool :=
  decide (p ∉ (({0, 1, 2, 3, 4, 9} : Finset (Fin 13)).image (fun u => u + r)))

lemma row_band : ∀ r : Fin 13,
    (Finset.univ.filter (fun p => row r p = false)).card = 6 := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma row_target : ∀ w r : Fin 13, target w (row r) = decide (w ≠ r) := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma row_separates_input : ∀ w p : Fin 13,
    ∃ r : Fin 13, row r p ≠ decide (w ≠ r) := by
  decide +kernel

lemma row_positive : ∀ w : Fin 13, ∃ r : Fin 13, decide (w ≠ r) = true := by
  decide +kernel

lemma thirteen_gates (gs : List Gate) (out : Fin 13 → ℕ)
    (hcorrect : ∀ (w : Fin 13) (x : Fin 13 → Bool),
      ((Finset.univ.filter (fun p : Fin 13 => x p = false)).card = 5 ∨
        (Finset.univ.filter (fun p : Fin 13 => x p = false)).card = 6) →
      Circuit.eval ⟨gs, out w⟩ (List.ofFn x) = target w x) :
    13 ≤ gs.length := by
  have spec (w r : Fin 13) : val gs (row r) (out w) = decide (w ≠ r) := by
    exact (hcorrect w (row r) (Or.inr (row_band r))).trans (row_target w r)
  have lower (w : Fin 13) : 13 ≤ out w := by
    by_contra! h
    obtain ⟨r, hr⟩ := row_separates_input w ⟨out w, h⟩
    have hv := spec w r
    rw [val_input gs (row r) ⟨out w, h⟩] at hv
    exact hr hv
  have upper (w : Fin 13) : out w < 13 + gs.length := by
    by_contra! h
    obtain ⟨r, hr⟩ := row_positive w
    have hv := spec w r
    rw [val_beyond gs (row r) (out w) h, hr] at hv
    contradiction
  have inj : Function.Injective out := by
    intro w v hv
    by_contra h
    have hw := spec w w
    have hval := spec v w
    rw [← hv] at hval
    rw [hw] at hval
    simpa [Ne.symm h] using hval
  let f : Fin 13 → Fin gs.length := fun w => ⟨out w - 13, by
    have := lower w
    have := upper w
    omega⟩
  have hf : Function.Injective f := by
    intro w v hv
    apply inj
    have hh := congrArg Fin.val hv
    change out w - 13 = out v - 13 at hh
    have := lower w
    have := lower v
    omega
  have hc := Fintype.card_le_of_injective f hf
  simpa using hc

end PEqualNP.Outside.L_meta_1024_aux


open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1024.OrOnly

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

lemma gate_mono {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or)
    (x y : Fin n → Bool)
    (h : ∀ r ∈ C.gates[k].inputs, r < n + k → value C x r = true → value C y r = true) :
    value C x (n + k) = true → value C y (n + k) = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  have hy := gate_value C y (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx hy
  rw [hx, hy]
  have hr (r : ℕ) (hm : r ∈ C.gates[k].inputs) :
      (if r < n + k then value C x r else false) = true →
      (if r < n + k then value C y r else false) = true := by
    by_cases h' : r < n + k
    · simpa [h'] using h r hm h'
    · simp [h']
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_eq_true, id_eq]
    intro hx b hb
    obtain ⟨r, hm, rfl⟩ := List.mem_map.mp hb
    exact hr r hm (hx _ (List.mem_map.mpr ⟨r, hm, rfl⟩))
  · simp only [hop, GateOp.eval, List.any_eq_true, id_eq]
    intro hx
    obtain ⟨b, hb, rfl⟩ := hx
    obtain ⟨r, hm, hv⟩ := List.mem_map.mp hb
    exact ⟨_, List.mem_map.mpr ⟨r, hm, rfl⟩, hr r hm hv⟩

lemma or_value {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.or) (x : Fin n → Bool) :
    value C x (n + k) = true ↔ ∃ r ∈ C.gates[k].inputs, r < n + k ∧ value C x r = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx
  rw [hx, hop]
  simp [GateOp.eval]

lemma and_value {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and) (x : Fin n → Bool) :
    value C x (n + k) = true ↔ ∀ r ∈ C.gates[k].inputs, r < n + k ∧ value C x r = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx
  rw [hx, hop]
  simp [GateOp.eval]

lemma mono {n : ℕ} (C : Circuit)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin n → Bool) (h : ∀ v, x v = true → y v = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using h p
    by_cases hw : w < n + C.gates.length
    · have hk : w - n < C.gates.length := by omega
      have hwk : w = n + (w - n) := by omega
      rw [hwk]
      exact gate_mono C (w - n) hk (hC _ (List.getElem_mem hk)).1 x y fun r _ hlt => ih r (by omega)
    · simp [missing_value C x w (by unfold Circuit.size; omega)]

def Sv {n : ℕ} {ι : Type*} (C : Circuit) (l : ι → Fin n → Bool) (y : Fin n → Bool)
    (p : ι) (w : ℕ) : Prop :=
  value C (l p) w = true ∧ value C y w = false

def Multi {n : ℕ} {ι : Type*} (C : Circuit) (T : Finset ι) (l : ι → Fin n → Bool)
    (y : Fin n → Bool) (w : ℕ) : Prop :=
  ∃ p ∈ T, ∃ p' ∈ T, p ≠ p' ∧ Sv C l y p w ∧ Sv C l y p' w

lemma list_cases (L : List ℕ) (hL : L.length ≤ 2) (Q : ℕ → Prop) :
    (L.length = 2 ∧ ∀ r ∈ L, Q r) ∨ ∃ c, ∀ r ∈ L, Q r → r = c := by
  rcases L with _ | ⟨a, _ | ⟨b, _ | ⟨c, tl⟩⟩⟩
  · exact Or.inr ⟨0, fun r hr => absurd hr (by simp)⟩
  · exact Or.inr ⟨a, fun r hr _ => by simpa using hr⟩
  · by_cases ha : Q a
    · by_cases hb : Q b
      · refine Or.inl ⟨rfl, fun r hr => ?_⟩
        rcases List.mem_pair.mp hr with rfl | rfl
        · exact ha
        · exact hb
      · refine Or.inr ⟨a, fun r hr hq => ?_⟩
        rcases List.mem_pair.mp hr with rfl | rfl
        · rfl
        · exact absurd hq hb
    · refine Or.inr ⟨b, fun r hr hq => ?_⟩
      rcases List.mem_pair.mp hr with rfl | rfl
      · exact absurd hq ha
      · rfl
  · simp at hL

lemma step_cases {n : ℕ} {ι : Type*} (C : Circuit) (T : Finset ι) (l : ι → Fin n → Bool)
    (y : Fin n → Bool)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (k : ℕ) (hk : k < C.gates.length) (hm : Multi C T l y (n + k)) :
    (∃ r ∈ C.gates[k].inputs, r < n + k ∧ ∀ p ∈ T, Sv C l y p (n + k) → Sv C l y p r) ∨
    (C.gates[k].op = GateOp.or ∧ C.gates[k].inputs.length = 2 ∧
      (∀ r ∈ C.gates[k].inputs, ∃ p ∈ T, value C (l p) r = true) ∧
      ∀ p ∈ T, Sv C l y p (n + k) → ∃ r ∈ C.gates[k].inputs, r < n + k ∧ Sv C l y p r) := by
  obtain ⟨p0, hp0, _, _, _, hs0, _⟩ := hm
  rcases (hC _ (List.getElem_mem hk)).1 with hop | hop
  · left
    have hy := hs0.2
    by_contra hcon
    have hall : ∀ r ∈ C.gates[k].inputs, r < n + k ∧ value C y r = true := by
      intro r hr
      by_contra hr2
      apply hcon
      have hlt := ((and_value C k hk hop (l p0)).mp hs0.1 r hr).1
      refine ⟨r, hr, hlt, fun p _ hsp => ⟨((and_value C k hk hop (l p)).mp hsp.1 r hr).2, ?_⟩⟩
      by_contra hne
      exact hr2 ⟨hlt, by simpa using hne⟩
    rw [(and_value C k hk hop y).mpr hall] at hy
    exact Bool.noConfusion hy
  · have hyall : ∀ r ∈ C.gates[k].inputs, r < n + k → value C y r = false := by
      intro r hr hlt
      by_contra h
      have h2 : value C y (n + k) = true :=
        (or_value C k hk hop y).mpr ⟨r, hr, hlt, by simpa using h⟩
      rw [hs0.2] at h2
      exact Bool.noConfusion h2
    have hsv : ∀ p ∈ T, Sv C l y p (n + k) →
        ∃ r ∈ C.gates[k].inputs, r < n + k ∧ value C (l p) r = true ∧ Sv C l y p r := by
      intro p _ hsp
      obtain ⟨r, hr, hlt, hv⟩ := (or_value C k hk hop (l p)).mp hsp.1
      exact ⟨r, hr, hlt, hv, hv, hyall r hr hlt⟩
    rcases list_cases C.gates[k].inputs (hC _ (List.getElem_mem hk)).2
      (fun r => ∃ p ∈ T, r < n + k ∧ value C (l p) r = true) with ⟨hlen, hQ⟩ | ⟨c, hc⟩
    · right
      refine ⟨hop, hlen, fun r hr => ?_, fun p hp hsp => ?_⟩
      · obtain ⟨p, hp, _, hv⟩ := hQ r hr
        exact ⟨p, hp, hv⟩
      · obtain ⟨r, hr, hlt, _, hs⟩ := hsv p hp hsp
        exact ⟨r, hr, hlt, hs⟩
    · left
      obtain ⟨r, hr, hlt, hv, _⟩ := hsv p0 hp0 hs0
      have hrc := hc r hr ⟨p0, hp0, hlt, hv⟩
      refine ⟨r, hr, hlt, fun p hp hsp => ?_⟩
      obtain ⟨r', hr', hlt', hv', hs'⟩ := hsv p hp hsp
      have hrc' := hc r' hr' ⟨p, hp, hlt', hv'⟩
      rw [hrc, ← hrc']
      exact hs'

lemma frontier {n : ℕ} {ι : Type*} (C : Circuit) (T : Finset ι) (l : ι → Fin n → Bool)
    (y : Fin n → Bool)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (W : Finset ℕ)
    (hW : ∀ k, ∀ hk : k < C.gates.length, Multi C T l y (n + k) →
      C.gates[k].op = GateOp.or → C.gates[k].inputs.length = 2 →
      (∀ r ∈ C.gates[k].inputs, ∃ p ∈ T, value C (l p) r = true) → n + k ∈ W)
    (hlen : ∀ w, Multi C T l y w → n ≤ w ∧ w < n + C.gates.length)
    (t : ℕ) (F : Finset ℕ) (hF : ∀ w ∈ F, Multi C T l y w → w < t)
    (T' : Finset ι) (hT' : T' ⊆ T) (hs : ∀ p ∈ T', ∃ w ∈ F, Sv C l y p w) :
    T'.card ≤ F.card + (W.filter (· < t)).card := by
  classical
  induction t generalizing F with
  | zero =>
    choose! f hfF hfs using hs
    have hinj : Set.InjOn f T' := by
      intro p hp p' hp' e
      by_contra hne
      have hc : Multi C T l y (f p) :=
        ⟨p, hT' hp, p', hT' hp', hne, hfs p hp, by rw [e]; exact hfs p' hp'⟩
      have := hF (f p) (hfF p hp) hc
      omega
    have := Finset.card_le_card_of_injOn f (fun p hp => hfF p hp) hinj
    omega
  | succ t ih =>
    have hle : (W.filter (· < t)).card ≤ (W.filter (· < t + 1)).card :=
      Finset.card_le_card fun w hw =>
        Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).1,
          by have := (Finset.mem_filter.mp hw).2; omega⟩
    by_cases hex : t ∈ F ∧ Multi C T l y t
    · obtain ⟨h1, h2⟩ := hlen t hex.2
      have hk : t - n < C.gates.length := by omega
      have htk : t = n + (t - n) := by omega
      have hm : Multi C T l y (n + (t - n)) := by rw [← htk]; exact hex.2
      have he := Finset.card_erase_add_one hex.1
      rcases step_cases C T l y hC (t - n) hk hm with ⟨r, hr, hlt, hall⟩ | ⟨hop, hlen2, hQ, hsv⟩
      · rw [← htk] at hlt hall
        let F' := insert r (F.erase t)
        have hF' : ∀ w ∈ F', Multi C T l y w → w < t := by
          intro w hw hg
          rcases Finset.mem_insert.mp hw with hw | hw
          · rw [hw]; exact hlt
          · have hne := (Finset.mem_erase.mp hw).1
            have hlt := hF w (Finset.mem_erase.mp hw).2 hg
            omega
        have hs' : ∀ p ∈ T', ∃ w ∈ F', Sv C l y p w := by
          intro p hp
          obtain ⟨w, hw, hsv⟩ := hs p hp
          by_cases h : w = t
          · subst h
            exact ⟨r, Finset.mem_insert_self _ _, hall p (hT' hp) hsv⟩
          · exact ⟨w, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨h, hw⟩), hsv⟩
        have hi := ih F' hF' hs'
        have hu := Finset.card_insert_le r (F.erase t)
        change F'.card ≤ _ at hu
        omega
      · rw [← htk] at hsv
        have htW : t ∈ W := by
          have := hW (t - n) hk hm hop hlen2 hQ
          rwa [← htk] at this
        let P : Finset ℕ := (C.gates[t - n].inputs.filter (· < t)).toFinset
        have hPcard : P.card ≤ 2 := by
          have h1 := List.toFinset_card_le (C.gates[t - n].inputs.filter (· < t))
          have h2 := List.length_filter_le (fun r => decide (r < t)) C.gates[t - n].inputs
          change P.card ≤ _ at h1
          omega
        let F' := F.erase t ∪ P
        have hF' : ∀ w ∈ F', Multi C T l y w → w < t := by
          intro w hw hg
          rcases Finset.mem_union.mp hw with hw | hw
          · have hne := (Finset.mem_erase.mp hw).1
            have hlt := hF w (Finset.mem_erase.mp hw).2 hg
            omega
          · have := (List.mem_filter.mp (List.mem_toFinset.mp hw)).2
            simpa using this
        have hs' : ∀ p ∈ T', ∃ w ∈ F', Sv C l y p w := by
          intro p hp
          obtain ⟨w, hw, hsvp⟩ := hs p hp
          by_cases h : w = t
          · subst h
            obtain ⟨r, hr, hlt, hsr⟩ := hsv p (hT' hp) hsvp
            exact ⟨r, Finset.mem_union_right _ (List.mem_toFinset.mpr
              (List.mem_filter.mpr ⟨hr, by simpa using hlt⟩)), hsr⟩
          · exact ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h, hw⟩), hsvp⟩
        have hi := ih F' hF' hs'
        have hu := Finset.card_union_le (F.erase t) P
        change F'.card ≤ _ at hu
        have hfilter : W.filter (· < t + 1) = insert t (W.filter (· < t)) := by
          ext w
          simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨hg, hlt⟩
            by_cases h : w = t
            · exact Or.inl h
            · exact Or.inr ⟨hg, by omega⟩
          · rintro (rfl | ⟨hg, hlt⟩)
            · exact ⟨htW, by omega⟩
            · exact ⟨hg, by omega⟩
        rw [hfilter, Finset.card_insert_of_notMem (by simp)]
        omega
    · have hF' : ∀ w ∈ F, Multi C T l y w → w < t := by
        intro w hw hg
        have hne : w ≠ t := fun e => hex ⟨e ▸ hw, e ▸ hg⟩
        have hlt := hF w hw hg
        omega
      have := ih F hF' hs
      omega

lemma family {n : ℕ} {ι : Type*} (gates : List Gate)
    (hC : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (T : Finset ι) (l : ι → Fin n → Bool) (y : Fin n → Bool) (o : ℕ)
    (ho : ∀ p ∈ T, Sv ⟨gates, 0⟩ l y p o)
    (hin : ∀ w, w < n → ¬ Multi ⟨gates, 0⟩ T l y w)
    (K : Finset (Fin gates.length))
    (hK : ∀ g : Fin gates.length, Multi ⟨gates, 0⟩ T l y (n + (g : ℕ)) →
      gates[(g : ℕ)].op = GateOp.or → gates[(g : ℕ)].inputs.length = 2 →
      (∀ r ∈ gates[(g : ℕ)].inputs, ∃ p ∈ T, value ⟨gates, 0⟩ (l p) r = true) → g ∈ K) :
    T.card ≤ K.card + 1 := by
  classical
  let C : Circuit := ⟨gates, 0⟩
  let W : Finset ℕ := Finset.image (fun g : Fin gates.length => n + (g : ℕ)) K
  have hlen : ∀ w, Multi C T l y w → n ≤ w ∧ w < n + C.gates.length := by
    intro w hc
    refine ⟨Nat.le_of_not_lt fun h => hin w h hc, ?_⟩
    by_contra hge
    obtain ⟨p, _, _, _, _, hsv, _⟩ := hc
    have hm := missing_value C (l p) w (by unfold Circuit.size; omega)
    have h1 := hsv.1
    rw [hm] at h1
    exact Bool.noConfusion h1
  have h := frontier C T l y hC W
    (fun k hk hm hop hl hQ => Finset.mem_image.mpr ⟨(⟨k, hk⟩ : Fin gates.length), hK ⟨k, hk⟩ hm hop hl hQ, rfl⟩)
    hlen (n + C.gates.length) {o}
    (fun w _ hc => (hlen w hc).2) T (Finset.Subset.refl T)
    (fun p hp => ⟨o, Finset.mem_singleton_self o, ho p hp⟩)
  have h1 := Finset.card_filter_le W (· < n + C.gates.length)
  have h2 : W.card ≤ K.card := Finset.card_image_le
  rw [Finset.card_singleton] at h
  omega


def rowL {n m : ℕ} (R : Fin m → Fin n → Finset (Fin n)) (i : Fin m) (p : Fin n) :
    Fin n → Bool :=
  fun v => decide (v ∈ R i p)

def coY {n m : ℕ} (S : Fin m → Finset (Fin n)) (i : Fin m) : Fin n → Bool :=
  fun v => decide (v ∉ S i)

lemma kill {n m : ℕ} (gates : List Gate)
    (hC : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (S : Fin m → Finset (Fin n)) (R : Fin m → Fin n → Finset (Fin n)) (i j : Fin m)
    (hint : (S i ∩ S j).card ≤ 1)
    (hnA : ¬ ∃ p ∈ S i \ S j, (R i p ∩ S j).Nonempty) (w : ℕ)
    (hi : Multi ⟨gates, 0⟩ (S i) (rowL R i) (coY S i) w)
    (hj : value ⟨gates, 0⟩ (coY S j) w = false) : False := by
  obtain ⟨p, hp, p', hp', hne, hs, hs'⟩ := hi
  have key : ∀ a ∈ S i, a ∉ S j → value ⟨gates, 0⟩ (rowL R i a) w = true → False := by
    intro a ha haj hv
    have := mono ⟨gates, 0⟩ hC (rowL R i a) (coY S j) (fun v hv => ?_) w hv
    · rw [hj] at this
      exact Bool.noConfusion this
    · simp only [rowL, coY, decide_eq_true_eq] at hv ⊢
      intro hvj
      exact hnA ⟨a, Finset.mem_sdiff.mpr ⟨ha, haj⟩, ⟨v, Finset.mem_inter.mpr ⟨hv, hvj⟩⟩⟩
  by_cases hpj : p ∈ S j
  · by_cases hpj' : p' ∈ S j
    · exact hne (Finset.card_le_one.mp hint p (Finset.mem_inter.mpr ⟨hp, hpj⟩) p'
        (Finset.mem_inter.mpr ⟨hp', hpj'⟩))
    · exact key p' hp' hpj' hs'.1
  · exact key p hp hpj hs.1

def InK {n m : ℕ} (gates : List Gate) (S : Fin m → Finset (Fin n))
    (R : Fin m → Fin n → Finset (Fin n)) (i : Fin m) (g : Fin gates.length) : Prop :=
  Multi ⟨gates, 0⟩ (S i) (rowL R i) (coY S i) (n + (g : ℕ)) ∧
    gates[(g : ℕ)].op = GateOp.or ∧ gates[(g : ℕ)].inputs.length = 2 ∧
    ∀ r ∈ gates[(g : ℕ)].inputs, ∃ p ∈ S i, value ⟨gates, 0⟩ (rowL R i p) r = true


lemma or_decomp {n : ℕ} (C : Circuit) (hC : ∀ g ∈ C.gates, g.op = GateOp.or)
    (x : Fin n → Bool) (w : ℕ) :
    value C x w = true → ∃ q : Fin n, x q = true ∧ value C (fun v => decide (v = q)) w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · intro h
      refine ⟨⟨w, hn⟩, ?_, ?_⟩
      · have h2 := input_value C x ⟨w, hn⟩
        rw [← h2]
        exact h
      · have h2 := input_value C (fun v => decide (v = (⟨w, hn⟩ : Fin n))) ⟨w, hn⟩
        simp only [decide_true] at h2
        exact h2
    by_cases hw : w < n + C.gates.length
    · have hk : w - n < C.gates.length := by omega
      have hwk : w = n + (w - n) := by omega
      intro h
      rw [hwk] at h
      obtain ⟨r, hr, hlt, hv⟩ := (or_value C (w - n) hk (hC _ (List.getElem_mem hk)) x).mp h
      obtain ⟨q, hq, hq2⟩ := ih r (by omega) hv
      refine ⟨q, hq, ?_⟩
      rw [hwk]
      exact (or_value C (w - n) hk (hC _ (List.getElem_mem hk)) _).mpr ⟨r, hr, hlt, hq2⟩
    · intro h
      rw [missing_value C x w (by unfold Circuit.size; omega)] at h
      exact Bool.noConfusion h

lemma lines_card : ∀ t : Fin 13, ({t, t + 1, t + 3, t + 9} : Finset (Fin 13)).card = 4 := by
  decide

lemma lines_inter : ∀ i j : Fin 13, i ≠ j →
    (({i, i + 1, i + 3, i + 9} : Finset (Fin 13)) ∩ {j, j + 1, j + 3, j + 9}).card ≤ 1 := by
  decide

lemma main : ∀ (q n m : ℕ) (S : Fin m → Finset (Fin n))
    (R : Fin m → Fin n → Finset (Fin n)),
    1 ≤ q → (∀ i : Fin m, (S i).card = q + 1) →
    (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) →
    (∀ (i : Fin m) (p : Fin n), p ∈ S i → R i p ∩ S i = {p}) →
    (∀ i j : Fin m, i ≠ j → ¬ ((∃ p ∈ S i \ S j, (R i p ∩ S j).Nonempty) ∧
      (∃ s ∈ S j \ S i, (R j s ∩ S i).Nonempty))) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
      g.inputs.length ≤ 2) →
    (∀ w : Fin m, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn (fun v : Fin n => decide (v ∉ S w))) = false) →
    (∀ (w : Fin m) (p : Fin n), p ∈ S w →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn (fun v : Fin n => decide (v ∈ R w p))) = true) →
    ∀ I : Finset (Fin gates.length), (∀ g : Fin gates.length, ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (gates.get g).inputs.length = 2 ∧
      (∃ i : Fin m, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (g : ℕ)⟩ (List.ofFn (fun v : Fin n => decide (v ∉ S i))) = false) ∧
      ∀ w ∈ (gates.get g).inputs, ∃ (i : Fin m) (p : Fin n), p ∈ S i ∧
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn (fun v : Fin n => decide (v ∈ R i p))) = true) → g ∈ I) → m * q ≤ I.card := by
  intro q n m S R hq hcard hint hR hno gates out hg hfalse htrue I hI
  classical
  let K : Fin m → Finset (Fin gates.length) := fun i => Finset.univ.filter fun g =>
    PEqualNP.Outside.L_meta_1024.OrOnly.InK gates S R i g
  have hKq : ∀ i, q ≤ (K i).card := by
    intro i
    have h := PEqualNP.Outside.L_meta_1024.OrOnly.family (n := n) gates hg (S i)
      (PEqualNP.Outside.L_meta_1024.OrOnly.rowL R i) (PEqualNP.Outside.L_meta_1024.OrOnly.coY S i) (out i)
      (fun p hp => ⟨htrue i p hp, hfalse i⟩)
      (fun w hw hc => by
        obtain ⟨p, hp, p', hp', hne, hs1, hs2⟩ := hc
        have e : ∀ a ∈ S i, PEqualNP.Outside.L_meta_1024.OrOnly.Sv ⟨gates, 0⟩
            (PEqualNP.Outside.L_meta_1024.OrOnly.rowL R i) (PEqualNP.Outside.L_meta_1024.OrOnly.coY S i) a w →
            (⟨w, hw⟩ : Fin n) = a := by
          intro a ha hsa
          have h1 : PEqualNP.Outside.L_meta_1024.OrOnly.value ⟨gates, 0⟩
            (PEqualNP.Outside.L_meta_1024.OrOnly.rowL R i a) ((⟨w, hw⟩ : Fin n) : ℕ) = true := hsa.1
          have h2 : PEqualNP.Outside.L_meta_1024.OrOnly.value ⟨gates, 0⟩
            (PEqualNP.Outside.L_meta_1024.OrOnly.coY S i) ((⟨w, hw⟩ : Fin n) : ℕ) = false := hsa.2
          rw [PEqualNP.Outside.L_meta_1024.OrOnly.input_value] at h1 h2
          simp only [PEqualNP.Outside.L_meta_1024.OrOnly.rowL, PEqualNP.Outside.L_meta_1024.OrOnly.coY,
            decide_eq_true_eq, decide_eq_false_iff_not, not_not] at h1 h2
          have h3 : (⟨w, hw⟩ : Fin n) ∈ R i a ∩ S i := Finset.mem_inter.mpr ⟨h1, h2⟩
          rw [hR i a ha] at h3
          exact Finset.mem_singleton.mp h3
        exact hne ((e p hp hs1).symm.trans (e p' hp' hs2)))
      (K i)
      (fun g hm hop hl hQ => Finset.mem_filter.mpr ⟨Finset.mem_univ g, hm, hop, hl, hQ⟩)
    have := hcard i
    omega
  have hKI : ∀ i, K i ⊆ I := by
    intro i g hgK
    obtain ⟨hm, hop, hl, hQ⟩ := (Finset.mem_filter.mp hgK).2
    refine hI g ⟨hop, hl, ⟨i, ?_⟩, fun w hw => ?_⟩
    · obtain ⟨p, _, _, _, _, hs, _⟩ := hm
      exact hs.2
    · obtain ⟨p, hp, hv⟩ := hQ w hw
      exact ⟨i, p, hp, hv⟩
  have hdisj : ∀ i ∈ (Finset.univ : Finset (Fin m)), ∀ j ∈ (Finset.univ : Finset (Fin m)),
      i ≠ j → Disjoint (K i) (K j) := by
    intro i _ j _ hij
    refine Finset.disjoint_left.mpr fun g hgi hgj => ?_
    have hmi := (Finset.mem_filter.mp hgi).2.1
    have hmj := (Finset.mem_filter.mp hgj).2.1
    have hyi : PEqualNP.Outside.L_meta_1024.OrOnly.value ⟨gates, 0⟩
        (PEqualNP.Outside.L_meta_1024.OrOnly.coY S i) (n + (g : ℕ)) = false := by
      obtain ⟨p, _, _, _, _, hs, _⟩ := hmi
      exact hs.2
    have hyj : PEqualNP.Outside.L_meta_1024.OrOnly.value ⟨gates, 0⟩
        (PEqualNP.Outside.L_meta_1024.OrOnly.coY S j) (n + (g : ℕ)) = false := by
      obtain ⟨p, _, _, _, _, hs, _⟩ := hmj
      exact hs.2
    by_cases hA : ∃ p ∈ S i \ S j, (R i p ∩ S j).Nonempty
    · have hB : ¬ ∃ s ∈ S j \ S i, (R j s ∩ S i).Nonempty := fun hB => hno i j hij ⟨hA, hB⟩
      exact PEqualNP.Outside.L_meta_1024.OrOnly.kill gates hg S R j i
        (by rw [Finset.inter_comm]; exact hint i j hij) hB _ hmj hyi
    · exact PEqualNP.Outside.L_meta_1024.OrOnly.kill gates hg S R i j (hint i j hij) hA _ hmi hyj
  have hsub : Finset.univ.biUnion K ⊆ I := fun g hgm => by
    obtain ⟨i, _, hgi⟩ := Finset.mem_biUnion.mp hgm
    exact hKI i hgi
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_biUnion hdisj] at h1
  have h2 : ∑ i : Fin m, q ≤ ∑ i : Fin m, (K i).card := Finset.sum_le_sum fun i _ => hKq i
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h2
  omega

def line (w : Fin 13) : Finset (Fin 13) := {w, w + 1, w + 3, w + 9}

def band (x : Fin 13 → Bool) : Prop :=
  (Finset.univ.filter (fun v => x v = false)).card = 5 ∨
    (Finset.univ.filter (fun v => x v = false)).card = 6

def positive (w p : Fin 13) (v : Fin 13) : Bool :=
  decide (v = p ∨ v ∈ (({2, 4, 5, 6, 7, 8} : Finset (Fin 13)).image (fun a => a + w)))

def negative (w q : Fin 13) (v : Fin 13) : Bool :=
  decide (v ∉ line w ∧
    (if q = w + 2 ∨ q = w + 4 then v ≠ w + 5 ∧ v ≠ w + 6
      else v ≠ w + 2 ∧ v ≠ w + 4))

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma positive_spec : ∀ w p : Fin 13, p ∈ line w →
    band (positive w p) ∧ positive w p p = true ∧
      (∀ v ∈ line w, positive w p v = true → v = p) := by
  unfold band
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma negative_spec : ∀ w q : Fin 13, q ∉ line w →
    band (negative w q) ∧ negative w q q = true ∧
      (∀ v ∈ line w, negative w q v = false) := by
  unfold band
  decide +kernel

lemma band_lower (gates : List Gate) (out : Fin 13 → ℕ)
    (hg : ∀ g ∈ gates, g.op = GateOp.or ∧ g.inputs.length ≤ 2)
    (hc : ∀ (w : Fin 13) (x : Fin 13 → Bool), band x →
      Circuit.eval ⟨gates, out w⟩ (List.ofFn x) =
        decide (∃ v ∈ line w, x v = true)) : 39 ≤ gates.length := by
  classical
  have hg' : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      g.inputs.length ≤ 2 := fun g hm => ⟨Or.inr (hg g hm).1, (hg g hm).2⟩
  have no_bad (w q : Fin 13) (hq : q ∉ line w) :
      value ⟨gates, 0⟩ (fun v : Fin 13 => decide (v = q)) (out w) = false := by
    obtain ⟨hb, hq', hn⟩ := negative_spec w q hq
    have hz : value ⟨gates, 0⟩ (negative w q) (out w) = false := by
      change Circuit.eval ⟨gates, out w⟩ (List.ofFn (negative w q)) = false
      rw [hc w _ hb]
      simp only [decide_eq_false_iff_not]
      rintro ⟨v, hv, he⟩
      exact Bool.false_ne_true ((hn v hv).symm.trans he)
    by_contra he
    have ht : value ⟨gates, 0⟩ (fun v : Fin 13 => decide (v = q)) (out w) = true := by
      simpa using he
    have hm := mono ⟨gates, 0⟩ hg' (fun v : Fin 13 => decide (v = q))
      (negative w q) (fun v hv => by
        have ev : v = q := by simpa only [decide_eq_true_eq] using hv
        simpa only [ev] using hq') (out w) ht
    exact Bool.false_ne_true (hz.symm.trans hm)
  have hfalse : ∀ w : Fin 13,
      value ⟨gates, 0⟩ (fun v : Fin 13 => decide (v ∉ line w)) (out w) = false := by
    intro w
    by_contra he
    have ht : value ⟨gates, 0⟩ (fun v : Fin 13 => decide (v ∉ line w)) (out w) = true := by
      simpa using he
    obtain ⟨q, hq, hs⟩ := or_decomp ⟨gates, 0⟩ (fun g hm => (hg g hm).1) _ _ ht
    have hq' : q ∉ line w := by simpa using hq
    exact Bool.false_ne_true ((no_bad w q hq').symm.trans hs)
  have htrue : ∀ (w p : Fin 13), p ∈ line w →
      value ⟨gates, 0⟩ (fun v : Fin 13 => decide (v ∈ ({p} : Finset (Fin 13))))
        (out w) = true := by
    intro w p hp
    obtain ⟨hb, hpos, heq⟩ := positive_spec w p hp
    have ht : value ⟨gates, 0⟩ (positive w p) (out w) = true := by
      change Circuit.eval ⟨gates, out w⟩ (List.ofFn (positive w p)) = true
      rw [hc w _ hb]
      simp only [decide_eq_true_eq]
      exact ⟨p, hp, hpos⟩
    obtain ⟨q, hq, hs⟩ := or_decomp ⟨gates, 0⟩ (fun g hm => (hg g hm).1) _ _ ht
    have hq' : q ∈ line w := by
      by_contra hn
      exact Bool.false_ne_true ((no_bad w q hn).symm.trans hs)
    have hqp : q = p := heq q hq' hq
    subst q
    simpa using hs
  have hmain := main 3 13 13 line (fun _ p => {p}) (by norm_num)
    (fun i => lines_card i)
    (fun i j hij => lines_inter i j hij)
    (fun i p hp => Finset.inter_eq_left.mpr (Finset.singleton_subset_iff.mpr hp))
    (fun i j _ hc => by
      obtain ⟨⟨p, hp, v, hv⟩, _⟩ := hc
      have h1 := Finset.mem_inter.mp hv
      have h2 := Finset.mem_singleton.mp h1.1
      rw [h2] at h1
      exact (Finset.mem_sdiff.mp hp).2 h1.2)
    gates out hg' hfalse htrue Finset.univ (fun g _ => Finset.mem_univ g)
  simpa using hmain

end PEqualNP.Outside.L_meta_1024.OrOnly


namespace PEqualNP.Outside.L_meta_1024_aux.AndRoot

lemma above_unique {α β : Type*} [Fintype α] [DecidableEq α]
    (f : β → Finset α) (hsep : ∀ i j, i ≠ j → f i ∪ f j = Finset.univ)
    {s : Finset α} {i j : β} (hi : f i ⊆ s) (hj : f j ⊆ s)
    (hs : s ≠ Finset.univ) : i = j := by
  by_contra hij
  apply hs
  apply Finset.Subset.antisymm (Finset.subset_univ _)
  rw [← hsep i j hij]
  exact Finset.union_subset hi hj

lemma intersection_triple {α : Type*} [Fintype α] [DecidableEq α]
    (f s t : Finset α) (h : s ∩ t = f) (hs : s ≠ f) (ht : t ≠ f) :
    ({f, s, t} : Finset (Finset α)).card = 3 ∧
      ∀ u ∈ ({f, s, t} : Finset (Finset α)), f ⊆ u ∧ u ≠ Finset.univ := by
  have hfs : f ⊆ s := h ▸ Finset.inter_subset_left
  have hft : f ⊆ t := h ▸ Finset.inter_subset_right
  have hst : s ≠ t := by
    intro he
    subst t
    simp only [Finset.inter_self] at h
    exact hs h
  have hsu : s ≠ Finset.univ := by
    intro he
    subst s
    simp only [Finset.univ_inter] at h
    exact ht h
  have htu : t ≠ Finset.univ := by
    intro he
    subst t
    simp only [Finset.inter_univ] at h
    exact hs h
  have hfu : f ≠ Finset.univ := by
    intro he
    apply hsu
    exact Finset.Subset.antisymm (Finset.subset_univ _) (he ▸ hfs)
  constructor
  · simp [hs, ht, hst, Ne.symm hs, Ne.symm ht]
  · intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl
    · exact ⟨Finset.Subset.refl _, hfu⟩
    · exact ⟨hfs, hsu⟩
    · exact ⟨hft, htu⟩

lemma count_triples {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (f s t : β → Finset α) (pool : Finset (Finset α))
    (hsep : ∀ i j, i ≠ j → f i ∪ f j = Finset.univ)
    (he : ∀ i, s i ∩ t i = f i) (hs : ∀ i, s i ≠ f i) (ht : ∀ i, t i ≠ f i)
    (hm : ∀ i, f i ∈ pool ∧ s i ∈ pool ∧ t i ∈ pool) :
    3 * Fintype.card β ≤ pool.card := by
  let triple (i : β) : Finset (Finset α) := {f i, s i, t i}
  have hp (i : β) := intersection_triple (f i) (s i) (t i) (he i) (hs i) (ht i)
  have hd : ∀ i ∈ (Finset.univ : Finset β),
      ∀ j ∈ (Finset.univ : Finset β), i ≠ j → Disjoint (triple i) (triple j) := by
    intro i _ j _ hij
    rw [Finset.disjoint_left]
    intro u hui huj
    obtain ⟨hi, hu⟩ := (hp i).2 u hui
    obtain ⟨hj, _⟩ := (hp j).2 u huj
    exact hij (above_unique f hsep hi hj hu)
  have hsub : (Finset.univ.biUnion triple) ⊆ pool := by
    intro u hu
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hu
    simp only [triple, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact (hm i).1
    · exact (hm i).2.1
    · exact (hm i).2.2
  have hc : (Finset.univ.biUnion triple).card = 3 * Fintype.card β := by
    rw [Finset.card_biUnion hd]
    have heq : ∀ i : β, (triple i).card = 3 := fun i => (hp i).1
    simp [heq, Nat.mul_comm]
  rw [← hc]
  exact Finset.card_le_card hsub

end PEqualNP.Outside.L_meta_1024_aux.AndRoot


namespace PEqualNP.Outside.L_meta_1024_aux.Minterms

abbrev Increasing (f : Finset (Fin 13) → Bool) : Prop :=
  ∀ S T, S ⊆ T → f S = true → f T = true

abbrev BandSpec (f : Finset (Fin 13) → Bool) (L : Finset (Fin 13)) : Prop :=
  ∀ S, S.card = 5 ∨ S.card = 6 → f S = decide (L ⊆ S)

def MinimalTrue (f : Finset (Fin 13) → Bool) (S : Finset (Fin 13)) : Prop :=
  f S = true ∧ ∀ T, T ⊂ S → f T = false

lemma avoid_extension (S : Finset (Fin 13)) (p : Fin 13) (hp : p ∉ S)
    (hs : S.card ≤ 6) :
    ∃ T : Finset (Fin 13), S ⊆ T ∧ T.card = 6 ∧ p ∉ T := by
  have hsub : S ⊆ Finset.univ.erase p := by
    intro q hq
    exact Finset.mem_erase.mpr ⟨fun h => hp (h ▸ hq), Finset.mem_univ q⟩
  have hc : 6 ≤ (Finset.univ.erase p).card := by simp
  obtain ⟨T, hST, hT, hcard⟩ := Finset.exists_subsuperset_card_eq hsub hs hc
  exact ⟨T, hST, hcard, fun h => (Finset.mem_erase.mp (hT h)).1 rfl⟩

lemma low_true_contains (f : Finset (Fin 13) → Bool) (L : Finset (Fin 13))
    (hmono : Increasing f) (hband : BandSpec f L) (S : Finset (Fin 13))
    (hs : S.card ≤ 6) (hf : f S = true) : L ⊆ S := by
  intro p hp
  by_contra hn
  obtain ⟨T, hST, hcard, hpT⟩ := avoid_extension S p hn hs
  have hfT := hmono S T hST hf
  rw [hband T (Or.inr hcard)] at hfT
  exact hpT (of_decide_eq_true hfT hp)

lemma low_exact_of_true (f : Finset (Fin 13) → Bool) (L : Finset (Fin 13))
    (hmono : Increasing f) (hband : BandSpec f L) (hfL : f L = true)
    (S : Finset (Fin 13)) (hs : S.card ≤ 6) : f S = decide (L ⊆ S) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact ⟨low_true_contains f L hmono hband S hs, fun h => hmono L S h hfL⟩

lemma extension_minimal_of_false (f : Finset (Fin 13) → Bool)
    (L : Finset (Fin 13)) (hmono : Increasing f) (hband : BandSpec f L)
    (hcard : L.card = 4) (hfL : f L = false) (p : Fin 13) (hp : p ∉ L) :
    MinimalTrue f (insert p L) := by
  have hc : (insert p L).card = 5 := by simp [hp, hcard]
  constructor
  · rw [hband _ (Or.inl hc)]
    exact decide_eq_true (Finset.subset_insert p L)
  · intro T hT
    have htcard : T.card < 5 := (Finset.card_lt_card hT).trans_eq hc
    cases hft : f T with
    | false => rfl
    | true =>
      have hLT := low_true_contains f L hmono hband T (by omega) hft
      have heq : L = T := Finset.eq_of_subset_of_card_le hLT (by omega)
      rw [← heq, hfL] at hft
      cases hft

lemma extensions_distinct (L : Finset (Fin 13)) (p q : Fin 13)
    (hp : p ∉ L) (hpq : p ≠ q) : insert p L ≠ insert q L := by
  intro h
  have hm : p ∈ insert q L := h ▸ Finset.mem_insert_self p L
  rcases Finset.mem_insert.mp hm with h | h
  · exact hpq h
  · exact hp h

lemma minterm_dichotomy (f : Finset (Fin 13) → Bool) (L : Finset (Fin 13))
    (hmono : Increasing f) (hband : BandSpec f L) (hcard : L.card = 4) :
    (f L = true ∧ ∀ S, S.card ≤ 6 → f S = decide (L ⊆ S)) ∨
      (f L = false ∧ (Finset.univ \ L).card = 9 ∧
        ∀ p, p ∉ L → MinimalTrue f (insert p L)) := by
  cases hfL : f L with
  | false =>
    refine Or.inr ⟨rfl, ?_, fun p hp =>
      extension_minimal_of_false f L hmono hband hcard hfL p hp⟩
    simp [Finset.card_sdiff, hcard]
  | true =>
    exact Or.inl ⟨rfl, low_exact_of_true f L hmono hband hfL⟩

end PEqualNP.Outside.L_meta_1024_aux.Minterms

namespace PEqualNP.Outside.L_meta_1024_aux.AndFirst26

open PEqualNP.CircuitLowerBounds

abbrev Row := Fin 13 × Fin 2
abbrev Mask := Finset Row

def row (r : Row) (p : Fin 13) : Bool :=
  decide (p ∉ ((if r.2 = 0 then ({0, 1, 2, 3, 4, 9} : Finset (Fin 13))
    else {0, 1, 2, 3, 5, 9}).image (fun u => u + r.1)))

def inputMask (p : Fin 13) : Mask := Finset.univ.filter (fun r => row r p = true)
def targetMask (w : Fin 13) : Mask := Finset.univ.filter (fun r => r.1 ≠ w)

def initial : List Mask := List.ofFn inputMask

def val (xs : List Mask) (i : ℕ) : Mask := xs.getD i ∅
def gateMask (xs : List Mask) (g : Gate) : Mask :=
  Finset.univ.filter (fun r => g.op.eval (g.inputs.map (fun i => decide (r ∈ val xs i))))
def next (xs : List Mask) (g : Gate) : List Mask := xs ++ [gateMask xs g]
def run (gs : List Gate) (xs : List Mask) : List Mask := gs.foldl next xs

def pool (xs : List Mask) : Finset Mask := insert ∅ (insert Finset.univ xs.toFinset)

lemma available (xs : List Mask) (i : ℕ) : val xs i ∈ pool xs := by
  by_cases h : i < xs.length
  · unfold val
    rw [List.getD_eq_getElem _ _ h]
    simp [pool, List.getElem_mem]
  · unfold val
    rw [List.getD_eq_default _ _ (by omega : xs.length ≤ i)]
    simp [pool]

lemma run_split (gs : List Gate) (xs : List Mask) :
    ∃ ys : List Mask, run gs xs = xs ++ ys ∧ ys.length = gs.length := by
  induction gs generalizing xs with
  | nil => exact ⟨[], by simp [run]⟩
  | cons g gs ih =>
    obtain ⟨ys, hys, hlen⟩ := ih (next xs g)
    refine ⟨gateMask xs g :: ys, ?_, by simp [hlen]⟩
    change run gs (next xs g) = _
    rw [hys]
    simp [next, List.append_assoc]

lemma run_includes (gs : List Gate) (xs : List Mask) {s : Mask} (hs : s ∈ xs) :
    s ∈ run gs xs := by
  obtain ⟨ys, he, _⟩ := run_split gs xs
  rw [he]
  exact List.mem_append_left ys hs

lemma pool_mono_run (gs : List Gate) (xs : List Mask) : pool xs ⊆ pool (run gs xs) := by
  intro s hs
  simp only [pool, Finset.mem_insert, List.mem_toFinset] at hs ⊢
  rcases hs with rfl | rfl | hs
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (run_includes gs xs hs))

lemma pool_mono_next (xs : List Mask) (g : Gate) : pool xs ⊆ pool (next xs g) := by
  simpa only [run, List.foldl_cons, List.foldl_nil] using pool_mono_run [g] xs

lemma target_next (xs : List Mask) (g : Gate) : gateMask xs g ∈ pool (next xs g) := by
  simp [pool, next]

lemma and_parents (xs : List Mask) (g : Gate) (w : Fin 13)
    (hop : g.op = GateOp.and) (hlen : g.inputs.length ≤ 2)
    (hfresh : targetMask w ∉ pool xs) (he : gateMask xs g = targetMask w) :
    ∃ s t : Mask, s ∈ pool xs ∧ t ∈ pool xs ∧ s ≠ targetMask w ∧
      t ≠ targetMask w ∧ s ∩ t = targetMask w := by
  obtain ⟨op, ins⟩ := g
  change op = GateOp.and at hop
  subst op
  change ins.length ≤ 2 at hlen
  match ins, hlen with
  | [], _ =>
    have h : (Finset.univ : Mask) = targetMask w := by
      simpa [gateMask, GateOp.eval] using he
    exact (hfresh (h ▸ (by simp [pool]))).elim
  | [a], _ =>
    have h : val xs a = targetMask w := by
      simpa [gateMask, GateOp.eval] using he
    exact (hfresh (h ▸ available xs a)).elim
  | [a, b], _ =>
    refine ⟨val xs a, val xs b, available xs a, available xs b,
      fun h => hfresh (h ▸ available xs a), fun h => hfresh (h ▸ available xs b), ?_⟩
    rw [← he]
    ext r
    simp [gateMask, GateOp.eval]
  | _ :: _ :: _ :: _, h => simp at h

lemma row_band : ∀ r : Row,
    (Finset.univ.filter (fun p : Fin 13 => row r p = false)).card = 6 := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma row_target : ∀ (w : Fin 13) (r : Row),
    decide (∃ p ∈ (({0, 1, 3, 9} : Finset (Fin 13)).image (fun u => u + w)),
      row r p = true) = decide (w ≠ r.1) := by
  decide +kernel

lemma target_separated : ∀ w v : Fin 13, w ≠ v →
    targetMask w ∪ targetMask v = Finset.univ := by
  decide +kernel

lemma target_nonempty : ∀ w : Fin 13, targetMask w ≠ ∅ := by decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma input_not_above : ∀ w p : Fin 13, ¬ targetMask w ⊆ inputMask p := by
  decide +kernel

lemma initial_not_above (w : Fin 13) (s : Mask) (hs : s ∈ initial) :
    ¬ targetMask w ⊆ s := by
  simp only [initial, List.mem_ofFn] at hs
  obtain ⟨p, rfl⟩ := hs
  exact input_not_above w p

lemma pool_to_list (w : Fin 13) (s : Mask) (xs : List Mask)
    (hsub : targetMask w ⊆ s) (hnot : s ≠ Finset.univ) (hm : s ∈ pool xs) :
    s ∈ xs := by
  simp only [pool, Finset.mem_insert, List.mem_toFinset] at hm
  rcases hm with rfl | he | hm
  · exact (target_nonempty w (Finset.Subset.antisymm hsub (Finset.empty_subset _))).elim
  · exact (hnot he).elim
  · exact hm

def AndFirst (gs : List Gate) : Prop :=
  ∀ w : Fin 13, ∃ (pre post : List Gate) (g : Gate),
    gs = pre ++ g :: post ∧ g.op = GateOp.and ∧
      targetMask w ∉ pool (run pre initial) ∧
      gateMask (run pre initial) g = targetMask w

lemma and_first_bound (gs : List Gate)
    (hfanin : ∀ g ∈ gs, g.inputs.length ≤ 2) (hfirst : AndFirst gs) : 39 ≤ gs.length := by
  classical
  have pairs (w : Fin 13) : ∃ s t : Mask,
      s ∩ t = targetMask w ∧ s ≠ targetMask w ∧ t ≠ targetMask w ∧
      targetMask w ∈ pool (run gs initial) ∧ s ∈ pool (run gs initial) ∧
      t ∈ pool (run gs initial) := by
    obtain ⟨pre, post, g, hgs, hop, hfresh, he⟩ := hfirst w
    have hlen := hfanin g (by simp [hgs])
    obtain ⟨s, t, hs, ht, hsf, htf, hst⟩ := and_parents _ g w hop hlen hfresh he
    have hrun : run gs initial = run post (next (run pre initial) g) := by
      simp only [hgs, run, List.foldl_append, List.foldl_cons]
    have hp : pool (run pre initial) ⊆ pool (run gs initial) := by
      rw [hrun]
      exact (pool_mono_next _ _).trans (pool_mono_run _ _)
    refine ⟨s, t, hst, hsf, htf, ?_, hp hs, hp ht⟩
    rw [hrun]
    apply pool_mono_run post _
    rw [← he]
    exact target_next _ _
  choose s t he hs ht hm using pairs
  obtain ⟨ys, hys, hlen⟩ := run_split gs initial
  have mem_generated (w : Fin 13) (u : Mask) (hu : targetMask w ⊆ u)
      (hnot : u ≠ Finset.univ) (hmem : u ∈ pool (run gs initial)) : u ∈ ys.toFinset := by
    have h := pool_to_list w u _ hu hnot hmem
    rw [hys, List.mem_append] at h
    rcases h with hi | hi
    · exact (initial_not_above w u hi hu).elim
    · exact List.mem_toFinset.mpr hi
  have allmem (w : Fin 13) : targetMask w ∈ ys.toFinset ∧
      s w ∈ ys.toFinset ∧ t w ∈ ys.toFinset := by
    have hp := AndRoot.intersection_triple (targetMask w) (s w) (t w) (he w) (hs w) (ht w)
    have hf := hp.2 (targetMask w) (by simp)
    have hss := hp.2 (s w) (by simp)
    have htt := hp.2 (t w) (by simp)
    exact ⟨mem_generated w _ hf.1 hf.2 (hm w).1,
      mem_generated w _ hss.1 hss.2 (hm w).2.1,
      mem_generated w _ htt.1 htt.2 (hm w).2.2⟩
  have hc := AndRoot.count_triples targetMask s t ys.toFinset target_separated he hs ht allmem
  have hcard : ys.toFinset.card ≤ ys.length := List.toFinset_card_le ys
  simp only [Fintype.card_fin] at hc
  omega


def witnessGates : List Gate :=
  [⟨GateOp.or, [0, 3]⟩,
   ⟨GateOp.or, [13, 4]⟩,
   ⟨GateOp.or, [0, 1]⟩,
   ⟨GateOp.or, [15, 5]⟩,
   ⟨GateOp.or, [1, 4]⟩,
   ⟨GateOp.or, [17, 5]⟩,
   ⟨GateOp.or, [1, 2]⟩,
   ⟨GateOp.or, [19, 6]⟩,
   ⟨GateOp.or, [2, 5]⟩,
   ⟨GateOp.or, [21, 6]⟩,
   ⟨GateOp.or, [2, 3]⟩,
   ⟨GateOp.or, [23, 7]⟩,
   ⟨GateOp.or, [3, 6]⟩,
   ⟨GateOp.or, [25, 7]⟩,
   ⟨GateOp.or, [3, 4]⟩,
   ⟨GateOp.or, [27, 8]⟩,
   ⟨GateOp.or, [0, 5]⟩,
   ⟨GateOp.or, [29, 8]⟩,
   ⟨GateOp.or, [0, 6]⟩,
   ⟨GateOp.or, [31, 9]⟩,
   ⟨GateOp.or, [1, 6]⟩,
   ⟨GateOp.or, [33, 9]⟩,
   ⟨GateOp.or, [1, 7]⟩,
   ⟨GateOp.or, [35, 10]⟩,
   ⟨GateOp.or, [2, 7]⟩,
   ⟨GateOp.or, [37, 10]⟩,
   ⟨GateOp.or, [2, 8]⟩,
   ⟨GateOp.or, [39, 11]⟩,
   ⟨GateOp.or, [3, 8]⟩,
   ⟨GateOp.or, [41, 11]⟩,
   ⟨GateOp.or, [3, 9]⟩,
   ⟨GateOp.or, [43, 12]⟩,
   ⟨GateOp.or, [4, 9]⟩,
   ⟨GateOp.or, [45, 12]⟩,
   ⟨GateOp.or, [0, 4]⟩,
   ⟨GateOp.or, [47, 10]⟩,
   ⟨GateOp.or, [0, 5]⟩,
   ⟨GateOp.or, [49, 10]⟩,
   ⟨GateOp.or, [1, 5]⟩,
   ⟨GateOp.or, [51, 11]⟩,
   ⟨GateOp.or, [0, 1]⟩,
   ⟨GateOp.or, [53, 6]⟩,
   ⟨GateOp.or, [0, 2]⟩,
   ⟨GateOp.or, [55, 6]⟩,
   ⟨GateOp.or, [0, 2]⟩,
   ⟨GateOp.or, [57, 7]⟩,
   ⟨GateOp.or, [0, 3]⟩,
   ⟨GateOp.or, [59, 7]⟩,
   ⟨GateOp.or, [0, 3]⟩,
   ⟨GateOp.or, [61, 8]⟩,
   ⟨GateOp.or, [0, 4]⟩,
   ⟨GateOp.or, [63, 12]⟩,
   ⟨GateOp.and, [14, 16]⟩,
   ⟨GateOp.and, [18, 20]⟩,
   ⟨GateOp.and, [22, 24]⟩,
   ⟨GateOp.and, [26, 28]⟩,
   ⟨GateOp.and, [30, 32]⟩,
   ⟨GateOp.and, [34, 36]⟩,
   ⟨GateOp.and, [38, 40]⟩,
   ⟨GateOp.and, [42, 44]⟩,
   ⟨GateOp.and, [46, 48]⟩,
   ⟨GateOp.and, [50, 52]⟩,
   ⟨GateOp.and, [54, 56]⟩,
   ⟨GateOp.and, [58, 60]⟩,
   ⟨GateOp.and, [62, 64]⟩]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 12000000 in
lemma witness_certificate : ∀ w : Fin 13,
    targetMask w ∉ pool (run (witnessGates.take (52 + w.val)) initial) ∧
    gateMask (run (witnessGates.take (52 + w.val)) initial)
      ⟨GateOp.and, [14 + 4 * w.val, 16 + 4 * w.val]⟩ = targetMask w := by
  decide +kernel

lemma witness_first : AndFirst witnessGates := by
  intro w
  refine ⟨witnessGates.take (52 + w.val), witnessGates.drop (53 + w.val),
    ⟨GateOp.and, [14 + 4 * w.val, 16 + 4 * w.val]⟩, ?_, rfl,
    (witness_certificate w).1, (witness_certificate w).2⟩
  fin_cases w <;> rfl

lemma witness_fanin : ∀ g ∈ witnessGates, g.inputs.length ≤ 2 := by
  have h : witnessGates.all (fun g => decide (g.inputs.length ≤ 2)) = true := by decide
  intro g hg
  simpa only [decide_eq_true_eq] using (List.all_eq_true.mp h g hg)

lemma condition_realized : ∃ gs : List Gate, AndFirst gs ∧
    (∀ g ∈ gs, g.inputs.length ≤ 2) ∧ gs.length = 65 := by
  exact ⟨witnessGates, witness_first, witness_fanin, rfl⟩

end PEqualNP.Outside.L_meta_1024_aux.AndFirst26
