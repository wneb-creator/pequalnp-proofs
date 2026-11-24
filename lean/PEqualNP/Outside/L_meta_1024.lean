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


namespace PEqualNP.Outside.L_meta_1024_aux.Tables

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Table := BitVec 8192
def sample (j : Fin 8192) (i : Fin 13) : Bool :=
  j.val.testBit i.val

def readTable (j : Fin 8192) (t : Table) : Bool := t.getLsbD j.val
lemma read_zero (j : Fin 8192) : readTable j 0 = false := BitVec.getLsbD_zero
lemma read_not (j : Fin 8192) (t : Table) : readTable j (~~~t) = !(readTable j t) := by
  simp [readTable, j.isLt]
def inputs : List Table := [727165423746277286308656163155855241632176107997488461621221857459814221232746196810842823016801324815971527864104683515406580546784789375740653176718369866052604199228128659692406550152032136773131234409061092131181257695072883040080860369267924200678600168357199944800006719733351023891200603531870587301567001086796983769274003541576373343231617356862367497229285945835179130852896058703745010462899963604451883427209933744070613504292336385342217662377224031494938254961874830087678505012776599484243829148288184912050018418588696804334528507800630466112331505253122567824699997933974080343770033410374180994328343561403832644419698021857547670487218953481109980216264092423501084273010778670285082290664205947794297454124937596873776936590492956555251618778271663580662341245837573313593411347882411166305747313238004175741388471143605438044383424854018014873951709940184506107013918869754940699576379169947311548654972789842284922526848298958679017985176627381810407720289793884972893327974276161827607066078284040370989175837543018407575105752255579080771995758680585691783696891193277129489622637110876713391475690313503780208002753816997223005571626435885957384720652367052608645271568520036623747707393863896781969410648618319918351825706672136079039286669851832485174569209006995893721241065768141070640205570937294547459809358579150812987665818402435744199237449881608688990292523549349834279611455341520718806486202358248536382914730152469081850909296860579870838948236765671714026412924966419911205459179775210518768719595452728762432227174492387879708668662948527169970040859212205620053099128821452772510612023710144104743601994746850770405248738624984977894352241991805799633434687487908396135390462559296438040897491136156017880735305969967464724717697457748530863024301080504339567345937349182547693021850805784652393154644220205928869776779624123385567094378891296353367624994207532556244843492396936602848970619149299683484789744936245236503073649584679845350384403920692051513805145294814651393590292390562730328077399901692602649770469295982057393953731308907178353309958943065457137309169707664903885209082555525937539336192011547616539109308447555685339488505567248706409412482520948067640132410498257903397930726126120294226372349881911694075475092529117045100226908646687953348931885643545698158829488018676793126440279215317333876958407101502846775730433916955900764748809484844403602387854312727204384312633725107998124337110317143861930, 872598508495532743570387395787026289958611329596986153945466228951777065479295436173011387620161589779165833436925620218487896656141747250888783812062043839263125039073754391630887860182438564127757481290873310557417509234087459648097032443121509040814320202028639933760008063680021228669440724238244704761880401304156380523128804249891648011877940828234840996675143135002214957023475270444494012555479956325342260112651920492884736205150803662410661194852668837793925905954249796105214206015331919381092594977945821894460022102306436165201434209360756559334797806303747081389639997520768896412524040092449017193194012273684599173303637626229057204584662744177331976259516910908201301127612934404342098748797047137353156944949925116248532323908591547866301942533925996296794809495005087976312093617458893399566896775885605010889666165372326525653260109824821617848742051928221407328416702643705928839491655003936773858385967347810741907032217958750414821582211952858172489264347752661967471993569131394193128479293940848445187011005051622089090126902706694896926394910416702830140436269431932555387547164533052056069770828376204536249603304580396667606685951723063148861664782840463130374325882224043948497248872636676138363292778341983902022190848006563294847144003822198982209483050808395072465489278921769284768246685124753456951771230294980975585198982082922893039084939857930426788351028259219801135533746409824862567783442829898243659497676182962898221091156232695845006737884118806056831695509959703893446551015730252622522463514543274514918672609390865455650402395538232603964049031054646744063718954585743327012734428452172925692322393696220924486298486349981973473222690390166959560121624985490075362468555071155725649076989363387221456882367163960957669661236949298237035629161296605207480815124819019057231626220966941582871785573064247114643732135548948062680513254669555624041149993049039067493812190876323923418764742979159620181747693923494283803688379501615814420461284704830461816566174353777581672308350868675276393692879882031123179724563155178468872744477570688614023971950731678548564771003649197884662250899066631125047203430413857139846931170137066822407386206680698447691294979025137681168158892597909484077516871351344353071646819858294032890570111034940454120272290376025544018718262772254837790595385622412151751728335058380800652350088521803416130876520700347080917698571381813284322865425175272645261175160470129597749204532380572634316, 1026586480582979698318102818572972105833660387761160181112313210531502429975641689615307514847248929151959804043441906139397525477813820295163275073014169222662500045969122813683397482567574781326773507401027424185197069687161717233055332286025304753899200237680752863247068310211789680787577322633229064425741648593125153556622122646931350602209342150864518819617815452943782302380559141699404720653505830970990894250178729991629101417824474896953719052767845691522265771710882113064957889429802258095403052915230378699364731885066395488472275540424419481570350360357349507517223526495022231073557694226410608462581190910217175498004279560269479064217250287267449383834725777539060354267779922828637763233878878985121361111705794254410038028127754762195649344157559995643288011170594221148602463079363403999490466795159535306929019018085090030180306011558613668057343590503789890974607885463183445693519594122278557480454079232718519890626138775000488025390837591597849987369820885484667614110081331051991915857992871586406102365888296025987164855179654935172854582247549062153106395611096391241632408428862414183611495092207299454411298005388701961890218766733015469249017391577015447499206920263581115879116320749030751015638562755275178849636291772427405702522357437881155540568295068700085253516798731493276197937276617357008178554388582330559511998802450497521222452870421094619751001209716729177806510289893911603020921697446939110187644324921132821436577830861995111772632804845654184507877070540828109937118842035591320614662958286205311669026599283371124294591053574391298781234154181937345957316417159698031779687562884909324343908698466142264101527630999978792321438459282549364188378382335870676897021829495477324293031752192220260537508667251718773729013219940350867100740189760712008800958970375316537919560259961107744555041850663820134874978982998762426682956770199477204754294109469457726463308459854498733433840874093128964919703169321757980945515740590136252259366217299800543313607263945620684320362765727853266345521035155330733152617133123739375144405267730221898851731706743151233605612945469644570190883410666624852996709918133949576290507258984784496949866125506704056107405857676632566080186932468128804797078672178052180084290376303875332812435424746988769553261518089441816492609720908535103283053394849896649119680394186330353708647162966827548389266494941584801079645378096250922732782853147379582660206071141328938528475920447732510960, 1086503979449690575651844228217308999170255352027375755885405421262913077639589648153165930110707037857327107781385986264265085330604510195659186069493595441884046741259149437050132744196032453388647447521709958670714408384855980884790079306610439272609270290463676182113628717422594525969731641074857219936971705904007944620238199844223063672377202587685405132046870829574742358939735745300537291897873875580192697416531574154564652084234463704168916662851572093751191789515019201376142202042436631135990779739076509751856836858902955536437583451344132680883794933919062513792547856835198625883298415679313951368957525010035298581545385371180149048510085907146872499622744791792312904127767077857546582099669475034836615651299517654472880714594355234697340940120063497334530502094947969464668754698781501509188353962192193009668066820697060265404837490832462714831118508237474125856394337922124113730106340860932947994877469071204036615759960104280672151386411770095778974959499147283383622715728101346855257250482727904678832075959597350461123893419712616214071775763942976286556185238203184504762704640663722404444850836888659344746587772240182621144511690861401586131255760735207010582818219111650052603578362816094802631337311554221200961482767945915386580101483358380055669395238360647561046523615778078486870968635174790296593645111651338179716979277301693874601195255854232438024405949583464343826345520821571813313971601967188474595483487854272869380346964958998717518117209797735168039465226408969828415939007913155016370382586201742586669164338541155431160034111176009467970800349951311121013190916215711535580058432313989635103280801489457960449865819579744091484168330446900494393925758736796980996069796197547985243986912826007435277051974678861892818255236668386909927631640524955900365217276039245518731985956067787184898721336111124812007759857492853618901806387137189882074583648932655648241322572297368309315193454293117036802176116947541520689417437511739535465165801967104076970043485576688039436337246217805791618605920475680775943625915212673579919370555730040297617396981455786519613722650458145226038600341250280000058774699347993325879447371376892541518924459680247094401612425245307618575139477164712198073172758102841217832400709551183231614717647981248814468821528872872272708131689054947657949379468479268048873747343263353526104093495435708533703815123051015820597912618062958175032361618895281114722085802920005724823912258217055420160, 1090731492377649913076371140926090508772288022347454197342151662049370236722216185228086315727659756087542381786669313644178532646766436284737006116912929052480815466086667985449476379848717017461066159075763944044793663983039270860309579287128095894281232142914478590317223256735391291218709799496421963380887780564207862618897899570488789617056638427895664654281211004766489910727727759201869928567754368100035673717570919126251088544271996521425780323822125382487425579684333175106262840178463933895343170737038950968066359623128053628535048757661064396306004795648304940834022134014394738759997701517820826227420441665932867910905808846005834356158743488457009559411929525941069176013153662608964473953666693646214666782585377199491581365863433169067968554135514558442306342887694230846994624550135534847376599232197823557564146242081587332064559992017476950946319619359444248109371748486692855799489698611814707943283617576829210629477688865539069261394552743917809639143313973756326583543848257378462564429616241730696091062171503561065325895232765192882741203763695870971284992282098111218660418751522767664574753593551408755505554155839084715661988085587581566973581015461353733620165345862546046674315694133031863752093388494672036462729057916866275750767303860636596466131368879010701380485553645594699302909325196756079672385052501103827150151831976334641466070132492510498840375913377104324412513915893203117957074929225098251683568818116610778983960015236926371712955543693067918514007296273844438273669212942647585898655890739354078797284894964671836167065386613546773833634383996775276160029552156249040219772103984039642838626279683147201335391793975777396995993145807139132507822505131625600404251400452096938297028960261358945050090842090295278274847010557189245433247492155849346122470894688100480162577170477926277810346432479715635924966607323646570559953092490196327592825540237991980241590165503279915261077067074366481305045563364399525904422723786141683588265993912136830065659108641858179205570900455649154556530215297251775499077409916111817294890330692445660632067110242139656963639480277435505310459643431014873489279414979373131151267245336657370517617194123667803452567018352064922735181294255470115135422465189162296162920296668926670039756221615001022346654653517921366037709997197050769974298091004898049521668450005074312059455258124511891747278706315095791213785601531930729995714415221299954221210448230969019753953267507156418560, 1090748135365456339041586926824709096400964067164273332347272707540109023476350483456643682700482416018057609895981362120404606980048375087448667425214590816869671144547395038055582970986878455636444962424714107236239490619974692554770930709212877821728916669614260327992795699918566977659395175021578144334544566109855586642133164142480791907459073081590624358274300179425040837504737754591061664838562273108983506886107634298866042884653729319819199997516446804694739144110610717674156946529148702714412442293984696868969709907445224692898230111221050144866923794893547112852427041007695329043678419482870554145720540889865230465166845682064128327460786411382323751884924288490359559578197608978570342104424944587739380487102228316436132266546300897104300298367464939913764498334082754312722554117819014494666733843304428703937824198941703283915032685136815704633686814941668193778404358975865825028806933982931557049500470592340750507523610764520132237088741246609468819349337613959440828784317324935031505062497594936585663442849809668662650964255879591527000676094851237579633838846544771148541303921518249715058663926914944350215064247014897203907073996515109866185678977480329325325801747949437443546148220516763024497923624659148936397529559134468581007943125037851605844897637030937792984208879998260560834990466014491803030020045397864796326702999835042686266982263606726267146269373602788359121917286258255297088099245591502185867918926029084430605200919372173516522535733737890028181875115540306551779084866614357067231533631720626002919587235295062368071686593937750462360071885117835669805146321374038164582655652795571977548739307436252124465110216812285016292939828102403759493188093620266844902118992158588255074301105296020131705096904108125908453231286645621791511653515435611337191921902927077389109450451989403004404527133421488734171726166453908082112971477795474787089400560567367842496129965928562701168456383421601224547224975507428722506692020725843928961435818309035149891715365798426895257374225068707636935783558936310339766210019945402769632483047091147946123851035813219440350036499475353738431721176746185131364175201392263406813394131677632259165477572009757420066823456072165146952257899881163435108097311824032068432359543340248227743649736365547338111070004318372011931585654645314294836757658558013694582114506887325604913720922722968365137005114262182509113579006044876988892546771973980841489093151046977170736321405274931855360, 1090748135619415929403854669820128643835281822143174671095392721590677921920417072578689030872885679376536174029528239896742254073353278082923030058229357091300030393146888777261730166167240147960083923101996823490514355455651568890737193309875090994887952495597058554419219395583801974058669822774425700320602000555580027419219660782965643544761919466940595449891933698401109894205870007440326040697196084961016514337994471542752611988248099510093894277317118938299181052534179992180611763502713740568706813166286568129787497207891105101070642977075903571570054027644364590446601280785149886722456526311428692503745869033851011170379573239871025633307907777362710306567563441148121858767949811499260469124776695938902641931594003381934561985005343743685083799012958615340497526215585095341939983925335426324943931358772634914039415810241181336029872642177025788124259913276625707191883433362498148979089190612769477364849156296598604956531440099537350932558545961732221916191503815951153776287037593938459242959091504280127175810734425619861520616741230751469122342495262459811324635237600645624320878844480106463393239977750409859338365102275402708239345773880027238141707183621557733481314949378274404868584905321709416744565607290993339377141986944120719563564133545054356921532678282631495561640293652704448981407979637281048067370092943735415862513219631905132205243835345916182893926006276981822640099165954635101713781042208879607159383576070856276803186793994557281304652875534793746532044826511343908913238927973380729497620328575369613527557267407888667221403469768087071709689761333129469855333306317190610121128804688744301302209854694241778786633133327396692416385648538584937903813623713078893779055091594531543783419179722909182516033055000345688034320365228169710990474860995658072338681123651241223172931351929918827568679587283744611196323840052692029991663662335786495300388236002058368899453352397682826240056654577137531924806502740465564271415492629087478374350216697724571799736835532009208639156739698175298800515035510452484116660223014932861307476880632787267150057929595142785268236485943223275300709970934124908318484485834183562070916059435823162768771276983699787719886834170973112315811783258262042268793707899620037982010519892205757909218844019984162560417654567467164875084760799557738260877398316200197677337735993893876640054030862480179650557345729971470059927578032767319931222828570259113571184368826210270342110464355294248960, 1090748135619415929462984244733782862445058741317256278077723357411872937927833784244419600432340383621359132078539296421583922726078535288895631126147893430149380770045156693316471592314481596094990093519266467060963746463149021913517350803079950400440665964304739215704920738623747423257015752366908264085893021118110308974552597077954159980749712419298225792610335570650809591039390908475045801933904902676564396390725443722970902476505668943463129909442136980589661502329916207474552401367763852856835262959009067319505910523234201508849530123021140590765937850147753368424740552323470408182285922748805210520738945273624250073532547213864411288330003393740150912580166278929704842831018825970092592589997564992748701241134099098189591461277259179911627931227354401824729735222739283906940258565844609867958833251463899830750255317198113101160530620734317932567900498223532817667589142046943165554232191512001478956898687683520250475974324734315380150309747612208712500051022967476984319077129296386777374636865231087169447708549517544139233017684215770290488418789440168334816327372623519038609022141979462139722689427219151234633118646875003741836690327166568052540560892638150017862105394046379266526690121410209850772135746339395758587591648792223654974745634225736271050568271311740257450712934213663479668020824855253157533409992242243185229562856090869187134982573538569852483225539869705077626849803583477586364785204481055628574836838979480433938208897652545831398860133527896735028968302348255129557764568722621963320682441686446392311846397899383114863434253848663932279264188564128386706056453584844520974679854641137384660894775927042925383218566634937141648684602149056050732108371054310349389279475071554719181040574555552962971974792722792653974763290140871652286270098969576677480222940290795746088405409748159994478121367758864292622252744789474675449474741606852764070764063110576030660846709793102667506631035454077016208694602827335899556351637399344567778304083178028820294133459605355876156179714463545661793044235280409193608501261558804583167350441282704397497970403108257267112393653696672675910688099839367469282734578305725116229359673050529813789252273363198230132949795533051518858815503461348243733779388689730783814640911372667854894579549420746122021822981211980082448791461461735149685581518666731366228054655612843460369296145991464644624232666058546546775071466057342070960016482455402459983974533531512623447503628532879196160, 1090748135619415929462984244733782862448264161996232692431832786189721331849109875331513870234605433463932241694048131051358947830205980188196448074959461356758486573232462591433156779577237490627406123547618423722668866652339479999293626021839890161927470072222416275310966999593803517697609822714708579884205550840414698745794222115405131762724689518277473450666725768294443700706103254859716733899036477127355717020008787842924414391583891235738543020558099725138939596081148014590965124539186821561529914566658849262988504621375111628343614858679068075902419555944729073976404444565343555827377610000620947577410278627011740831480055497987845581365988527549373552036103980380460119398337457819050480022405702325635582620236066168807184261870584892432597683277669260204163001806232850994074559052885958077900805983585439963419680319621217850405971289333030803245070840561728370555174569443676693629170452149296065798196661572238035681751946495873207469100150493032277188951439284275065790528306049503847529562489086229780168252138484384622224460015690956455991882709903488025930330456108229822033526376707136090265975193250434767826227728688689631822571110448349847083887734391639427413322727296020796085661840741564416933944834885347677704020625164362236290082483231096646670146316488035415210816619742524561606952935611302947966659440338951555748352481673455328318110092907812432976349828140055049776760942184789064042974347999533186945347522493599199813729152746600124370793863684351800627532861582603373243844541669894180917405990955855670211102417040532303109059148651080538307108200472206951864724440163912445823502524921620535906589683568560322180265439851314707032130422408981737587067461745778054108010454979688805716669890106223718629918609636282362876953861912714996254991032203811132391157099002202347885731138448079694323323449229027719621743895573011766662593894349081522104383894908548239240269319053774558041228754281281816861897527545504098214377454609550129806936928314745701910920161391616609369496032529549582045082542643910019366151847658440920119593061651167368561688293227455295170854030179178723762426736301386023622466277453636011514339531108046811378554467570571147700293987047007133169604516470460363030434395212791168390261169656611459540138630944243057585634982081359365277395087425491626723439059966600654655183801562224994052115182662706659658702893140791266483454391692605083442515414863001025232435847470731267136086799620306370560, 1090748135619415929462984244733782862448264161996232692431832786189721331849119295216264234525201987223957291796157025273109870820177184063610979765077554717727193825132424258268072070423477350441019325238935081369672808088954075376607323183064685826513719267367765025669297838401423262150842341357600244555889201894556085847866483922724148646867108659100934137092282466892797007055681424336981376513709740535026193493673249209257320971410979203369564857482654510028075971351626483674957465557609650341383284243352703413714646767970869719760282612297099758526022496503350912508240831354915423886988443810272342344732317150627439462977141579914873924393499344568782246440509166066283446893682365040319921619212785451204784909812620149202475072920645750021639932387054565814599265491865025466591172979897528545547657398713095194110513475640015533832552892834462456004562452971528736770337713855531343214788202807563614479213467081621550379582167079624431075961285990652132534019881887236124261807921871717536754538527881569172145267614894322853623609813920928459120198997814593256579843388566344082288016681611654470716138650900737275301237931416801181903989453821932064570156865659395968836640923032250896569702084633936822519618352768176774084397451792927718879958100081887861393908320621408161687515022883010853676704976685223953947630891854814753738450680771222651381548932686869654811143303224385700414066978115266169823947267240120243654344301634559922544942816043553794364709175132165894258852632905428043741747989065584385717223677332433400389608789558933209058517367950612903452919800029473576992005403338790727107551494317528931418468321870206715879080915763252955490226179218331260318126443739420462473525613282748278965996483750636045783491802222016697761633212650864259383149056931239290285624805626122759894380826805436467577805724137767574570906567601847329444596436887515074101490955904440736746378578909097694701009073306364306371857928229086986807866811037349498795349771504573858928341772320617473445645992985275412333509090804871751065163475735116124159825908647121640421907667647356208564338125924147715960797202874727558317522397417637853954101630500329587808124225607721416501990667502342789749660037118355919877562034711995165307625661050344070739613757088494470672876611099532221420366583803436275263239830405586791170387133117796852392016463145034898659808641129024904249424733643211466577601264042611135606503976088487910839773519358050959360, 1090748135619415929462984244733782862448264161996232692431832786189721331849119295216264234525201987223957291796157025273109870820177184063610979765077554799078906298842192989538609825228048205159696851613591638196771886542609324560121290553901886301017900252535799917200010079600026535836800905297805880952344434142288520078948840015587307354938660586662128298270350249817014271693665765110592008613298778505422237692146259873858659415573867216038413367887863225808775353059030740090896360912642226573857037049962736349533220384817969976483149973107413139227644176078619320341055567499174066505299371568329139777241183089138566334553194650577629094056611619967969653726624148744303488035402293152604489486492100208017863024726771025350917773611238726097375366394777344426511988513556879991178832915713510549481697173215445101845957529458649240419039109240935740910191672068265273719092589036748465496772589128171977093240953165534992672018013618814995161462309538660641385783569275376409313809965475889555022982121273477969648053452876833585167683334003690463172464081216829623878909681066796095037273252169666759578152053991219528513242729480885311699333643283995611022633415058770494955457423321606395672379513094283755488117583208734138564299317466532948220527445976808475956204587074983904100207162912865380688486391072610835612762060729181212793646168221753156439697858063620473480211440842709029593612453629476963272918555621144668718781463666529288238422362202825387580631554852164914519052059660040464663126781487560119934326441860936571324105415002310162950779332518014848112844743427605942506544050522057943770995582957029023526909557365112077631459260712531564908022807631888258826691914906113986248716550085419858013381711311649991056871703624067763554136461504317273126870747233315465647396625310067987550217403326963292546153158772672740041967708838522805761174003091611777775043411335156923698959839678510230832295163313316789267444620224432518792403169045198033711681799380593647401842461843648423716417664365528718045683794601856283379413891052412969460121927658025990683597601528175797008376299141662638078090891860989403913605461823884961828737140171022361679405979038786444181270716007518309822554612689912150227475032388745809549109277022071797772295031123798251651255599727407916691739326020171853970956314931166813991316312725113081108713697206841284865031993483234062808071776305097470274820616405375977422257119466656882704639478857686056960, 1090748135619415929462984244733782862448264161996232692431832786189721331849119295216264234525201987223957291796157025273109870820177184063610979765077554799078906298842192989538609825228048205159696851613591638196771886542609324560121290553901886301017900252535799917200010079600026535836800905297805880952350501630195475653911005312364560014847426035293551245843928918752768696279344088055617515694349945406677825140814900616105920256438504578013326493565836047242407382442812245131517757519164899226365743722432277368075027627883045206501792761700945699168497257879683851737049996900961120515655050115561271491492481590583927528068362121611832823090350947768974356780606151520143159909137700592185973126172549006476832634892320043175548198813118732027663641737580234180498216659031323755528672469578345747574178638520542422428423677558820978627530386229456967934723788568179648262880758976714398711940255399001607683329891312982140614519561421728861174053416163557141099001227260702498594974247602767107850237371185829184296776123032637607387534110972932388406207584762847633426555552446542114214004891266591088458003495784055858294944168684601688858744297754455478086944868426545830699462053020840665064540392958400443325645527374926882973919246656771539390355706463348469275233864897316857752844929570354333768590343841311070850781091725431885844774325016901949773780261558722409401181833978850211680880235006737620395003207721429913359698783128999341087064869360477360260946612352621282830392338045342868360685801099549739965616135919539306625022788065057280252729962269737132309764754628744321772059641657719823547449320592935611616099240742902136329711517410404030324521840342033994485065200736874265167184988389293259882587602113424959054628993094268364393026247954669688793470940786540624498332650203138482502473546445070830271563685172304095213304349600298515635788989580172037008658825732196098316200861698353829406714272630544531590748563008319858775677970324879375646607814716537093794936528532510075217655406621358266156154358999433998158724863016801311862884415003624026624271858216959376261551815071325789099581359312420237157949795754513740566131017746235944565634476856040075065074597078314422621893894702231993235077806982696786165968173125570545073461288474360408005636640266535246648614607443110206856314723120840607763815821602035459921424929857198102394553285216706183381968298312489240849692137274288006245419386744015437915115941622091612160, 1090748135619415929462984244733782862448264161996232692431832786189721331849119295216264234525201987223957291796157025273109870820177184063610979765077554799078906298842192989538609825228048205159696851613591638196771886542609324560121290553901886301017900252535799917200010079600026535836800905297805880952350501630195475653911005312364560014847426035293551245843928918752768696279344088055617515694349945406677825140814900616105920256438504578013326493565836047242407382442812245131517757519164899226365743722432277368075027627883045206501792761700945699168497257879683851737049996900961120515655050115561271491492515342105748966629547032786321505730828430221664970324396138635251626409516168005427623435996308921691446181187406395310665404885739434832877428167407495370993511868756359970390117021823616749458620969857006263612082706715408157066575137281027022310927564910276759160520878304632411049364568754920967322982459184763427383790272448438018526977764941072715611580434690827459339991961414242741410599117426060556483763756314527611362658628383368621157993638020878537675545336789915694234433955666315070087213535470255670312004130725495834508357439653828936077080978550578912967907352780054935621561090795845172954115972926435488646325407501512365848213380395168763512806429730109607098577644744240048503459529594006823631373147762011780218660740030215430505248911586325182120160839367048207709418842650690943826010989109302792718425868852384783378651199618535121913835737651699662333815683378345818068070160548347800369481364172406204671458973952634913932812733482191175501628465349005403383205634207163186366050321349674463279843106828789837369958673440743379029655723491233599261110682223445532527992025505094106028374148434683256837486589543018181873279720349434704460879700399438016504650780473547823239120431423814382915239771713285086798751923825359346515261480728322427217167293613096521198247560588729708788376007087530154941809492620352947595475014394229254625965054086766970439573627357949092810593883736061141168581582787315634913260797956280083967967201275577888581524322407185240031043931510925713450658807511908275263101371880394716465807521940885628037330976885109586390268456528362201664202524947917653322271271470730573883899274644538470640093205628124760082118516398285556726512915645798229781241791101398278815512033744564071010914628794915292515492524789530849844709747037539932187090270337487885794730917151571753381797325072561602560]
lemma repeated_halves_get (w n j : ℕ) (hw : 0 < w) (hj : j < (w + w) * n) :
    (((BitVec.allOnes w) ++ (0 : BitVec w)).replicate n).getLsbD j =
      decide (j / w % 2 = 1) := by
  rw [BitVec.getLsbD_replicate]
  simp only [hj, decide_true, Bool.true_and, BitVec.getLsbD_append,
    BitVec.getLsbD_allOnes]
  have hm : j % (w + w) < w + w := Nat.mod_lt _ (by omega)
  have hd : j % (w + w) / w = j / w % 2 := by
    simpa [Nat.mul_two] using Nat.mod_mul_right_div_self j w 2
  by_cases h : j % (w + w) < w
  · rw [ite_eq_left h]
    have hz : j / w % 2 = 0 := hd.symm.trans (Nat.div_eq_of_lt h)
    simp [hz]
  · rw [ite_eq_right h]
    have hone : j % (w + w) / w = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    have he : j / w % 2 = 1 := hd.symm.trans hone
    simp [he, show j % (w + w) - w < w by omega]

lemma column_width (p : Fin 13) :
    (2 ^ p.val + 2 ^ p.val) * 2 ^ (12 - p.val) = 8192 := by
  fin_cases p <;> rfl

def periodicColumn (p : Fin 13) : Table :=
  (((BitVec.allOnes (2 ^ p.val)) ++ (0 : BitVec (2 ^ p.val))).replicate
    (2 ^ (12 - p.val))).cast (column_width p)

lemma periodicColumn_read (j : Fin 8192) (p : Fin 13) :
    readTable j (periodicColumn p) = sample j p := by
  unfold readTable periodicColumn sample
  rw [BitVec.getLsbD_cast]
  rw [repeated_halves_get _ _ _ (Nat.two_pow_pos _) (by rw [column_width]; exact j.isLt)]
  exact Nat.testBit_eq_decide_div_mod_eq.symm

def periodicInputs : List Table := List.ofFn periodicColumn

set_option maxRecDepth 65536 in
set_option maxHeartbeats 20000000 in
lemma periodicInputs_eq : periodicInputs = inputs := by
  decide +kernel

lemma inputTables : ∀ j : Fin 8192, List.ofFn (sample j) = inputs.map (readTable j) := by
  intro j
  rw [← periodicInputs_eq]
  simp only [periodicInputs, List.map_ofFn]
  apply congrArg (fun f : Fin 13 → Bool => List.ofFn f)
  funext p
  exact (periodicColumn_read j p).symm


lemma table_ext (a b : Table) (h : ∀ j, readTable j a = readTable j b) : a = b := by
  apply BitVec.eq_of_getLsbD_eq
  exact fun i hi => h ⟨i,hi⟩

lemma getD_table (x : Fin 8192) (ws : List Table) (i : ℕ) :
    (ws.map (readTable x)).getD i false = readTable x (ws.getD i 0) := by
  by_cases hi : i < ws.length
  · simp [List.getD_eq_getElem?_getD, hi]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
    simp [readTable]

def gateTable (ws : List Table) (g : Gate) : Table :=
  match g.op, g.inputs with
  | .and, [] => ~~~0
  | .and, [i] => ws.getD i 0
  | .and, i :: j :: _ => ws.getD i 0 &&& ws.getD j 0
  | .or, [] => 0
  | .or, [i] => ws.getD i 0
  | .or, i :: j :: _ => ws.getD i 0 ||| ws.getD j 0
  | .not, [] => ~~~0
  | .not, i :: _ => ~~~(ws.getD i 0)
  | _, _ => 0

lemma read_gateTable (x : Fin 8192) (ws : List Table) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    g.op.eval (g.inputs.map fun i => (ws.map (readTable x)).getD i false) =
      readTable x (gateTable ws g) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only [getD_table]
  cases op with
  | and =>
    match ins, hlen with
    | [], _ =>
      change true = readTable x (~~~0)
      simp only [read_not, read_zero, Bool.not_false]
    | [i], _ => simp [gateTable, GateOp.eval]
    | [i, j], _ => simp [gateTable, GateOp.eval, readTable]
    | _ :: _ :: _ :: _, h => simp at h
  | or =>
    match ins, hlen with
    | [], _ => simp [gateTable, GateOp.eval, readTable]
    | [i], _ => simp [gateTable, GateOp.eval]
    | [i, j], _ => simp [gateTable, GateOp.eval, readTable]
    | _ :: _ :: _ :: _, h => simp at h
  | not =>
    cases ins with
    | nil =>
      change true = readTable x (~~~0)
      simp only [read_not, read_zero, Bool.not_false]
    | cons i is =>
      exact (read_not x (ws.getD i 0)).symm
  | mod m => simp at hop
  | maj => simp at hop

def wireTables (gs : List Gate) (ws : List Table) : List Table :=
  gs.foldl (fun vs g => vs ++ [gateTable vs g]) ws

lemma read_wireTables (x : Fin 8192) (gs : List Gate) (ws : List Table)
    (h : FanInTwo ⟨gs, 0⟩) :
    (Circuit.wires ⟨gs, 0⟩ (ws.map (readTable x))) = (wireTables gs ws).map (readTable x) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    have hg := read_gateTable x ws g (h g List.mem_cons_self)
    change Circuit.wires ⟨gs, 0⟩
        (ws.map (readTable x) ++ [g.op.eval (g.inputs.map fun i =>
          (ws.map (readTable x)).getD i false)]) =
      (wireTables gs (ws ++ [gateTable ws g])).map (readTable x)
    rw [hg, ← List.map_singleton, ← List.map_append]
    exact ih _ (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))

lemma wires_match (C : Circuit) (h : FanInTwo C) (j : Fin 8192) (o : ℕ) :
    (C.wires (List.ofFn (sample j))).getD o false =
    readTable j ((wireTables C.gates inputs).getD o 0) := by
  change (Circuit.wires ⟨C.gates, 0⟩ (List.ofFn (sample j))).getD o false = _
  rw [inputTables, read_wireTables j C.gates inputs h, getD_table]


def encodeVec (x : Fin 13 → Bool) : BitVec 13 :=
  (BitVec.ofBoolListLE (List.ofFn x)).cast (by simp)

def encode (x : Fin 13 → Bool) : Fin 8192 := (encodeVec x).toFin

lemma list_bits {n : ℕ} (x : Fin n → Bool) (p : Fin n) :
    (BitVec.ofBoolListLE (List.ofFn x)).getLsbD p.val = x p := by
  rw [BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem _ _ (by simpa using p.isLt)]
  simp only [List.getElem_ofFn]

lemma sample_encode (x : Fin 13 → Bool) : sample (encode x) = x := by
  funext p
  change (encodeVec x).getLsbD p.val = x p
  rw [encodeVec, BitVec.getLsbD_cast]
  exact list_bits x p

lemma read_inputs (j : Fin 8192) (p : Fin 13) :
    readTable j (inputs.getD p.val 0) = sample j p := by
  have h := congrArg (fun l : List Bool => l.getD p.val false) (inputTables j)
  rw [getD_table] at h
  have hl : (List.ofFn (sample j)).getD p.val false = sample j p := by
    rw [List.getD_eq_getElem _ _ (by simpa using p.isLt)]
    simp only [List.getElem_ofFn]
  exact h.symm.trans hl

lemma read_or (j : Fin 8192) (a b : Table) :
    readTable j (a ||| b) = (readTable j a || readTable j b) := BitVec.getLsbD_or

lemma read_and (j : Fin 8192) (a b : Table) :
    readTable j (a &&& b) = (readTable j a && readTable j b) := BitVec.getLsbD_and

def countTable : List Table → ℕ → Table
  | [], 0 => ~~~0
  | [], _ + 1 => 0
  | a :: xs, 0 => countTable xs 0 &&& a
  | a :: xs, k + 1 =>
    (countTable xs (k + 1) &&& a) ||| (countTable xs k &&& ~~~a)

lemma read_countTable (j : Fin 8192) (xs : List Table) (k : ℕ) :
    readTable j (countTable xs k) = decide ((xs.map (readTable j)).count false = k) := by
  induction xs generalizing k with
  | nil =>
    cases k with
    | zero =>
      change readTable j (~~~0) = true
      rw [read_not, read_zero]
      rfl
    | succ k => exact read_zero j
  | cons a xs ih =>
    cases k <;> cases h : readTable j a <;>
      simp [countTable, read_or, read_and, read_not, ih, h, List.count_cons]

lemma count_false_sum (xs : List Bool) :
    xs.count false = (xs.map (fun b => if b = false then 1 else 0)).sum := by
  induction xs with
  | nil => rfl
  | cons b xs ih => cases b <;> simp [ih, Nat.add_comm]

lemma count_false_ofFn {n : ℕ} (x : Fin n → Bool) :
    (List.ofFn x).count false = (Finset.univ.filter (fun p => x p = false)).card := by
  rw [count_false_sum, List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_def]
  exact Finset.sum_boole _ _

lemma read_band_count (inputs : List Table) (sample : Fin 8192 → Fin 13 → Bool)
    (hinputs : ∀ j : Fin 8192, List.ofFn (sample j) = inputs.map (readTable j))
    (j : Fin 8192) :
    readTable j (countTable inputs 5 ||| countTable inputs 6) =
      decide ((Finset.univ.filter (fun p : Fin 13 => sample j p = false)).card = 5 ∨
        (Finset.univ.filter (fun p : Fin 13 => sample j p = false)).card = 6) := by
  rw [read_or, read_countTable, read_countTable, ← hinputs j, count_false_ofFn]
  simp


def targetTable (w : Fin 13) : Table :=
  inputs.getD w.val 0 ||| inputs.getD (1 + w).val 0 |||
    inputs.getD (3 + w).val 0 ||| inputs.getD (9 + w).val 0

lemma target_read (j : Fin 8192) (w : Fin 13) :
    readTable j (targetTable w) =
      decide (∃ p ∈ (({0, 1, 3, 9} : Finset (Fin 13)).image (fun u => u + w)),
        sample j p = true) := by
  simp only [targetTable, read_or, read_inputs]
  apply Bool.eq_iff_iff.mpr
  simp [Finset.mem_image, or_assoc]

def bandTable : Table := 253963482093500741048171002881345291100833901725786740745400765124991330254168356485675455298333386261325701389070121129673281789489992184358608508524252914048695625728158324809120147893945895088671692975769836152052710367517742148886212013731404478204326866209674687544976739469585088819937663882383649856985397424015822795808608558952657677376232849335896184850618888043784566387058420556326102990227166514875444307681862443227338985169698031261968251760792981998927517210027441164036457158774855962213437548689155857574415809173027318171095760784465803227896257858032156752193843249797134955321944026563108776147899084871723638891047885592515312125548528044629827458297315772464526687962864100273968400996314443033471294269524165803089389602465461587020773083683995792483813070341440156881175460873118677662365979821733268404564827908985241599524929716663430201765852107199207953070090819874082194852077159509527376853306675643054504156972517461910607562230351929906146738795699037630916664204905921388111472604566695860908746733934454488215966445511969060242956097808283183809941493835885468497831548852708491716974058644975417543620626269023735503354285710556565477200237192011813788507928705957363451506063194277392665333863436092384898690535382980810357787509256834347532606505855674427656493753610727694588016688424396166182279172072968304887422265106750497791924160705039416252502550660166152210686093278219104344238657511837359569462617744160109523533278618122881193352208770634137186992164364420445944335354599273324579558030471046062210203378743249932043886875075617738358795894949102965974126327458777108585726864914974068512286745831108997763038970999665579236685470297067388115809751212678003117945992921715677035715724414160479631803157840021209633026120599875862796671027771481289361170851870461949350473740261724775048940672381189067439532740117254822599076333851863159685262748365080823278956832825961384778784177511479628273131897072853260756999435472052148650519018673210647935586597734569910145348599318219267390457662466217148290010995683512361404484195690430089361644366947685329031681966074688851560706497024163946853825346047751740498799163686135697271154795041591999846771362044920923470654266278657701526635135305350344134538184798470678000604215877775929259144807353756082076249181181362084619882524377818349122048696483892278553359710741336922041077898411751700366557480277212510474153435826245741533998309720530299910833045504

set_option maxRecDepth 12000 in
set_option maxHeartbeats 12000000 in
lemma band_value : bandTable = countTable inputs 5 ||| countTable inputs 6 := by
  decide +kernel

lemma band_read (j : Fin 8192) : readTable j bandTable =
    decide ((Finset.univ.filter (fun p : Fin 13 => sample j p = false)).card = 5 ∨
      (Finset.univ.filter (fun p : Fin 13 => sample j p = false)).card = 6) := by
  rw [band_value]
  exact read_band_count inputs sample inputTables j

lemma validate (gs : List Gate) (out : Fin 13 → ℕ) (hg : FanInTwo ⟨gs, 0⟩)
    (hc : ∀ w : Fin 13,
      (wireTables gs inputs).getD (out w) 0 &&& bandTable = targetTable w &&& bandTable) :
    ∀ (w : Fin 13) (x : Fin 13 → Bool),
      ((Finset.univ.filter (fun p : Fin 13 => x p = false)).card = 5 ∨
        (Finset.univ.filter (fun p : Fin 13 => x p = false)).card = 6) →
      Circuit.eval ⟨gs, out w⟩ (List.ofFn x) =
        decide (∃ p ∈ (({0, 1, 3, 9} : Finset (Fin 13)).image (fun u => u + w)),
          x p = true) := by
  intro w x hx
  have hbit := congrArg (readTable (encode x)) (hc w)
  simp only [read_and] at hbit
  have hb : readTable (encode x) bandTable = true := by
    rw [band_read, sample_encode]
    exact decide_eq_true hx
  rw [hb, Bool.and_true, Bool.and_true, target_read, sample_encode] at hbit
  have he := wires_match ⟨gs, 0⟩ hg (encode x) (out w)
  rw [sample_encode] at he
  exact he.trans hbit

def benchmarkGates : List Gate :=
  [⟨GateOp.or, [0, 1]⟩,
   ⟨GateOp.or, [13, 3]⟩,
   ⟨GateOp.or, [14, 9]⟩,
   ⟨GateOp.or, [1, 2]⟩,
   ⟨GateOp.or, [16, 4]⟩,
   ⟨GateOp.or, [17, 10]⟩,
   ⟨GateOp.or, [2, 3]⟩,
   ⟨GateOp.or, [19, 5]⟩,
   ⟨GateOp.or, [20, 11]⟩,
   ⟨GateOp.or, [3, 4]⟩,
   ⟨GateOp.or, [22, 6]⟩,
   ⟨GateOp.or, [23, 12]⟩,
   ⟨GateOp.or, [4, 5]⟩,
   ⟨GateOp.or, [25, 7]⟩,
   ⟨GateOp.or, [26, 0]⟩,
   ⟨GateOp.or, [5, 6]⟩,
   ⟨GateOp.or, [28, 8]⟩,
   ⟨GateOp.or, [29, 1]⟩,
   ⟨GateOp.or, [6, 7]⟩,
   ⟨GateOp.or, [31, 9]⟩,
   ⟨GateOp.or, [32, 2]⟩,
   ⟨GateOp.or, [7, 8]⟩,
   ⟨GateOp.or, [34, 10]⟩,
   ⟨GateOp.or, [35, 3]⟩,
   ⟨GateOp.or, [8, 9]⟩,
   ⟨GateOp.or, [37, 11]⟩,
   ⟨GateOp.or, [38, 4]⟩,
   ⟨GateOp.or, [9, 10]⟩,
   ⟨GateOp.or, [40, 12]⟩,
   ⟨GateOp.or, [41, 5]⟩,
   ⟨GateOp.or, [10, 11]⟩,
   ⟨GateOp.or, [43, 0]⟩,
   ⟨GateOp.or, [44, 6]⟩,
   ⟨GateOp.or, [11, 12]⟩,
   ⟨GateOp.or, [46, 1]⟩,
   ⟨GateOp.or, [47, 7]⟩,
   ⟨GateOp.or, [12, 0]⟩,
   ⟨GateOp.or, [49, 2]⟩,
   ⟨GateOp.or, [50, 8]⟩]

def benchmarkOut (w : Fin 13) : ℕ := 15 + 3 * w.val

set_option maxRecDepth 65536 in
set_option maxHeartbeats 20000000 in
lemma benchmark_tables : ∀ w : Fin 13,
    (wireTables benchmarkGates inputs).getD (benchmarkOut w) 0 &&& bandTable =
      targetTable w &&& bandTable := by
  decide +kernel

lemma benchmark_fanin : FanInTwo ⟨benchmarkGates, 0⟩ := by
  intro g hg
  simp only [benchmarkGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

lemma benchmark_valid : ∀ (w : Fin 13) (x : Fin 13 → Bool),
    ((Finset.univ.filter (fun p : Fin 13 => x p = false)).card = 5 ∨
      (Finset.univ.filter (fun p : Fin 13 => x p = false)).card = 6) →
    Circuit.eval ⟨benchmarkGates, benchmarkOut w⟩ (List.ofFn x) =
      decide (∃ p ∈ (({0, 1, 3, 9} : Finset (Fin 13)).image (fun u => u + w)),
        x p = true) := by
  exact validate benchmarkGates benchmarkOut benchmark_fanin benchmark_tables

end PEqualNP.Outside.L_meta_1024_aux.Tables



namespace PEqualNP.Outside.L_meta_1024_aux.CrossContext

open PEqualNP.Outside.L_meta_1024_aux.Minterms

lemma residual_subset_of_small_union
    (f : Finset (Fin 13) → Bool) (L M R T : Finset (Fin 13))
    (hmono : Increasing f) (hband : BandSpec f L)
    (hT : T ⊆ M) (hsmall : (R ∪ T).card ≤ 6)
    (htrue : f (R ∪ T) = true) : L \ R ⊆ L ∩ M := by
  have hcontains := low_true_contains f L hmono hband (R ∪ T) hsmall htrue
  intro p hp
  obtain ⟨hpL, hpR⟩ := Finset.mem_sdiff.mp hp
  refine Finset.mem_inter.mpr ⟨hpL, ?_⟩
  rcases Finset.mem_union.mp (hcontains hpL) with h | h
  · exact (hpR h).elim
  · exact hT h

lemma missing_at_most_one
    (f : Finset (Fin 13) → Bool) (L M R T : Finset (Fin 13))
    (hmono : Increasing f) (hband : BandSpec f L)
    (hL : L.card = 4) (hM : M.card = 4)
    (hinter : (L ∩ M).card ≤ 1) (hR : R ⊆ L) (hT : T ⊆ M)
    (htrue : f (R ∪ T) = true) : (L \ R).card ≤ 1 := by
  by_contra! hmissing
  have hpartition := Finset.card_sdiff_add_card_eq_card hR
  have hRcard : R.card ≤ 2 := by omega
  have hTcard := Finset.card_le_card hT
  have hcard := Finset.card_union_le R T
  have hsmall : (R ∪ T).card ≤ 6 := by omega
  have hsub := residual_subset_of_small_union f L M R T hmono hband hT hsmall htrue
  have hbound := Finset.card_le_card hsub
  omega

lemma missing_point_in_other_of_small_union
    (f : Finset (Fin 13) → Bool) (L M R T : Finset (Fin 13))
    (hmono : Increasing f) (hband : BandSpec f L)
    (hT : T ⊆ M) (hsmall : (R ∪ T).card ≤ 6)
    (htrue : f (R ∪ T) = true) (p : Fin 13) (hp : p ∈ L \ R) : p ∈ M := by
  exact (Finset.mem_inter.mp
    (residual_subset_of_small_union f L M R T hmono hband hT hsmall htrue hp)).2

end PEqualNP.Outside.L_meta_1024_aux.CrossContext



namespace PEqualNP.Outside.L_meta_1024_aux.Global

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
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

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
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  · rw [if_pos h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hl, h]
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

lemma gate_cases {X : Type} (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : g.inputs.length ≤ 2) (f : X → ℕ → Bool) (z : X) :
    (∀ y, g.op.eval (g.inputs.map (f y)) = false) ∨
    ∃ a b, g.op.eval (g.inputs.map (f z)) = false →
      (f z a = false ∧ f z b = false ∧
        ∀ y, g.op.eval (g.inputs.map (f y)) = true → f y a = true ∨ f y b = true) := by
  obtain ⟨op, ins⟩ := g
  simp only at hop hlen ⊢
  match ins, hlen with
  | [], _ =>
    rcases hop with rfl | rfl
    · right
      exact ⟨0, 0, by simp [GateOp.eval]⟩
    · left
      simp [GateOp.eval]
  | [a], _ =>
    right
    refine ⟨a, a, ?_⟩
    rcases hop with rfl | rfl <;> simp [GateOp.eval]
  | [a, b], _ =>
    rcases hop with rfl | rfl
    · right
      by_cases h : f z a = false
      · refine ⟨a, a, ?_⟩
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          Bool.and_true, id_eq, Bool.and_eq_true]
        intro _
        exact ⟨h, h, fun y hy => Or.inl hy.1⟩
      · refine ⟨b, b, ?_⟩
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          Bool.and_true, id_eq, Bool.and_eq_true]
        intro hz
        have hb : f z b = false := by
          cases ha : f z a <;> cases hb : f z b <;> simp_all
        exact ⟨hb, hb, fun y hy => Or.inl hy.2⟩
    · right
      refine ⟨a, b, ?_⟩
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        Bool.or_false, id_eq, Bool.or_eq_true, Bool.or_eq_false_iff]
      intro hz
      exact ⟨hz.1, hz.2, fun y hy => hy⟩
  | _ :: _ :: _ :: _, h => simp at h

def Zof {n : ℕ} (S : Finset (Fin n)) : Fin n → Bool := fun c => decide (c ∉ S)

def eof {n : ℕ} (u : Fin n) : Fin n → Bool := fun c => decide (c = u)

def Inv {n : ℕ} (S : Finset (Fin n)) (gs : List Gate) (l : Fin n → Fin n) : Prop :=
  ∀ i u v, val gs (Zof S) i = false → val gs (eof u) i = true → val gs (eof v) i = true →
    u ∈ S ∧ l u = l v

def Cnt {n : ℕ} (S : Finset (Fin n)) (gs : List Gate) (i : ℕ) : Prop :=
  val gs (Zof S) i = false ∧
    ∃ u v : Fin n, u ≠ v ∧ val gs (eof u) i = true ∧ val gs (eof v) i = true

open Classical in
noncomputable def D {n : ℕ} (S : Finset (Fin n)) (gs : List Gate) : Finset ℕ :=
  (Finset.Ico n (n + gs.length)).filter fun i => Cnt S gs i

lemma D_mono {n : ℕ} (S : Finset (Fin n)) (gs : List Gate) (g : Gate) :
    D S gs ⊆ D S (gs ++ [g]) := by
  classical
  intro i hi
  simp only [D, Finset.mem_filter, Finset.mem_Ico, List.length_append, List.length_cons,
    List.length_nil] at hi ⊢
  refine ⟨⟨hi.1.1, by omega⟩, ?_⟩
  have hne : i ≠ n + gs.length := by omega
  obtain ⟨hz, u, v, huv, hu, hv⟩ := hi.2
  refine ⟨?_, u, v, huv, ?_, ?_⟩
  · rw [val_snoc, if_neg hne]; exact hz
  · rw [val_snoc, if_neg hne]; exact hu
  · rw [val_snoc, if_neg hne]; exact hv

lemma main_inv {n : ℕ} (S : Finset (Fin n)) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∃ l : Fin n → Fin n, Inv S gs l ∧ S.card ≤ (S.image l).card + (D S gs).card := by
  classical
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨id, ?_, by simp⟩
    intro i u v hz hu hv
    rw [val_nil] at hz hu hv
    by_cases h : i < n
    · simp only [h, dite_true, Zof, eof, decide_eq_false_iff_not, not_not,
        decide_eq_true_eq] at hz hu hv
      subst hu
      subst hv
      exact ⟨hz, rfl⟩
    · simp [h] at hu
  | append_singleton gs g ih =>
    obtain ⟨l, hinv, hcard⟩ := ih (fun g' hg' => hg g' (by simp [hg']))
    obtain ⟨hop, hlen⟩ := hg g (by simp)
    set N := n + gs.length with hN
    set P : (Fin n → Bool) → Bool := fun x => g.op.eval (g.inputs.map fun j => val gs x j)
      with hP
    have hnew : ∀ x : Fin n → Bool, val (gs ++ [g]) x N = P x := by
      intro x
      rw [val_snoc, if_pos hN]
    have hold : ∀ (x : Fin n → Bool) (i : ℕ), i ≠ N → val (gs ++ [g]) x i = val gs x i := by
      intro x i hi
      rw [val_snoc, if_neg hi]
    -- facts about the new wire from the old invariant
    have key : P (Zof S) = false → ∀ u, P (eof u) = true →
        u ∈ S ∧ ∃ A B : Fin n → Prop, (∀ w, P (eof w) = true → A w ∨ B w) ∧
          (∀ w w', A w → A w' → l w = l w') ∧ (∀ w w', B w → B w' → l w = l w') := by
      intro hz u hu
      rcases gate_cases g hop hlen (fun x j => val gs x j) (Zof S) with hall | ⟨a, b, hab⟩
      · have := hall (eof u)
        simp only [hP] at hu
        rw [this] at hu
        exact absurd hu (by simp)
      · obtain ⟨ha, hb, hy⟩ := hab hz
        refine ⟨?_, fun w => val gs (eof w) a = true, fun w => val gs (eof w) b = true,
          fun w hw => hy (eof w) hw, fun w w' hw hw' => (hinv a w w' ha hw hw').2,
          fun w w' hw hw' => (hinv b w w' hb hw hw').2⟩
        rcases hy (eof u) hu with h | h
        · exact (hinv a u u ha h h).1
        · exact (hinv b u u hb h h).1
    by_cases hm : P (Zof S) = false ∧ ∃ u v, P (eof u) = true ∧ P (eof v) = true ∧ l u ≠ l v
    · obtain ⟨hz, u0, v0, hu0, hv0, hne⟩ := hm
      refine ⟨fun w => if l w = l v0 then l u0 else l w, ?_, ?_⟩
      · intro i u v hiz hiu hiv
        by_cases hi : i = N
        · subst hi
          rw [hnew] at hiz hiu hiv
          obtain ⟨huS, A, B, hAB, hA, hB⟩ := key hiz u hiu
          refine ⟨huS, ?_⟩
          have two : ∀ w, P (eof w) = true → l w = l u0 ∨ l w = l v0 := by
            intro w hw
            rcases hAB w hw with h | h <;> rcases hAB u0 hu0 with h0 | h0 <;>
              rcases hAB v0 hv0 with h1 | h1
            · exact Or.inl (hA w u0 h h0)
            · exact Or.inl (hA w u0 h h0)
            · exact Or.inr (hA w v0 h h1)
            · exact absurd (hB u0 v0 h0 h1) hne
            · exact absurd (hA u0 v0 h0 h1) hne
            · exact Or.inr (hB w v0 h h1)
            · exact Or.inl (hB w u0 h h0)
            · exact Or.inl (hB w u0 h h0)
          have red : ∀ w, P (eof w) = true → (if l w = l v0 then l u0 else l w) = l u0 := by
            intro w hw
            rcases two w hw with h | h
            · rw [h]; split_ifs <;> rfl
            · rw [if_pos h]
          show (if l u = l v0 then l u0 else l u) = (if l v = l v0 then l u0 else l v)
          rw [red u hiu, red v hiv]
        · rw [hold _ _ hi] at hiz hiu hiv
          obtain ⟨huS, hl⟩ := hinv i u v hiz hiu hiv
          refine ⟨huS, ?_⟩
          show (if l u = l v0 then l u0 else l u) = (if l v = l v0 then l u0 else l v)
          rw [hl]
      · have himg : S.image l ⊆
            insert (l v0) (S.image fun w => if l w = l v0 then l u0 else l w) := by
          intro y hy
          obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
          by_cases h : l w = l v0
          · rw [h]; exact Finset.mem_insert_self _ _
          · refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨w, hw, ?_⟩)
            rw [if_neg h]
        have h1 : (S.image l).card ≤
            (S.image fun w => if l w = l v0 then l u0 else l w).card + 1 :=
          (Finset.card_le_card himg).trans (Finset.card_insert_le _ _)
        have hNin : N ∈ D S (gs ++ [g]) := by
          simp only [D, Finset.mem_filter, Finset.mem_Ico, List.length_append,
            List.length_cons, List.length_nil]
          refine ⟨⟨by omega, by omega⟩, ?_, u0, v0, ?_, ?_, ?_⟩
          · rw [hnew]; exact hz
          · intro h; exact hne (by rw [h])
          · rw [hnew]; exact hu0
          · rw [hnew]; exact hv0
        have hNnot : N ∉ D S gs := by
          simp only [D, Finset.mem_filter, Finset.mem_Ico]
          intro h
          omega
        have h2 : (D S gs).card + 1 ≤ (D S (gs ++ [g])).card := by
          rw [← Finset.card_insert_of_notMem hNnot]
          apply Finset.card_le_card
          intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hi
          · exact hNin
          · exact D_mono S gs g hi
        omega
    · refine ⟨l, ?_, ?_⟩
      · intro i u v hiz hiu hiv
        by_cases hi : i = N
        · subst hi
          rw [hnew] at hiz hiu hiv
          obtain ⟨huS, -⟩ := key hiz u hiu
          refine ⟨huS, ?_⟩
          by_contra hne
          exact hm ⟨hiz, u, v, hiu, hiv, hne⟩
        · rw [hold _ _ hi] at hiz hiu hiv
          exact hinv i u v hiz hiu hiv
      · have := Finset.card_le_card (D_mono S gs g)
        omega

lemma family_bound : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin m) (x : Fin n → Bool), (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x)) = decide (∃ v ∈ S w, x v = true)) → ∑ w, ((S w).card - 1) ≤ gates.length := by
  classical
  intro n m S hS gates out hg hev
  have hval : ∀ (w : Fin m) (x : Fin n → Bool),
      val gates x (out w) = decide (∃ v ∈ S w, x v = true) := fun w x => hev w x
  have hZ : ∀ w, val gates (Zof (S w)) (out w) = false := by
    intro w
    rw [hval]
    simp [Zof]
  have hE : ∀ w, ∀ u ∈ S w, val gates (eof u) (out w) = true := by
    intro w u hu
    rw [hval]
    simp only [decide_eq_true_eq]
    exact ⟨u, hu, by simp [eof]⟩
  choose l hinv hcard using fun w => main_inv (S w) gates hg
  have hbound : ∀ w, (S w).card - 1 ≤ (D (S w) gates).card := by
    intro w
    have h1 : ((S w).image (l w)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
      exact (hinv w (out w) u v (hZ w) (hE w u hu) (hE w v hv)).2
    have := hcard w
    omega
  have hdisj : ∀ a ∈ (Finset.univ : Finset (Fin m)), ∀ b ∈ (Finset.univ : Finset (Fin m)),
      a ≠ b → Disjoint (D (S a) gates) (D (S b) gates) := by
    intro a _ b _ hab
    rw [Finset.disjoint_left]
    intro i hia hib
    simp only [D, Finset.mem_filter, Finset.mem_Ico] at hia hib
    obtain ⟨-, hza, u, v, huv, hu, hv⟩ := hia
    obtain ⟨-, hzb, -⟩ := hib
    have hua := (hinv a i u u hza hu hu).1
    have hva := (hinv a i v v hza hv hv).1
    have hub := (hinv b i u u hzb hu hu).1
    have hvb := (hinv b i v v hzb hv hv).1
    have hsub : ({u, v} : Finset (Fin n)) ⊆ S a ∩ S b := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨hua, hub⟩
      · exact Finset.mem_inter.mpr ⟨hva, hvb⟩
    have h2 : ({u, v} : Finset (Fin n)).card = 2 := Finset.card_pair huv
    have := Finset.card_le_card hsub
    have := hS a b hab
    omega
  calc ∑ w, ((S w).card - 1) ≤ ∑ w, (D (S w) gates).card :=
        Finset.sum_le_sum fun w _ => hbound w
    _ = (Finset.univ.biUnion fun w => D (S w) gates).card :=
        (Finset.card_biUnion hdisj).symm
    _ ≤ (Finset.Ico n (n + gates.length)).card := by
        apply Finset.card_le_card
        intro i hi
        obtain ⟨w, -, hw⟩ := Finset.mem_biUnion.mp hi
        simp only [D, Finset.mem_filter] at hw
        exact hw.1
    _ = gates.length := by simp

def line (w : Fin 13) : Finset (Fin 13) :=
  ({0, 1, 3, 9} : Finset (Fin 13)).image (fun u => u + w)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma line_intersection : ∀ i j : Fin 13, i ≠ j → (line i ∩ line j).card ≤ 1 := by
  decide +kernel

lemma line_card : ∀ w : Fin 13, (line w).card = 4 := by decide +kernel

lemma global_bound (gs : List Gate) (out : Fin 13 → ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (he : ∀ (w : Fin 13) (x : Fin 13 → Bool),
      Circuit.eval ⟨gs, out w⟩ (List.ofFn x) = decide (∃ p ∈ line w, x p = true)) :
    39 ≤ gs.length := by
  have h := family_bound 13 13 line line_intersection gs out hg he
  simpa [line_card] using h

end PEqualNP.Outside.L_meta_1024_aux.Global


namespace PEqualNP.Outside.L_meta_1024_aux.Support

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp

lemma gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l₁ l₂ : List Bool) (hlen : l₁.length = l₂.length)
    (hle : ∀ i, l₁.getD i false = true → l₂.getD i false = true) :
    op.eval l₁ = true → op.eval l₂ = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq]
    intro h b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      have hi1 : i < l₁.length := by omega
      rw [List.getD_eq_getElem _ _ hi1]
      exact h _ (List.getElem_mem hi1)
    have h2 := hle i h1
    rwa [List.getD_eq_getElem _ _ hi] at h2
  · simp only [GateOp.eval, List.any_eq_true, id_eq]
    rintro ⟨b, hb, rfl⟩
    obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      rw [List.getD_eq_getElem _ _ hi]; exact hbi
    have h2 := hle i h1
    have hi2 : i < l₂.length := by omega
    rw [List.getD_eq_getElem _ _ hi2] at h2
    exact ⟨l₂[i], List.getElem_mem hi2, h2⟩

lemma wiresFrom_mono (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w₁ w₂ : List Bool), w₁.length = w₂.length →
      (∀ i, w₁.getD i false = true → w₂.getD i false = true) →
      ∀ i, (wiresFrom gs w₁).getD i false = true → (wiresFrom gs w₂).getD i false = true := by
  induction gs with
  | nil =>
    intro w₁ w₂ _ hle i hi
    exact hle i hi
  | cons g gs ih =>
    intro w₁ w₂ hlen hle i hi
    have hstep1 : wiresFrom (g :: gs) w₁ =
        wiresFrom gs (w₁ ++ [g.op.eval (g.inputs.map fun j => w₁.getD j false)]) := rfl
    have hstep2 : wiresFrom (g :: gs) w₂ =
        wiresFrom gs (w₂ ++ [g.op.eval (g.inputs.map fun j => w₂.getD j false)]) := rfl
    rw [hstep1] at hi
    rw [hstep2]
    apply ih (fun g' hg' => hmono g' (List.mem_cons_of_mem g hg')) _ _ (by simp [hlen]) _ i hi
    intro j hj
    by_cases hlt : j < w₁.length
    · rw [List.getD_append _ _ _ _ hlt] at hj
      rw [List.getD_append _ _ _ _ (by omega)]
      exact hle j hj
    · by_cases heq : j = w₁.length
      · subst heq
        rw [getD_snoc_eq] at hj
        rw [hlen, getD_snoc_eq]
        exact gateOp_eval_mono g.op (hmono g List.mem_cons_self)
          (g.inputs.map fun k => w₁.getD k false) (g.inputs.map fun k => w₂.getD k false)
          (by simp) (by
            intro t ht
            by_cases ht_lt : t < g.inputs.length
            · rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)] at ht
              rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)]
              simp only [List.getElem_map] at ht ⊢
              exact hle _ ht
            · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt ht_lt)] at ht
              exact Bool.noConfusion ht) hj
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
        exact Bool.noConfusion hj


def line (w : Fin 13) : Finset (Fin 13) :=
  ({0, 1, 3, 9} : Finset (Fin 13)).image (fun u => u + w)

def zeroSet (x : Fin 13 → Bool) : Finset (Fin 13) :=
  Finset.univ.filter (fun p => x p = false)

def Band (x : Fin 13 → Bool) : Prop := (zeroSet x).card = 5 ∨ (zeroSet x).card = 6

def target (w : Fin 13) (x : Fin 13 → Bool) : Bool := decide (∃ p ∈ line w, x p = true)

def row (w p : Fin 13) : Bool :=
  decide (p ∉ (({0, 1, 2, 3, 4, 9} : Finset (Fin 13)).image (fun u => u + w)))

def flip (w p q : Fin 13) : Bool := if q = p then true else row w q

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma row_spec : ∀ w : Fin 13, (zeroSet (row w)).card = 6 ∧ target w (row w) = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma flip_spec : ∀ w p : Fin 13, p ∈ line w →
    (zeroSet (flip w p)).card = 5 ∧ target w (flip w p) = true := by
  decide +kernel

def Supports (f : (Fin 13 → Bool) → Bool) (S : Finset (Fin 13)) : Prop :=
  ∀ x y, (∀ p ∈ S, x p = y p) → f x = f y

lemma support_contains_line (w : Fin 13) (f : (Fin 13 → Bool) → Bool)
    (hcorrect : ∀ x, Band x → f x = target w x) (S : Finset (Fin 13))
    (hsupport : Supports f S) : line w ⊆ S := by
  intro p hp
  by_contra hnot
  have hsame : f (row w) = f (flip w p) := by
    apply hsupport
    intro q hq
    have hqp : q ≠ p := by intro he; subst q; exact hnot hq
    simp [flip, hqp]
  rw [hcorrect _ (Or.inr (row_spec w).1),
    hcorrect _ (Or.inl (flip_spec w p hp).1), (row_spec w).2,
    (flip_spec w p hp).2] at hsame
  exact Bool.noConfusion hsame

def fromZeros (Z : Finset (Fin 13)) (p : Fin 13) : Bool := decide (p ∉ Z)

lemma zeroSet_fromZeros (Z : Finset (Fin 13)) : zeroSet (fromZeros Z) = Z := by
  ext p
  simp [zeroSet, fromZeros]

lemma complete_input (S : Finset (Fin 13)) (hS : S.card ≤ 7) (x : Fin 13 → Bool)
    (hz : (S.filter (fun p => x p = false)).card ≤ 6) :
    ∃ y : Fin 13 → Bool, Band y ∧ ∀ p ∈ S, y p = x p := by
  let Z := S.filter (fun p => x p = false)
  have hzc : Z.card ≤ 6 := hz
  have hcomp : 6 ≤ (Finset.univ \ S).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ S)]
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨B, hB, hBc⟩ := Finset.exists_subset_card_eq
    (show 6 - Z.card ≤ (Finset.univ \ S).card by omega)
  have hd : Disjoint Z B := by
    rw [Finset.disjoint_left]
    intro p hpZ hpB
    exact (Finset.mem_sdiff.mp (hB hpB)).2 (Finset.mem_filter.mp hpZ).1
  refine ⟨fromZeros (Z ∪ B), Or.inr ?_, ?_⟩
  · rw [zeroSet_fromZeros, Finset.card_union_of_disjoint hd, hBc]
    omega
  · intro p hpS
    have hpB : p ∉ B := fun h => (Finset.mem_sdiff.mp (hB h)).2 hpS
    cases hx : x p <;> simp [fromZeros, Z, hpS, hpB, hx]

lemma target_eq_of_agree (w : Fin 13) (S : Finset (Fin 13)) (hline : line w ⊆ S)
    (x y : Fin 13 → Bool) (hxy : ∀ p ∈ S, x p = y p) : target w x = target w y := by
  apply Bool.eq_iff_iff.mpr
  simp only [target, decide_eq_true_eq]
  constructor
  · rintro ⟨p, hp, hx⟩
    exact ⟨p, hp, (hxy p (hline hp)).symm.trans hx⟩
  · rintro ⟨p, hp, hy⟩
    exact ⟨p, hp, (hxy p (hline hp)).trans hy⟩

lemma small_support_exact (w : Fin 13) (f : (Fin 13 → Bool) → Bool)
    (hcorrect : ∀ x, Band x → f x = target w x) (hzero : f (fun _ => false) = false)
    (S : Finset (Fin 13)) (hS : S.card ≤ 7) (hsupport : Supports f S) :
    ∀ x, f x = target w x := by
  have hline := support_contains_line w f hcorrect S hsupport
  intro x
  by_cases hz : (S.filter (fun p => x p = false)).card ≤ 6
  · obtain ⟨y, hy, hxy⟩ := complete_input S hS x hz
    calc f x = f y := hsupport x y (fun p hp => (hxy p hp).symm)
      _ = target w y := hcorrect y hy
      _ = target w x := target_eq_of_agree w S hline y x hxy
  · have hle := Finset.card_le_card (Finset.filter_subset (fun p => x p = false) S)
    have he : S.filter (fun p => x p = false) = S :=
      Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
    have hfalse : ∀ p ∈ S, x p = false := by
      intro p hp
      have hmem : p ∈ S.filter (fun p => x p = false) := he.symm ▸ hp
      exact (Finset.mem_filter.mp hmem).2
    have ht : target w x = false := by
      apply decide_eq_false_iff_not.mpr
      rintro ⟨p, hp, hx⟩
      rw [hfalse p (hline hp)] at hx
      exact Bool.noConfusion hx
    rw [ht, ← hzero]
    exact hsupport x (fun _ => false) hfalse

lemma zero_input_read (n i : ℕ) :
    (List.ofFn (fun _ : Fin n => false)).getD i false = false := by
  by_cases h : i < n <;> simp [List.getD_eq_getElem?_getD, h]

lemma circuit_zero (gs : List Gate) (o : ℕ)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (y : Fin 13 → Bool) (hy : Circuit.eval ⟨gs, o⟩ (List.ofFn y) = false) :
    Circuit.eval ⟨gs, o⟩ (List.ofFn (fun _ : Fin 13 => false)) = false := by
  cases hzero : Circuit.eval ⟨gs, o⟩ (List.ofFn (fun _ : Fin 13 => false)) with
  | false => rfl
  | true =>
    have hm := wiresFrom_mono gs hmono
      (List.ofFn (fun _ : Fin 13 => false)) (List.ofFn y) (by simp)
      (by intro i hi; rw [zero_input_read] at hi; exact Bool.noConfusion hi) o hzero
    change Circuit.eval ⟨gs, o⟩ (List.ofFn y) = true at hm
    rw [hy] at hm
    exact Bool.noConfusion hm

lemma circuit_support_exact (gs : List Gate) (o : ℕ) (w : Fin 13)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hcorrect : ∀ x, Band x → Circuit.eval ⟨gs, o⟩ (List.ofFn x) = target w x)
    (S : Finset (Fin 13)) (hS : S.card ≤ 7)
    (hsupport : Supports (fun x => Circuit.eval ⟨gs, o⟩ (List.ofFn x)) S) :
    ∀ x, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = target w x := by
  apply small_support_exact w _ hcorrect _ S hS hsupport
  apply circuit_zero gs o hmono (row w)
  rw [hcorrect _ (Or.inr (row_spec w).1)]
  exact (row_spec w).2

lemma small_support_bound (gs : List Gate) (out : Fin 13 → ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ (w : Fin 13) (x : Fin 13 → Bool), Band x →
      Circuit.eval ⟨gs, out w⟩ (List.ofFn x) = target w x)
    (hsupport : ∀ w : Fin 13, ∃ S : Finset (Fin 13), S.card ≤ 7 ∧
      Supports (fun x => Circuit.eval ⟨gs, out w⟩ (List.ofFn x)) S) :
    39 ≤ gs.length := by
  apply Global.global_bound gs out hg
  intro w x
  obtain ⟨S, hS, hs⟩ := hsupport w
  exact circuit_support_exact gs (out w) w (fun g hm => (hg g hm).1)
    (hcorrect w) S hS hs x

lemma some_large_support (gs : List Gate) (out : Fin 13 → ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ (w : Fin 13) (x : Fin 13 → Bool), Band x →
      Circuit.eval ⟨gs, out w⟩ (List.ofFn x) = target w x)
    (hsmall : gs.length < 39) :
    ∃ w : Fin 13, ∀ S : Finset (Fin 13),
      Supports (fun x => Circuit.eval ⟨gs, out w⟩ (List.ofFn x)) S → 8 ≤ S.card := by
  classical
  by_contra! h
  have hs : ∀ w : Fin 13, ∃ S : Finset (Fin 13), S.card ≤ 7 ∧
      Supports (fun x => Circuit.eval ⟨gs, out w⟩ (List.ofFn x)) S := by
    intro w
    obtain ⟨S, hsupport, hcard⟩ := h w
    exact ⟨S, by omega, hsupport⟩
  have hb := small_support_bound gs out hg hcorrect hs
  omega

end PEqualNP.Outside.L_meta_1024_aux.Support



namespace PEqualNP.Outside.L_meta_1024_aux.CrossContext

open PEqualNP.Outside.L_meta_1024_aux.Minterms

lemma residual_subset_of_union_card
    (f : Finset (Fin 13) → Bool) (L M R T : Finset (Fin 13))
    (hmono : Increasing f) (hband : BandSpec f L)
    (hR : R ⊆ L) (hT : T ⊆ M) (hunion : (L ∪ M).card ≤ 7)
    (htrue : f (R ∪ T) = true) : L \ R ⊆ L ∩ M := by
  intro p hp
  obtain ⟨hpL, hpR⟩ := Finset.mem_sdiff.mp hp
  refine Finset.mem_inter.mpr ⟨hpL, ?_⟩
  by_contra hpM
  have hpU : p ∈ L ∪ M := Finset.mem_union_left M hpL
  have hpS : p ∉ R ∪ T := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact hpR h
    · exact hpM (hT h)
  have hsub : R ∪ T ⊆ (L ∪ M).erase p := by
    intro q hq
    refine Finset.mem_erase.mpr ⟨?_, ?_⟩
    · intro he
      subst q
      exact hpS hq
    · rcases Finset.mem_union.mp hq with h | h
      · exact Finset.mem_union_left M (hR h)
      · exact Finset.mem_union_right L (hT h)
  have hcard := Finset.card_le_card hsub
  have herase := Finset.card_erase_lt_of_mem hpU
  have hsmall : (R ∪ T).card ≤ 6 := by omega
  have hcontains := low_true_contains f L hmono hband (R ∪ T) hsmall htrue
  exact hpS (hcontains hpL)

end PEqualNP.Outside.L_meta_1024_aux.CrossContext


namespace PEqualNP.Outside.L_meta_1024_aux.Clamp

open PEqualNP.Outside.L_meta_1024_aux.Support

lemma line_card : ∀ w : Fin 13, (Support.line w).card = 4 := by decide +kernel

lemma row_line_false : ∀ w q : Fin 13, q ∈ Support.line w → Support.row w q = false := by
  decide +kernel

lemma extend_eight (w : Fin 13) (Q : Finset (Fin 13))
    (hQ : Q ⊆ Finset.univ \ Support.line w) (hcard : Q.card ≤ 8) :
    ∃ Y : Finset (Fin 13), Q ⊆ Y ∧ Y ⊆ Finset.univ \ Support.line w ∧ Y.card = 8 := by
  have houtside : (Finset.univ \ Support.line w).card = 9 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), line_card]
    decide
  have havail : 8 - Q.card ≤ ((Finset.univ \ Support.line w) \ Q).card := by
    rw [Finset.card_sdiff_of_subset hQ, houtside]
    omega
  obtain ⟨B, hB, hBc⟩ := Finset.exists_subset_card_eq havail
  have hd : Disjoint Q B := by
    rw [Finset.disjoint_left]
    intro p hpQ hpB
    exact (Finset.mem_sdiff.mp (hB hpB)).2 hpQ
  refine ⟨Q ∪ B, Finset.subset_union_left, ?_, ?_⟩
  · intro p hp
    rcases Finset.mem_union.mp hp with h | h
    · exact hQ h
    · exact (Finset.mem_sdiff.mp (hB h)).1
  · rw [Finset.card_union_of_disjoint hd, hBc]
    omega

def fromTrue (Y : Finset (Fin 13)) (p : Fin 13) : Bool := decide (p ∈ Y)
def singleton (q p : Fin 13) : Bool := decide (p = q)

lemma fromTrue_band (Y : Finset (Fin 13)) (hY : Y.card = 8) : Support.Band (fromTrue Y) := by
  apply Or.inl
  have hz : Support.zeroSet (fromTrue Y) = Finset.univ \ Y := by
    ext p
    simp [Support.zeroSet, fromTrue]
  rw [hz, Finset.card_sdiff_of_subset (Finset.subset_univ _), hY]
  decide

lemma fromTrue_misses (w : Fin 13) (Y : Finset (Fin 13))
    (hY : Y ⊆ Finset.univ \ Support.line w) : Support.target w (fromTrue Y) = false := by
  apply decide_eq_false_iff_not.mpr
  rintro ⟨p, hp, htrue⟩
  have hin : p ∈ Y := by simpa [fromTrue] using htrue
  exact (Finset.mem_sdiff.mp (hY hin)).2 hp

lemma supported_mono {m : ℕ} (F : (Fin m → Bool) → Bool) (E : Finset (Fin m))
    (hmono : ∀ a b, (∀ i, a i = true → b i = true) → F a = true → F b = true)
    (hsupport : ∀ a b, (∀ i ∈ E, a i = b i) → F a = F b)
    (a b : Fin m → Bool) (hab : ∀ i ∈ E, a i = true → b i = true)
    (ha : F a = true) : F b = true := by
  let c : Fin m → Bool := fun i => if i ∈ E then b i else a i
  have hc : F c = true := hmono a c (by
    intro i hi
    by_cases he : i ∈ E
    · simpa [c, he] using hab i he hi
    · simpa [c, he] using hi) ha
  have he : F c = F b := hsupport c b (by intro i hi; simp [c, hi])
  exact he ▸ hc

set_option maxHeartbeats 2000000 in
lemma missing_raw_impossible {m : ℕ} (w p : Fin 13) (hp : p ∈ Support.line w)
    (E : Finset (Fin m)) (hE : E.card ≤ 8) (F : (Fin m → Bool) → Bool)
    (leaf : Fin m → (Fin 13 → Bool) → Bool)
    (hmono : ∀ a b, (∀ i, a i = true → b i = true) → F a = true → F b = true)
    (hsupport : ∀ a b, (∀ i ∈ E, a i = b i) → F a = F b)
    (hleaf : ∀ i ∈ E, ∀ x y, (∀ q, x q = true → y q = true) →
      leaf i x = true → leaf i y = true)
    (hcorrect : ∀ x, Support.Band x → F (fun i => leaf i x) = Support.target w x)
    (hclass : ∀ i ∈ E,
      (∃ q ∈ Support.line w, q ≠ p ∧ ∀ x, leaf i x = x q) ∨
      ∃ q : Fin 13, q ∉ Support.line w ∧ leaf i (singleton q) = true) : False := by
  classical
  let foreign : Fin m → Prop := fun i => ∃ q : Fin 13,
    q ∉ Support.line w ∧ leaf i (singleton q) = true
  let q : Fin m → Fin 13 := fun i => if h : foreign i then Classical.choose h else 0
  have q_spec (i : Fin m) (hi : foreign i) :
      q i ∉ Support.line w ∧ leaf i (singleton (q i)) = true := by
    simpa only [q, dite_eq_left hi] using Classical.choose_spec hi
  let Q := (E.filter foreign).image q
  have hQcard : Q.card ≤ 8 :=
    (Finset.card_image_le.trans (Finset.card_filter_le _ _)).trans hE
  have hQ : Q ⊆ Finset.univ \ Support.line w := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (q_spec i (Finset.mem_filter.mp hi).2).1⟩
  obtain ⟨Y, hQY, hY, hYcard⟩ := extend_eight w Q hQ hQcard
  have hpband : Support.Band (Support.flip w p) := Or.inl (Support.flip_spec w p hp).1
  have hptrue : F (fun i => leaf i (Support.flip w p)) = true :=
    (hcorrect _ hpband).trans (Support.flip_spec w p hp).2
  have hyfalse : F (fun i => leaf i (fromTrue Y)) = false :=
    (hcorrect _ (fromTrue_band Y hYcard)).trans (fromTrue_misses w Y hY)
  have hcompare : ∀ i ∈ E, leaf i (Support.flip w p) = true → leaf i (fromTrue Y) = true := by
    intro i hi hpos
    rcases hclass i hi with ⟨r, hr, hrp, hraw⟩ | hforeign
    · rw [hraw, Support.flip, ite_eq_right hrp, row_line_false w r hr] at hpos
      exact Bool.noConfusion hpos
    · have hfor : foreign i := hforeign
      have hqi : q i ∈ Y := hQY (Finset.mem_image.mpr
        ⟨i, Finset.mem_filter.mpr ⟨hi, hfor⟩, rfl⟩)
      apply hleaf i hi (singleton (q i)) (fromTrue Y) _ (q_spec i hfor).2
      intro r hr
      have he : r = q i := by simpa [singleton] using hr
      subst r
      simp [fromTrue, hqi]
  have hytrue := supported_mono F E hmono hsupport _ _ hcompare hptrue
  rw [hyfalse] at hytrue
  exact Bool.noConfusion hytrue

end PEqualNP.Outside.L_meta_1024_aux.Clamp

namespace PEqualNP.Outside.L_meta_1024_aux.Charges

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_1024_aux.Global

lemma disjoint_charges (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (a b : Fin 13) (hab : a ≠ b) : Disjoint (Global.D (Global.line a) gs) (Global.D (Global.line b) gs) := by
  classical
  obtain ⟨la, hia, _⟩ := Global.main_inv (Global.line a) gs hg
  obtain ⟨lb, hib, _⟩ := Global.main_inv (Global.line b) gs hg
  rw [Finset.disjoint_left]
  intro i hiA hiB
  simp only [Global.D, Finset.mem_filter, Finset.mem_Ico] at hiA hiB
  obtain ⟨_, hza, u, v, huv, hu, hv⟩ := hiA
  obtain ⟨_, hzb, _⟩ := hiB
  have hua := (hia i u u hza hu hu).1
  have hva := (hia i v v hza hv hv).1
  have hub := (hib i u u hzb hu hu).1
  have hvb := (hib i v v hzb hv hv).1
  have hsub : ({u, v} : Finset (Fin 13)) ⊆ Global.line a ∩ Global.line b := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact Finset.mem_inter.mpr ⟨hua, hub⟩
    · exact Finset.mem_inter.mpr ⟨hva, hvb⟩
  have h2 : ({u, v} : Finset (Fin 13)).card = 2 := Finset.card_pair huv
  have := Finset.card_le_card hsub
  have := Global.line_intersection a b hab
  omega

lemma ordinary_charge_count (gs : List Gate) (o : ℕ) (w : Fin 13)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (he : ∀ x : Fin 13 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) =
      decide (∃ p ∈ Global.line w, x p = true)) : 3 ≤ (Global.D (Global.line w) gs).card := by
  classical
  obtain ⟨l, hinv, hcard⟩ := Global.main_inv (Global.line w) gs hg
  have hZ : Global.val gs (Global.Zof (Global.line w)) o = false := by
    change Circuit.eval ⟨gs, o⟩ (List.ofFn _) = false
    rw [he]
    simp [Global.Zof]
  have hE : ∀ u ∈ Global.line w, Global.val gs (Global.eof u) o = true := by
    intro u hu
    change Circuit.eval ⟨gs, o⟩ (List.ofFn _) = true
    rw [he]
    simp only [decide_eq_true_eq]
    exact ⟨u, hu, by simp [Global.eof]⟩
  have himg : ((Global.line w).image l).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
    exact (hinv o u v hZ (hE u hu) (hE v hv)).2
  rw [Global.line_card] at hcard
  omega

lemma charge_outside (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w a : Fin 13) (hwa : a ≠ w) (i : ℕ) (hi : i ∈ Global.D (Global.line a) gs) :
    ∃ q : Fin 13, q ∉ Global.line w ∧ Global.val gs (Global.eof q) i = true := by
  classical
  obtain ⟨l, hinv, _⟩ := Global.main_inv (Global.line a) gs hg
  simp only [Global.D, Finset.mem_filter, Finset.mem_Ico] at hi
  obtain ⟨_, hz, u, v, huv, hu, hv⟩ := hi
  have hua := (hinv i u u hz hu hu).1
  have hva := (hinv i v v hz hv hv).1
  by_cases huw : u ∈ Global.line w
  · refine ⟨v, ?_, hv⟩
    intro hvw
    have hsub : ({u, v} : Finset (Fin 13)) ⊆ Global.line a ∩ Global.line w := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨hua, huw⟩
      · exact Finset.mem_inter.mpr ⟨hva, hvw⟩
    have h2 : ({u, v} : Finset (Fin 13)).card = 2 := Finset.card_pair huv
    have := Finset.card_le_card hsub
    have := Global.line_intersection a w hwa
    omega
  · exact ⟨u, huw, hu⟩

lemma twelve_ordinary_charges (gs : List Gate) (out : Fin 13 → ℕ) (w : Fin 13)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hordinary : ∀ a : Fin 13, a ≠ w → ∀ x : Fin 13 → Bool,
      Circuit.eval ⟨gs, out a⟩ (List.ofFn x) = decide (∃ p ∈ Global.line a, x p = true)) :
    ∃ P : Finset ℕ, P ⊆ Finset.Ico 13 (13 + gs.length) ∧ 36 ≤ P.card ∧
      ∀ i ∈ P, ∃ q : Fin 13, q ∉ Global.line w ∧ Global.val gs (Global.eof q) i = true := by
  classical
  let W : Finset (Fin 13) := Finset.univ.erase w
  let P := W.biUnion (fun a => Global.D (Global.line a) gs)
  have hW : W.card = 12 := by simp [W]
  have hne (a : Fin 13) (ha : a ∈ W) : a ≠ w := (Finset.mem_erase.mp ha).1
  have hsubset : P ⊆ Finset.Ico 13 (13 + gs.length) := by
    intro i hi
    obtain ⟨a, _, hai⟩ := Finset.mem_biUnion.mp hi
    exact (Finset.mem_filter.mp hai).1
  have hcount : 36 ≤ P.card := by
    have hd : ∀ a ∈ W, ∀ b ∈ W, a ≠ b → Disjoint (Global.D (Global.line a) gs) (Global.D (Global.line b) gs) := by
      intro a _ b _ hab
      exact disjoint_charges gs hg a b hab
    have hsum : (∑ _a ∈ W, (3 : ℕ)) ≤ ∑ a ∈ W, (Global.D (Global.line a) gs).card := by
      apply Finset.sum_le_sum
      intro a ha
      exact ordinary_charge_count gs (out a) a hg (hordinary a (hne a ha))
    rw [← Finset.card_biUnion hd] at hsum
    simpa [P, hW] using hsum
  refine ⟨P, hsubset, hcount, ?_⟩
  intro i hi
  obtain ⟨a, ha, hai⟩ := Finset.mem_biUnion.mp hi
  exact charge_outside gs hg w a (hne a ha) i hai

end PEqualNP.Outside.L_meta_1024_aux.Charges

namespace PEqualNP.Outside.L_meta_1024_aux.Bridge

open PEqualNP.CircuitLowerBounds

lemma val_input {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : Fin n) :
    Global.val gs x i.val = x i := by
  induction gs using List.reverseRecOn with
  | nil => simp [Global.val_nil, i.isLt]
  | append_singleton gs g ih =>
    rw [Global.val_snoc, ite_eq_right (by omega)]
    exact ih

lemma val_mono (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin 13 → Bool) (hxy : ∀ p, x p = true → y p = true)
    (i : ℕ) (hx : Global.val gs x i = true) : Global.val gs y i = true := by
  apply Support.wiresFrom_mono gs hg (List.ofFn x) (List.ofFn y) (by simp) _ i hx
  intro k hk
  by_cases hlt : k < 13
  · rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hlt)] at hk
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hlt)]
    simp only [List.getElem_ofFn] at hk ⊢
    exact hxy ⟨k, hlt⟩ hk
  · rw [List.getD_eq_default _ _ (by simpa only [List.length_ofFn] using Nat.le_of_not_lt hlt)] at hk
    exact Bool.noConfusion hk

def rawIndex (gs : List Gate) (p : Fin 13) : Fin (13 + gs.length) :=
  ⟨p.val, by omega⟩

lemma raw_line_members (gs : List Gate) (o : ℕ) (w : Fin 13)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hcorrect : ∀ x : Fin 13 → Bool, Support.Band x →
      Global.val gs x o = Support.target w x)
    (P : Finset ℕ)
    (hPoutside : ∀ i ∈ P, ∃ q : Fin 13,
      q ∉ Global.line w ∧ Global.val gs (Global.eof q) i = true)
    (F : (Fin (13 + gs.length) → Bool) → Bool)
    (E : Finset (Fin (13 + gs.length))) (hEcard : E.card ≤ 8)
    (hallowed : ∀ i ∈ E, i.val < 13 ∨ i.val ∈ P)
    (hmono : ∀ a b, (∀ i, a i = true → b i = true) → F a = true → F b = true)
    (hsupport : ∀ a b, (∀ i ∈ E, a i = b i) → F a = F b)
    (hfactor : ∀ x : Fin 13 → Bool, F (fun i => Global.val gs x i.val) = Global.val gs x o)
    (p : Fin 13) (hp : p ∈ Global.line w) : rawIndex gs p ∈ E := by
  classical
  by_contra hpnot
  apply Clamp.missing_raw_impossible w p hp E hEcard F
    (fun i x => Global.val gs x i.val) hmono hsupport
  · intro i _ x y hxy hx
    exact val_mono gs hg x y hxy i.val hx
  · intro x hx
    rw [hfactor]
    exact hcorrect x hx
  · intro i hi
    rcases hallowed i hi with hiraw | hipaid
    · let q : Fin 13 := ⟨i.val, hiraw⟩
      have hraw : ∀ x : Fin 13 → Bool, Global.val gs x i.val = x q := fun x => val_input gs x q
      by_cases hql : q ∈ Global.line w
      · left
        refine ⟨q, hql, ?_, hraw⟩
        intro hqp
        have hie : i = rawIndex gs p := by
          apply Fin.ext
          exact congrArg (fun t : Fin 13 => t.val) hqp
        exact hpnot (hie ▸ hi)
      · right
        refine ⟨q, hql, ?_⟩
        rw [hraw]
        simp [Clamp.singleton]
    · obtain ⟨q, hq, hqtrue⟩ := hPoutside i.val hipaid
      exact Or.inr ⟨q, hq, hqtrue⟩

lemma cut_contradiction (gs : List Gate) (o : ℕ) (w : Fin 13)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ x : Fin 13 → Bool, Support.Band x →
      Global.val gs x o = Support.target w x)
    (hsmall : gs.length < 39)
    (P : Finset ℕ) (hP : P ⊆ Finset.Ico 13 (13 + gs.length)) (hPcard : 36 ≤ P.card)
    (hPoutside : ∀ i ∈ P, ∃ q : Fin 13,
      q ∉ Global.line w ∧ Global.val gs (Global.eof q) i = true)
    (F : (Fin (13 + gs.length) → Bool) → Bool)
    (E : Finset (Fin (13 + gs.length)))
    (hEcard : E.card ≤ gs.length - P.card + 1)
    (hallowed : ∀ i ∈ E, i.val < 13 ∨ i.val ∈ P)
    (hmono : ∀ a b, (∀ i, a i = true → b i = true) → F a = true → F b = true)
    (hsupport : ∀ a b, (∀ i ∈ E, a i = b i) → F a = F b)
    (hfactor : ∀ x : Fin 13 → Bool, F (fun i => Global.val gs x i.val) = Global.val gs x o) :
    False := by
  classical
  have hPupper : P.card ≤ gs.length := by
    have hh := Finset.card_le_card hP
    simpa using hh
  have hE3 : E.card ≤ 3 := by omega
  have hinj : Function.Injective (rawIndex gs) := by
    intro a b h
    apply Fin.ext
    exact congrArg (fun t : Fin (13 + gs.length) => t.val) h
  have hlinecard : ((Global.line w).image (rawIndex gs)).card = 4 := by
    rw [Finset.card_image_of_injective _ hinj, Global.line_card]
  have hsub : (Global.line w).image (rawIndex gs) ⊆ E := by
    intro i hi
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hi
    exact raw_line_members gs o w (fun g hm => (hg g hm).1) hcorrect P hPoutside F E
      (by omega) hallowed hmono hsupport hfactor p hp
  have hh := Finset.card_le_card hsub
  omega

end PEqualNP.Outside.L_meta_1024_aux.Bridge

namespace PEqualNP.Outside.L_meta_1024_aux.Cut

open PEqualNP.CircuitLowerBounds

def source {M : ℕ} (x : Fin M → Bool) (i : ℕ) : Bool :=
  (List.ofFn x).getD i false

lemma source_eq {M : ℕ} (x : Fin M → Bool) (i : ℕ) :
    source x i = if h : i < M then x ⟨i, h⟩ else false := by
  unfold source
  by_cases h : i < M <;> simp [List.getD_eq_getElem?_getD, h]

lemma source_dep {M : ℕ} (x y : Fin M → Bool) (i : ℕ) (t : Fin M)
    (hxy : ∀ j, j ≠ t → x j = y j) (hne : source x i ≠ source y i) : t.val = i := by
  rw [source_eq, source_eq] at hne
  by_cases h : i < M
  · simp only [h, dite_true] at hne
    have he : (⟨i, h⟩ : Fin M) = t := by
      by_contra ht
      exact hne (hxy _ ht)
    exact (congrArg Fin.val he).symm
  · simp [h] at hne

def cutStep {M : ℕ} (P : Finset ℕ) (x : Fin M → Bool) (w : List Bool) (g : Gate) :
    List Bool :=
  w ++ [if w.length ∈ P then source x w.length
    else g.op.eval (g.inputs.map fun i => w.getD i false)]

def cutRun {M : ℕ} (n : ℕ) (P : Finset ℕ) (gs : List Gate) (x : Fin M → Bool) :
    List Bool :=
  gs.foldl (cutStep P x) (List.ofFn (fun i : Fin n => source x i.val))

def cutVal {M : ℕ} (n : ℕ) (P : Finset ℕ) (gs : List Gate) (x : Fin M → Bool)
    (i : ℕ) : Bool := (cutRun n P gs x).getD i false

lemma fold_length {M : ℕ} (P : Finset ℕ) (x : Fin M → Bool) (gs : List Gate)
    (w : List Bool) :
    (gs.foldl (cutStep P x) w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_cons, cutStep, List.length_append,
      List.length_cons, List.length_nil]
    omega

lemma run_length {M : ℕ} (n : ℕ) (P : Finset ℕ) (gs : List Gate) (x : Fin M → Bool) :
    (cutRun n P gs x).length = n + gs.length := by
  simp [cutRun, fold_length]

lemma cutVal_nil {M : ℕ} (n : ℕ) (P : Finset ℕ) (x : Fin M → Bool) (i : ℕ) :
    cutVal n P [] x i = if i < n then source x i else false := by
  unfold cutVal cutRun
  by_cases h : i < n <;> simp [List.getD_eq_getElem?_getD, h]

lemma cutVal_snoc {M : ℕ} (n : ℕ) (P : Finset ℕ) (gs : List Gate) (g : Gate)
    (x : Fin M → Bool) (i : ℕ) :
    cutVal n P (gs ++ [g]) x i =
      if i = n + gs.length then
        if i ∈ P then source x i
        else g.op.eval (g.inputs.map fun j => cutVal n P gs x j)
      else cutVal n P gs x i := by
  unfold cutVal cutRun
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, cutStep]
  have hl : (gs.foldl (cutStep P x) (List.ofFn (fun i : Fin n => source x i.val))).length =
      n + gs.length := by rw [fold_length]; simp
  rcases lt_trichotomy i (n + gs.length) with h | h | h
  · rw [ite_eq_right (show i ≠ n + gs.length by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  · rw [ite_eq_left h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hl, h]
  · rw [ite_eq_right (show i ≠ n + gs.length by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

def unpaid (n : ℕ) (P : Finset ℕ) (gs : List Gate) : ℕ :=
  ((Finset.Ico n (n + gs.length)) \ P).card

lemma unpaid_nil (n : ℕ) (P : Finset ℕ) : unpaid n P [] = 0 := by simp [unpaid]

lemma unpaid_snoc (n : ℕ) (P : Finset ℕ) (gs : List Gate) (g : Gate) :
    unpaid n P (gs ++ [g]) = unpaid n P gs + if n + gs.length ∈ P then 0 else 1 := by
  have he : Finset.Ico n (n + (gs ++ [g]).length) =
      insert (n + gs.length) (Finset.Ico n (n + gs.length)) := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    rw [← Nat.add_assoc]
    exact Nat.Ico_succ_right_eq_insert_Ico (by omega)
  unfold unpaid
  rw [he]
  by_cases hp : n + gs.length ∈ P
  · rw [Finset.insert_sdiff_of_mem _ hp]
    simp [hp]
  · rw [Finset.insert_sdiff_of_notMem _ hp, Finset.card_insert_of_notMem]
    · simp [hp]
    · simp

lemma unpaid_eq_sub (n : ℕ) (P : Finset ℕ) (gs : List Gate)
    (hP : P ⊆ Finset.Ico n (n + gs.length)) :
    unpaid n P gs = gs.length - P.card := by
  rw [unpaid, Finset.card_sdiff_of_subset hP]
  simp

def Depends {M : ℕ} (n : ℕ) (P : Finset ℕ) (gs : List Gate) (i : ℕ) (t : Fin M) : Prop :=
  ∃ x y : Fin M → Bool, (∀ j, j ≠ t → x j = y j) ∧
    cutVal n P gs x i ≠ cutVal n P gs y i

lemma two_inputs (ins : List ℕ) (h : ins.length ≤ 2) :
    ∃ a b : ℕ, ∀ j ∈ ins, j = a ∨ j = b := by
  match ins, h with
  | [], _ => exact ⟨0, 0, by simp⟩
  | [a], _ => exact ⟨a, a, by simp⟩
  | [a, b], _ => exact ⟨a, b, by simp⟩
  | _ :: _ :: _ :: _, h => simp at h

lemma components {M : ℕ} (n : ℕ) (P : Finset ℕ) (S : Finset (Fin M))
    (gs : List Gate) (hg : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    ∃ (label : Fin M → ℕ) (wire : ℕ → ℕ),
      S.card ≤ (S.image label).card + unpaid n P gs ∧
      ∀ i t, Depends n P gs i t → label t = wire i := by
  classical
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨Fin.val, id, ?_, ?_⟩
    · simp [unpaid_nil, Finset.card_image_of_injective _ Fin.val_injective]
    · rintro i t ⟨x, y, hxy, hne⟩
      rw [cutVal_nil, cutVal_nil] at hne
      by_cases hi : i < n
      · simp only [hi, ite_true] at hne
        exact source_dep x y i t hxy hne
      · simp [hi] at hne
  | append_singleton gs g ih =>
    obtain ⟨label, wire, hcount, hdep⟩ := ih (fun g' h => hg g' (by simp [h]))
    by_cases hp : n + gs.length ∈ P
    · refine ⟨label, fun i => if h : i = n + gs.length then
        if hi : i < M then label ⟨i, hi⟩ else 0 else wire i, ?_, ?_⟩
      · simpa [unpaid_snoc, hp] using hcount
      · rintro i t ⟨x, y, hxy, hne⟩
        rw [cutVal_snoc, cutVal_snoc] at hne
        by_cases hi : i = n + gs.length
        · simp only [hi, ite_true, hp] at hne ⊢
          have ht := source_dep x y (n + gs.length) t hxy hne
          have hlt : n + gs.length < M := by omega
          simp only [hlt, dite_true]
          congr 1
          exact Fin.ext ht
        · simp only [hi, ite_false, dite_false] at hne ⊢
          exact hdep i t ⟨x, y, hxy, hne⟩
    · obtain ⟨a, b, hinputs⟩ := two_inputs g.inputs (hg g (by simp))
      let merge (k : ℕ) := if k = wire b then wire a else k
      have ha : merge (wire a) = wire a := by simp [merge]
      have hb : merge (wire b) = wire a := by simp [merge]
      refine ⟨merge ∘ label,
        fun i => if i = n + gs.length then wire a else merge (wire i), ?_, ?_⟩
      · have hsub : S.image label ⊆ insert (wire b) (S.image (merge ∘ label)) := by
          intro v hv
          obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hv
          by_cases he : label t = wire b
          · simp [he]
          · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨t, ht, by simp [merge, he]⟩)
        have hc := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
        rw [unpaid_snoc]
        simp only [hp, ite_false]
        omega
      · rintro i t ⟨x, y, hxy, hne⟩
        rw [cutVal_snoc, cutVal_snoc] at hne
        by_cases hi : i = n + gs.length
        · simp only [hi, ite_true, hp, ite_false, Function.comp_apply] at hne ⊢
          have hd : cutVal n P gs x a ≠ cutVal n P gs y a ∨
              cutVal n P gs x b ≠ cutVal n P gs y b := by
            by_contra! hh
            apply hne
            apply congrArg g.op.eval
            apply List.map_congr_left
            intro j hj
            rcases hinputs j hj with rfl | rfl
            · exact hh.1
            · exact hh.2
          rcases hd with hd | hd
          · rw [hdep a t ⟨x, y, hxy, hd⟩, ha]
          · rw [hdep b t ⟨x, y, hxy, hd⟩, hb]
        · simp only [hi, ite_false, Function.comp_apply] at hne ⊢
          rw [hdep i t ⟨x, y, hxy, hne⟩]

open Classical in
noncomputable def essential {M : ℕ} (n : ℕ) (P : Finset ℕ) (gs : List Gate) (o : ℕ) :
    Finset (Fin M) := Finset.univ.filter (Depends n P gs o)

lemma essential_card {M : ℕ} (n : ℕ) (P : Finset ℕ) (gs : List Gate) (o : ℕ)
    (hg : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (essential (M := M) n P gs o).card ≤ unpaid n P gs + 1 := by
  classical
  obtain ⟨label, wire, hc, hd⟩ := components n P (essential (M := M) n P gs o) gs hg
  have hsmall : ((essential (M := M) n P gs o).image label).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
    exact (hd o u (Finset.mem_filter.mp hu).2).trans
      (hd o v (Finset.mem_filter.mp hv).2).symm
  omega


lemma source_congr {M : ℕ} (x y : Fin M → Bool) (i : ℕ)
    (hxy : ∀ t : Fin M, t.val = i → x t = y t) : source x i = source y i := by
  rw [source_eq, source_eq]
  split_ifs with hi
  · exact hxy ⟨i, hi⟩ rfl
  · rfl

lemma cutVal_congr {M : ℕ} (n : ℕ) (P : Finset ℕ) (gs : List Gate)
    (x y : Fin M → Bool) (hxy : ∀ t, t.val < n ∨ t.val ∈ P → x t = y t) :
    ∀ i, cutVal n P gs x i = cutVal n P gs y i := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro i
    rw [cutVal_nil, cutVal_nil]
    split_ifs with hi
    · exact source_congr x y i (fun t ht => hxy t (Or.inl (by omega)))
    · rfl
  | append_singleton gs g ih =>
    intro i
    rw [cutVal_snoc, cutVal_snoc]
    split_ifs with hi hp
    · exact source_congr x y i (fun t ht => hxy t (Or.inr (ht ▸ hp)))
    · congr 1
      exact List.map_congr_left (fun j _ => ih j)
    · exact ih i

lemma essential_sources {M : ℕ} (n : ℕ) (P : Finset ℕ) (gs : List Gate) (o : ℕ)
    (t : Fin M) (ht : t ∈ essential n P gs o) : t.val < n ∨ t.val ∈ P := by
  classical
  obtain ⟨x, y, hxy, hne⟩ := (Finset.mem_filter.mp ht).2
  by_contra hn
  apply hne
  apply cutVal_congr
  intro u hu
  apply hxy u
  intro he
  subst u
  exact hn hu

lemma essential_supports {M : ℕ} (n : ℕ) (P : Finset ℕ) (gs : List Gate) (o : ℕ)
    (x y : Fin M → Bool) (hxy : ∀ t ∈ essential n P gs o, x t = y t) :
    cutVal n P gs x o = cutVal n P gs y o := by
  classical
  have key : ∀ S : Finset (Fin M), (∀ t ∈ S, ¬ Depends n P gs o t) →
      ∀ x y : Fin M → Bool, (∀ t, t ∉ S → x t = y t) →
        cutVal n P gs x o = cutVal n P gs y o := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _ x y h
      have he : x = y := funext (fun t => h t (by simp))
      rw [he]
    | @insert a S ha ih =>
      intro hS x y h
      let z : Fin M → Bool := Function.update x a (y a)
      have hfirst : cutVal n P gs x o = cutVal n P gs z o := by
        by_contra hne
        apply hS a (Finset.mem_insert_self a S)
        refine ⟨x, z, ?_, hne⟩
        intro j hj
        simp [z, Function.update_of_ne hj]
      have hnext : cutVal n P gs z o = cutVal n P gs y o := by
        apply ih (fun t ht => hS t (Finset.mem_insert_of_mem ht)) z y
        intro j hj
        by_cases he : j = a
        · subst j
          simp [z]
        · rw [show z j = x j by simp [z, Function.update_of_ne he]]
          exact h j (by simp [he, hj])
      exact hfirst.trans hnext
  apply key (Finset.univ \ essential n P gs o)
  · intro t ht
    have hn := (Finset.mem_sdiff.mp ht).2
    simpa [essential] using hn
  · intro t ht
    apply hxy t
    simpa using ht

lemma source_mono {M : ℕ} (x y : Fin M → Bool) (hxy : ∀ t, x t = true → y t = true)
    (i : ℕ) (hi : source x i = true) : source y i = true := by
  rw [source_eq] at hi ⊢
  split_ifs at hi ⊢ with h
  · exact hxy ⟨i, h⟩ hi

lemma gate_mono (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (f h : ℕ → Bool) (hfh : ∀ i, f i = true → h i = true)
    (hf : g.op.eval (g.inputs.map f) = true) : g.op.eval (g.inputs.map h) = true := by
  rcases hop with hop | hop
  · rw [hop] at hf ⊢
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at hf ⊢
    intro b hb
    obtain ⟨i, hi, rfl⟩ := hb
    exact hfh i (hf _ ⟨i, hi, rfl⟩)
  · rw [hop] at hf ⊢
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hf ⊢
    obtain ⟨b, ⟨i, hi, rfl⟩, hf⟩ := hf
    exact ⟨h i, ⟨i, hi, rfl⟩, hfh i hf⟩

lemma cutVal_mono {M : ℕ} (n : ℕ) (P : Finset ℕ) (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin M → Bool) (hxy : ∀ t, x t = true → y t = true) :
    ∀ i, cutVal n P gs x i = true → cutVal n P gs y i = true := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro i hi
    rw [cutVal_nil] at hi ⊢
    split_ifs at hi ⊢ with h
    · exact source_mono x y hxy i hi
  | append_singleton gs g ih =>
    have hprev := ih (fun g' hg' => hg g' (by simp [hg']))
    intro i hi
    rw [cutVal_snoc] at hi ⊢
    split_ifs at hi ⊢ with he hp
    · exact source_mono x y hxy i hi
    · exact gate_mono g (hg g (by simp)) _ _ hprev hi
    · exact hprev i hi

lemma essential_bound {M : ℕ} (n : ℕ) (P : Finset ℕ) (gs : List Gate) (o : ℕ)
    (hg : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (hP : P ⊆ Finset.Ico n (n + gs.length)) :
    (essential (M := M) n P gs o).card ≤ gs.length - P.card + 1 := by
  rw [← unpaid_eq_sub n P gs hP]
  exact essential_card n P gs o hg


lemma cut_empty {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) :
    cutVal n ∅ gs x i = Circuit.eval ⟨gs, i⟩ (List.ofFn x) := by
  have he : (fun j : Fin n => source x j.val) = x := by
    funext j
    simp [source_eq]
  unfold cutVal cutRun
  simp only [cutStep, Finset.notMem_empty, ite_false, he]
  rfl

lemma cutVal_factor {M n : ℕ} (P : Finset ℕ) (gs : List Gate)
    (x : Fin n → Bool) (y : Fin M → Bool)
    (hsrc : ∀ i, i < n + gs.length → source y i = cutVal n ∅ gs x i) :
    ∀ i, cutVal n P gs y i = cutVal n ∅ gs x i := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro i
    rw [cutVal_nil, cutVal_nil]
    by_cases hi : i < n
    · simpa [cutVal_nil, hi] using hsrc i (by simpa using hi)
    · simp [hi]
  | append_singleton gs g ih =>
    have hprevsrc : ∀ i, i < n + gs.length → source y i = cutVal n ∅ gs x i := by
      intro i hi
      have h := hsrc i (by simp; omega)
      rw [cutVal_snoc, ite_eq_right (show i ≠ n + gs.length by omega)] at h
      exact h
    have hprev := ih hprevsrc
    intro i
    rw [cutVal_snoc, cutVal_snoc]
    by_cases hi : i = n + gs.length
    · simp only [hi, ite_true, Finset.notMem_empty, ite_false]
      by_cases hp : n + gs.length ∈ P
      · rw [ite_eq_left hp]
        have h := hsrc (n + gs.length) (by simp)
        rw [cutVal_snoc, ite_eq_left rfl] at h
        simpa using h
      · rw [ite_eq_right hp]
        congr 1
        exact List.map_congr_left (fun j _ => hprev j)
    · simp only [hi, ite_false]
      exact hprev i

def actualSources {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    Fin (n + gs.length) → Bool :=
  fun t => Circuit.eval ⟨gs, t.val⟩ (List.ofFn x)

lemma source_actual {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ)
    (hi : i < n + gs.length) :
    source (actualSources gs x) i = Circuit.eval ⟨gs, i⟩ (List.ofFn x) := by
  simp [source_eq, hi, actualSources]

lemma factor {n : ℕ} (P : Finset ℕ) (gs : List Gate) (x : Fin n → Bool) (i : ℕ) :
    cutVal n P gs (actualSources gs x) i = Circuit.eval ⟨gs, i⟩ (List.ofFn x) := by
  apply (cutVal_factor P gs x (actualSources gs x) ?_ i).trans (cut_empty gs x i)
  intro j hj
  rw [source_actual gs x j hj, cut_empty]

lemma actualSources_mono {n : ℕ} (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (hxy : ∀ t, x t = true → y t = true)
    (i : Fin (n + gs.length)) (hi : actualSources gs x i = true) :
    actualSources gs y i = true := by
  unfold actualSources at hi ⊢
  rw [← cut_empty] at hi ⊢
  exact cutVal_mono n ∅ gs hg x y hxy i.val hi

end PEqualNP.Outside.L_meta_1024_aux.Cut

namespace PEqualNP.Outside.L_meta_1024_aux.Bridge

open PEqualNP.CircuitLowerBounds

lemma one_exotic_bound (gs : List Gate) (out : Fin 13 → ℕ) (w : Fin 13)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ (a : Fin 13) (x : Fin 13 → Bool), Support.Band x →
      Circuit.eval ⟨gs, out a⟩ (List.ofFn x) = Support.target a x)
    (hordinary : ∀ a : Fin 13, a ≠ w → ∀ x : Fin 13 → Bool,
      Circuit.eval ⟨gs, out a⟩ (List.ofFn x) = decide (∃ p ∈ Global.line a, x p = true)) :
    39 ≤ gs.length := by
  classical
  by_contra! hsmall
  obtain ⟨P, hP, hPcard, hPoutside⟩ := Charges.twelve_ordinary_charges gs out w hg hordinary
  let F : (Fin (13 + gs.length) → Bool) → Bool := fun x => Cut.cutVal 13 P gs x (out w)
  let E := Cut.essential (M := 13 + gs.length) 13 P gs (out w)
  apply cut_contradiction gs (out w) w hg (hcorrect w) hsmall P hP hPcard hPoutside F E
  · exact Cut.essential_bound 13 P gs (out w) (fun g hm => (hg g hm).2) hP
  · exact Cut.essential_sources 13 P gs (out w)
  · intro a b hab ha
    exact Cut.cutVal_mono 13 P gs (fun g hm => (hg g hm).1) a b hab (out w) ha
  · exact Cut.essential_supports 13 P gs (out w)
  · intro x
    exact Cut.factor P gs x (out w)

end PEqualNP.Outside.L_meta_1024_aux.Bridge



namespace PEqualNP.Outside.L_meta_1024_aux.Charges

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_1024_aux.Global

lemma ordinary_charge_family (gs : List Gate) (out : Fin 13 → ℕ) (W : Finset (Fin 13))
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hordinary : ∀ a ∈ W, ∀ x : Fin 13 → Bool,
      Circuit.eval ⟨gs, out a⟩ (List.ofFn x) = decide (∃ p ∈ Global.line a, x p = true)) :
    ∃ P : Finset ℕ, P ⊆ Finset.Ico 13 (13 + gs.length) ∧ 3 * W.card ≤ P.card ∧
      ∀ w ∉ W, ∀ i ∈ P, ∃ q : Fin 13, q ∉ Global.line w ∧ Global.val gs (Global.eof q) i = true := by
  classical
  let P := W.biUnion (fun a => Global.D (Global.line a) gs)
  have hsubset : P ⊆ Finset.Ico 13 (13 + gs.length) := by
    intro i hi
    obtain ⟨a, _, hai⟩ := Finset.mem_biUnion.mp hi
    exact (Finset.mem_filter.mp hai).1
  have hcount : 3 * W.card ≤ P.card := by
    have hd : ∀ a ∈ W, ∀ b ∈ W, a ≠ b → Disjoint (Global.D (Global.line a) gs) (Global.D (Global.line b) gs) := by
      intro a _ b _ hab
      exact disjoint_charges gs hg a b hab
    have hsum : (∑ _a ∈ W, (3 : ℕ)) ≤ ∑ a ∈ W, (Global.D (Global.line a) gs).card := by
      apply Finset.sum_le_sum
      intro a ha
      exact ordinary_charge_count gs (out a) a hg (hordinary a ha)
    rw [← Finset.card_biUnion hd] at hsum
    simpa [P, Nat.mul_comm] using hsum
  refine ⟨P, hsubset, hcount, ?_⟩
  intro w hw i hi
  obtain ⟨a, ha, hai⟩ := Finset.mem_biUnion.mp hi
  have hne : a ≠ w := fun he => hw (he ▸ ha)
  exact charge_outside gs hg w a hne i hai

end PEqualNP.Outside.L_meta_1024_aux.Charges

namespace PEqualNP.Outside.L_meta_1024_aux.Bridge

open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma pair_geometry : ∀ a b : Fin 13, a ≠ b →
    (Global.line a ∪ Global.line b).card = 7 ∧
      ∃ p : Fin 13, p ∈ Global.line a ∧ p ∈ Global.line b := by
  decide +kernel

lemma two_exotic_bound (gs : List Gate) (out : Fin 13 → ℕ)
    (a b : Fin 13) (hab : a ≠ b)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ (w : Fin 13) (x : Fin 13 → Bool), Support.Band x →
      Circuit.eval ⟨gs, out w⟩ (List.ofFn x) = Support.target w x)
    (hordinary : ∀ w : Fin 13, w ≠ a → w ≠ b → ∀ x : Fin 13 → Bool,
      Circuit.eval ⟨gs, out w⟩ (List.ofFn x) = decide (∃ p ∈ Global.line w, x p = true)) :
    39 ≤ gs.length := by
  classical
  by_contra! hsmall
  let W : Finset (Fin 13) := (Finset.univ.erase a).erase b
  have hW : W.card = 11 := by simp [W, hab, Ne.symm hab]
  have hord : ∀ w ∈ W, ∀ x : Fin 13 → Bool,
      Circuit.eval ⟨gs, out w⟩ (List.ofFn x) = decide (∃ p ∈ Global.line w, x p = true) := by
    intro w hw
    have hwb : w ≠ b := (Finset.mem_erase.mp hw).1
    have hwa : w ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hw).2).1
    exact hordinary w hwa hwb
  obtain ⟨P, hP, hPcard, hPoutside⟩ := Charges.ordinary_charge_family gs out W hg hord
  have hP33 : 33 ≤ P.card := by simpa [hW] using hPcard
  have hPupper : P.card ≤ gs.length := by simpa using Finset.card_le_card hP
  have hbudget : Cut.unpaid 13 P gs ≤ 5 := by
    rw [Cut.unpaid_eq_sub 13 P gs hP]
    omega
  let E (w : Fin 13) := Cut.essential (M := 13 + gs.length) 13 P gs (out w)
  have hraw (w : Fin 13) (hw : w = a ∨ w = b) (p : Fin 13) (hp : p ∈ Global.line w) :
      rawIndex gs p ∈ E w := by
    have hnot : w ∉ W := by rcases hw with rfl | rfl <;> simp [W]
    apply raw_line_members gs (out w) w (fun g hm => (hg g hm).1) (hcorrect w) P
      (hPoutside w hnot) (fun x => Cut.cutVal 13 P gs x (out w)) (E w)
    · have hh := Cut.essential_card (M := 13 + gs.length) 13 P gs (out w)
        (fun g hm => (hg g hm).2)
      change (E w).card ≤ _ at hh
      omega
    · exact Cut.essential_sources 13 P gs (out w)
    · intro x y hxy hx
      exact Cut.cutVal_mono 13 P gs (fun g hm => (hg g hm).1) x y hxy (out w) hx
    · exact Cut.essential_supports 13 P gs (out w)
    · intro x
      exact Cut.factor P gs x (out w)
    · exact hp
  let S := (Global.line a ∪ Global.line b).image (rawIndex gs)
  have hinj : Function.Injective (rawIndex gs) := by
    intro p q hpq
    apply Fin.ext
    exact congrArg (fun t : Fin (13 + gs.length) => t.val) hpq
  have hS : S.card = 7 := by
    rw [Finset.card_image_of_injective _ hinj]
    exact (pair_geometry a b hab).1
  obtain ⟨label, wire, hc, hd⟩ := Cut.components 13 P S gs (fun g hm => (hg g hm).2)
  have hl (w : Fin 13) (hw : w = a ∨ w = b) (p : Fin 13) (hp : p ∈ Global.line w) :
      label (rawIndex gs p) = wire (out w) := by
    exact hd (out w) (rawIndex gs p) (Finset.mem_filter.mp (hraw w hw p hp)).2
  obtain ⟨p, hpa, hpb⟩ := (pair_geometry a b hab).2
  have hwire : wire (out a) = wire (out b) :=
    (hl a (Or.inl rfl) p hpa).symm.trans (hl b (Or.inr rfl) p hpb)
  have himg : S.image label ⊆ {wire (out a)} := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hi
    apply Finset.mem_singleton.mpr
    rcases Finset.mem_union.mp hq with hqa | hqb
    · exact hl a (Or.inl rfl) q hqa
    · exact (hl b (Or.inr rfl) q hqb).trans hwire.symm
  have hcard : (S.image label).card ≤ 1 := by
    simpa using Finset.card_le_card himg
  rw [hS] at hc
  omega

end PEqualNP.Outside.L_meta_1024_aux.Bridge



namespace PEqualNP.Outside.L_meta_1024_aux.OneAnd

def line (w : Fin 13) : Finset (Fin 13) :=
  ({0, 1, 3, 9} : Finset (Fin 13)).image (fun u => u + w)

def hit (S X : Finset (Fin 13)) : Bool := decide (∃ p ∈ S, p ∈ X)

lemma hit_true (S X : Finset (Fin 13)) (p : Fin 13) (hp : p ∈ S) (hx : p ∈ X) :
    hit S X = true := decide_eq_true ⟨p, hp, hx⟩

lemma hit_false (S X : Finset (Fin 13)) (h : Disjoint S X) : hit S X = false := by
  simp only [hit, decide_eq_false_iff_not]
  rintro ⟨p, hp, hx⟩
  exact Finset.disjoint_left.mp h hp hx

lemma line_card : ∀ w : Fin 13, (line w).card = 4 := by decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma line_meet : ∀ w u : Fin 13, w ≠ u → (line w ∩ line u).card = 1 := by decide +kernel

lemma outside_card (w : Fin 13) : (Finset.univ \ line w).card = 9 := by
  simp [Finset.card_sdiff, line_card]

lemma outside_row (w : Fin 13) (T : Finset (Fin 13)) (hT : Disjoint T (line w))
    (hc : T.card ≤ 7) :
    ∃ X, T ⊆ X ∧ X.card = 7 ∧ Disjoint (line w) X := by
  have hsub : T ⊆ Finset.univ \ line w := by
    intro p hp
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ p,
      fun h => Finset.disjoint_left.mp hT hp h⟩
  obtain ⟨X, hTX, hX, hcard⟩ := Finset.exists_subsuperset_card_eq hsub hc
    (by rw [outside_card]; omega)
  refine ⟨X, hTX, hcard, Finset.disjoint_left.mpr ?_⟩
  intro p hp hx
  exact (Finset.mem_sdiff.mp (hX hx)).2 hp

lemma one_point_row (w : Fin 13) (p : Fin 13) (hp : p ∈ line w) :
    ∃ X : Finset (Fin 13), X.card = 7 ∧ p ∈ X ∧
      ∀ q ∈ line w, q ∈ X → q = p := by
  obtain ⟨T, hT, hcard⟩ := Finset.exists_subset_card_eq
    (show 6 ≤ (Finset.univ \ line w).card by rw [outside_card]; omega)
  have hn : p ∉ T := fun h => (Finset.mem_sdiff.mp (hT h)).2 hp
  refine ⟨insert p T, by simp [hn, hcard], Finset.mem_insert_self _ _, ?_⟩
  intro q hq hX
  rcases Finset.mem_insert.mp hX with h | h
  · exact h
  · exact ((Finset.mem_sdiff.mp (hT h)).2 hq).elim

def separatingRow (w u : Fin 13) (p : Fin 13) : Finset (Fin 13) :=
  insert p (Finset.univ \ (line w ∪ line u))

lemma separating_row (w u : Fin 13) (hwu : w ≠ u) (p : Fin 13)
    (hp : p ∈ line w) (hpu : p ∉ line u) :
    (separatingRow w u p).card = 7 ∧ p ∈ separatingRow w u p ∧
      Disjoint (line u) (separatingRow w u p) ∧
      ∀ q ∈ line w, q ∈ separatingRow w u p → q = p := by
  have hu : (line w ∪ line u).card = 7 := by
    have hc := Finset.card_union_add_card_inter (line w) (line u)
    rw [line_card, line_card, line_meet w u hwu] at hc
    omega
  have hn : p ∉ Finset.univ \ (line w ∪ line u) := by simp [hp]
  refine ⟨?_, Finset.mem_insert_self _ _, ?_, ?_⟩
  · simp [separatingRow, hn, Finset.card_sdiff, hu]
  · apply Finset.disjoint_left.mpr
    intro q hq hX
    rcases Finset.mem_insert.mp hX with h | h
    · exact hpu (h ▸ hq)
    · exact (Finset.mem_sdiff.mp h).2 (Finset.mem_union_right _ hq)
  · intro q hq hX
    rcases Finset.mem_insert.mp hX with h | h
    · exact h
    · exact ((Finset.mem_sdiff.mp h).2 (Finset.mem_union_left _ hq)).elim

def output (S A B X : Finset (Fin 13)) (u : Bool) : Bool :=
  hit S X || (u && (hit A X && hit B X))

abbrev Correct (S : Fin 13 → Finset (Fin 13)) (A B : Finset (Fin 13))
    (u : Fin 13 → Bool) : Prop :=
  ∀ w X, X.card = 7 → output (S w) A B X (u w) = hit (line w) X

lemma support_subset (S : Fin 13 → Finset (Fin 13)) (A B : Finset (Fin 13))
    (u : Fin 13 → Bool) (hcorrect : Correct S A B u) (w : Fin 13) : S w ⊆ line w := by
  intro p hp
  by_contra hn
  obtain ⟨X, hPX, hc, hd⟩ := outside_row w {p} (by simpa using hn) (by simp)
  have hs : hit (S w) X = true := hit_true _ _ p hp (hPX (by simp))
  have h := hcorrect w X hc
  rw [hit_false _ _ hd] at h
  simp [output, hs] at h

lemma unused_complete (S : Fin 13 → Finset (Fin 13)) (A B : Finset (Fin 13))
    (u : Fin 13 → Bool) (hcorrect : Correct S A B u) (w : Fin 13) (hu : u w = false) :
    S w = line w := by
  apply Finset.Subset.antisymm (support_subset S A B u hcorrect w)
  intro p hp
  by_contra hn
  obtain ⟨X, hc, hpX, hrow⟩ := one_point_row w p hp
  have hs : hit (S w) X = false := hit_false _ _ (Finset.disjoint_left.mpr (by
    intro q hq hX
    have he := hrow q (support_subset S A B u hcorrect w hq) hX
    exact hn (he ▸ hq)))
  have h := hcorrect w X hc
  rw [hit_true _ _ p hp hpX] at h
  simp [output, hu, hs] at h

lemma parent_subset (S : Fin 13 → Finset (Fin 13)) (A B : Finset (Fin 13))
    (u : Fin 13 → Bool) (hcorrect : Correct S A B u) (w : Fin 13) (hu : u w = true) :
    A ⊆ line w ∨ B ⊆ line w := by
  by_contra hn
  obtain ⟨a, ha, hna⟩ := Finset.not_subset.mp (show ¬ A ⊆ line w from fun h => hn (Or.inl h))
  obtain ⟨b, hb, hnb⟩ := Finset.not_subset.mp (show ¬ B ⊆ line w from fun h => hn (Or.inr h))
  have hd : Disjoint ({a, b} : Finset (Fin 13)) (line w) := by
    simp [hna, hnb]
  obtain ⟨X, hPX, hc, hd⟩ := outside_row w {a, b} hd (by
    have h := Finset.card_insert_le a ({b} : Finset (Fin 13))
    simp only [Finset.card_singleton] at h
    omega)
  have hA : hit A X = true := hit_true _ _ a ha (hPX (by simp))
  have hB : hit B X = true := hit_true _ _ b hb (hPX (by simp))
  have h := hcorrect w X hc
  rw [hit_false _ _ hd] at h
  simp [output, hu, hA, hB] at h

lemma parent_complete_left (S : Fin 13 → Finset (Fin 13)) (A B : Finset (Fin 13))
    (u : Fin 13 → Bool) (hcorrect : Correct S A B u) (w : Fin 13)
    (hA : A ⊆ line w) : S w ∪ A = line w := by
  apply Finset.Subset.antisymm (Finset.union_subset (support_subset S A B u hcorrect w) hA)
  intro p hp
  by_contra hn
  obtain ⟨X, hc, hpX, hrow⟩ := one_point_row w p hp
  have hzero : ∀ T ⊆ line w, p ∉ T → hit T X = false := by
    intro T hT hpT
    apply hit_false
    apply Finset.disjoint_left.mpr
    intro q hq hX
    exact hpT ((hrow q (hT hq) hX) ▸ hq)
  have hs := hzero (S w) (support_subset S A B u hcorrect w)
    (fun h => hn (Finset.mem_union_left _ h))
  have ha := hzero A hA (fun h => hn (Finset.mem_union_right _ h))
  have h := hcorrect w X hc
  rw [hit_true _ _ p hp hpX] at h
  simp [output, hs, ha] at h

lemma residual_subset_user (S : Fin 13 → Finset (Fin 13)) (A B : Finset (Fin 13))
    (u : Fin 13 → Bool) (hcorrect : Correct S A B u) (w v : Fin 13)
    (hw : u w = true) (hv : u v = true) : line w \ S w ⊆ line v := by
  intro p hp
  obtain ⟨hpw, hps⟩ := Finset.mem_sdiff.mp hp
  by_cases hwv : w = v
  · simpa [hwv] using hpw
  by_contra hpv
  obtain ⟨hc, hpX, hd, hrow⟩ := separating_row w v hwv p hpw hpv
  have hvzero := hcorrect v (separatingRow w v p) hc
  rw [hit_false _ _ hd] at hvzero
  have hh : (hit A (separatingRow w v p) && hit B (separatingRow w v p)) = false := by
    simp only [output, hv, Bool.true_and, Bool.or_eq_false_iff] at hvzero
    exact hvzero.2
  have hs : hit (S w) (separatingRow w v p) = false := hit_false _ _
    (Finset.disjoint_left.mpr (by
      intro q hq hX
      exact hps ((hrow q (support_subset S A B u hcorrect w hq) hX) ▸ hq)))
  have h := hcorrect w (separatingRow w v p) hc
  rw [hit_true _ _ p hpw hpX] at h
  simp [output, hw, hs, hh] at h


lemma normalize_supports (S : Fin 13 → Finset (Fin 13)) (A B : Finset (Fin 13))
    (u : Fin 13 → Bool) (hcorrect : Correct S A B u) :
    ∃ R : Finset (Fin 13),
      (R = ∅ ∨ R = A ∨ R = B ∨ ∃ p, R = {p}) ∧
      ∀ w, S w ∪ (if u w then R else ∅) = line w := by
  classical
  by_cases hpair : ∃ a b : Fin 13, u a = true ∧ u b = true ∧ a ≠ b
  · obtain ⟨a, b, ha, hb, hab⟩ := hpair
    by_cases hres : ∃ w : Fin 13, u w = true ∧ ∃ p, p ∈ line w \ S w
    · obtain ⟨w, hw, p, hp⟩ := hres
      have hpall : ∀ v, u v = true → p ∈ line v := by
        intro v hv
        exact residual_subset_user S A B u hcorrect w v hw hv hp
      refine ⟨{p}, Or.inr (Or.inr (Or.inr ⟨p, rfl⟩)), ?_⟩
      intro v
      cases hv : u v with
      | false => simpa [hv] using unused_complete S A B u hcorrect v hv
      | true =>
        simp only [ite_true]
        apply Finset.Subset.antisymm
        · exact Finset.union_subset (support_subset S A B u hcorrect v)
            (Finset.singleton_subset_iff.mpr (hpall v hv))
        · intro q hq
          by_cases hqs : q ∈ S v
          · exact Finset.mem_union_left _ hqs
          · have hqr : q ∈ line v \ S v := Finset.mem_sdiff.mpr ⟨hq, hqs⟩
            have hqa := residual_subset_user S A B u hcorrect v a hv ha hqr
            have hqb := residual_subset_user S A B u hcorrect v b hv hb hqr
            have hqp : q = p := Finset.card_le_one.mp (line_meet a b hab).le q
              (Finset.mem_inter.mpr ⟨hqa, hqb⟩) p
              (Finset.mem_inter.mpr ⟨hpall a ha, hpall b hb⟩)
            exact Finset.mem_union_right _ (by simpa using hqp)
    · refine ⟨∅, Or.inl rfl, ?_⟩
      intro v
      cases hv : u v with
      | false => simpa [hv] using unused_complete S A B u hcorrect v hv
      | true =>
        simp only [ite_true, Finset.union_empty]
        apply Finset.Subset.antisymm (support_subset S A B u hcorrect v)
        intro p hp
        by_contra hn
        exact hres ⟨v, hv, p, Finset.mem_sdiff.mpr ⟨hp, hn⟩⟩
  · by_cases huser : ∃ w : Fin 13, u w = true
    · obtain ⟨w, hw⟩ := huser
      have unique : ∀ v, u v = true → v = w := by
        intro v hv
        by_contra hvw
        exact hpair ⟨v, w, hv, hw, hvw⟩
      rcases parent_subset S A B u hcorrect w hw with hA | hB
      · refine ⟨A, Or.inr (Or.inl rfl), ?_⟩
        intro v
        cases hv : u v with
        | false => simpa [hv] using unused_complete S A B u hcorrect v hv
        | true =>
          have he := unique v hv
          subst v
          simpa [hw] using parent_complete_left S A B u hcorrect w hA
      · have hswap : Correct S B A u := by
          intro v X hc
          simpa [output, Bool.and_comm] using hcorrect v X hc
        refine ⟨B, Or.inr (Or.inr (Or.inl rfl)), ?_⟩
        intro v
        cases hv : u v with
        | false => simpa [hv] using unused_complete S A B u hcorrect v hv
        | true =>
          have he := unique v hv
          subst v
          simpa [hw] using parent_complete_left S B A u hswap w hB
    · refine ⟨∅, Or.inl rfl, ?_⟩
      intro v
      cases hv : u v with
      | false => simpa [hv] using unused_complete S A B u hcorrect v hv
      | true => exact (huser ⟨v, hv⟩).elim

end PEqualNP.Outside.L_meta_1024_aux.OneAnd


namespace PEqualNP.Outside.L_meta_1024_aux.Cut

open PEqualNP.CircuitLowerBounds

lemma cutVal_append_old {M : ℕ} (n : ℕ) (P : Finset ℕ) (gs hs : List Gate)
    (x : Fin M → Bool) (i : ℕ) (hi : i < n + gs.length) :
    cutVal n P (gs ++ hs) x i = cutVal n P gs x i := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, cutVal_snoc,
      ite_eq_right (show i ≠ n + (gs ++ hs).length by simp; omega)]
    exact ih

lemma cutVal_take {M : ℕ} (n : ℕ) (P : Finset ℕ) (gs : List Gate)
    (x : Fin M → Bool) (k i : ℕ) (hk : k ≤ gs.length) (hi : i < n + k) :
    cutVal n P gs x i = cutVal n P (gs.take k) x i := by
  have hlen : (gs.take k).length = k := by simp [List.length_take, Nat.min_eq_left hk]
  have h := cutVal_append_old n P (gs.take k) (gs.drop k) x i (by rw [hlen]; exact hi)
  simpa only [List.take_append_drop] using h

lemma essential_take {M : ℕ} (n : ℕ) (P : Finset ℕ) (gs : List Gate)
    (k i : ℕ) (hk : k ≤ gs.length) (hi : i < n + k) :
    essential (M := M) n P gs i = essential n P (gs.take k) i := by
  classical
  ext t
  simp only [essential, Finset.mem_filter, Finset.mem_univ, true_and, Depends]
  constructor
  · rintro ⟨x, y, hxy, hne⟩
    refine ⟨x, y, hxy, ?_⟩
    rwa [cutVal_take n P gs x k i hk hi, cutVal_take n P gs y k i hk hi] at hne
  · rintro ⟨x, y, hxy, hne⟩
    refine ⟨x, y, hxy, ?_⟩
    rwa [cutVal_take n P gs x k i hk hi, cutVal_take n P gs y k i hk hi]

lemma unpaid_two_later (n : ℕ) (P : Finset ℕ) (gs : List Gate) (k i j : ℕ)
    (hk : k ≤ gs.length) (hi : n + k ≤ i) (hj : n + k ≤ j)
    (hiend : i < n + gs.length) (hjend : j < n + gs.length)
    (hip : i ∉ P) (hjp : j ∉ P) (hij : i ≠ j) :
    unpaid n P (gs.take k) + 2 ≤ unpaid n P gs := by
  classical
  let D := (Finset.Ico n (n + (gs.take k).length)) \ P
  let F := (Finset.Ico n (n + gs.length)) \ P
  have hlen : (gs.take k).length = k := by simp [List.length_take, Nat.min_eq_left hk]
  have hD : D ⊆ F := by
    intro a ha
    simp only [D, F, Finset.mem_sdiff, Finset.mem_Ico] at ha ⊢
    exact ⟨⟨ha.1.1, by rw [hlen] at ha; omega⟩, ha.2⟩
  have hiD : i ∉ D := by
    simp only [D, Finset.mem_sdiff, Finset.mem_Ico, hlen]
    omega
  have hjD : j ∉ D := by
    simp only [D, Finset.mem_sdiff, Finset.mem_Ico, hlen]
    omega
  have hiF : i ∈ F := by
    simp only [F, Finset.mem_sdiff, Finset.mem_Ico]
    exact ⟨⟨by omega, hiend⟩, hip⟩
  have hjF : j ∈ F := by
    simp only [F, Finset.mem_sdiff, Finset.mem_Ico]
    exact ⟨⟨by omega, hjend⟩, hjp⟩
  have hsub : insert i (insert j D) ⊆ F :=
    Finset.insert_subset_iff.mpr ⟨hiF, Finset.insert_subset_iff.mpr ⟨hjF, hD⟩⟩
  have hc := Finset.card_le_card hsub
  have hnot : i ∉ insert j D := by simp [hij, hiD]
  rw [Finset.card_insert_of_notMem hnot, Finset.card_insert_of_notMem hjD] at hc
  change D.card + 2 ≤ F.card
  omega

def rawSupport {M n : ℕ} (E : Finset (Fin M)) (hraw : ∀ t ∈ E, t.val < n) :
    Finset (Fin n) :=
  E.attach.image fun t => (⟨t.val.val, hraw t.val t.property⟩ : Fin n)

lemma rawSupport_card {M n : ℕ} (E : Finset (Fin M)) (hraw : ∀ t ∈ E, t.val < n) :
    (rawSupport E hraw).card ≤ E.card := by
  exact (Finset.card_image_le).trans_eq Finset.card_attach

lemma actualSources_raw {n : ℕ} (gs : List Gate) (x : Fin n → Bool)
    (t : Fin (n + gs.length)) (ht : t.val < n) :
    actualSources gs x t = x ⟨t.val, ht⟩ := by
  unfold actualSources
  rw [← cut_empty]
  have h := cutVal_append_old n ∅ [] gs x t.val (by simpa using ht)
  simp only [List.nil_append] at h
  rw [h, cutVal_nil]
  simp [ht, source_eq]

lemma raw_essential_support {n : ℕ} (P : Finset ℕ) (gs : List Gate) (o : ℕ)
    (hraw : ∀ t ∈ essential (M := n + gs.length) n P gs o, t.val < n) :
    ∀ x y : Fin n → Bool,
      (∀ p ∈ rawSupport (essential n P gs o) hraw, x p = y p) →
      Circuit.eval ⟨gs, o⟩ (List.ofFn x) = Circuit.eval ⟨gs, o⟩ (List.ofFn y) := by
  intro x y hxy
  rw [← factor P gs x o, ← factor P gs y o]
  apply essential_supports n P gs o
  intro t ht
  rw [actualSources_raw gs x t (hraw t ht), actualSources_raw gs y t (hraw t ht)]
  apply hxy
  exact Finset.mem_image.mpr ⟨⟨t, ht⟩, by simp, rfl⟩

lemma raw_support_exists {n : ℕ} (P : Finset ℕ) (gs : List Gate) (o b : ℕ)
    (hraw : ∀ t ∈ essential (M := n + gs.length) n P gs o, t.val < n)
    (hcard : (essential (M := n + gs.length) n P gs o).card ≤ b) :
    ∃ S : Finset (Fin n), S.card ≤ b ∧
      ∀ x y : Fin n → Bool, (∀ p ∈ S, x p = y p) →
        Circuit.eval ⟨gs, o⟩ (List.ofFn x) = Circuit.eval ⟨gs, o⟩ (List.ofFn y) := by
  exact ⟨rawSupport (essential n P gs o) hraw,
    (rawSupport_card _ hraw).trans hcard, raw_essential_support P gs o hraw⟩

end PEqualNP.Outside.L_meta_1024_aux.Cut


namespace PEqualNP.Outside.L_meta_1024_aux.Clamp9

set_option maxHeartbeats 2000000 in
lemma positive_frontier_impossible {m : ℕ} (w : Fin 13)
    (E : Finset (Fin m)) (F : (Fin m → Bool) → Bool)
    (leaf : Fin m → (Fin 13 → Bool) → Bool)
    (hmono : ∀ a b, (∀ i, a i = true → b i = true) → F a = true → F b = true)
    (hsupport : ∀ a b, (∀ i ∈ E, a i = b i) → F a = F b)
    (hleaf : ∀ i ∈ E, ∀ x y, (∀ q, x q = true → y q = true) →
      leaf i x = true → leaf i y = true)
    (hcorrect : ∀ x, Support.Band x → F (fun i => leaf i x) = Support.target w x)
    (x : Fin 13 → Bool) (hx : Support.Band x) (hpos : Support.target w x = true)
    (hcount : (E.filter (fun i => leaf i x = true)).card ≤ 8)
    (hforeign : ∀ i ∈ E, leaf i x = true →
      ∃ q : Fin 13, q ∉ Support.line w ∧ leaf i (Clamp.singleton q) = true) : False := by
  classical
  let T := E.filter (fun i => leaf i x = true)
  let q : Fin m → Fin 13 := fun i => if h : i ∈ T then
    Classical.choose (hforeign i (Finset.mem_filter.mp h).1 (Finset.mem_filter.mp h).2) else 0
  have q_spec (i : Fin m) (hi : i ∈ T) :
      q i ∉ Support.line w ∧ leaf i (Clamp.singleton (q i)) = true := by
    simpa only [q, dite_eq_left hi] using Classical.choose_spec
      (hforeign i (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hi).2)
  let Q := T.image q
  have hQcard : Q.card ≤ 8 := Finset.card_image_le.trans hcount
  have hQ : Q ⊆ Finset.univ \ Support.line w := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (q_spec i hi).1⟩
  obtain ⟨Y, hQY, hY, hYcard⟩ := Clamp.extend_eight w Q hQ hQcard
  have hptrue : F (fun i => leaf i x) = true := (hcorrect x hx).trans hpos
  have hyfalse : F (fun i => leaf i (Clamp.fromTrue Y)) = false :=
    (hcorrect _ (Clamp.fromTrue_band Y hYcard)).trans (Clamp.fromTrue_misses w Y hY)
  have hcompare : ∀ i ∈ E, leaf i x = true → leaf i (Clamp.fromTrue Y) = true := by
    intro i hi hix
    have hiT : i ∈ T := Finset.mem_filter.mpr ⟨hi, hix⟩
    have hqi : q i ∈ Y := hQY (Finset.mem_image.mpr ⟨i, hiT, rfl⟩)
    apply hleaf i hi (Clamp.singleton (q i)) (Clamp.fromTrue Y) _ (q_spec i hiT).2
    intro r hr
    have he : r = q i := by simpa [Clamp.singleton] using hr
    subst r
    simp [Clamp.fromTrue, hqi]
  have hytrue := Clamp.supported_mono F E hmono hsupport _ _ hcompare hptrue
  rw [hyfalse] at hytrue
  exact Bool.noConfusion hytrue

set_option maxHeartbeats 2000000 in
lemma missing_raw_impossible {m : ℕ} (w p : Fin 13) (hp : p ∈ Support.line w)
    (E : Finset (Fin m)) (hE : E.card ≤ 9) (F : (Fin m → Bool) → Bool)
    (leaf : Fin m → (Fin 13 → Bool) → Bool)
    (hmono : ∀ a b, (∀ i, a i = true → b i = true) → F a = true → F b = true)
    (hsupport : ∀ a b, (∀ i ∈ E, a i = b i) → F a = F b)
    (hleaf : ∀ i ∈ E, ∀ x y, (∀ q, x q = true → y q = true) →
      leaf i x = true → leaf i y = true)
    (hcorrect : ∀ x, Support.Band x → F (fun i => leaf i x) = Support.target w x)
    (hclass : ∀ i ∈ E,
      (∃ q ∈ Support.line w, q ≠ p ∧ ∀ x, leaf i x = x q) ∨
      ∃ q : Fin 13, q ∉ Support.line w ∧ leaf i (Clamp.singleton q) = true)
    (hnotabove : ∀ i ∈ E, ∃ x : Fin 13 → Bool,
      Support.Band x ∧ Support.target w x = true ∧ leaf i x = false) : False := by
  classical
  let x := Support.flip w p
  have hx : Support.Band x := Or.inl (Support.flip_spec w p hp).1
  have hxpos : Support.target w x = true := (Support.flip_spec w p hp).2
  have hforeign (i : Fin m) (hi : i ∈ E) (hit : leaf i x = true) :
      ∃ q : Fin 13, q ∉ Support.line w ∧ leaf i (Clamp.singleton q) = true := by
    rcases hclass i hi with ⟨q, hq, hqp, hraw⟩ | hforeign
    · have hfalse : leaf i x = false := by
        rw [hraw]
        exact (ite_eq_right hqp).trans (Clamp.row_line_false w q hq)
      rw [hfalse] at hit
      exact Bool.noConfusion hit
    · exact hforeign
  let T := E.filter (fun i => leaf i x = true)
  by_cases hT : T.card ≤ 8
  · exact positive_frontier_impossible w E F leaf hmono hsupport hleaf hcorrect x hx hxpos hT hforeign
  have hTE : T = E := Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
  have hE9 : E.card = 9 := by rw [hTE] at hT; omega
  have hEpos : E.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨i, hi⟩ := hEpos
  obtain ⟨y, hy, hypos, hiy⟩ := hnotabove i hi
  have hforeignall (j : Fin m) (hj : j ∈ E) :
      ∃ q : Fin 13, q ∉ Support.line w ∧ leaf j (Clamp.singleton q) = true := by
    apply hforeign j hj
    have hjT : j ∈ T := hTE.symm ▸ hj
    exact (Finset.mem_filter.mp hjT).2
  have hcount : (E.filter (fun j => leaf j y = true)).card ≤ 8 := by
    have hs : E.filter (fun j => leaf j y = true) ⊆ E.erase i := by
      intro j hj
      obtain ⟨hjE, hjtrue⟩ := Finset.mem_filter.mp hj
      apply Finset.mem_erase.mpr
      refine ⟨?_, hjE⟩
      intro he
      subst j
      rw [hiy] at hjtrue
      exact Bool.noConfusion hjtrue
    have hh := Finset.card_le_card hs
    rw [Finset.card_erase_of_mem hi, hE9] at hh
    exact hh
  exact positive_frontier_impossible w E F leaf hmono hsupport hleaf hcorrect y hy hypos hcount
    (fun j hj _ => hforeignall j hj)

end PEqualNP.Outside.L_meta_1024_aux.Clamp9

namespace PEqualNP.Outside.L_meta_1024_aux.Charges

open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma line_difference : ∀ w a : Fin 13, a ≠ w →
    ∃ p ∈ Global.line w, p ∉ Global.line a := by decide +kernel

lemma charge_not_above (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w a : Fin 13) (hwa : a ≠ w) (i : ℕ) (hi : i ∈ Global.D (Global.line a) gs) :
    ∃ x : Fin 13 → Bool, Support.Band x ∧ Support.target w x = true ∧
      Global.val gs x i = false := by
  classical
  obtain ⟨p, hpw, hpa⟩ := line_difference w a hwa
  have hsub : ({p} : Finset (Fin 13)) ⊆ Finset.univ \ Support.line a := by
    intro q hq
    have he : q = p := Finset.mem_singleton.mp hq
    subst q
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hpa⟩
  obtain ⟨Y, hpY, hY, hYcard⟩ := Clamp.extend_eight a {p} hsub (by simp)
  refine ⟨Clamp.fromTrue Y, Clamp.fromTrue_band Y hYcard, ?_, ?_⟩
  · apply decide_eq_true_iff.mpr
    exact ⟨p, hpw, by simp [Clamp.fromTrue, hpY (Finset.mem_singleton_self p)]⟩
  · have hz : Global.val gs (Global.Zof (Global.line a)) i = false :=
      (Finset.mem_filter.mp hi).2.1
    cases he : Global.val gs (Clamp.fromTrue Y) i
    · rfl
    · have ht := Bridge.val_mono gs hg (Clamp.fromTrue Y) (Global.Zof (Global.line a))
        (by
          intro q hq
          have hqY : q ∈ Y := by simpa [Clamp.fromTrue] using hq
          simpa [Global.Zof, Global.line, Support.line] using (Finset.mem_sdiff.mp (hY hqY)).2) i he
      rw [hz] at ht
      exact Bool.noConfusion ht

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma raw_not_above : ∀ w q : Fin 13, ∃ r : Fin 13,
    Support.target w (Support.row r) = true ∧ Support.row r q = false := by
  decide +kernel

end PEqualNP.Outside.L_meta_1024_aux.Charges

namespace PEqualNP.Outside.L_meta_1024_aux.Charges
open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_1024_aux.Global
lemma ordinary_charge_family_strong (gs : List Gate) (out : Fin 13 → ℕ) (W : Finset (Fin 13))
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hordinary : ∀ a ∈ W, ∀ x : Fin 13 → Bool,
      Circuit.eval ⟨gs, out a⟩ (List.ofFn x) = decide (∃ p ∈ Global.line a, x p = true)) :
    ∃ P : Finset ℕ, P ⊆ Finset.Ico 13 (13 + gs.length) ∧ 3 * W.card ≤ P.card ∧
      ∀ w ∉ W, ∀ i ∈ P, (∃ q : Fin 13, q ∉ Global.line w ∧ Global.val gs (Global.eof q) i = true) ∧
      (∃ x : Fin 13 → Bool, Support.Band x ∧ Support.target w x = true ∧ Global.val gs x i = false) := by
  classical
  let P := W.biUnion (fun a => Global.D (Global.line a) gs)
  have hsubset : P ⊆ Finset.Ico 13 (13 + gs.length) := by
    intro i hi
    obtain ⟨a, _, hai⟩ := Finset.mem_biUnion.mp hi
    exact (Finset.mem_filter.mp hai).1
  have hcount : 3 * W.card ≤ P.card := by
    have hd : ∀ a ∈ W, ∀ b ∈ W, a ≠ b → Disjoint (Global.D (Global.line a) gs) (Global.D (Global.line b) gs) := by
      intro a _ b _ hab
      exact disjoint_charges gs hg a b hab
    have hsum : (∑ _a ∈ W, (3 : ℕ)) ≤ ∑ a ∈ W, (Global.D (Global.line a) gs).card := by
      apply Finset.sum_le_sum
      intro a ha
      exact ordinary_charge_count gs (out a) a hg (hordinary a ha)
    rw [← Finset.card_biUnion hd] at hsum
    simpa [P, Nat.mul_comm] using hsum
  refine ⟨P, hsubset, hcount, ?_⟩
  intro w hw i hi
  obtain ⟨a, ha, hai⟩ := Finset.mem_biUnion.mp hi
  have hne : a ≠ w := fun he => hw (he ▸ ha)
  exact ⟨charge_outside gs hg w a hne i hai,
    charge_not_above gs (fun g hm => (hg g hm).1) w a hne i hai⟩

end PEqualNP.Outside.L_meta_1024_aux.Charges

namespace PEqualNP.Outside.L_meta_1024_aux.Bridge
open PEqualNP.CircuitLowerBounds
lemma raw_line_members9 (gs : List Gate) (o : ℕ) (w : Fin 13)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hcorrect : ∀ x : Fin 13 → Bool, Support.Band x →
      Global.val gs x o = Support.target w x)
    (P : Finset ℕ)
    (hPoutside : ∀ i ∈ P, ∃ q : Fin 13,
      q ∉ Global.line w ∧ Global.val gs (Global.eof q) i = true)
    (hPnotabove : ∀ i ∈ P, ∃ x : Fin 13 → Bool, Support.Band x ∧
      Support.target w x = true ∧ Global.val gs x i = false)
    (F : (Fin (13 + gs.length) → Bool) → Bool)
    (E : Finset (Fin (13 + gs.length))) (hEcard : E.card ≤ 9)
    (hallowed : ∀ i ∈ E, i.val < 13 ∨ i.val ∈ P)
    (hmono : ∀ a b, (∀ i, a i = true → b i = true) → F a = true → F b = true)
    (hsupport : ∀ a b, (∀ i ∈ E, a i = b i) → F a = F b)
    (hfactor : ∀ x : Fin 13 → Bool, F (fun i => Global.val gs x i.val) = Global.val gs x o)
    (p : Fin 13) (hp : p ∈ Global.line w) : rawIndex gs p ∈ E := by
  classical
  by_contra hpnot
  apply Clamp9.missing_raw_impossible w p hp E hEcard F
    (fun i x => Global.val gs x i.val) hmono hsupport
  · intro i _ x y hxy hx
    exact val_mono gs hg x y hxy i.val hx
  · intro x hx
    rw [hfactor]
    exact hcorrect x hx
  · intro i hi
    rcases hallowed i hi with hiraw | hipaid
    · let q : Fin 13 := ⟨i.val, hiraw⟩
      have hraw : ∀ x : Fin 13 → Bool, Global.val gs x i.val = x q := fun x => val_input gs x q
      by_cases hql : q ∈ Global.line w
      · left
        refine ⟨q, hql, ?_, hraw⟩
        intro hqp
        have hie : i = rawIndex gs p := by
          apply Fin.ext
          exact congrArg (fun t : Fin 13 => t.val) hqp
        exact hpnot (hie ▸ hi)
      · right
        refine ⟨q, hql, ?_⟩
        rw [hraw]
        simp [Clamp.singleton]
    · obtain ⟨q, hq, hqtrue⟩ := hPoutside i.val hipaid
      exact Or.inr ⟨q, hq, hqtrue⟩
  · intro i hi
    rcases hallowed i hi with hiraw | hipaid
    · let q : Fin 13 := ⟨i.val, hiraw⟩
      obtain ⟨r, hrt, hrq⟩ := Charges.raw_not_above w q
      refine ⟨Support.row r, Or.inr (Support.row_spec r).1, hrt, ?_⟩
      exact (val_input gs (Support.row r) q).trans hrq
    · exact hPnotabove i.val hipaid

lemma output_index (gs : List Gate) (o : ℕ) (w : Fin 13)
    (hcorrect : ∀ x : Fin 13 → Bool, Support.Band x →
      Global.val gs x o = Support.target w x) : 13 ≤ o ∧ o < 13 + gs.length := by
  constructor
  · by_contra! ho
    let q : Fin 13 := ⟨o, ho⟩
    obtain ⟨r, hrt, hrq⟩ := Charges.raw_not_above w q
    have hval := hcorrect (Support.row r) (Or.inr (Support.row_spec r).1)
    have hi : Global.val gs (Support.row r) o = false :=
      (val_input gs (Support.row r) q).trans hrq
    rw [hi, hrt] at hval
    exact Bool.noConfusion hval
  · by_contra! ho
    have hne : (Global.line w).Nonempty := Finset.card_pos.mp (by rw [Global.line_card]; decide)
    obtain ⟨p, hp⟩ := hne
    have hv : Global.val gs (Support.flip w p) o = false := by
      unfold Global.val
      apply List.getD_eq_default
      rw [Global.fold_length, List.length_ofFn]
      exact ho
    have hh := hcorrect (Support.flip w p) (Or.inl (Support.flip_spec w p hp).1)
    rw [hv, (Support.flip_spec w p hp).2] at hh
    exact Bool.noConfusion hh

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma row_targets : ∀ a b : Fin 13, a ≠ b → Support.target b (Support.row a) = true := by
  decide +kernel

lemma output_distinct (gs : List Gate) (out : Fin 13 → ℕ)
    (hcorrect : ∀ (w : Fin 13) (x : Fin 13 → Bool), Support.Band x →
      Global.val gs x (out w) = Support.target w x) : Function.Injective out := by
  intro a b hab
  by_contra hne
  have ha := hcorrect a (Support.row a) (Or.inr (Support.row_spec a).1)
  have hb := hcorrect b (Support.row a) (Or.inr (Support.row_spec a).1)
  rw [hab, hb, (Support.row_spec a).2, row_targets a b hne] at ha
  exact Bool.noConfusion ha

end PEqualNP.Outside.L_meta_1024_aux.Bridge




namespace PEqualNP.Outside.L_meta_1024_aux.Bridge
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma triple_geometry : ∀ a b c : Fin 13, a ≠ b → a ≠ c → b ≠ c →
    9 ≤ ((Global.line a ∪ Global.line b) ∪ Global.line c).card := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma three_exotic_core (gs : List Gate) (out : Fin 13 → ℕ)
    (a b c : Fin 13) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ (w : Fin 13) (x : Fin 13 → Bool), Support.Band x →
      Circuit.eval ⟨gs, out w⟩ (List.ofFn x) = Support.target w x)
    (hordinary : ∀ w : Fin 13, w ≠ a → w ≠ b → w ≠ c → ∀ x : Fin 13 → Bool,
      Circuit.eval ⟨gs, out w⟩ (List.ofFn x) = Support.target w x)
    (hnona : ¬ ∀ x : Fin 13 → Bool, Circuit.eval ⟨gs, out a⟩ (List.ofFn x) = Support.target a x)
    (hminb : out a ≤ out b) (hminc : out a ≤ out c) : 39 ≤ gs.length := by
  classical
  by_contra! hsmall
  let T : Finset (Fin 13) := {a, b, c}
  let W : Finset (Fin 13) := Finset.univ \ T
  have hT : T.card = 3 := by simp [T, hab, hac, hbc]
  have hW : W.card = 10 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), hT]
    decide
  have hord : ∀ w ∈ W, ∀ x : Fin 13 → Bool,
      Circuit.eval ⟨gs, out w⟩ (List.ofFn x) = decide (∃ p ∈ Global.line w, x p = true) := by
    intro w hw
    have hnt := (Finset.mem_sdiff.mp hw).2
    have hwa : w ≠ a := fun h => hnt (by simp [T, h])
    have hwb : w ≠ b := fun h => hnt (by simp [T, h])
    have hwc : w ≠ c := fun h => hnt (by simp [T, h])
    exact hordinary w hwa hwb hwc
  obtain ⟨P, hP, hPcard, hPprops⟩ := Charges.ordinary_charge_family_strong gs out W hg hord
  have hP30 : 30 ≤ P.card := by simpa [hW] using hPcard
  have hPupper : P.card ≤ gs.length := by simpa using Finset.card_le_card hP
  have hbudget : Cut.unpaid 13 P gs ≤ 8 := by
    rw [Cut.unpaid_eq_sub 13 P gs hP]
    omega
  have hnotW (w : Fin 13) (hw : w ∈ T) : w ∉ W := by
    intro hh
    exact (Finset.mem_sdiff.mp hh).2 hw
  let E (w : Fin 13) := Cut.essential (M := 13 + gs.length) 13 P gs (out w)
  have hraw (w : Fin 13) (hw : w ∈ T) (p : Fin 13) (hp : p ∈ Global.line w) :
      rawIndex gs p ∈ E w := by
    apply raw_line_members9 gs (out w) w (fun g hm => (hg g hm).1) (hcorrect w) P
      (fun i hi => (hPprops w (hnotW w hw) i hi).1)
      (fun i hi => (hPprops w (hnotW w hw) i hi).2)
      (fun x => Cut.cutVal 13 P gs x (out w)) (E w)
    · have hh := Cut.essential_card (M := 13 + gs.length) 13 P gs (out w)
        (fun g hm => (hg g hm).2)
      change (E w).card ≤ _ at hh
      omega
    · exact Cut.essential_sources 13 P gs (out w)
    · intro x y hxy hx
      exact Cut.cutVal_mono 13 P gs (fun g hm => (hg g hm).1) x y hxy (out w) hx
    · exact Cut.essential_supports 13 P gs (out w)
    · intro x
      exact Cut.factor P gs x (out w)
    · exact hp
  let S := (E a ∪ E b) ∪ E c
  obtain ⟨label, wire, hcomponents, hdepends⟩ := Cut.components 13 P S gs (fun g hm => (hg g hm).2)
  have hlabel (w : Fin 13) (i : Fin (13 + gs.length)) (hi : i ∈ E w) :
      label i = wire (out w) :=
    hdepends (out w) i (Finset.mem_filter.mp hi).2
  have habwire : wire (out a) = wire (out b) := by
    obtain ⟨p, hpa, hpb⟩ := (pair_geometry a b hab).2
    exact (hlabel a _ (hraw a (by simp [T]) p hpa)).symm.trans
      (hlabel b _ (hraw b (by simp [T]) p hpb))
  have hacwire : wire (out a) = wire (out c) := by
    obtain ⟨p, hpa, hpc⟩ := (pair_geometry a c hac).2
    exact (hlabel a _ (hraw a (by simp [T]) p hpa)).symm.trans
      (hlabel c _ (hraw c (by simp [T]) p hpc))
  have himg : S.image label ⊆ {wire (out a)} := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
    apply Finset.mem_singleton.mpr
    rcases Finset.mem_union.mp hi with hiab | hic
    · rcases Finset.mem_union.mp hiab with hia | hib
      · exact hlabel a i hia
      · exact (hlabel b i hib).trans habwire.symm
    · exact (hlabel c i hic).trans hacwire.symm
  have himgcard : (S.image label).card ≤ 1 := by simpa using Finset.card_le_card himg
  have hS9 : S.card ≤ 9 := by omega
  let R := ((Global.line a ∪ Global.line b) ∪ Global.line c).image (rawIndex gs)
  have hinj : Function.Injective (rawIndex gs) := by
    intro p q hpq
    apply Fin.ext
    exact congrArg (fun t : Fin (13 + gs.length) => t.val) hpq
  have hR9 : 9 ≤ R.card := by
    rw [Finset.card_image_of_injective _ hinj]
    exact triple_geometry a b c hab hac hbc
  have hRS : R ⊆ S := by
    intro i hi
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hi
    rcases Finset.mem_union.mp hp with hpab | hpc
    · rcases Finset.mem_union.mp hpab with hpa | hpb
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (hraw a (by simp [T]) p hpa))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (hraw b (by simp [T]) p hpb))
    · exact Finset.mem_union_right _ (hraw c (by simp [T]) p hpc)
  have hReq : R = S := Finset.eq_of_subset_of_card_le hRS (by omega)
  have hrawonly : ∀ i ∈ E a, i.val < 13 := by
    intro i hi
    have hiS : i ∈ S := Finset.mem_union_left _ (Finset.mem_union_left _ hi)
    have hiR : i ∈ R := hReq.symm ▸ hiS
    obtain ⟨p, _, he⟩ := Finset.mem_image.mp hiR
    rw [← he]
    exact p.isLt
  have hE8 : 8 ≤ (E a).card := by
    by_contra! hlt
    have hE7 : (E a).card ≤ 7 := by omega
    obtain ⟨Q, hQcard, hQsupport⟩ := Cut.raw_support_exists (n := 13) P gs (out a) 7 hrawonly hE7
    exact hnona (Support.circuit_support_exact gs (out a) a (fun g hm => (hg g hm).1)
      (hcorrect a) Q hQcard hQsupport)
  have hindices (w : Fin 13) := output_index gs (out w) w (hcorrect w)
  have houtinj := output_distinct gs out hcorrect
  have houtab : out a ≠ out b := fun he => hab (houtinj he)
  have houtac : out a ≠ out c := fun he => hac (houtinj he)
  have houtbc : out b ≠ out c := fun he => hbc (houtinj he)
  have hnotpaid (w : Fin 13) (hw : w ∈ T) : out w ∉ P := by
    intro hi
    obtain ⟨x, hx, hxt, hxf⟩ := (hPprops w (hnotW w hw) (out w) hi).2
    have hh := hcorrect w x hx
    change Global.val gs x (out w) = _ at hh
    rw [hxf, hxt] at hh
    exact Bool.noConfusion hh
  let k := out a + 1 - 13
  have hk : k ≤ gs.length := by have := hindices a; omega
  have hka : out a < 13 + k := by have := hindices a; omega
  have hkb : 13 + k ≤ out b := by have := hindices a; omega
  have hkc : 13 + k ≤ out c := by have := hindices a; omega
  have hprefix := Cut.essential_card (M := 13 + gs.length) 13 P (gs.take k) (out a)
    (fun g hm => (hg g (List.mem_of_mem_take hm)).2)
  rw [← Cut.essential_take 13 P gs k (out a) hk hka] at hprefix
  change (E a).card ≤ Cut.unpaid 13 P (gs.take k) + 1 at hprefix
  have hlater := Cut.unpaid_two_later 13 P gs k (out b) (out c) hk hkb hkc
    (hindices b).2 (hindices c).2 (hnotpaid b (by simp [T])) (hnotpaid c (by simp [T])) houtbc
  omega

end PEqualNP.Outside.L_meta_1024_aux.Bridge

namespace PEqualNP.Outside.L_meta_1024_aux.Bridge
open PEqualNP.CircuitLowerBounds

lemma three_exotic_bound (gs : List Gate) (out : Fin 13 → ℕ)
    (a b c : Fin 13) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ (w : Fin 13) (x : Fin 13 → Bool), Support.Band x →
      Circuit.eval ⟨gs, out w⟩ (List.ofFn x) = Support.target w x)
    (hordinary : ∀ w : Fin 13, w ≠ a → w ≠ b → w ≠ c → ∀ x : Fin 13 → Bool,
      Circuit.eval ⟨gs, out w⟩ (List.ofFn x) = Support.target w x) : 39 ≤ gs.length := by
  classical
  by_cases ha : ∀ x : Fin 13 → Bool, Circuit.eval ⟨gs, out a⟩ (List.ofFn x) = Support.target a x
  · apply two_exotic_bound gs out b c hbc hg hcorrect
    intro w hwb hwc x
    by_cases hwa : w = a
    · subst w
      exact ha x
    · exact hordinary w hwa hwb hwc x
  by_cases hb : ∀ x : Fin 13 → Bool, Circuit.eval ⟨gs, out b⟩ (List.ofFn x) = Support.target b x
  · apply two_exotic_bound gs out a c hac hg hcorrect
    intro w hwa hwc x
    by_cases hwb : w = b
    · subst w
      exact hb x
    · exact hordinary w hwa hwb hwc x
  by_cases hc : ∀ x : Fin 13 → Bool, Circuit.eval ⟨gs, out c⟩ (List.ofFn x) = Support.target c x
  · apply two_exotic_bound gs out a b hab hg hcorrect
    intro w hwa hwb x
    by_cases hwc : w = c
    · subst w
      exact hc x
    · exact hordinary w hwa hwb hwc x
  rcases Nat.le_total (out a) (out b) with habo | hbao
  · rcases Nat.le_total (out a) (out c) with haco | hcao
    · exact three_exotic_core gs out a b c hab hac hbc hg hcorrect hordinary ha habo haco
    · exact three_exotic_core gs out c a b hac.symm hbc.symm hab hg hcorrect
        (fun w hwc hwa hwb => hordinary w hwa hwb hwc) hc hcao (hcao.trans habo)
  · rcases Nat.le_total (out b) (out c) with hbco | hcbo
    · exact three_exotic_core gs out b a c hab.symm hbc hac hg hcorrect
        (fun w hwb hwa hwc => hordinary w hwa hwb hwc) hb hbao hbco
    · exact three_exotic_core gs out c a b hac.symm hbc.symm hab hg hcorrect
        (fun w hwc hwa hwb => hordinary w hwa hwb hwc) hc (hcbo.trans hbao) hcbo

end PEqualNP.Outside.L_meta_1024_aux.Bridge



namespace PEqualNP.Outside.L_meta_1024_aux.Bridge
open PEqualNP.CircuitLowerBounds

lemma ten_ordinary_bound (gs : List Gate) (out : Fin 13 → ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ (w : Fin 13) (x : Fin 13 → Bool), Support.Band x →
      Circuit.eval ⟨gs, out w⟩ (List.ofFn x) = Support.target w x)
    (W : Finset (Fin 13)) (hW : 10 ≤ W.card)
    (hordinary : ∀ w ∈ W, ∀ x : Fin 13 → Bool,
      Circuit.eval ⟨gs, out w⟩ (List.ofFn x) = Support.target w x) : 39 ≤ gs.length := by
  classical
  obtain ⟨V, hVW, hVcard⟩ := Finset.exists_subset_card_eq hW
  have hcomp : (Finset.univ \ V).card = 3 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), hVcard]
    decide
  obtain ⟨a, b, c, hab, hac, hbc, hC⟩ := Finset.card_eq_three.mp hcomp
  apply three_exotic_bound gs out a b c hab hac hbc hg hcorrect
  intro w hwa hwb hwc x
  apply hordinary w (hVW ?_) x
  by_contra hwV
  have hh : w ∈ Finset.univ \ V := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hwV⟩
  rw [hC] at hh
  simp only [Finset.mem_insert, Finset.mem_singleton] at hh
  rcases hh with h | h | h
  · exact hwa h
  · exact hwb h
  · exact hwc h

noncomputable def exoticSet (gs : List Gate) (out : Fin 13 → ℕ) : Finset (Fin 13) := by
  classical
  exact Finset.univ.filter (fun w => ¬ ∀ x : Fin 13 → Bool,
    Circuit.eval ⟨gs, out w⟩ (List.ofFn x) = Support.target w x)

lemma four_exotic_outputs (gs : List Gate) (out : Fin 13 → ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ (w : Fin 13) (x : Fin 13 → Bool), Support.Band x →
      Circuit.eval ⟨gs, out w⟩ (List.ofFn x) = Support.target w x)
    (hsmall : gs.length < 39) : 4 ≤ (exoticSet gs out).card := by
  classical
  by_contra! hfew
  let W := Finset.univ \ exoticSet gs out
  have hW : 10 ≤ W.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    have hu : (Finset.univ : Finset (Fin 13)).card = 13 := by decide
    rw [hu]
    omega
  have hord : ∀ w ∈ W, ∀ x : Fin 13 → Bool,
      Circuit.eval ⟨gs, out w⟩ (List.ofFn x) = Support.target w x := by
    intro w hw
    have hn := (Finset.mem_sdiff.mp hw).2
    simpa [exoticSet] using hn
  have hh := ten_ordinary_bound gs out hg hcorrect W hW hord
  omega

end PEqualNP.Outside.L_meta_1024_aux.Bridge



namespace PEqualNP.Outside.L_meta_1024_aux.OneAndCircuit

open PEqualNP.CircuitLowerBounds

abbrev Form := Finset (Fin 13) × Bool

def emptyForm : Form := (∅, false)

def join (a b : Form) : Form := (a.1 ∪ b.1, a.2 || b.2)

def evalForm (x : Fin 13 → Bool) (h : Bool) (f : Form) : Bool :=
  decide (∃ p ∈ f.1, x p = true) || (f.2 && h)

def readForm (ws : List Form) (i : ℕ) : Form := ws.getD i emptyForm

def collect (ws : List Form) (ins : List ℕ) : Form :=
  ins.foldr (fun i f => join (readForm ws i) f) emptyForm

def formStep (ws : List Form) (g : Gate) : List Form :=
  ws ++ [collect ws g.inputs]

def runForms (gs : List Gate) (ws : List Form) : List Form := gs.foldl formStep ws

def initial : List Form := List.ofFn (fun p : Fin 13 => ({p}, false))

lemma eval_empty (x : Fin 13 → Bool) (h : Bool) : evalForm x h emptyForm = false := by
  simp [evalForm, emptyForm]

lemma eval_join (x : Fin 13 → Bool) (h : Bool) (a b : Form) :
    evalForm x h (join a b) = (evalForm x h a || evalForm x h b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [evalForm, join, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, Finset.mem_union]
  constructor
  · rintro (⟨p, hp | hp, hx⟩ | ⟨ha | hb, hh⟩)
    · exact Or.inl (Or.inl ⟨p, hp, hx⟩)
    · exact Or.inr (Or.inl ⟨p, hp, hx⟩)
    · exact Or.inl (Or.inr ⟨ha, hh⟩)
    · exact Or.inr (Or.inr ⟨hb, hh⟩)
  · rintro ((⟨p, hp, hx⟩ | ⟨ha, hh⟩) | (⟨p, hp, hx⟩ | ⟨hb, hh⟩))
    · exact Or.inl ⟨p, Or.inl hp, hx⟩
    · exact Or.inr ⟨Or.inl ha, hh⟩
    · exact Or.inl ⟨p, Or.inr hp, hx⟩
    · exact Or.inr ⟨Or.inr hb, hh⟩

lemma read_map (ws : List Form) (x : Fin 13 → Bool) (h : Bool) (i : ℕ) :
    (ws.map (evalForm x h)).getD i false = evalForm x h (readForm ws i) := by
  by_cases hi : i < ws.length
  · simp [readForm, hi]
  · simp [readForm, Nat.le_of_not_lt hi, eval_empty]

lemma eval_collect (ws : List Form) (ins : List ℕ) (x : Fin 13 → Bool) (h : Bool) :
    evalForm x h (collect ws ins) =
      (ins.map (fun i => evalForm x h (readForm ws i))).any id := by
  induction ins with
  | nil => simp [collect, eval_empty]
  | cons i ins ih => simpa only [collect, List.foldr_cons, eval_join, List.map_cons,
      List.any_cons, id_eq] using congrArg (fun b => evalForm x h (readForm ws i) || b) ih

lemma map_step (ws : List Form) (g : Gate) (hop : g.op = GateOp.or)
    (x : Fin 13 → Bool) (h : Bool) :
    (formStep ws g).map (evalForm x h) = Global.step (ws.map (evalForm x h)) g := by
  simp only [formStep, List.map_append, List.map_cons, List.map_nil,
    Global.step, hop, GateOp.eval, eval_collect, read_map]

lemma map_run (gs : List Gate) (ws : List Form)
    (hg : ∀ g ∈ gs, g.op = GateOp.or) (x : Fin 13 → Bool) (h : Bool) :
    (runForms gs ws).map (evalForm x h) =
      gs.foldl Global.step (ws.map (evalForm x h)) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    have hg0 := hg g (by simp)
    have hgs : ∀ a ∈ gs, a.op = GateOp.or := fun a ha => hg a (by simp [ha])
    change (runForms gs (formStep ws g)).map (evalForm x h) = _
    rw [ih _ hgs, map_step ws g hg0]
    rfl

lemma read_run (gs : List Gate) (ws : List Form)
    (hg : ∀ g ∈ gs, g.op = GateOp.or) (x : Fin 13 → Bool) (h : Bool) (i : ℕ) :
    evalForm x h (readForm (runForms gs ws) i) =
      (gs.foldl Global.step (ws.map (evalForm x h))).getD i false := by
  rw [← map_run gs ws hg x h, read_map]

lemma run_length (gs : List Gate) (ws : List Form) :
    (runForms gs ws).length = ws.length + gs.length := by
  induction gs generalizing ws with
  | nil => simp [runForms]
  | cons g gs ih =>
    change (runForms gs (formStep ws g)).length = _
    rw [ih]
    simp [formStep]
    omega

lemma initial_eval (x : Fin 13 → Bool) (h : Bool) :
    initial.map (evalForm x h) = List.ofFn x := by
  simp [initial, evalForm]

lemma collect_closed (ws : List Form) (hc : ∀ f ∈ ws, f.2 = false) (ins : List ℕ) :
    (collect ws ins).2 = false := by
  have hread (i : ℕ) : (readForm ws i).2 = false := by
    by_cases hi : i < ws.length
    · rw [readForm, List.getD_eq_getElem _ _ hi]
      exact hc _ (List.getElem_mem hi)
    · unfold readForm
      rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi)]
      rfl
  induction ins with
  | nil => rfl
  | cons i ins ih =>
    change (join (readForm ws i) (collect ws ins)).2 = false
    simp only [join, hread, ih, Bool.false_or]

lemma run_closed (gs : List Gate) (ws : List Form) (hc : ∀ f ∈ ws, f.2 = false) :
    ∀ f ∈ runForms gs ws, f.2 = false := by
  induction gs generalizing ws with
  | nil => exact hc
  | cons g gs ih =>
    apply ih
    intro f hf
    simp only [formStep, List.mem_append, List.mem_singleton] at hf
    rcases hf with hf | rfl
    · exact hc f hf
    · exact collect_closed ws hc g.inputs

lemma initial_closed : ∀ f ∈ initial, f.2 = false := by
  intro f hf
  simp only [initial, List.mem_ofFn] at hf
  obtain ⟨p, rfl⟩ := hf
  rfl

lemma read_closed (gs : List Gate) (i : ℕ) :
    (readForm (runForms gs initial) i).2 = false := by
  by_cases hi : i < (runForms gs initial).length
  · rw [readForm, List.getD_eq_getElem _ _ hi]
    exact run_closed gs initial initial_closed _ (List.getElem_mem hi)
  · unfold readForm
    rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi)]
    rfl

end PEqualNP.Outside.L_meta_1024_aux.OneAndCircuit


namespace PEqualNP.Outside.L_meta_1024_aux.OneAndCircuit

open PEqualNP.CircuitLowerBounds

def freeForm : Form := (∅, true)

def suffixForms (pre post : List Gate) : List Form :=
  runForms post (runForms pre initial ++ [freeForm])

lemma prefix_map (pre : List Gate) (hg : ∀ g ∈ pre, g.op = GateOp.or)
    (x : Fin 13 → Bool) (h : Bool) :
    (runForms pre initial).map (evalForm x h) =
      pre.foldl Global.step (List.ofFn x) := by
  rw [map_run pre initial hg, initial_eval]

lemma prefix_read (pre : List Gate) (hg : ∀ g ∈ pre, g.op = GateOp.or)
    (x : Fin 13 → Bool) (i : ℕ) :
    decide (∃ p ∈ (readForm (runForms pre initial) i).1, x p = true) =
      (pre.foldl Global.step (List.ofFn x)).getD i false := by
  simpa only [evalForm, Bool.and_false, Bool.or_false, initial_eval] using
    read_run pre initial hg x false i

lemma eval_split (pre post : List Gate) (g : Gate)
    (hpre : ∀ a ∈ pre, a.op = GateOp.or)
    (hpost : ∀ a ∈ post, a.op = GateOp.or) (x : Fin 13 → Bool) (o : ℕ) :
    Circuit.eval ⟨pre ++ g :: post, o⟩ (List.ofFn x) =
      evalForm x
        (g.op.eval (g.inputs.map fun i =>
          (pre.foldl Global.step (List.ofFn x)).getD i false))
        (readForm (suffixForms pre post) o) := by
  let W := pre.foldl Global.step (List.ofFn x)
  let h := g.op.eval (g.inputs.map fun i => W.getD i false)
  have hm : (runForms pre initial ++ [freeForm]).map (evalForm x h) = W ++ [h] := by
    simp only [List.map_append, List.map_cons, List.map_nil, prefix_map pre hpre]
    simp [freeForm, evalForm, W]
  have hr := read_run post (runForms pre initial ++ [freeForm]) hpost x h o
  rw [hm] at hr
  change ((pre ++ g :: post).foldl Global.step (List.ofFn x)).getD o false = _
  rw [List.foldl_append, List.foldl_cons]
  change (post.foldl Global.step (W ++ [h])).getD o false = _
  exact hr.symm

lemma eval_split_binary (pre post : List Gate) (a b : ℕ)
    (hpre : ∀ g ∈ pre, g.op = GateOp.or)
    (hpost : ∀ g ∈ post, g.op = GateOp.or) (x : Fin 13 → Bool) (o : ℕ) :
    Circuit.eval ⟨pre ++ ⟨GateOp.and, [a, b]⟩ :: post, o⟩ (List.ofFn x) =
      evalForm x
        (decide (∃ p ∈ (readForm (runForms pre initial) a).1, x p = true) &&
          decide (∃ p ∈ (readForm (runForms pre initial) b).1, x p = true))
        (readForm (suffixForms pre post) o) := by
  rw [eval_split pre post _ hpre hpost]
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
    List.all_nil, id_eq, Bool.and_true]
  rw [prefix_read pre hpre x a, prefix_read pre hpre x b]

lemma eval_split_copy (pre post : List Gate) (a : ℕ)
    (hpre : ∀ g ∈ pre, g.op = GateOp.or)
    (hpost : ∀ g ∈ post, g.op = GateOp.or) (x : Fin 13 → Bool) (o : ℕ) :
    Circuit.eval ⟨pre ++ ⟨GateOp.or, [a]⟩ :: post, o⟩ (List.ofFn x) =
      evalForm x
        (decide (∃ p ∈ (readForm (runForms pre initial) a).1, x p = true))
        (readForm (suffixForms pre post) o) := by
  rw [eval_split pre post _ hpre hpost]
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
    List.any_nil, id_eq, Bool.or_false]
  rw [prefix_read pre hpre x a]

lemma eval_split_zero (pre post : List Gate)
    (hpre : ∀ g ∈ pre, g.op = GateOp.or)
    (hpost : ∀ g ∈ post, g.op = GateOp.or) (x : Fin 13 → Bool) (o : ℕ) :
    Circuit.eval ⟨pre ++ ⟨GateOp.or, []⟩ :: post, o⟩ (List.ofFn x) =
      evalForm x false (readForm (suffixForms pre post) o) := by
  rw [eval_split pre post _ hpre hpost]
  rfl

end PEqualNP.Outside.L_meta_1024_aux.OneAndCircuit


namespace PEqualNP.Outside.L_meta_1024_aux.OneAndCircuit

open PEqualNP.CircuitLowerBounds

lemma eval_substitution (x : Fin 13 → Bool) (f : Form) (R : Finset (Fin 13)) :
    evalForm x (decide (∃ p ∈ R, x p = true)) f =
      decide (∃ p ∈ f.1 ∪ (if f.2 then R else ∅), x p = true) := by
  rcases f with ⟨S, u⟩
  cases u with
  | false => simp [evalForm]
  | true =>
    apply Bool.eq_iff_iff.mpr
    simp only [evalForm, Bool.true_and, Bool.or_eq_true, decide_eq_true_eq,
      ite_true, Finset.mem_union]
    constructor
    · rintro (⟨p, hp, hx⟩ | ⟨p, hp, hx⟩)
      · exact ⟨p, Or.inl hp, hx⟩
      · exact ⟨p, Or.inr hp, hx⟩
    · rintro ⟨p, hp | hp, hx⟩
      · exact Or.inl ⟨p, hp, hx⟩
      · exact Or.inr ⟨p, hp, hx⟩

lemma replacement_gate (pre : List Gate) (hpre : ∀ g ∈ pre, g.op = GateOp.or)
    (a b : ℕ) (R : Finset (Fin 13))
    (hR : R = ∅ ∨ R = (readForm (runForms pre initial) a).1 ∨
      R = (readForm (runForms pre initial) b).1 ∨ ∃ p, R = {p}) :
    ∃ g : Gate, g.op = GateOp.or ∧ g.inputs.length ≤ 2 ∧
      ∀ x : Fin 13 → Bool,
        g.op.eval (g.inputs.map fun i =>
          (pre.foldl Global.step (List.ofFn x)).getD i false) =
            decide (∃ p ∈ R, x p = true) := by
  rcases hR with rfl | rfl | rfl | ⟨p, rfl⟩
  · refine ⟨⟨GateOp.or, []⟩, rfl, by simp, ?_⟩
    intro x
    simp [GateOp.eval]
  · refine ⟨⟨GateOp.or, [a]⟩, rfl, by simp, ?_⟩
    intro x
    simpa [GateOp.eval] using (prefix_read pre hpre x a).symm
  · refine ⟨⟨GateOp.or, [b]⟩, rfl, by simp, ?_⟩
    intro x
    simpa [GateOp.eval] using (prefix_read pre hpre x b).symm
  · refine ⟨⟨GateOp.or, [p.val]⟩, rfl, by simp, ?_⟩
    intro x
    simpa [GateOp.eval, Global.val] using Bridge.val_input pre x p

lemma binary_normalization (pre post : List Gate) (a b : ℕ) (out : Fin 13 → ℕ)
    (hpre : ∀ g ∈ pre, g.op = GateOp.or)
    (hpost : ∀ g ∈ post, g.op = GateOp.or)
    (hc : ∀ (w : Fin 13) (x : Fin 13 → Bool),
      PEqualNP.Outside.L_meta_1024.OrOnly.band x →
      Circuit.eval ⟨pre ++ ⟨GateOp.and, [a, b]⟩ :: post, out w⟩ (List.ofFn x) =
        decide (∃ p ∈ OneAnd.line w, x p = true)) :
    ∃ g : Gate, g.op = GateOp.or ∧ g.inputs.length ≤ 2 ∧
      ∀ (w : Fin 13) (x : Fin 13 → Bool),
        Circuit.eval ⟨pre ++ g :: post, out w⟩ (List.ofFn x) =
          decide (∃ p ∈ OneAnd.line w, x p = true) := by
  let S : Fin 13 → Finset (Fin 13) := fun w =>
    (readForm (suffixForms pre post) (out w)).1
  let u : Fin 13 → Bool := fun w =>
    (readForm (suffixForms pre post) (out w)).2
  let A := (readForm (runForms pre initial) a).1
  let B := (readForm (runForms pre initial) b).1
  have hsem : OneAnd.Correct S A B u := by
    intro w X hX
    let x : Fin 13 → Bool := fun p => decide (p ∈ X)
    have hz : (Finset.univ.filter (fun p : Fin 13 => x p = false)) = Finset.univ \ X := by
      ext p
      simp [x]
    have hb : PEqualNP.Outside.L_meta_1024.OrOnly.band x := by
      apply Or.inr
      rw [hz]
      simp [Finset.card_sdiff, hX]
    have he := hc w x hb
    rw [eval_split_binary pre post a b hpre hpost] at he
    simpa [OneAnd.output, OneAnd.hit, evalForm, S, A, B, u, x] using he
  obtain ⟨R, hR, hnormal⟩ := OneAnd.normalize_supports S A B u hsem
  obtain ⟨g, hgo, hgl, hge⟩ := replacement_gate pre hpre a b R hR
  refine ⟨g, hgo, hgl, ?_⟩
  intro w x
  rw [eval_split pre post g hpre hpost, hge, eval_substitution]
  change decide (∃ p ∈ S w ∪ (if u w then R else ∅), x p = true) = _
  rw [hnormal w]

lemma oneAnd_line_eq : ∀ w : Fin 13,
    OneAnd.line w = PEqualNP.Outside.L_meta_1024.OrOnly.line w := by
  decide +kernel

lemma binary_lower (pre post : List Gate) (a b : ℕ) (out : Fin 13 → ℕ)
    (hpre : ∀ g ∈ pre, g.op = GateOp.or ∧ g.inputs.length ≤ 2)
    (hpost : ∀ g ∈ post, g.op = GateOp.or ∧ g.inputs.length ≤ 2)
    (hc : ∀ (w : Fin 13) (x : Fin 13 → Bool),
      PEqualNP.Outside.L_meta_1024.OrOnly.band x →
      Circuit.eval ⟨pre ++ ⟨GateOp.and, [a, b]⟩ :: post, out w⟩ (List.ofFn x) =
        decide (∃ p ∈ OneAnd.line w, x p = true)) :
    39 ≤ (pre ++ ⟨GateOp.and, [a, b]⟩ :: post).length := by
  obtain ⟨g, hgo, hgl, hge⟩ := binary_normalization pre post a b out
    (fun g hg => (hpre g hg).1) (fun g hg => (hpost g hg).1) hc
  have hor : ∀ q ∈ pre ++ g :: post, q.op = GateOp.or ∧ q.inputs.length ≤ 2 := by
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hpre q hq
    · rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨hgo, hgl⟩
      · exact hpost q hq
  have hbound := PEqualNP.Outside.L_meta_1024.OrOnly.band_lower (pre ++ g :: post) out hor
    (fun w x _ => by simpa only [oneAnd_line_eq] using hge w x)
  simpa using hbound

end PEqualNP.Outside.L_meta_1024_aux.OneAndCircuit


namespace PEqualNP.Outside.L_meta_1024_aux.OneAndCircuit

open PEqualNP.CircuitLowerBounds

lemma replacement_lower (pre post : List Gate) (g q : Gate) (out : Fin 13 → ℕ)
    (hpre : ∀ g ∈ pre, g.op = GateOp.or ∧ g.inputs.length ≤ 2)
    (hpost : ∀ g ∈ post, g.op = GateOp.or ∧ g.inputs.length ≤ 2)
    (hq : q.op = GateOp.or ∧ q.inputs.length ≤ 2)
    (hc : ∀ (w : Fin 13) (x : Fin 13 → Bool),
      PEqualNP.Outside.L_meta_1024.OrOnly.band x →
      Circuit.eval ⟨pre ++ q :: post, out w⟩ (List.ofFn x) =
        decide (∃ p ∈ OneAnd.line w, x p = true)) : 39 ≤ (pre ++ g :: post).length := by
  have hor : ∀ a ∈ pre ++ q :: post, a.op = GateOp.or ∧ a.inputs.length ≤ 2 := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hpre a ha
    · rcases List.mem_cons.mp ha with rfl | ha
      · exact hq
      · exact hpost a ha
  have hbound := PEqualNP.Outside.L_meta_1024.OrOnly.band_lower (pre ++ q :: post) out hor
    (fun w x hx => by simpa only [oneAnd_line_eq] using hc w x hx)
  simpa using hbound

lemma unary_lower (pre post : List Gate) (a : ℕ) (out : Fin 13 → ℕ)
    (hpre : ∀ g ∈ pre, g.op = GateOp.or ∧ g.inputs.length ≤ 2)
    (hpost : ∀ g ∈ post, g.op = GateOp.or ∧ g.inputs.length ≤ 2)
    (hc : ∀ (w : Fin 13) (x : Fin 13 → Bool),
      PEqualNP.Outside.L_meta_1024.OrOnly.band x →
      Circuit.eval ⟨pre ++ ⟨GateOp.and, [a]⟩ :: post, out w⟩ (List.ofFn x) =
        decide (∃ p ∈ OneAnd.line w, x p = true)) :
    39 ≤ (pre ++ ⟨GateOp.and, [a]⟩ :: post).length := by
  apply replacement_lower pre post _ ⟨GateOp.or, [a]⟩ out hpre hpost ⟨rfl, by simp⟩
  intro w x hx
  have he := hc w x hx
  rw [eval_split pre post _ (fun g hg => (hpre g hg).1)
    (fun g hg => (hpost g hg).1)] at he ⊢
  simpa [GateOp.eval] using he

lemma nullary_lower (pre post : List Gate) (out : Fin 13 → ℕ)
    (hpre : ∀ g ∈ pre, g.op = GateOp.or ∧ g.inputs.length ≤ 2)
    (hpost : ∀ g ∈ post, g.op = GateOp.or ∧ g.inputs.length ≤ 2)
    (hc : ∀ (w : Fin 13) (x : Fin 13 → Bool),
      PEqualNP.Outside.L_meta_1024.OrOnly.band x →
      Circuit.eval ⟨pre ++ ⟨GateOp.and, []⟩ :: post, out w⟩ (List.ofFn x) =
        decide (∃ p ∈ OneAnd.line w, x p = true)) :
    39 ≤ (pre ++ ⟨GateOp.and, []⟩ :: post).length := by
  have hu (w : Fin 13) : (readForm (suffixForms pre post) (out w)).2 = false := by
    have hb : PEqualNP.Outside.L_meta_1024.OrOnly.band (Support.row w) :=
      Or.inr (Support.row_spec w).1
    have hz : decide (∃ p ∈ OneAnd.line w, Support.row w p = true) = false := by
      exact (Support.row_spec w).2
    have he := hc w (Support.row w) hb
    rw [hz, eval_split pre post _ (fun g hg => (hpre g hg).1)
      (fun g hg => (hpost g hg).1)] at he
    simp only [GateOp.eval, List.map_nil, List.all_nil, evalForm,
      Bool.and_true, Bool.or_eq_false_iff] at he
    exact he.2
  apply replacement_lower pre post _ ⟨GateOp.or, []⟩ out hpre hpost ⟨rfl, by simp⟩
  intro w x hx
  have he := hc w x hx
  rw [eval_split pre post _ (fun g hg => (hpre g hg).1)
    (fun g hg => (hpost g hg).1)] at he ⊢
  simpa [GateOp.eval, evalForm, hu w] using he

def isAnd (g : Gate) : Bool := match g.op with
  | GateOp.and => true
  | _ => false

lemma isAnd_true (g : Gate) : isAnd g = true ↔ g.op = GateOp.and := by
  rcases g with ⟨op, ins⟩
  cases op <;> simp [isAnd]

lemma at_most_one_and_lower (gs : List Gate) (out : Fin 13 → ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcount : (gs.filter isAnd).length ≤ 1)
    (hc : ∀ (w : Fin 13) (x : Fin 13 → Bool),
      PEqualNP.Outside.L_meta_1024.OrOnly.band x →
      Circuit.eval ⟨gs, out w⟩ (List.ofFn x) =
        decide (∃ p ∈ OneAnd.line w, x p = true)) : 39 ≤ gs.length := by
  by_cases he : ∃ g ∈ gs, g.op = GateOp.and
  · obtain ⟨g, hmem, hop⟩ := he
    obtain ⟨pre, post, rfl⟩ := List.append_of_mem hmem
    have hgAnd : isAnd g = true := (isAnd_true g).mpr hop
    have hcounts : (pre.filter isAnd).length + (post.filter isAnd).length ≤ 0 := by
      simp only [List.filter_append, List.length_append, List.filter_cons, hgAnd,
        ite_true, List.length_cons] at hcount
      omega
    have hpre : ∀ q ∈ pre, q.op = GateOp.or ∧ q.inputs.length ≤ 2 := by
      intro q hq
      obtain ⟨hopq, hlen⟩ := hg q (by simp [hq])
      refine ⟨?_, hlen⟩
      rcases hopq with hopq | hopq
      · have hm : q ∈ pre.filter isAnd := by
          simp [hq, (isAnd_true q).mpr hopq]
        have hh := List.length_pos_of_mem hm
        omega
      · exact hopq
    have hpost : ∀ q ∈ post, q.op = GateOp.or ∧ q.inputs.length ≤ 2 := by
      intro q hq
      obtain ⟨hopq, hlen⟩ := hg q (by simp [hq])
      refine ⟨?_, hlen⟩
      rcases hopq with hopq | hopq
      · have hm : q ∈ post.filter isAnd := by
          simp [hq, (isAnd_true q).mpr hopq]
        have hh := List.length_pos_of_mem hm
        omega
      · exact hopq
    have hlen := (hg g (by simp)).2
    rcases g with ⟨op, ins⟩
    change op = GateOp.and at hop
    subst op
    match ins, hlen with
    | [], _ => exact nullary_lower pre post out hpre hpost hc
    | [a], _ => exact unary_lower pre post a out hpre hpost hc
    | [a, b], _ => exact binary_lower pre post a b out hpre hpost hc
    | _ :: _ :: _ :: _, h => simp at h
  · apply PEqualNP.Outside.L_meta_1024.OrOnly.band_lower gs out
    · intro g hmem
      refine ⟨?_, (hg g hmem).2⟩
      rcases (hg g hmem).1 with h | h
      · exact (he ⟨g, hmem, h⟩).elim
      · exact h
    · intro w x hx
      simpa only [oneAnd_line_eq] using hc w x hx

end PEqualNP.Outside.L_meta_1024_aux.OneAndCircuit



namespace PEqualNP.Outside.L_meta_1024_aux.Bridge
open PEqualNP.CircuitLowerBounds

lemma ordinary_iff_extremes (gs : List Gate) (o : ℕ) (w : Fin 13)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    (∀ x : Fin 13 → Bool, Global.val gs x o = Support.target w x) ↔
      Global.val gs (Global.Zof (Global.line w)) o = false ∧
      ∀ p ∈ Global.line w, Global.val gs (Global.eof p) o = true := by
  constructor
  · intro he
    constructor
    · rw [he]
      simp [Support.target, Support.line, Global.line, Global.Zof]
    · intro p hp
      rw [he]
      apply decide_eq_true_iff.mpr
      exact ⟨p, hp, by simp [Global.eof]⟩
  · rintro ⟨hz, he⟩ x
    cases ht : Support.target w x
    · cases hv : Global.val gs x o
      · rfl
      · have hm := val_mono gs hg x (Global.Zof (Global.line w)) (by
          intro q hqx
          have hnot : q ∉ Global.line w := by
            intro hq
            have hh : Support.target w x = true := decide_eq_true_iff.mpr ⟨q, hq, hqx⟩
            rw [ht] at hh
            exact Bool.noConfusion hh
          simpa [Global.Zof] using hnot) o hv
        rw [hz] at hm
        exact Bool.noConfusion hm
    · have hex : ∃ p ∈ Global.line w, x p = true := decide_eq_true_iff.mp ht
      obtain ⟨p, hp, hpx⟩ := hex
      exact val_mono gs hg (Global.eof p) x (by
        intro q hq
        have hqp : q = p := by simpa [Global.eof] using hq
        simpa [hqp] using hpx) o (he p hp)

lemma exotic_iff_extremes (gs : List Gate) (o : ℕ) (w : Fin 13)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    (¬ ∀ x : Fin 13 → Bool, Global.val gs x o = Support.target w x) ↔
      Global.val gs (Global.Zof (Global.line w)) o = true ∨
      ∃ p ∈ Global.line w, Global.val gs (Global.eof p) o = false := by
  rw [ordinary_iff_extremes gs o w hg]
  simp only [not_and_or, not_forall, Bool.not_eq_false, Bool.not_eq_true, exists_prop]

lemma mem_exoticSet_iff (gs : List Gate) (out : Fin 13 → ℕ) (w : Fin 13)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    w ∈ exoticSet gs out ↔
      Global.val gs (Global.Zof (Global.line w)) (out w) = true ∨
      ∃ p ∈ Global.line w, Global.val gs (Global.eof p) (out w) = false := by
  classical
  simp only [exoticSet, Finset.mem_filter, Finset.mem_univ, true_and]
  change (¬ ∀ x : Fin 13 → Bool, Global.val gs x (out w) = Support.target w x) ↔ _
  exact exotic_iff_extremes gs (out w) w hg

lemma four_exotic_witnesses (gs : List Gate) (out : Fin 13 → ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ (w : Fin 13) (x : Fin 13 → Bool), Support.Band x →
      Circuit.eval ⟨gs, out w⟩ (List.ofFn x) = Support.target w x)
    (hsmall : gs.length < 39) :
    4 ≤ (Finset.univ.filter (fun w : Fin 13 =>
      Global.val gs (Global.Zof (Global.line w)) (out w) = true ∨
      ∃ p ∈ Global.line w, Global.val gs (Global.eof p) (out w) = false)).card := by
  classical
  have he : exoticSet gs out = Finset.univ.filter (fun w : Fin 13 =>
      Global.val gs (Global.Zof (Global.line w)) (out w) = true ∨
      ∃ p ∈ Global.line w, Global.val gs (Global.eof p) (out w) = false) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact mem_exoticSet_iff gs out w (fun g hm => (hg g hm).1)
  rw [← he]
  exact four_exotic_outputs gs out hg hcorrect hsmall

end PEqualNP.Outside.L_meta_1024_aux.Bridge
