import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1024_aux.Basic

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

end PEqualNP.Outside.L_meta_1024_aux.Basic

namespace PEqualNP.Outside.L_meta_1024.OrOnly
open PEqualNP.CircuitLowerBounds

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

end PEqualNP.Outside.L_meta_1024_aux.Support

namespace PEqualNP.Outside.L_meta_1024_aux.Clamp

open PEqualNP.Outside.L_meta_1024_aux.Support

lemma line_card : ∀ w : Fin 13, (line w).card = 4 := by decide +kernel

lemma row_line_false : ∀ w q : Fin 13, q ∈ line w → row w q = false := by
  decide +kernel

lemma extend_eight (w : Fin 13) (Q : Finset (Fin 13))
    (hQ : Q ⊆ Finset.univ \ line w) (hcard : Q.card ≤ 8) :
    ∃ Y : Finset (Fin 13), Q ⊆ Y ∧ Y ⊆ Finset.univ \ line w ∧ Y.card = 8 := by
  have houtside : (Finset.univ \ line w).card = 9 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), line_card]
    decide
  have havail : 8 - Q.card ≤ ((Finset.univ \ line w) \ Q).card := by
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

lemma fromTrue_band (Y : Finset (Fin 13)) (hY : Y.card = 8) : Band (fromTrue Y) := by
  apply Or.inl
  have hz : zeroSet (fromTrue Y) = Finset.univ \ Y := by
    ext p
    simp [zeroSet, fromTrue]
  rw [hz, Finset.card_sdiff_of_subset (Finset.subset_univ _), hY]
  decide

lemma fromTrue_misses (w : Fin 13) (Y : Finset (Fin 13))
    (hY : Y ⊆ Finset.univ \ line w) : target w (fromTrue Y) = false := by
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
lemma missing_raw_impossible {m : ℕ} (w p : Fin 13) (hp : p ∈ line w)
    (E : Finset (Fin m)) (hE : E.card ≤ 8) (F : (Fin m → Bool) → Bool)
    (leaf : Fin m → (Fin 13 → Bool) → Bool)
    (hmono : ∀ a b, (∀ i, a i = true → b i = true) → F a = true → F b = true)
    (hsupport : ∀ a b, (∀ i ∈ E, a i = b i) → F a = F b)
    (hleaf : ∀ i ∈ E, ∀ x y, (∀ q, x q = true → y q = true) →
      leaf i x = true → leaf i y = true)
    (hcorrect : ∀ x, Band x → F (fun i => leaf i x) = target w x)
    (hclass : ∀ i ∈ E,
      (∃ q ∈ line w, q ≠ p ∧ ∀ x, leaf i x = x q) ∨
      ∃ q : Fin 13, q ∉ line w ∧ leaf i (singleton q) = true) : False := by
  classical
  let foreign : Fin m → Prop := fun i => ∃ q : Fin 13,
    q ∉ line w ∧ leaf i (singleton q) = true
  let q : Fin m → Fin 13 := fun i => if h : foreign i then Classical.choose h else 0
  have q_spec (i : Fin m) (hi : foreign i) :
      q i ∉ line w ∧ leaf i (singleton (q i)) = true := by
    simpa only [q, dite_eq_left hi] using Classical.choose_spec hi
  let Q := (E.filter foreign).image q
  have hQcard : Q.card ≤ 8 :=
    (Finset.card_image_le.trans (Finset.card_filter_le _ _)).trans hE
  have hQ : Q ⊆ Finset.univ \ line w := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (q_spec i (Finset.mem_filter.mp hi).2).1⟩
  obtain ⟨Y, hQY, hY, hYcard⟩ := extend_eight w Q hQ hQcard
  have hpband : Band (Support.flip w p) := Or.inl (flip_spec w p hp).1
  have hptrue : F (fun i => leaf i (Support.flip w p)) = true :=
    (hcorrect _ hpband).trans (flip_spec w p hp).2
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
    (a b : Fin 13) (hab : a ≠ b) : Disjoint (D (line a) gs) (D (line b) gs) := by
  classical
  obtain ⟨la, hia, _⟩ := main_inv (line a) gs hg
  obtain ⟨lb, hib, _⟩ := main_inv (line b) gs hg
  rw [Finset.disjoint_left]
  intro i hiA hiB
  simp only [D, Finset.mem_filter, Finset.mem_Ico] at hiA hiB
  obtain ⟨_, hza, u, v, huv, hu, hv⟩ := hiA
  obtain ⟨_, hzb, _⟩ := hiB
  have hua := (hia i u u hza hu hu).1
  have hva := (hia i v v hza hv hv).1
  have hub := (hib i u u hzb hu hu).1
  have hvb := (hib i v v hzb hv hv).1
  have hsub : ({u, v} : Finset (Fin 13)) ⊆ line a ∩ line b := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact Finset.mem_inter.mpr ⟨hua, hub⟩
    · exact Finset.mem_inter.mpr ⟨hva, hvb⟩
  have h2 : ({u, v} : Finset (Fin 13)).card = 2 := Finset.card_pair huv
  have := Finset.card_le_card hsub
  have := line_intersection a b hab
  omega

lemma ordinary_charge_count (gs : List Gate) (o : ℕ) (w : Fin 13)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (he : ∀ x : Fin 13 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) =
      decide (∃ p ∈ line w, x p = true)) : 3 ≤ (D (line w) gs).card := by
  classical
  obtain ⟨l, hinv, hcard⟩ := main_inv (line w) gs hg
  have hZ : val gs (Zof (line w)) o = false := by
    change Circuit.eval ⟨gs, o⟩ (List.ofFn _) = false
    rw [he]
    simp [Zof]
  have hE : ∀ u ∈ line w, val gs (eof u) o = true := by
    intro u hu
    change Circuit.eval ⟨gs, o⟩ (List.ofFn _) = true
    rw [he]
    simp only [decide_eq_true_eq]
    exact ⟨u, hu, by simp [eof]⟩
  have himg : ((line w).image l).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
    exact (hinv o u v hZ (hE u hu) (hE v hv)).2
  rw [line_card] at hcard
  omega

lemma charge_outside (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w a : Fin 13) (hwa : a ≠ w) (i : ℕ) (hi : i ∈ D (line a) gs) :
    ∃ q : Fin 13, q ∉ line w ∧ val gs (eof q) i = true := by
  classical
  obtain ⟨l, hinv, _⟩ := main_inv (line a) gs hg
  simp only [D, Finset.mem_filter, Finset.mem_Ico] at hi
  obtain ⟨_, hz, u, v, huv, hu, hv⟩ := hi
  have hua := (hinv i u u hz hu hu).1
  have hva := (hinv i v v hz hv hv).1
  by_cases huw : u ∈ line w
  · refine ⟨v, ?_, hv⟩
    intro hvw
    have hsub : ({u, v} : Finset (Fin 13)) ⊆ line a ∩ line w := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨hua, huw⟩
      · exact Finset.mem_inter.mpr ⟨hva, hvw⟩
    have h2 : ({u, v} : Finset (Fin 13)).card = 2 := Finset.card_pair huv
    have := Finset.card_le_card hsub
    have := line_intersection a w hwa
    omega
  · exact ⟨u, huw, hu⟩

lemma twelve_ordinary_charges (gs : List Gate) (out : Fin 13 → ℕ) (w : Fin 13)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hordinary : ∀ a : Fin 13, a ≠ w → ∀ x : Fin 13 → Bool,
      Circuit.eval ⟨gs, out a⟩ (List.ofFn x) = decide (∃ p ∈ line a, x p = true)) :
    ∃ P : Finset ℕ, P ⊆ Finset.Ico 13 (13 + gs.length) ∧ 36 ≤ P.card ∧
      ∀ i ∈ P, ∃ q : Fin 13, q ∉ line w ∧ val gs (eof q) i = true := by
  classical
  let W : Finset (Fin 13) := Finset.univ.erase w
  let P := W.biUnion (fun a => D (line a) gs)
  have hW : W.card = 12 := by simp [W]
  have hne (a : Fin 13) (ha : a ∈ W) : a ≠ w := (Finset.mem_erase.mp ha).1
  have hsubset : P ⊆ Finset.Ico 13 (13 + gs.length) := by
    intro i hi
    obtain ⟨a, _, hai⟩ := Finset.mem_biUnion.mp hi
    exact (Finset.mem_filter.mp hai).1
  have hcount : 36 ≤ P.card := by
    have hd : ∀ a ∈ W, ∀ b ∈ W, a ≠ b → Disjoint (D (line a) gs) (D (line b) gs) := by
      intro a _ b _ hab
      exact disjoint_charges gs hg a b hab
    have hsum : (∑ _a ∈ W, (3 : ℕ)) ≤ ∑ a ∈ W, (D (line a) gs).card := by
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
      Circuit.eval ⟨gs, out a⟩ (List.ofFn x) = decide (∃ p ∈ line a, x p = true)) :
    ∃ P : Finset ℕ, P ⊆ Finset.Ico 13 (13 + gs.length) ∧ 3 * W.card ≤ P.card ∧
      ∀ w ∉ W, ∀ i ∈ P, ∃ q : Fin 13, q ∉ line w ∧ val gs (eof q) i = true := by
  classical
  let P := W.biUnion (fun a => D (line a) gs)
  have hsubset : P ⊆ Finset.Ico 13 (13 + gs.length) := by
    intro i hi
    obtain ⟨a, _, hai⟩ := Finset.mem_biUnion.mp hi
    exact (Finset.mem_filter.mp hai).1
  have hcount : 3 * W.card ≤ P.card := by
    have hd : ∀ a ∈ W, ∀ b ∈ W, a ≠ b → Disjoint (D (line a) gs) (D (line b) gs) := by
      intro a _ b _ hab
      exact disjoint_charges gs hg a b hab
    have hsum : (∑ _a ∈ W, (3 : ℕ)) ≤ ∑ a ∈ W, (D (line a) gs).card := by
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
      ∀ w ∉ W, ∀ i ∈ P, (∃ q : Fin 13, q ∉ Global.line w ∧ val gs (eof q) i = true) ∧
      (∃ x : Fin 13 → Bool, Support.Band x ∧ Support.target w x = true ∧ val gs x i = false) := by
  classical
  let P := W.biUnion (fun a => D (Global.line a) gs)
  have hsubset : P ⊆ Finset.Ico 13 (13 + gs.length) := by
    intro i hi
    obtain ⟨a, _, hai⟩ := Finset.mem_biUnion.mp hi
    exact (Finset.mem_filter.mp hai).1
  have hcount : 3 * W.card ≤ P.card := by
    have hd : ∀ a ∈ W, ∀ b ∈ W, a ≠ b → Disjoint (D (Global.line a) gs) (D (Global.line b) gs) := by
      intro a _ b _ hab
      exact disjoint_charges gs hg a b hab
    have hsum : (∑ _a ∈ W, (3 : ℕ)) ≤ ∑ a ∈ W, (D (Global.line a) gs).card := by
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

namespace PEqualNP.Outside.L_meta_1024_aux.Sink
open PEqualNP.CircuitLowerBounds

def clamp (n : ℕ) (O : Finset ℕ) (i : ℕ) : Bool := decide (i < n ∧ i ∈ O)

noncomputable def gate (n : ℕ) (O : Finset ℕ) (g : Gate) : Gate := by
  classical
  exact if g.op = GateOp.or ∧ g.inputs.any (clamp n O) = true then ⟨GateOp.and, []⟩
  else ⟨g.op, g.inputs.filter (fun i => !(clamp n O i))⟩

noncomputable def transform (n : ℕ) (O : Finset ℕ) : List Gate → List Gate
  | [] => []
  | g :: gs => gate n O g :: transform (n + 1) O gs

lemma transform_length (n : ℕ) (O : Finset ℕ) (gs : List Gate) :
    (transform n O gs).length = gs.length := by
  induction gs generalizing n with
  | nil => rfl
  | cons g gs ih => simp only [transform, List.length_cons, ih]

lemma transform_append (n : ℕ) (O : Finset ℕ) (gs hs : List Gate) :
    transform n O (gs ++ hs) = transform n O gs ++ transform (n + gs.length) O hs := by
  induction gs generalizing n with
  | nil => simp [transform]
  | cons g gs ih => simp [transform, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

lemma gate_allowed (n : ℕ) (O : Finset ℕ) (g : Gate)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ((gate n O g).op = GateOp.and ∨ (gate n O g).op = GateOp.or) ∧
      (gate n O g).inputs.length ≤ 2 := by
  unfold gate
  split
  · exact ⟨Or.inl rfl, by simp⟩
  · exact ⟨hg.1, (List.length_filter_le _ _).trans hg.2⟩

lemma gate_sink (n : ℕ) (O : Finset ℕ) (g : Gate) :
    ∀ i ∈ (gate n O g).inputs, i < n → i ∉ O := by
  intro i hi hn hO
  unfold gate at hi
  split at hi
  · simp at hi
  · have hh := (List.mem_filter.mp hi).2
    simp [clamp, hn, hO] at hh

lemma gate_ge (n : ℕ) (O : Finset ℕ) (g : Gate)
    (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (r s : ℕ → Bool) (hrs : ∀ i, r i = true → s i = true) :
    g.op.eval (g.inputs.map r) = true →
      (gate n O g).op.eval ((gate n O g).inputs.map s) = true := by
  intro ht
  unfold gate
  split
  · simp [GateOp.eval]
  · rename_i hn
    rcases hg with hop | hop
    · simp only [hop, GateOp.eval, List.all_eq_true, List.mem_map, forall_exists_index,
        and_imp, forall_apply_eq_imp_iff₂, id_eq] at ht ⊢
      intro i hi
      exact hrs i (ht i (List.mem_of_mem_filter hi))
    · simp only [hop, GateOp.eval, List.any_eq_true, List.mem_map, exists_exists_and_eq_and,
        id_eq] at ht ⊢
      obtain ⟨i, hi, hir⟩ := ht
      refine ⟨i, ?_, hrs i hir⟩
      apply List.mem_filter.mpr
      refine ⟨hi, ?_⟩
      have hc : clamp n O i = false := by
        cases he : clamp n O i
        · rfl
        · exact False.elim (hn ⟨hop, List.any_eq_true.mpr ⟨i, hi, he⟩⟩)
      simp [hc]

lemma gate_eq (n : ℕ) (O : Finset ℕ) (g : Gate)
    (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (r : ℕ → Bool)
    (hclamp : ∀ i ∈ g.inputs, clamp n O i = true → r i = true) :
    (gate n O g).op.eval ((gate n O g).inputs.map r) = g.op.eval (g.inputs.map r) := by
  have hforward := gate_ge n O g hg r r (fun _ h => h)
  have hback : (gate n O g).op.eval ((gate n O g).inputs.map r) = true →
      g.op.eval (g.inputs.map r) = true := by
    intro ht
    unfold gate at ht
    split at ht
    · rename_i hc
      obtain ⟨i, hi, hic⟩ := List.any_eq_true.mp hc.2
      simp only [hc.1, GateOp.eval, List.any_eq_true, List.mem_map, exists_exists_and_eq_and, id_eq]
      exact ⟨i, hi, hclamp i hi hic⟩
    · rcases hg with hop | hop
      · simp only [hop, GateOp.eval, List.all_eq_true, List.mem_map, forall_exists_index,
          and_imp, forall_apply_eq_imp_iff₂, id_eq] at ht ⊢
        intro i hi
        cases hc : clamp n O i
        · exact ht i (List.mem_filter.mpr ⟨hi, by simp [hc]⟩)
        · exact hclamp i hi hc
      · simp only [hop, GateOp.eval, List.any_eq_true, List.mem_map, exists_exists_and_eq_and,
          id_eq] at ht ⊢
        obtain ⟨i, hi, hir⟩ := ht
        exact ⟨i, List.mem_of_mem_filter hi, hir⟩
  cases h₁ : (gate n O g).op.eval ((gate n O g).inputs.map r) <;>
    cases h₂ : g.op.eval (g.inputs.map r) <;> simp_all

lemma transform_allowed (n : ℕ) (O : Finset ℕ) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ g ∈ transform n O gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  induction gs generalizing n with
  | nil => simp [transform]
  | cons g gs ih =>
    intro h hh
    simp only [transform, List.mem_cons] at hh
    rcases hh with rfl | hh
    · exact gate_allowed n O g (hg g (by simp))
    · exact ih (n + 1) (fun k hk => hg k (List.mem_cons_of_mem g hk)) h hh

lemma val_ge {n : ℕ} (O : Finset ℕ) (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x : Fin n → Bool) : ∀ i, Global.val gs x i = true → Global.val (transform n O gs) x i = true := by
  induction gs using List.reverseRecOn with
  | nil => exact fun _ h => h
  | append_singleton gs g ih =>
    have hgg := hg g (by simp)
    have hgs : ∀ h ∈ gs, h.op = GateOp.and ∨ h.op = GateOp.or :=
      fun h hh => hg h (List.mem_append_left _ hh)
    intro i hi
    rw [transform_append]
    simp only [transform, List.append_nil]
    rw [Global.val_snoc] at hi
    rw [Global.val_snoc, transform_length]
    by_cases he : i = n + gs.length
    · rw [ite_eq_left he] at hi ⊢
      exact gate_ge (n + gs.length) O g hgg _ _ (ih hgs) hi
    · rw [ite_eq_right he] at hi ⊢
      exact ih hgs i hi

lemma val_append_old {n : ℕ} (gs hs : List Gate) (x : Fin n → Bool) (i : ℕ)
    (hi : i < n + gs.length) : Global.val (gs ++ hs) x i = Global.val gs x i := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, Global.val_snoc,
      ite_eq_right (show i ≠ n + (gs ++ hs).length by simp; omega)]
    exact ih

lemma val_take {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (k i : ℕ)
    (hk : k ≤ gs.length) (hi : i < n + k) :
    Global.val gs x i = Global.val (gs.take k) x i := by
  have hlen : (gs.take k).length = k := by simp [List.length_take, Nat.min_eq_left hk]
  have h := val_append_old (gs.take k) (gs.drop k) x i (by rw [hlen]; exact hi)
  simpa only [List.take_append_drop] using h

lemma prefix_eq {n : ℕ} (O : Finset ℕ) (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x : Fin n → Bool) (t : ℕ) (hbound : n + gs.length ≤ t + 1)
    (hO : ∀ i ∈ O, i < t → i < n + gs.length → Global.val gs x i = true) :
    ∀ i, Global.val (transform n O gs) x i = Global.val gs x i := by
  induction gs using List.reverseRecOn with
  | nil => intro i; rfl
  | append_singleton gs g ih =>
    have hgs : ∀ h ∈ gs, h.op = GateOp.and ∨ h.op = GateOp.or :=
      fun h hh => hg h (List.mem_append_left _ hh)
    have hbound' : n + gs.length ≤ t + 1 := by simp only [List.length_append, List.length_singleton] at hbound; omega
    have hO' : ∀ i ∈ O, i < t → i < n + gs.length → Global.val gs x i = true := by
      intro i hiO hit hi
      have hh := hO i hiO hit (by simp; omega)
      rw [Global.val_snoc, ite_eq_right (by omega)] at hh
      exact hh
    have heq := ih hgs hbound' hO'
    intro i
    rw [transform_append]
    simp only [transform, List.append_nil]
    rw [Global.val_snoc, Global.val_snoc, transform_length]
    by_cases hi : i = n + gs.length
    · simp only [ite_eq_left hi]
      simp_rw [heq]
      apply gate_eq (n + gs.length) O g (hg g (by simp))
      intro k _ hk
      have hkc : k < n + gs.length ∧ k ∈ O := by simpa [clamp] using hk
      exact hO' k hkc.2 (by simp only [List.length_append, List.length_singleton] at hbound; omega) hkc.1
    · simp only [ite_eq_right hi]
      exact heq i

lemma output_eq {n : ℕ} (O : Finset ℕ) (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x : Fin n → Bool) (o : ℕ) (ho : n ≤ o ∧ o < n + gs.length)
    (hO : ∀ i ∈ O, i < o → Global.val gs x i = true) :
    Global.val (transform n O gs) x o = Global.val gs x o := by
  let k := o + 1 - n
  have hk : k ≤ gs.length := by omega
  have hko : o < n + k := by omega
  have hlen : (gs.take k).length = k := by simp [List.length_take, Nat.min_eq_left hk]
  have hsplit : transform n O gs = transform n O (gs.take k) ++
      transform (n + k) O (gs.drop k) := by
    have hh := transform_append n O (gs.take k) (gs.drop k)
    rw [List.take_append_drop, hlen] at hh
    exact hh
  rw [hsplit, val_append_old _ _ _ _ (by rw [transform_length, hlen]; exact hko)]
  rw [prefix_eq O (gs.take k) (fun g hm => hg g (List.mem_of_mem_take hm)) x o
    (by rw [hlen]; omega) (by
      intro i hiO hio hi
      rw [← val_take gs x k i hk (by rwa [hlen] at hi)]
      exact hO i hiO hio)]
  exact (val_take gs x k o hk hko).symm

end PEqualNP.Outside.L_meta_1024_aux.Sink

namespace PEqualNP.Outside.L_meta_1024_aux.Sink
open PEqualNP.CircuitLowerBounds

lemma transform_get (n : ℕ) (O : Finset ℕ) (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    (transform n O gs)[j]'(by rw [transform_length]; exact hj) = gate (n + j) O gs[j] := by
  induction gs generalizing n j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero => simp [transform]
    | succ j =>
      have hh := ih (n + 1) j (by simpa using hj)
      simpa [transform, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hh

lemma transform_sink (n : ℕ) (O : Finset ℕ) (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∀ i ∈ ((transform n O gs)[j]'(by rw [transform_length]; exact hj)).inputs,
      i < n + j → i ∉ O := by
  rw [transform_get]
  exact gate_sink (n + j) O gs[j]

lemma false_target_zero (w : Fin 13) (x : Fin 13 → Bool) (hf : Support.target w x = false) :
    Global.line w ⊆ Support.zeroSet x := by
  intro p hp
  have hfalse : x p = false := by
    cases he : x p
    · rfl
    · have ht : Support.target w x = true := decide_eq_true_iff.mpr ⟨p, hp, he⟩
      rw [hf] at ht
      exact Bool.noConfusion ht
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfalse⟩

lemma other_target_true (a b : Fin 13) (hab : a ≠ b) (x : Fin 13 → Bool)
    (hx : Support.Band x) (ha : Support.target a x = false) : Support.target b x = true := by
  cases hb : Support.target b x
  · have hsub : Global.line a ∪ Global.line b ⊆ Support.zeroSet x :=
      Finset.union_subset (false_target_zero a x ha) (false_target_zero b x hb)
    have hc := Finset.card_le_card hsub
    rw [(Bridge.pair_geometry a b hab).1] at hc
    rcases hx with hx | hx <;> omega
  · rfl

lemma other_extreme_true (gs : List Gate) (out : Fin 13 → ℕ)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hcorrect : ∀ (w : Fin 13) (x : Fin 13 → Bool), Support.Band x →
      Global.val gs x (out w) = Support.target w x)
    (w v : Fin 13) (hvw : v ≠ w) : Global.val gs (Global.Zof (Global.line w)) (out v) = true := by
  obtain ⟨p, hpv, hpw⟩ := Charges.line_difference v w hvw.symm
  have hsub : ({p} : Finset (Fin 13)) ⊆ Finset.univ \ Support.line w := by
    intro q hq
    have he := Finset.mem_singleton.mp hq
    subst q
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hpw⟩
  obtain ⟨Y, hpY, hY, hYcard⟩ := Clamp.extend_eight w {p} hsub (by simp)
  have htarget : Support.target v (Clamp.fromTrue Y) = true := by
    apply decide_eq_true_iff.mpr
    exact ⟨p, hpv, by simp [Clamp.fromTrue, hpY (Finset.mem_singleton_self p)]⟩
  have hv : Global.val gs (Clamp.fromTrue Y) (out v) = true :=
    (hcorrect v _ (Clamp.fromTrue_band Y hYcard)).trans htarget
  apply Bridge.val_mono gs hg (Clamp.fromTrue Y) (Global.Zof (Global.line w)) _ (out v) hv
  intro q hq
  have hqY : q ∈ Y := by simpa [Clamp.fromTrue] using hq
  simpa [Global.Zof, Global.line, Support.line] using (Finset.mem_sdiff.mp (hY hqY)).2

lemma band_correct (gs : List Gate) (out : Fin 13 → ℕ)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hcorrect : ∀ (w : Fin 13) (x : Fin 13 → Bool), Support.Band x →
      Global.val gs x (out w) = Support.target w x) :
    ∀ (w : Fin 13) (x : Fin 13 → Bool), Support.Band x →
      Global.val (transform 13 (Finset.univ.image out) gs) x (out w) = Support.target w x := by
  intro w x hx
  cases ht : Support.target w x
  · have heq := output_eq (Finset.univ.image out) gs hg x (out w)
      (Bridge.output_index gs (out w) w (hcorrect w)) (by
        intro i hi hio
        obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hi
        have hvw : v ≠ w := by intro he; subst v; omega
        exact (hcorrect v x hx).trans (other_target_true w v hvw.symm x hx ht))
    exact heq.trans ((hcorrect w x hx).trans ht)
  · exact val_ge (Finset.univ.image out) gs hg x (out w) ((hcorrect w x hx).trans ht)

lemma preserves_ordinary (gs : List Gate) (out : Fin 13 → ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ (w : Fin 13) (x : Fin 13 → Bool), Support.Band x →
      Global.val gs x (out w) = Support.target w x)
    (w : Fin 13) (hordinary : ∀ x : Fin 13 → Bool, Global.val gs x (out w) = Support.target w x) :
    ∀ x : Fin 13 → Bool,
      Global.val (transform 13 (Finset.univ.image out) gs) x (out w) = Support.target w x := by
  let O := Finset.univ.image out
  have hop : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hm => (hg g hm).1
  have hgnew := transform_allowed 13 O gs hg
  apply (Bridge.ordinary_iff_extremes (transform 13 O gs) (out w) w (fun g hm => (hgnew g hm).1)).mpr
  obtain ⟨hz, he⟩ := (Bridge.ordinary_iff_extremes gs (out w) w hop).mp hordinary
  constructor
  · have heq := output_eq O gs hop (Global.Zof (Global.line w)) (out w)
      (Bridge.output_index gs (out w) w (hcorrect w)) (by
        intro i hi hio
        obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hi
        have hvw : v ≠ w := by intro hh; subst v; omega
        exact other_extreme_true gs out hop hcorrect w v hvw)
    exact heq.trans hz
  · intro p hp
    exact val_ge O gs hop (Global.eof p) (out w) (he p hp)

lemma exotic_subset (gs : List Gate) (out : Fin 13 → ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ (w : Fin 13) (x : Fin 13 → Bool), Support.Band x →
      Global.val gs x (out w) = Support.target w x) :
    Bridge.exoticSet (transform 13 (Finset.univ.image out) gs) out ⊆ Bridge.exoticSet gs out := by
  classical
  intro w hw
  simp only [Bridge.exoticSet, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
  intro hord
  exact hw (preserves_ordinary gs out hg hcorrect w hord)

end PEqualNP.Outside.L_meta_1024_aux.Sink

namespace PEqualNP.Outside.L_meta_1024_aux.Sink
open PEqualNP.CircuitLowerBounds

def override (n : ℕ) (P : Finset ℕ) (r : ℕ → Bool) (i : ℕ) : Bool :=
  if clamp n P i then true else r i

lemma gate_override (n : ℕ) (P : Finset ℕ) (g : Gate)
    (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (r : ℕ → Bool) :
    (gate n P g).op.eval ((gate n P g).inputs.map r) =
      g.op.eval (g.inputs.map (override n P r)) := by
  have hmap : (gate n P g).inputs.map r = (gate n P g).inputs.map (override n P r) := by
    apply List.map_congr_left
    intro i hi
    have hc : clamp n P i = false := by
      cases he : clamp n P i
      · rfl
      · have hh : i < n ∧ i ∈ P := by simpa [clamp] using he
        exact False.elim (gate_sink n P g i hi hh.1 hh.2)
    simp [override, hc]
  rw [hmap]
  apply gate_eq n P g hg
  intro i _ hi
  simp [override, hi]

lemma override_succ_ne (m : ℕ) (P : Finset ℕ) (r : ℕ → Bool) (i : ℕ) (hne : i ≠ m) :
    override (m + 1) P r i = override m P r i := by
  by_cases hi : i < m
  · have hi' : i < m + 1 := by omega
    simp [override, clamp, hi, hi']
  · have hi' : ¬ i < m + 1 := by omega
    simp [override, clamp, hi, hi']

lemma transform_cut_eq {n M : ℕ} (P : Finset ℕ) (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hP : ∀ i ∈ P, n ≤ i) (x : Fin n → Bool) (z : Fin M → Bool)
    (hinput : ∀ i : Fin n, Cut.source z i.val = x i)
    (hpaid : ∀ i ∈ P, n ≤ i → i < n + gs.length → Cut.source z i = true) :
    ∀ i, override (n + gs.length) P (Global.val (transform n P gs) x) i =
      Cut.cutVal n P gs z i := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro i
    by_cases hi : i < n
    · have hin : i ∉ P := fun hp => by have := hP i hp; omega
      simp only [List.length_nil, Nat.add_zero, transform, override, clamp,
        Global.val_nil, Cut.cutVal_nil, hi, hin, and_false, decide_false, Bool.false_eq_true,
        if_false, dite_true]
      exact (hinput ⟨i, hi⟩).symm
    · simp [transform, override, clamp, Global.val_nil, Cut.cutVal_nil, hi]
  | append_singleton gs g ih =>
    have hop : ∀ h ∈ gs, h.op = GateOp.and ∨ h.op = GateOp.or :=
      fun h hh => hg h (List.mem_append_left _ hh)
    have hpast : ∀ i ∈ P, n ≤ i → i < n + gs.length → Cut.source z i = true := by
      intro i hi hn hb
      exact hpaid i hi hn (by simp; omega)
    have heq := ih hop hpast
    intro i
    have hval (j : ℕ) : Global.val (transform n P (gs ++ [g])) x j =
        if j = n + gs.length then
          (gate (n + gs.length) P g).op.eval
            ((gate (n + gs.length) P g).inputs.map (Global.val (transform n P gs) x))
        else Global.val (transform n P gs) x j := by
      rw [transform_append]
      simp only [transform, Global.val_snoc, transform_length]
    change (if clamp (n + (gs ++ [g]).length) P i then true
      else Global.val (transform n P (gs ++ [g])) x i) = _
    rw [hval, Cut.cutVal_snoc]
    simp only [List.length_append, List.length_singleton, ← Nat.add_assoc]
    by_cases hi : i = n + gs.length
    · subst i
      simp only [ite_eq_left]
      by_cases hp : n + gs.length ∈ P
      · have hz := hpaid (n + gs.length) hp (by omega) (by simp)
        simp [clamp, hp, hz]
      · simp only [clamp, hp, and_false, decide_false, Bool.false_eq_true, if_false]
        rw [gate_override (n + gs.length) P g (hg g (by simp))]
        apply congrArg g.op.eval
        apply List.map_congr_left
        intro j _
        exact heq j
    · simp only [ite_eq_right hi]
      change override (n + gs.length + 1) P (Global.val (transform n P gs) x) i = _
      rw [override_succ_ne _ _ _ _ hi]
      exact heq i

lemma transform_cut_output {n M : ℕ} (P : Finset ℕ) (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hP : ∀ i ∈ P, n ≤ i) (x : Fin n → Bool) (z : Fin M → Bool)
    (hinput : ∀ i : Fin n, Cut.source z i.val = x i)
    (hpaid : ∀ i ∈ P, n ≤ i → i < n + gs.length → Cut.source z i = true)
    (i : ℕ) (hi : i ∉ P) :
    Global.val (transform n P gs) x i = Cut.cutVal n P gs z i := by
  have hh := transform_cut_eq P gs hg hP x z hinput hpaid i
  simpa [override, clamp, hi] using hh

end PEqualNP.Outside.L_meta_1024_aux.Sink

namespace PEqualNP.Outside.L_meta_1024_aux.Dead
open PEqualNP.CircuitLowerBounds

def remap (n : ℕ) (cs : List Gate) (is : List ℕ) (i : ℕ) : ℕ :=
  if i < is.length then is.getD i 0 else n + cs.length

def step (n : ℕ) (P : Finset ℕ) (s : List Gate × List ℕ) (g : Gate) : List Gate × List ℕ :=
  if s.2.length ∈ P then (s.1, s.2 ++ [0])
  else (s.1 ++ [⟨g.op, g.inputs.map (remap n s.1 s.2)⟩], s.2 ++ [n + s.1.length])

def compile (n : ℕ) (P : Finset ℕ) (gs : List Gate) : List Gate × List ℕ :=
  gs.foldl (step n P) ([], List.range n)

def code (n : ℕ) (P : Finset ℕ) (gs : List Gate) : List Gate := (compile n P gs).1
def indices (n : ℕ) (P : Finset ℕ) (gs : List Gate) : List ℕ := (compile n P gs).2

lemma compile_snoc (n : ℕ) (P : Finset ℕ) (gs : List Gate) (g : Gate) :
    compile n P (gs ++ [g]) = step n P (compile n P gs) g := by
  simp [compile, List.foldl_append]

lemma step_length (n : ℕ) (P : Finset ℕ) (s : List Gate × List ℕ) (g : Gate) :
    (step n P s g).2.length = s.2.length + 1 := by
  unfold step
  split <;> simp

lemma indices_length (n : ℕ) (P : Finset ℕ) (gs : List Gate) :
    (indices n P gs).length = n + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [indices, compile]
  | append_singleton gs g ih =>
    change (compile n P (gs ++ [g])).2.length = _
    rw [compile_snoc, step_length]
    change (indices n P gs).length + 1 = _
    rw [ih]
    simp [Nat.add_assoc]

def nextGate (n : ℕ) (P : Finset ℕ) (gs : List Gate) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (remap n (code n P gs) (indices n P gs))⟩

lemma code_snoc (n : ℕ) (P : Finset ℕ) (gs : List Gate) (g : Gate) :
    code n P (gs ++ [g]) = if n + gs.length ∈ P then code n P gs
      else code n P gs ++ [nextGate n P gs g] := by
  unfold code
  rw [compile_snoc]
  change (step n P (code n P gs, indices n P gs) g).1 = _
  unfold step
  rw [indices_length]
  split <;> rfl

lemma indices_snoc (n : ℕ) (P : Finset ℕ) (gs : List Gate) (g : Gate) :
    indices n P (gs ++ [g]) = indices n P gs ++
      [if n + gs.length ∈ P then 0 else n + (code n P gs).length] := by
  unfold indices
  rw [compile_snoc]
  change (step n P (code n P gs, indices n P gs) g).2 = _
  unfold step
  rw [indices_length]
  split <;> simp_all [indices]

lemma code_length (n : ℕ) (P : Finset ℕ) (gs : List Gate) :
    (code n P gs).length = Cut.unpaid n P gs := by
  induction gs using List.reverseRecOn with
  | nil => simp [code, compile, Cut.unpaid_nil]
  | append_singleton gs g ih =>
    rw [code_snoc, Cut.unpaid_snoc]
    by_cases hp : n + gs.length ∈ P <;> simp [hp, ih]

lemma code_allowed (n : ℕ) (P : Finset ℕ) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ g ∈ code n P gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  induction gs using List.reverseRecOn with
  | nil => simp [code, compile]
  | append_singleton gs g ih =>
    have hgs : ∀ h ∈ gs, (h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2 :=
      fun h hh => hg h (List.mem_append_left _ hh)
    rw [code_snoc]
    split
    · exact ih hgs
    · intro h hh
      rcases List.mem_append.mp hh with hh | hh
      · exact ih hgs h hh
      · have he : h = nextGate n P gs g := by simpa using hh
        subst h
        have hgg := hg g (by simp)
        simpa [nextGate] using hgg

lemma mapped_valid (n : ℕ) (P : Finset ℕ) (gs : List Gate) :
    ∀ i, i < n + gs.length → i ∉ P → (indices n P gs).getD i 0 < n + (code n P gs).length := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro i hi _
    have hil : i < n := by simpa using hi
    change (List.range n).getD i 0 < n
    rw [List.getD_eq_getElem _ _ (by simpa using hil)]
    simpa using hil
  | append_singleton gs g ih =>
    intro i hi hip
    rw [indices_snoc, code_snoc]
    by_cases he : i = n + gs.length
    · subst i
      have hget : (indices n P gs ++ [if n + gs.length ∈ P then 0 else n + (code n P gs).length]).getD
          (indices n P gs).length 0 = if n + gs.length ∈ P then 0 else n + (code n P gs).length := by simp
      rw [indices_length] at hget
      rw [hget]
      simp only [ite_eq_right hip, List.length_append, List.length_singleton]
      omega
    · have hit : i < n + gs.length := by simp only [List.length_append, List.length_singleton] at hi; omega
      rw [List.getD_append _ _ _ _ (by rw [indices_length]; exact hit)]
      have hh := ih i hit hip
      by_cases hp : n + gs.length ∈ P
      · simp only [ite_eq_left hp]
        exact hh
      · simp only [ite_eq_right hp, List.length_append, List.length_singleton]
        omega

end PEqualNP.Outside.L_meta_1024_aux.Dead

namespace PEqualNP.Outside.L_meta_1024_aux.Dead
open PEqualNP.CircuitLowerBounds

def NoReads (n : ℕ) (P : Finset ℕ) (gs : List Gate) : Prop :=
  ∀ j (hj : j < gs.length), ∀ i ∈ gs[j].inputs, i < n + j → i ∉ P

lemma noReads_prefix (n : ℕ) (P : Finset ℕ) (gs : List Gate) (g : Gate)
    (h : NoReads n P (gs ++ [g])) : NoReads n P gs := by
  intro j hj i hi hn
  have hh := h j (by simp; omega) i
  apply hh
  · simpa only [List.getElem_append_left hj] using hi
  · exact hn

lemma noReads_last (n : ℕ) (P : Finset ℕ) (gs : List Gate) (g : Gate)
    (h : NoReads n P (gs ++ [g])) : ∀ i ∈ g.inputs, i < n + gs.length → i ∉ P := by
  simpa using h gs.length (by simp)

lemma transform_noReads (n : ℕ) (P : Finset ℕ) (gs : List Gate) :
    NoReads n P (Sink.transform n P gs) := by
  intro j hj
  have hjold : j < gs.length := by simpa [Sink.transform_length] using hj
  exact Sink.transform_sink n P gs j hjold

lemma val_invalid {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ)
    (hi : n + gs.length ≤ i) : Global.val gs x i = false := by
  unfold Global.val
  apply List.getD_eq_default
  rw [Global.fold_length, List.length_ofFn]
  exact hi

lemma eval {n : ℕ} (P : Finset ℕ) (gs : List Gate) (hreads : NoReads n P gs)
    (x : Fin n → Bool) : ∀ i, i < n + gs.length → i ∉ P →
      Global.val (code n P gs) x ((indices n P gs).getD i 0) = Global.val gs x i := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro i hi _
    have hil : i < n := by simpa using hi
    change Global.val [] x ((List.range n).getD i 0) = Global.val [] x i
    have hr : (List.range n).getD i 0 = i := by
      rw [List.getD_eq_getElem _ _ (by simpa using hil)]
      simp
    rw [hr]
  | append_singleton gs g ih =>
    have hprev := noReads_prefix n P gs g hreads
    have hlast := noReads_last n P gs g hreads
    intro i hi hip
    rw [code_snoc, indices_snoc]
    by_cases hp : n + gs.length ∈ P
    · simp only [ite_eq_left hp]
      have hne : i ≠ n + gs.length := by intro he; exact hip (he.symm ▸ hp)
      have hit : i < n + gs.length := by simp only [List.length_append, List.length_singleton] at hi; omega
      rw [List.getD_append _ _ _ _ (by rw [indices_length]; exact hit)]
      rw [Global.val_snoc, ite_eq_right hne]
      exact ih hprev i hit hip
    · simp only [ite_eq_right hp]
      by_cases he : i = n + gs.length
      · subst i
        have hget : (indices n P gs ++ [n + (code n P gs).length]).getD (indices n P gs).length 0 =
            n + (code n P gs).length := by simp
        rw [indices_length] at hget
        rw [hget]
        rw [Global.val_snoc, ite_eq_left rfl, Global.val_snoc, ite_eq_left rfl]
        change g.op.eval ((g.inputs.map (remap n (code n P gs) (indices n P gs))).map
          (fun j => Global.val (code n P gs) x j)) =
          g.op.eval (g.inputs.map (fun j => Global.val gs x j))
        rw [List.map_map]
        apply congrArg g.op.eval
        apply List.map_congr_left
        intro j hj
        by_cases hjlt : j < n + gs.length
        · simp only [Function.comp_apply, remap, indices_length, ite_eq_left hjlt]
          exact ih hprev j hjlt (hlast j hj hjlt)
        · simp only [Function.comp_apply, remap, indices_length, ite_eq_right hjlt]
          rw [val_invalid _ _ _ (by omega), val_invalid _ _ _ (by omega)]
      · have hit : i < n + gs.length := by simp only [List.length_append, List.length_singleton] at hi; omega
        rw [List.getD_append _ _ _ _ (by rw [indices_length]; exact hit)]
        have hvalid := mapped_valid n P gs i hit hip
        rw [Global.val_snoc, ite_eq_right (show (indices n P gs).getD i 0 ≠ n + (code n P gs).length by omega)]
        rw [Global.val_snoc, ite_eq_right he]
        exact ih hprev i hit hip

lemma code_op_at (n : ℕ) (P : Finset ℕ) (gs : List Gate) (j : ℕ)
    (hj : j < gs.length) (hp : n + j ∉ P) :
    ∃ k : ℕ, ∃ hk : k < (code n P gs).length, (indices n P gs).getD (n + j) 0 = n + k ∧
      ((code n P gs)[k]'hk).op = gs[j].op := by
  induction gs using List.reverseRecOn generalizing j with
  | nil => simp at hj
  | append_singleton gs g ih =>
    by_cases hlast : j = gs.length
    · subst j
      refine ⟨(code n P gs).length, ?_, ?_, ?_⟩
      · rw [code_snoc, ite_eq_right hp]
        simp
      · rw [indices_snoc]
        have hget : (indices n P gs ++ [if n + gs.length ∈ P then 0 else n + (code n P gs).length]).getD
            (indices n P gs).length 0 = if n + gs.length ∈ P then 0 else n + (code n P gs).length := by simp
        rw [indices_length] at hget
        rw [hget, ite_eq_right hp]
      · simp only [code_snoc, ite_eq_right hp]
        simp [nextGate]
    · have hjold : j < gs.length := by simp only [List.length_append, List.length_singleton] at hj; omega
      obtain ⟨k, hk, hmap, hop⟩ := ih j hjold hp
      have hget : (indices n P (gs ++ [g])).getD (n + j) 0 = (indices n P gs).getD (n + j) 0 := by
        rw [indices_snoc, List.getD_append _ _ _ _ (by rw [indices_length]; omega)]
      by_cases hpaid : n + gs.length ∈ P
      · refine ⟨k, ?_, hget.trans hmap, ?_⟩
        · simpa only [code_snoc, ite_eq_left hpaid] using hk
        · simpa only [code_snoc, ite_eq_left hpaid, List.getElem_append_left hjold] using hop
      · refine ⟨k, ?_, hget.trans hmap, ?_⟩
        · simp only [code_snoc, ite_eq_right hpaid, List.length_append, List.length_singleton]
          omega
        · simpa only [code_snoc, ite_eq_right hpaid, List.getElem_append_left hk,
            List.getElem_append_left hjold] using hop

end PEqualNP.Outside.L_meta_1024_aux.Dead

namespace PEqualNP.Outside.L_meta_1024_aux.Dead
open PEqualNP.CircuitLowerBounds

lemma wire_eq_gate {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (j : ℕ) (hj : j < gs.length) :
    Global.val gs x (n + j) = gs[j].op.eval (gs[j].inputs.map
      (fun i => if i < n + j then Global.val gs x i else false)) := by
  induction gs using List.reverseRecOn generalizing j with
  | nil => simp at hj
  | append_singleton gs g ih =>
    by_cases hlast : j = gs.length
    · subst j
      rw [Global.val_snoc, ite_eq_left rfl]
      have hget : (gs ++ [g])[gs.length]'(by simp) = g := by simp
      rw [hget]
      apply congrArg g.op.eval
      apply List.map_congr_left
      intro i _
      by_cases hi : i < n + gs.length
      · rw [ite_eq_left hi, Global.val_snoc, ite_eq_right (by omega)]
      · rw [ite_eq_right hi, val_invalid _ _ _ (by omega)]
    · have hjold : j < gs.length := by simp only [List.length_append, List.length_singleton] at hj; omega
      rw [Global.val_snoc, ite_eq_right (by omega), List.getElem_append_left hjold, ih j hjold]
      apply congrArg gs[j].op.eval
      apply List.map_congr_left
      intro i _
      by_cases hi : i < n + j
      · simp only [ite_eq_left hi]
        rw [Global.val_snoc, ite_eq_right (by omega)]
      · simp only [ite_eq_right hi]

lemma deleted_formula {n : ℕ} (P : Finset ℕ) (gs : List Gate) (hreads : NoReads n P gs)
    (x : Fin n → Bool) (j : ℕ) (hj : j < gs.length) :
    Global.val gs x (n + j) = gs[j].op.eval (gs[j].inputs.map
      (fun i => if i < n + j then Global.val (code n P gs) x ((indices n P gs).getD i 0) else false)) := by
  rw [wire_eq_gate gs x j hj]
  apply congrArg gs[j].op.eval
  apply List.map_congr_left
  intro i hi
  by_cases hib : i < n + j
  · simp only [ite_eq_left hib]
    exact (eval P gs hreads x i (by omega) (hreads j hj i hi hib)).symm
  · simp only [ite_eq_right hib]

noncomputable def paidCode (n : ℕ) (P : Finset ℕ) (gs : List Gate) : List Gate :=
  code n P (Sink.transform n P gs)

noncomputable def paidIndex (n : ℕ) (P : Finset ℕ) (gs : List Gate) (i : ℕ) : ℕ :=
  (indices n P (Sink.transform n P gs)).getD i 0

def trueSources {n : ℕ} (gs : List Gate) (x : Fin n → Bool) : Fin (n + gs.length) → Bool :=
  fun i => if h : i.val < n then x ⟨i.val, h⟩ else true

lemma trueSources_input {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : Fin n) :
    Cut.source (trueSources gs x) i.val = x i := by
  rw [Cut.source_eq]
  have hi : i.val < n + gs.length := by omega
  simp [trueSources, hi, i.isLt]

lemma trueSources_paid {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ)
    (hin : n ≤ i) (hvalid : i < n + gs.length) : Cut.source (trueSources gs x) i = true := by
  rw [Cut.source_eq]
  simp [trueSources, hvalid, show ¬ i < n by omega]

lemma paid_length (n : ℕ) (P : Finset ℕ) (gs : List Gate) :
    (paidCode n P gs).length = Cut.unpaid n P gs := by
  rw [paidCode, code_length]
  simp only [Cut.unpaid, Sink.transform_length]

lemma paid_allowed (n : ℕ) (P : Finset ℕ) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ g ∈ paidCode n P gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 :=
  code_allowed n P (Sink.transform n P gs) (Sink.transform_allowed n P gs hg)

lemma paid_eval {n : ℕ} (P : Finset ℕ) (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hP : ∀ i ∈ P, n ≤ i) (x : Fin n → Bool) (i : ℕ)
    (hvalid : i < n + gs.length) (hip : i ∉ P) :
    Global.val (paidCode n P gs) x (paidIndex n P gs i) =
      Cut.cutVal n P gs (trueSources gs x) i := by
  change Global.val (code n P (Sink.transform n P gs)) x
    ((indices n P (Sink.transform n P gs)).getD i 0) = _
  rw [eval P (Sink.transform n P gs) (transform_noReads n P gs) x i
    (by rwa [Sink.transform_length]) hip]
  exact Sink.transform_cut_output P gs hg hP x (trueSources gs x) (trueSources_input gs x)
    (fun i _ hn hi => trueSources_paid gs x i hn hi) i hip

end PEqualNP.Outside.L_meta_1024_aux.Dead

namespace PEqualNP.Outside.L_meta_1024_aux.Sink
open PEqualNP.CircuitLowerBounds

lemma or_preserved_of_false {n : ℕ} (P : Finset ℕ) (gs : List Gate) (j : ℕ)
    (hj : j < gs.length) (hor : gs[j].op = GateOp.or) (x : Fin n → Bool)
    (hf : Global.val (transform n P gs) x (n + j) = false) :
    ((transform n P gs)[j]'(by rw [transform_length]; exact hj)).op = GateOp.or := by
  classical
  by_cases hcl : gs[j].op = GateOp.or ∧ gs[j].inputs.any (clamp (n + j) P) = true
  · have hgate : (transform n P gs)[j]'(by rw [transform_length]; exact hj) = ⟨GateOp.and, []⟩ := by
      rw [transform_get n P gs j hj]
      unfold gate
      rw [ite_eq_left hcl]
    have he := Dead.wire_eq_gate (transform n P gs) x j (by rwa [transform_length])
    rw [hgate] at he
    simp only [List.map_nil, GateOp.eval, List.all_nil] at he
    rw [hf] at he
    exact Bool.noConfusion he
  · rw [transform_get n P gs j hj]
    unfold gate
    rw [ite_eq_right hcl]
    exact hor

end PEqualNP.Outside.L_meta_1024_aux.Sink

namespace PEqualNP.Outside.L_meta_1024_aux.Sink
open PEqualNP.CircuitLowerBounds

lemma gate_inputs_subset (n : ℕ) (P : Finset ℕ) (g : Gate) :
    ∀ i ∈ (gate n P g).inputs, i ∈ g.inputs := by
  intro i hi
  unfold gate at hi
  split at hi
  · simp at hi
  · exact List.mem_of_mem_filter hi

lemma preserves_noReads (n : ℕ) (P Q : Finset ℕ) (gs : List Gate)
    (hQ : Dead.NoReads n Q gs) : Dead.NoReads n Q (transform n P gs) := by
  intro j hj i hi hn
  have hjold : j < gs.length := by simpa [transform_length] using hj
  rw [transform_get n P gs j hjold] at hi
  exact hQ j hjold i (gate_inputs_subset (n + j) P gs[j] i hi) hn

end PEqualNP.Outside.L_meta_1024_aux.Sink

namespace PEqualNP.Outside.L_meta_1024_aux.Dead
open PEqualNP.CircuitLowerBounds

lemma noReads_union (n : ℕ) (P Q : Finset ℕ) (gs : List Gate)
    (hP : NoReads n P gs) (hQ : NoReads n Q gs) : NoReads n (P ∪ Q) gs := by
  intro j hj i hi hn hip
  rcases Finset.mem_union.mp hip with hp | hq
  · exact hP j hj i hi hn hp
  · exact hQ j hj i hi hn hq

lemma double_transform_noReads (n : ℕ) (P Q : Finset ℕ) (gs : List Gate) :
    NoReads n (P ∪ Q) (Sink.transform n P (Sink.transform n Q gs)) := by
  apply noReads_union
  · exact transform_noReads n P _
  · exact Sink.preserves_noReads n P Q _ (transform_noReads n Q gs)

end PEqualNP.Outside.L_meta_1024_aux.Dead

namespace PEqualNP.Outside.L_meta_1024_aux.Cut
open PEqualNP.CircuitLowerBounds

lemma cutVal_invalid {M : ℕ} (n : ℕ) (P : Finset ℕ) (gs : List Gate) (z : Fin M → Bool) (i : ℕ)
    (hi : n + gs.length ≤ i) : cutVal n P gs z i = false := by
  unfold cutVal cutRun
  apply List.getD_eq_default
  rw [fold_length, List.length_ofFn]
  exact hi

lemma cutVal_add_sinks {M : ℕ} (n : ℕ) (P Q : Finset ℕ) (gs : List Gate)
    (hreads : Dead.NoReads n Q gs) (z : Fin M → Bool) :
    ∀ i, i ∉ Q → cutVal n (P ∪ Q) gs z i = cutVal n P gs z i := by
  induction gs using List.reverseRecOn with
  | nil => intro i _; rfl
  | append_singleton gs g ih =>
    have hprev := Dead.noReads_prefix n Q gs g hreads
    have hlast := Dead.noReads_last n Q gs g hreads
    intro i hiQ
    rw [cutVal_snoc, cutVal_snoc]
    by_cases hi : i = n + gs.length
    · subst i
      simp only [ite_eq_left, Finset.mem_union, hiQ, or_false]
      by_cases hp : n + gs.length ∈ P
      · simp only [ite_eq_left hp]
      · simp only [ite_eq_right hp]
        apply congrArg g.op.eval
        apply List.map_congr_left
        intro j hj
        by_cases hjlt : j < n + gs.length
        · exact ih hprev j (hlast j hj hjlt)
        · rw [cutVal_invalid _ _ _ _ _ (by omega), cutVal_invalid _ _ _ _ _ (by omega)]
    · simp only [ite_eq_right hi]
      exact ih hprev i hiQ

lemma essential_add_sinks {M : ℕ} (n : ℕ) (P Q : Finset ℕ) (gs : List Gate)
    (hreads : Dead.NoReads n Q gs) (o : ℕ) (ho : o ∉ Q) :
    essential (M := M) n (P ∪ Q) gs o = essential n P gs o := by
  classical
  ext t
  simp only [essential, Finset.mem_filter, Finset.mem_univ, true_and, Depends]
  constructor
  · rintro ⟨x, y, hxy, hne⟩
    refine ⟨x, y, hxy, ?_⟩
    rwa [cutVal_add_sinks n P Q gs hreads x o ho, cutVal_add_sinks n P Q gs hreads y o ho] at hne
  · rintro ⟨x, y, hxy, hne⟩
    refine ⟨x, y, hxy, ?_⟩
    rw [cutVal_add_sinks n P Q gs hreads x o ho, cutVal_add_sinks n P Q gs hreads y o ho]
    exact hne

end PEqualNP.Outside.L_meta_1024_aux.Cut

namespace PEqualNP.Outside.L_meta_1024_aux.PaidClamp
open PEqualNP.CircuitLowerBounds

lemma outside_true_row (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) (w : Fin 13)
    (T : Finset (Fin (13 + gs.length))) (hT : T.card ≤ 8)
    (hforeign : ∀ i ∈ T, ∃ q : Fin 13,
      q ∉ Global.line w ∧ Global.val gs (Global.eof q) i.val = true) :
    ∃ x : Fin 13 → Bool, Support.Band x ∧ Support.target w x = false ∧
      ∀ i ∈ T, Global.val gs x i.val = true := by
  classical
  let q : Fin (13 + gs.length) → Fin 13 := fun i =>
    if h : i ∈ T then Classical.choose (hforeign i h) else 0
  have hq (i : Fin (13 + gs.length)) (hi : i ∈ T) :
      q i ∉ Global.line w ∧ Global.val gs (Global.eof (q i)) i.val = true := by
    simpa only [q, dite_eq_left hi] using Classical.choose_spec (hforeign i hi)
  let Q := T.image q
  have hQ : Q ⊆ Finset.univ \ Support.line w := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (hq i hi).1⟩
  have hQcard : Q.card ≤ 8 := Finset.card_image_le.trans hT
  obtain ⟨Y, hQY, hY, hYcard⟩ := Clamp.extend_eight w Q hQ hQcard
  refine ⟨Clamp.fromTrue Y, Clamp.fromTrue_band Y hYcard, Clamp.fromTrue_misses w Y hY, ?_⟩
  intro i hi
  have hqi : q i ∈ Y := hQY (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  apply Bridge.val_mono gs hg (Global.eof (q i)) (Clamp.fromTrue Y) _ i.val (hq i hi).2
  intro r hr
  have he : r = q i := by simpa [Global.eof] using hr
  subst r
  simp [Clamp.fromTrue, hqi]

set_option maxHeartbeats 2000000 in
lemma correct_and_bounded (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w : Fin 13) (P : Finset ℕ) (hP : ∀ i ∈ P, 13 ≤ i)
    (hPoutside : ∀ i ∈ P, ∃ q : Fin 13,
      q ∉ Global.line w ∧ Global.val gs (Global.eof q) i = true)
    (E : Finset (Fin (13 + gs.length))) (hEcard : E.card ≤ 12)
    (hallowed : ∀ i ∈ E, i.val < 13 ∨ i.val ∈ P)
    (hraw : ∀ p ∈ Global.line w, Bridge.rawIndex gs p ∈ E)
    (F : (Fin (13 + gs.length) → Bool) → Bool)
    (hmono : ∀ a b, (∀ i, a i = true → b i = true) → F a = true → F b = true)
    (hsupport : ∀ a b, (∀ i ∈ E, a i = b i) → F a = F b)
    (hcorrect : ∀ x : Fin 13 → Bool, Support.Band x →
      F (fun i => Global.val gs x i.val) = Support.target w x) :
    (∀ x : Fin 13 → Bool, Support.target w x = false → F (Dead.trueSources gs x) = false) ∧
    (∀ x : Fin 13 → Bool, Support.Band x → F (Dead.trueSources gs x) = Support.target w x) := by
  classical
  let R := (Global.line w).image (Bridge.rawIndex gs)
  have hinj : Function.Injective (Bridge.rawIndex gs) := by
    intro p q hpq
    apply Fin.ext
    exact congrArg (fun i : Fin (13 + gs.length) => i.val) hpq
  have hRcard : R.card = 4 := by
    rw [Finset.card_image_of_injective _ hinj]
    exact Global.line_card w
  have hRE : R ⊆ E := by
    intro i hi
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hi
    exact hraw p hp
  let T := E \ R
  have hTcard : T.card ≤ 8 := by
    rw [Finset.card_sdiff_of_subset hRE, hRcard]
    omega
  have hforeign : ∀ i ∈ T, ∃ q : Fin 13,
      q ∉ Global.line w ∧ Global.val gs (Global.eof q) i.val = true := by
    intro i hi
    obtain ⟨hiE, hiR⟩ := Finset.mem_sdiff.mp hi
    rcases hallowed i hiE with hiraw | hipaid
    · let q : Fin 13 := ⟨i.val, hiraw⟩
      have hql : q ∉ Global.line w := by
        intro hq
        apply hiR
        exact Finset.mem_image.mpr ⟨q, hq, by apply Fin.ext; rfl⟩
      refine ⟨q, hql, ?_⟩
      change Global.val gs (Global.eof q) q.val = true
      rw [Bridge.val_input]
      simp [Global.eof]
    · exact hPoutside i.val hipaid
  obtain ⟨y, hyband, hyfalse, hyforeign⟩ := outside_true_row gs hg w T hTcard hforeign
  have hbound (x : Fin 13 → Bool) (hxt : Support.target w x = false) :
      F (Dead.trueSources gs x) = false := by
    cases hfx : F (Dead.trueSources gs x)
    · rfl
    · have hcompare : ∀ i ∈ E, Dead.trueSources gs x i = true → Global.val gs y i.val = true := by
        intro i hi hpos
        by_cases hiR : i ∈ R
        · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hiR
          have hxp : x p = false := (Finset.mem_filter.mp (Sink.false_target_zero w x hxt hp)).2
          have hh : Dead.trueSources gs x (Bridge.rawIndex gs p) = false := by
            simp [Dead.trueSources, Bridge.rawIndex, hxp]
          rw [hh] at hpos
          exact Bool.noConfusion hpos
        · exact hyforeign i (Finset.mem_sdiff.mpr ⟨hi, hiR⟩)
      have hytrue := Clamp.supported_mono F E hmono hsupport _ _ hcompare hfx
      have hyzero := (hcorrect y hyband).trans hyfalse
      rw [hyzero] at hytrue
      exact Bool.noConfusion hytrue
  refine ⟨hbound, ?_⟩
  intro x hx
  cases ht : Support.target w x
  · exact hbound x ht
  · have hpos : F (fun i => Global.val gs x i.val) = true := (hcorrect x hx).trans ht
    apply Clamp.supported_mono F E hmono hsupport _ _ _ hpos
    intro i hi hiv
    rcases hallowed i hi with hiraw | hipaid
    · let q : Fin 13 := ⟨i.val, hiraw⟩
      have he : Global.val gs x i.val = x q := Bridge.val_input gs x q
      rw [he] at hiv
      simpa only [Dead.trueSources, dite_eq_left hiraw] using hiv
    · have hn : ¬ i.val < 13 := by have := hP i.val hipaid; omega
      simp [Dead.trueSources, hn]

end PEqualNP.Outside.L_meta_1024_aux.PaidClamp

namespace PEqualNP.Outside.L_meta_1024_aux.AppendLine
open PEqualNP.CircuitLowerBounds

def pairGate (a b : Fin 13) : Gate := ⟨GateOp.or, [a.val, b.val]⟩

def appendLine (gs : List Gate) (w : Fin 13) : List Gate :=
  ((gs ++ [pairGate w (1 + w)]) ++ [pairGate (3 + w) (9 + w)]) ++
    [⟨GateOp.or, [13 + gs.length, 14 + gs.length]⟩]

lemma length (gs : List Gate) (w : Fin 13) : (appendLine gs w).length = gs.length + 3 := by
  simp [appendLine, Nat.add_assoc]

lemma allowed (gs : List Gate) (w : Fin 13)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ g ∈ appendLine gs w, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hm
  simp only [appendLine, List.mem_append, List.mem_singleton] at hm
  rcases hm with ((hm | rfl) | rfl) | rfl
  · exact hg g hm
  · simp [pairGate]
  · simp [pairGate]
  · simp

lemma target_eq (w : Fin 13) (x : Fin 13 → Bool) :
    Support.target w x = ((x w || x (1 + w)) || (x (3 + w) || x (9 + w))) := by
  have he : Support.target w x = true ↔
      ((x w || x (1 + w)) || (x (3 + w) || x (9 + w))) = true := by
    simp [Support.target, Support.line, Finset.mem_image, Bool.or_eq_true, or_assoc]
  cases ht : Support.target w x <;>
    cases hv : ((x w || x (1 + w)) || (x (3 + w) || x (9 + w))) <;> simp_all

lemma eval (gs : List Gate) (w : Fin 13) (x : Fin 13 → Bool) :
    Global.val (appendLine gs w) x (15 + gs.length) = Support.target w x := by
  let l := pairGate w (1 + w)
  let r := pairGate (3 + w) (9 + w)
  let j : Gate := ⟨GateOp.or, [13 + gs.length, 14 + gs.length]⟩
  have hl : Global.val ((gs ++ [l]) ++ [r]) x (13 + gs.length) = (x w || x (1 + w)) := by
    rw [Global.val_snoc, ite_eq_right (by simp only [List.length_append, List.length_singleton]; omega), Global.val_snoc, ite_eq_left rfl]
    simp [l, pairGate, GateOp.eval, Bridge.val_input]
  have hr : Global.val ((gs ++ [l]) ++ [r]) x (14 + gs.length) = (x (3 + w) || x (9 + w)) := by
    rw [Global.val_snoc, ite_eq_left (by simp only [List.length_append, List.length_singleton]; omega)]
    simp [r, pairGate, GateOp.eval, Bridge.val_input]
  change Global.val (((gs ++ [l]) ++ [r]) ++ [j]) x (15 + gs.length) = _
  rw [Global.val_snoc, ite_eq_left (by simp only [List.length_append, List.length_singleton]; omega)]
  simp only [j, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
  rw [hl, hr]
  exact (target_eq w x).symm

lemma old (gs : List Gate) (w : Fin 13) (x : Fin 13 → Bool) (i : ℕ)
    (hi : i < 13 + gs.length) : Global.val (appendLine gs w) x i = Global.val gs x i := by
  have hs : appendLine gs w = gs ++ [pairGate w (1 + w), pairGate (3 + w) (9 + w),
      ⟨GateOp.or, [13 + gs.length, 14 + gs.length]⟩] := by simp [appendLine, List.append_assoc]
  rw [hs]
  exact Sink.val_append_old gs _ x i hi

lemma output_valid (gs : List Gate) (w : Fin 13) :
    13 ≤ 15 + gs.length ∧ 15 + gs.length < 13 + (appendLine gs w).length := by
  rw [length]
  omega

end PEqualNP.Outside.L_meta_1024_aux.AppendLine

namespace PEqualNP.Outside.L_meta_1024_aux.AppendLine
open PEqualNP.CircuitLowerBounds

def appendLines : List Gate → List (Fin 13) → List Gate
  | gs, [] => gs
  | gs, w :: ws => appendLines (appendLine gs w) ws

lemma lines_length (gs : List Gate) (ws : List (Fin 13)) :
    (appendLines gs ws).length = gs.length + 3 * ws.length := by
  induction ws generalizing gs with
  | nil => simp [appendLines]
  | cons w ws ih =>
    rw [appendLines, ih, length]
    simp only [List.length_cons]
    omega

lemma lines_allowed (gs : List Gate) (ws : List (Fin 13))
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ g ∈ appendLines gs ws, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  induction ws generalizing gs with
  | nil => exact hg
  | cons w ws ih => exact ih (appendLine gs w) (allowed gs w hg)

lemma lines_old (gs : List Gate) (ws : List (Fin 13)) (x : Fin 13 → Bool) (i : ℕ)
    (hi : i < 13 + gs.length) : Global.val (appendLines gs ws) x i = Global.val gs x i := by
  induction ws generalizing gs with
  | nil => rfl
  | cons w ws ih =>
    exact (ih (appendLine gs w) (by rw [length]; omega)).trans (old gs w x i hi)

lemma lines_generated (gs : List Gate) (ws : List (Fin 13)) :
    ∀ w ∈ ws, ∃ i : ℕ, 13 ≤ i ∧ i < 13 + (appendLines gs ws).length ∧
      ∀ x : Fin 13 → Bool, Global.val (appendLines gs ws) x i = Support.target w x := by
  induction ws generalizing gs with
  | nil => simp
  | cons v ws ih =>
    intro w hw
    rcases List.mem_cons.mp hw with he | hw
    · subst w
      have hv := output_valid gs v
      refine ⟨15 + gs.length, hv.1, ?_, ?_⟩
      · rw [lines_length]
        simp only [List.length_cons]
        omega
      · intro x
        change Global.val (appendLines (appendLine gs v) ws) x (15 + gs.length) = _
        rw [lines_old _ _ _ _ hv.2]
        exact eval gs v x
    · exact ih (appendLine gs v) w hw

end PEqualNP.Outside.L_meta_1024_aux.AppendLine

namespace PEqualNP.Outside.L_meta_1024_aux.Dead
open PEqualNP.CircuitLowerBounds

lemma or_two (is : List ℕ) (his : is.length ≤ 2) (f : ℕ → Bool) (d : ℕ) (hd : f d = false) :
    GateOp.or.eval (is.map f) = (f (is.getD 0 d) || f (is.getD 1 d)) := by
  cases is with
  | nil => simp [GateOp.eval, hd]
  | cons a is =>
    cases is with
    | nil => simp [GateOp.eval, hd]
    | cons b is =>
      cases is with
      | nil => simp [GateOp.eval]
      | cons c is => simp at his

lemma deleted_or_pair (P : Finset ℕ) (gs : List Gate) (hreads : NoReads 13 P gs)
    (hsize : (code 13 P gs).length ≤ 7) (j : ℕ) (hj : j < gs.length)
    (hor : gs[j].op = GateOp.or) (hfan : gs[j].inputs.length ≤ 2) :
    ∃ a b : ℕ, ∀ x : Fin 13 → Bool, Global.val gs x (13 + j) =
      (Global.val (code 13 P gs) x a || Global.val (code 13 P gs) x b) := by
  let d := 13 + gs.length
  let ix : ℕ → ℕ := fun i => if i < 13 + j then (indices 13 P gs).getD i 0 else 20
  let a := ix (gs[j].inputs.getD 0 d)
  let b := ix (gs[j].inputs.getD 1 d)
  refine ⟨a, b, ?_⟩
  intro x
  have hz : Global.val (code 13 P gs) x 20 = false := val_invalid _ _ _ (by omega)
  have hmap : (fun i => if i < 13 + j then Global.val (code 13 P gs) x ((indices 13 P gs).getD i 0) else false) =
      (fun i => Global.val (code 13 P gs) x (ix i)) := by
    funext i
    by_cases hi : i < 13 + j <;> simp [ix, hi, hz]
  have hd : Global.val (code 13 P gs) x (ix d) = false := by
    have hn : ¬ d < 13 + j := by dsimp [d]; omega
    simp [ix, hn, hz]
  rw [deleted_formula P gs hreads x j hj, hor, hmap]
  exact or_two gs[j].inputs hfan (fun i => Global.val (code 13 P gs) x (ix i)) d hd

end PEqualNP.Outside.L_meta_1024_aux.Dead

namespace PEqualNP.Outside.L_meta_1024_aux.FourReduction
open PEqualNP.CircuitLowerBounds

lemma small_four_nonordinary (gs : List Gate) (hsize : gs.length ≤ 11)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (lineId : Fin 4 → Fin 13) (hinj : Function.Injective lineId) (out : Fin 4 → ℕ)
    (hvalid : ∀ u, out u < 13 + gs.length)
    (hcorrect : ∀ u (x : Fin 13 → Bool), Support.Band x → Global.val gs x (out u) = Support.target (lineId u) x) :
    ∀ u, ¬ ∀ x : Fin 13 → Bool, Global.val gs x (out u) = Support.target (lineId u) x := by
  classical
  intro u₀ hexact
  let A : Finset (Fin 13) := Finset.univ.image lineId
  let W := Finset.univ \ A
  have hA : A.card = 4 := by
    rw [Finset.card_image_of_injective _ hinj]
    decide
  have hW : W.card = 9 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), hA]
    decide
  have houtside (u : Fin 4) : lineId u ∉ W := by
    intro hu
    exact (Finset.mem_sdiff.mp hu).2 (Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩)
  let cs := AppendLine.appendLines gs W.toList
  have hcs : cs.length ≤ 38 := by
    rw [AppendLine.lines_length, Finset.length_toList, hW]
    omega
  have hallowed := AppendLine.lines_allowed gs W.toList hg
  have hwitness : ∀ w : Fin 13, ∃ i : ℕ,
      (∀ x : Fin 13 → Bool, Support.Band x → Global.val cs x i = Support.target w x) ∧
      ((w ∈ W ∨ w = lineId u₀) → ∀ x : Fin 13 → Bool, Global.val cs x i = Support.target w x) := by
    intro w
    by_cases hw : w ∈ W
    · obtain ⟨i, _, _, hi⟩ := AppendLine.lines_generated gs W.toList w (by simpa using hw)
      exact ⟨i, fun x _ => hi x, fun _ => hi⟩
    · have hwA : w ∈ A := by simpa [W] using hw
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hwA
      have hold (x : Fin 13 → Bool) : Global.val cs x (out u) = Global.val gs x (out u) :=
        AppendLine.lines_old gs W.toList x (out u) (hvalid u)
      refine ⟨out u, ?_, ?_⟩
      · intro x hx
        exact (hold x).trans (hcorrect u x hx)
      · rintro (hu | he)
        · exact False.elim (hw hu)
        · have huu : u = u₀ := hinj he
          subst u
          intro x
          exact (hold x).trans (hexact x)
  choose out' hband hord using hwitness
  have hten : 10 ≤ (insert (lineId u₀) W).card := by
    rw [Finset.card_insert_of_notMem (houtside u₀), hW]
  have htenord : ∀ w ∈ insert (lineId u₀) W, ∀ x : Fin 13 → Bool,
      Circuit.eval ⟨cs, out' w⟩ (List.ofFn x) = Support.target w x := by
    intro w hw
    rcases Finset.mem_insert.mp hw with he | hw
    · exact hord w (Or.inr he)
    · exact hord w (Or.inl hw)
  have hh := Bridge.ten_ordinary_bound cs out' hallowed hband (insert (lineId u₀) W) hten htenord
  omega

end PEqualNP.Outside.L_meta_1024_aux.FourReduction
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

end PEqualNP.Outside.L_meta_1024_aux.OneAnd


namespace PEqualNP.Outside.L_meta_1024_aux.FourOrSinks

open PEqualNP.CircuitLowerBounds

lemma three_triples_labels (A B C : Finset (Fin 13))
    (hAcard : A.card = 3) (hBcard : B.card = 3) (hCcard : C.card = 3)
    (hAB : Disjoint A B) (hAC : (A ∩ C).card ≤ 1) (hBC : (B ∩ C).card ≤ 1)
    (label : Fin 13 → ℕ) (a b c : ℕ)
    (hA : ∀ p ∈ A, label p = a) (hB : ∀ p ∈ B, label p = b)
    (hC : ∀ p ∈ C, label p = c) :
    6 + (((A ∪ B) ∪ C).image label).card ≤ ((A ∪ B) ∪ C).card := by
  have hABcard : (A ∪ B).card = 6 := by
    rw [Finset.card_union_of_disjoint hAB, hAcard, hBcard]
  have hdisj : Disjoint (A ∩ C) (B ∩ C) :=
    hAB.mono Finset.inter_subset_left Finset.inter_subset_left
  have hinter : ((A ∪ B) ∩ C).card = (A ∩ C).card + (B ∩ C).card := by
    have he : (A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C) := by
      ext p
      simp only [Finset.mem_inter, Finset.mem_union]
      tauto
    rw [he, Finset.card_union_of_disjoint hdisj]
  have hsum := Finset.card_union_add_card_inter (A ∪ B) C
  rw [hABcard, hCcard, hinter] at hsum
  have himage (K : Finset ℕ) (ha : a ∈ K) (hb : b ∈ K) (hc : c ∈ K) :
      (((A ∪ B) ∪ C).image label) ⊆ K := by
    intro v hv
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
    rcases Finset.mem_union.mp hp with hp | hp
    · rcases Finset.mem_union.mp hp with hp | hp
      · exact (hA p hp) ▸ ha
      · exact (hB p hp) ▸ hb
    · exact (hC p hp) ▸ hc
  by_cases ha : (A ∩ C).Nonempty
  · obtain ⟨p, hp⟩ := ha
    have hac : a = c := (hA p (Finset.mem_inter.mp hp).1).symm.trans
      (hC p (Finset.mem_inter.mp hp).2)
    by_cases hb : (B ∩ C).Nonempty
    · obtain ⟨q, hq⟩ := hb
      have hbc : b = c := (hB q (Finset.mem_inter.mp hq).1).symm.trans
        (hC q (Finset.mem_inter.mp hq).2)
      have hi := Finset.card_le_card (himage {c} (by simp [hac]) (by simp [hbc]) (by simp))
      simp only [Finset.card_singleton] at hi
      omega
    · have hb0 : (B ∩ C).card = 0 := by
        have hn : ¬ 0 < (B ∩ C).card := fun h => hb (Finset.card_pos.mp h)
        omega
      have hi := Finset.card_le_card (himage {b, c} (by simp [hac]) (by simp) (by simp))
      have hk : ({b, c} : Finset ℕ).card ≤ 2 := by
        simpa using List.toFinset_card_le [b, c]
      omega
  · have ha0 : (A ∩ C).card = 0 := by
      have hn : ¬ 0 < (A ∩ C).card := fun h => ha (Finset.card_pos.mp h)
      omega
    by_cases hb : (B ∩ C).Nonempty
    · obtain ⟨q, hq⟩ := hb
      have hbc : b = c := (hB q (Finset.mem_inter.mp hq).1).symm.trans
        (hC q (Finset.mem_inter.mp hq).2)
      have hi := Finset.card_le_card (himage {a, c} (by simp) (by simp [hbc]) (by simp))
      have hk : ({a, c} : Finset ℕ).card ≤ 2 := by
        simpa using List.toFinset_card_le [a, c]
      omega
    · have hb0 : (B ∩ C).card = 0 := by
        have hn : ¬ 0 < (B ∩ C).card := fun h => hb (Finset.card_pos.mp h)
        omega
      have hi := Finset.card_le_card (himage {a, b, c} (by simp) (by simp) (by simp))
      have hk : ({a, b, c} : Finset ℕ).card ≤ 3 := by
        simpa using List.toFinset_card_le [a, b, c]
      omega

lemma three_triples_lower (gs : List Gate) (o₁ o₂ o₃ : ℕ)
    (hg : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (A B C : Finset (Fin 13))
    (hAcard : A.card = 3) (hBcard : B.card = 3) (hCcard : C.card = 3)
    (hAB : Disjoint A B) (hAC : (A ∩ C).card ≤ 1) (hBC : (B ∩ C).card ≤ 1)
    (hA : ∀ p ∈ A, Cut.Depends 13 ∅ gs o₁ p)
    (hB : ∀ p ∈ B, Cut.Depends 13 ∅ gs o₂ p)
    (hC : ∀ p ∈ C, Cut.Depends 13 ∅ gs o₃ p) : 6 ≤ gs.length := by
  obtain ⟨label, wire, hcount, hdepends⟩ := Cut.components 13 ∅ ((A ∪ B) ∪ C) gs hg
  have hlabels := three_triples_labels A B C hAcard hBcard hCcard hAB hAC hBC
    label (wire o₁) (wire o₂) (wire o₃)
    (fun p hp => hdepends o₁ p (hA p hp))
    (fun p hp => hdepends o₂ p (hB p hp))
    (fun p hp => hdepends o₃ p (hC p hp))
  have hunpaid : Cut.unpaid 13 ∅ gs = gs.length := by
    rw [Cut.unpaid_eq_sub 13 ∅ gs (Finset.empty_subset _)]
    simp
  rw [hunpaid] at hcount
  omega

end PEqualNP.Outside.L_meta_1024_aux.FourOrSinks


namespace PEqualNP.Outside.L_meta_1024_aux.FourOrSinks

lemma four_two_ownership : ∀ (which : Fin 4 → Fin 2) (both : Fin 4 → Bool),
    (∀ a b, both a = true → both b = true → a = b) →
    ∃ a b c d : Fin 4,
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      both a = false ∧ both b = false ∧ both c = false ∧
      which a = which b ∧ d ≠ c ∧
      (both d = true ∨ which d = which c) := by
  letI (which : Fin 4 → Fin 2) (both : Fin 4 → Bool) : Decidable
      (∃ a b c d : Fin 4,
        a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
        both a = false ∧ both b = false ∧ both c = false ∧
        which a = which b ∧ d ≠ c ∧
        (both d = true ∨ which d = which c)) := by infer_instance
  decide

end PEqualNP.Outside.L_meta_1024_aux.FourOrSinks


namespace PEqualNP.Outside.L_meta_1024_aux.FourOrSinks

open PEqualNP.CircuitLowerBounds

lemma shared_parent_essential_band (a b : Fin 13) (hab : a ≠ b)
    (h k : (Fin 13 → Bool) → Bool)
    (hcorrect : ∀ x, Support.Band x → (h x || k x) = Support.target a x)
    (hupperh : ∀ x, Support.Band x → h x = true → Support.target b x = true)
    (hmono : ∀ x y, (∀ q, x q = true → y q = true) → k x = true → k y = true)
    (p : Fin 13) (hp : p ∈ Support.line a \ Support.line b) :
    ∃ x y : Fin 13 → Bool, (∀ q, q ≠ p → x q = y q) ∧ k x ≠ k y := by
  obtain ⟨hpa, hpb⟩ := Finset.mem_sdiff.mp hp
  obtain ⟨hcard, hpX, hBX, hAX⟩ := OneAnd.separating_row a b hab p hpa hpb
  let X := OneAnd.separatingRow a b p
  let x : Fin 13 → Bool := fun q => decide (q ∈ X)
  let y : Fin 13 → Bool := Function.update x p false
  have hzero : Support.zeroSet x = Finset.univ \ X := by
    ext q
    simp [Support.zeroSet, x]
  have hxband : Support.Band x := by
    apply Or.inr
    rw [hzero]
    simp [Finset.card_sdiff, show X.card = 7 from hcard]
  have hax : Support.target a x = true := by
    apply decide_eq_true
    exact ⟨p, hpa, by simp [x, X, hpX]⟩
  have hbx : Support.target b x = false := by
    simp only [Support.target, decide_eq_false_iff_not]
    rintro ⟨q, hqb, hqx⟩
    have hqX : q ∈ X := by simpa [x] using hqx
    exact Finset.disjoint_left.mp hBX hqb hqX
  have hhx : h x = false := by
    cases he : h x with
    | false => rfl
    | true =>
      have ht := hupperh x hxband he
      rw [hbx] at ht
      cases ht
  have hkx : k x = true := by
    have he := hcorrect x hxband
    simpa only [hhx, Bool.false_or, hax] using he
  let T := X.erase p
  have hTsub : T ⊆ Finset.univ \ Support.line a := by
    intro q hq
    obtain ⟨hqp, hqX⟩ := Finset.mem_erase.mp hq
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ q, fun hqa => hqp (hAX q hqa hqX)⟩
  have hTcard : T.card ≤ 8 := by
    have hle := Finset.card_le_card (Finset.erase_subset p X)
    change T.card ≤ X.card at hle
    have hc : X.card = 7 := hcard
    omega
  obtain ⟨Y, hTY, hYsub, hYcard⟩ := Clamp.extend_eight a T hTsub hTcard
  have hyY : ∀ q, y q = true → Clamp.fromTrue Y q = true := by
    intro q hyq
    apply decide_eq_true
    apply hTY
    apply Finset.mem_erase.mpr
    by_cases hqp : q = p
    · simp [y, hqp] at hyq
    · refine ⟨hqp, ?_⟩
      simpa [y, Function.update_of_ne hqp, x] using hyq
  have hky : k y = false := by
    cases he : k y with
    | false => rfl
    | true =>
      have hkY := hmono y (Clamp.fromTrue Y) hyY he
      have ht := hcorrect (Clamp.fromTrue Y) (Clamp.fromTrue_band Y hYcard)
      rw [hkY, Bool.or_true, Clamp.fromTrue_misses a Y hYsub] at ht
      cases ht
  refine ⟨x, y, ?_, ?_⟩
  · intro q hqp
    simp [y, Function.update_of_ne hqp]
  · rw [hkx, hky]
    decide

lemma shared_parent_cut_depends_band (gs : List Gate) (o : ℕ)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (a b : Fin 13) (hab : a ≠ b) (h : (Fin 13 → Bool) → Bool)
    (hcorrect : ∀ x, Support.Band x →
      (h x || Cut.cutVal 13 ∅ gs x o) = Support.target a x)
    (hupperh : ∀ x, Support.Band x → h x = true → Support.target b x = true)
    (p : Fin 13) (hp : p ∈ Support.line a \ Support.line b) :
    Cut.Depends 13 ∅ gs o p := by
  exact shared_parent_essential_band a b hab h (fun x => Cut.cutVal 13 ∅ gs x o)
    hcorrect hupperh (fun x y hxy => Cut.cutVal_mono 13 ∅ gs hg x y hxy o) p hp

end PEqualNP.Outside.L_meta_1024_aux.FourOrSinks

namespace PEqualNP.Outside.L_meta_1024_aux.FourOrSinks

open PEqualNP.CircuitLowerBounds

lemma high_network_lower_band (gs : List Gate) (out : Fin 4 → ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (lineId : Fin 4 → Fin 13) (hinj : Function.Injective lineId)
    (which : Fin 4 → Fin 2) (both : Fin 4 → Bool)
    (high : Fin 2 → (Fin 13 → Bool) → Bool)
    (f : Fin 4 → (Fin 13 → Bool) → Bool)
    (hsingle : ∀ w, both w = false → ∀ x,
      f w x = (high (which w) x || Cut.cutVal 13 ∅ gs x (out w)))
    (hdouble : ∀ w, both w = true → ∀ x,
      f w x = (high 0 x || high 1 x))
    (hcorrect : ∀ w x, Support.Band x → f w x = Support.target (lineId w) x) :
    6 ≤ gs.length := by
  have hboth_unique : ∀ a b, both a = true → both b = true → a = b := by
    intro a b ha hb
    by_contra hab
    have hne : lineId a ≠ lineId b := fun h => hab (hinj h)
    let x := Support.row (lineId a)
    have hx : Support.Band x := Or.inr (Support.row_spec (lineId a)).1
    have hae := hcorrect a x hx
    have hbe := hcorrect b x hx
    rw [hdouble a ha] at hae
    rw [hdouble b hb] at hbe
    have he := hae.symm.trans hbe
    rw [(Support.row_spec (lineId a)).2, Bridge.row_targets (lineId a) (lineId b) hne] at he
    cases he
  obtain ⟨a, b, c, d, hab, hac, hbc, ha, hb, hc, habhigh, hdc, hcdhigh⟩ :=
    four_two_ownership which both hboth_unique
  have high_upper (w u : Fin 4)
      (huse : both u = true ∨ which u = which w) :
      ∀ x, Support.Band x → high (which w) x = true →
        Support.target (lineId u) x = true := by
    intro x hxband hx
    rw [← hcorrect u x hxband]
    cases hu : both u with
    | false =>
      have he : which u = which w := huse.resolve_left (by simp [hu])
      rw [hsingle u hu, he, hx]
      simp
    | true =>
      rw [hdouble u hu]
      have he := (which w).isLt
      have hi : which w = 0 ∨ which w = 1 := by omega
      rcases hi with hi | hi
      · simp [← hi, hx]
      · simp [← hi, hx]
  have low_dep (w u : Fin 4) (hwu : w ≠ u) (hw : both w = false)
      (huse : both u = true ∨ which u = which w) :
      ∀ p ∈ Support.line (lineId w) \ Support.line (lineId u),
        Cut.Depends 13 ∅ gs (out w) p := by
    intro p hp
    apply shared_parent_cut_depends_band gs (out w) (fun g hm => (hg g hm).1)
      (lineId w) (lineId u)
      (fun he => hwu (hinj he)) (high (which w))
    · intro x hx
      rw [← hsingle w hw]
      exact hcorrect w x hx
    · exact high_upper w u huse
    · exact hp
  let A := Support.line (lineId a) \ Support.line (lineId b)
  let B := Support.line (lineId b) \ Support.line (lineId a)
  let C := Support.line (lineId c) \ Support.line (lineId d)
  have hline_card (w u : Fin 4) (hwu : w ≠ u) :
      (Support.line (lineId w) \ Support.line (lineId u)).card = 3 := by
    have hne : lineId w ≠ lineId u := fun h => hwu (hinj h)
    have hl := OneAnd.line_card (lineId w)
    have hm := OneAnd.line_meet (lineId w) (lineId u) hne
    change (Support.line (lineId w)).card = 4 at hl
    change (Support.line (lineId w) ∩ Support.line (lineId u)).card = 1 at hm
    rw [Finset.card_sdiff, hl, Finset.inter_comm, hm]
  have hAB : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro p hpA hpB
    exact (Finset.mem_sdiff.mp hpA).2 (Finset.mem_sdiff.mp hpB).1
  have hAC : (A ∩ C).card ≤ 1 := by
    have hsub : A ∩ C ⊆ Support.line (lineId a) ∩ Support.line (lineId c) := by
      intro p hp
      exact Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp (Finset.mem_inter.mp hp).1).1,
        (Finset.mem_sdiff.mp (Finset.mem_inter.mp hp).2).1⟩
    have hsmall := Global.line_intersection (lineId a) (lineId c)
      (fun he => hac (hinj he))
    exact (Finset.card_le_card hsub).trans hsmall
  have hBC : (B ∩ C).card ≤ 1 := by
    have hsub : B ∩ C ⊆ Support.line (lineId b) ∩ Support.line (lineId c) := by
      intro p hp
      exact Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp (Finset.mem_inter.mp hp).1).1,
        (Finset.mem_sdiff.mp (Finset.mem_inter.mp hp).2).1⟩
    have hsmall := Global.line_intersection (lineId b) (lineId c)
      (fun he => hbc (hinj he))
    exact (Finset.card_le_card hsub).trans hsmall
  exact three_triples_lower gs (out a) (out b) (out c) (fun g hm => (hg g hm).2) A B C
    (hline_card a b hab) (hline_card b a hab.symm) (hline_card c d hdc.symm)
    hAB hAC hBC (low_dep a b hab ha (Or.inr habhigh.symm))
    (low_dep b a hab.symm hb (Or.inr habhigh)) (low_dep c d hdc.symm hc hcdhigh)

end PEqualNP.Outside.L_meta_1024_aux.FourOrSinks

namespace PEqualNP.Outside.L_meta_1024_aux.FourOrSinks

open PEqualNP.CircuitLowerBounds

lemma cut_ge_false (gs : List Gate) (x : Fin 13 → Bool) (i : ℕ)
    (hi : 13 + gs.length ≤ i) : Cut.cutVal 13 ∅ gs x i = false := by
  unfold Cut.cutVal
  apply List.getD_eq_default
  rw [Cut.run_length]
  exact hi

lemma low_prefix_value (gs : List Gate) (hsize : gs.length ≤ 7)
    (i : ℕ) (hi0 : i ≠ 18) (hi1 : i ≠ 19) (x : Fin 13 → Bool) :
    Cut.cutVal 13 ∅ gs x i = Cut.cutVal 13 ∅ (gs.take 5) x i := by
  by_cases hs : 5 ≤ gs.length
  · by_cases hi : i < 18
    · exact Cut.cutVal_take 13 ∅ gs x 5 i hs hi
    · have hi20 : 20 ≤ i := by omega
      rw [cut_ge_false gs x i (by omega),
        cut_ge_false (gs.take 5) x i (by simp only [List.length_take]; omega)]
  · have hs5 : gs.length ≤ 5 := by omega
    rw [List.take_of_length_le hs5]

lemma low_pair_exact (gs : List Gate) (hsize : gs.length ≤ 7)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : Fin 13) (i j : ℕ)
    (hi0 : i ≠ 18) (hi1 : i ≠ 19) (hj0 : j ≠ 18) (hj1 : j ≠ 19)
    (hcorrect : ∀ x, Support.Band x →
      (Cut.cutVal 13 ∅ gs x i || Cut.cutVal 13 ∅ gs x j) = Support.target w x) :
    ∀ x, (Cut.cutVal 13 ∅ gs x i || Cut.cutVal 13 ∅ gs x j) = Support.target w x := by
  let pre := gs.take 5
  let g : Gate := ⟨GateOp.or, [i, j]⟩
  let code := pre ++ [g]
  let o := 13 + pre.length
  have hval (x : Fin 13 → Bool) :
      Cut.cutVal 13 ∅ code x o =
        (Cut.cutVal 13 ∅ gs x i || Cut.cutVal 13 ∅ gs x j) := by
    rw [low_prefix_value gs hsize i hi0 hi1 x, low_prefix_value gs hsize j hj0 hj1 x]
    change Cut.cutVal 13 ∅ (pre ++ [g]) x (13 + pre.length) = _
    rw [Cut.cutVal_snoc]
    simp [g, GateOp.eval, pre]
  have hcode : ∀ q ∈ code, (q.op = GateOp.and ∨ q.op = GateOp.or) ∧ q.inputs.length ≤ 2 := by
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hg q (List.mem_of_mem_take hq)
    · have he : q = g := by simpa using hq
      subst q
      simp [g]
  let E := Cut.essential (M := 13) 13 ∅ code o
  have hE : E.card ≤ 7 := by
    have he := Cut.essential_bound (M := 13) 13 ∅ code o (fun q hq => (hcode q hq).2)
      (Finset.empty_subset _)
    have hlen : code.length ≤ 6 := by
      simp only [code, List.length_append, List.length_singleton, pre, List.length_take]
      omega
    simp only [Finset.card_empty, Nat.sub_zero] at he
    exact he.trans (by omega)
  have hband : ∀ x, Support.Band x → Circuit.eval ⟨code, o⟩ (List.ofFn x) = Support.target w x := by
    intro x hx
    rw [← Cut.cut_empty, hval]
    exact hcorrect x hx
  have hsupp : Support.Supports (fun x => Circuit.eval ⟨code, o⟩ (List.ofFn x)) E := by
    intro x y hxy
    simpa only [Cut.cut_empty] using Cut.essential_supports 13 ∅ code o x y hxy
  have he : ∀ x, Cut.cutVal 13 ∅ code x o = Support.target w x := by
    simpa only [Cut.cut_empty] using Support.circuit_support_exact code o w
      (fun q hq => (hcode q hq).1) hband E hE hsupp
  intro x
  rw [← hval, he]

end PEqualNP.Outside.L_meta_1024_aux.FourOrSinks

namespace PEqualNP.Outside.L_meta_1024_aux.FourOrSinks

open PEqualNP.CircuitLowerBounds

lemma pair_representation (gs : List Gate) (hsize : gs.length ≤ 7) (i j : ℕ)
    (hhigh : i = 18 ∨ i = 19 ∨ j = 18 ∨ j = 19) :
    ∃ (both : Bool) (which : Fin 2) (o : ℕ),
      (both = false → ∀ x : Fin 13 → Bool,
        (Cut.cutVal 13 ∅ gs x i || Cut.cutVal 13 ∅ gs x j) =
          (Cut.cutVal 13 ∅ gs x (18 + which.val) || Cut.cutVal 13 ∅ (gs.take 5) x o)) ∧
      (both = true → ∀ x : Fin 13 → Bool,
        (Cut.cutVal 13 ∅ gs x i || Cut.cutVal 13 ∅ gs x j) =
          (Cut.cutVal 13 ∅ gs x 18 || Cut.cutVal 13 ∅ gs x 19)) := by
  have hfalse (x : Fin 13 → Bool) : Cut.cutVal 13 ∅ (gs.take 5) x 20 = false :=
    cut_ge_false (gs.take 5) x 20 (by simp only [List.length_take]; omega)
  by_cases hi0 : i = 18
  · subst i
    by_cases hj1 : j = 19
    · refine ⟨true, 0, 20, by simp, ?_⟩
      intro _ x
      rw [hj1]
    · by_cases hj0 : j = 18
      · refine ⟨false, 0, 20, ?_, by simp⟩
        intro _ x
        simp [hj0, hfalse]
      · refine ⟨false, 0, j, ?_, by simp⟩
        intro _ x
        simpa using congrArg (fun z => Cut.cutVal 13 ∅ gs x 18 || z)
          (low_prefix_value gs hsize j hj0 hj1 x)
  · by_cases hi1 : i = 19
    · subst i
      by_cases hj0 : j = 18
      · refine ⟨true, 0, 20, by simp, ?_⟩
        intro _ x
        simp [hj0, Bool.or_comm]
      · by_cases hj1 : j = 19
        · refine ⟨false, 1, 20, ?_, by simp⟩
          intro _ x
          simp [hj1, hfalse]
        · refine ⟨false, 1, j, ?_, by simp⟩
          intro _ x
          simpa using congrArg (fun z => Cut.cutVal 13 ∅ gs x 19 || z)
            (low_prefix_value gs hsize j hj0 hj1 x)
    · have hj : j = 18 ∨ j = 19 := by tauto
      rcases hj with hj | hj
      · refine ⟨false, 0, i, ?_, by simp⟩
        intro _ x
        rw [hj, low_prefix_value gs hsize i hi0 hi1 x]
        simp [Bool.or_comm]
      · refine ⟨false, 1, i, ?_, by simp⟩
        intro _ x
        rw [hj, low_prefix_value gs hsize i hi0 hi1 x]
        simp [Bool.or_comm]

lemma four_pairs_impossible (gs : List Gate) (hsize : gs.length ≤ 7)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (lineId : Fin 4 → Fin 13) (hinj : Function.Injective lineId)
    (left right : Fin 4 → ℕ)
    (hcorrect : ∀ w x, Support.Band x →
      (Cut.cutVal 13 ∅ gs x (left w) || Cut.cutVal 13 ∅ gs x (right w)) =
        Support.target (lineId w) x)
    (hnotexact : ∀ w, ¬ ∀ x : Fin 13 → Bool,
      (Cut.cutVal 13 ∅ gs x (left w) || Cut.cutVal 13 ∅ gs x (right w)) =
        Support.target (lineId w) x) : False := by
  have hhigh (w : Fin 4) : left w = 18 ∨ left w = 19 ∨ right w = 18 ∨ right w = 19 := by
    by_contra h
    push Not at h
    exact hnotexact w (low_pair_exact gs hsize hg (lineId w) (left w) (right w)
      h.1 h.2.1 h.2.2.1 h.2.2.2 (hcorrect w))
  have hrep (w : Fin 4) := pair_representation gs hsize (left w) (right w) (hhigh w)
  choose both which out hsingle hdouble using hrep
  have hcount := high_network_lower_band (gs.take 5) out
    (fun g hgmem => hg g (List.mem_of_mem_take hgmem)) lineId hinj which both
    (fun u x => Cut.cutVal 13 ∅ gs x (18 + u.val))
    (fun w x => Cut.cutVal 13 ∅ gs x (left w) || Cut.cutVal 13 ∅ gs x (right w))
    hsingle hdouble hcorrect
  simp only [List.length_take] at hcount
  omega

end PEqualNP.Outside.L_meta_1024_aux.FourOrSinks


namespace PEqualNP.Outside.L_meta_1024_aux.FourReduction
open PEqualNP.CircuitLowerBounds

set_option maxHeartbeats 4000000 in
lemma four_or_sink_bound (gs : List Gate) (out : Fin 13 → ℕ)
    (lineId : Fin 4 → Fin 13) (hinj : Function.Injective lineId)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ w (x : Fin 13 → Bool), Support.Band x → Global.val gs x (out w) = Support.target w x)
    (hordinary : ∀ w ∉ Finset.univ.image lineId, ∀ x : Fin 13 → Bool,
      Global.val gs x (out w) = Support.target w x)
    (hsinks : Dead.NoReads 13 (Finset.univ.image (fun u : Fin 4 => out (lineId u))) gs)
    (hor : ∀ u : Fin 4, ∃ j : ℕ, ∃ hj : j < gs.length,
      out (lineId u) = 13 + j ∧ gs[j].op = GateOp.or) : 39 ≤ gs.length := by
  classical
  by_contra! hsmall
  let A : Finset (Fin 13) := Finset.univ.image lineId
  let W := Finset.univ \ A
  let Q : Finset ℕ := Finset.univ.image (fun u : Fin 4 => out (lineId u))
  have houtinj := Bridge.output_distinct gs out hcorrect
  have hindex (w : Fin 13) := Bridge.output_index gs (out w) w (hcorrect w)
  have hA : A.card = 4 := by rw [Finset.card_image_of_injective _ hinj]; decide
  have hW : W.card = 9 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), hA]
    decide
  have hQ : Q.card = 4 := by
    have hi : Function.Injective (fun u : Fin 4 => out (lineId u)) := houtinj.comp hinj
    change (Finset.univ.image (fun u : Fin 4 => out (lineId u))).card = 4
    rw [Finset.card_image_of_injective _ hi]
    decide
  have hnotW (u : Fin 4) : lineId u ∉ W := by
    intro hu
    exact (Finset.mem_sdiff.mp hu).2 (Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩)
  have hord : ∀ w ∈ W, ∀ x : Fin 13 → Bool,
      Circuit.eval ⟨gs, out w⟩ (List.ofFn x) = decide (∃ p ∈ Global.line w, x p = true) := by
    intro w hw x
    change Global.val gs x (out w) = Support.target w x
    exact hordinary w (Finset.mem_sdiff.mp hw).2 x
  obtain ⟨P, hP, hPcount, hPprops⟩ := Charges.ordinary_charge_family_strong gs out W hg hord
  have hP27 : 27 ≤ P.card := by simpa [hW] using hPcount
  have hPupper : P.card ≤ gs.length := by simpa using Finset.card_le_card hP
  have hPraw : ∀ i ∈ P, 13 ≤ i := fun i hi => (Finset.mem_Ico.mp (hP hi)).1
  have hnotP (u : Fin 4) : out (lineId u) ∉ P := by
    intro hu
    obtain ⟨x, hx, hxt, hxf⟩ := (hPprops (lineId u) (hnotW u) _ hu).2
    have hh := hcorrect (lineId u) x hx
    rw [hxf, hxt] at hh
    exact Bool.noConfusion hh
  have hdisj : Disjoint P Q := by
    rw [Finset.disjoint_left]
    intro i hiP hiQ
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hiQ
    exact hnotP u hiP
  have hQsub : Q ⊆ Finset.Ico 13 (13 + gs.length) := by
    intro i hi
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_Ico.mpr (hindex (lineId u))
  let E (u : Fin 4) := Cut.essential (M := 13 + gs.length) 13 P gs (out (lineId u))
  have hE9 (u : Fin 4) : (E u).card ≤ 9 := by
    let R := Q.erase (out (lineId u))
    have hoQ : out (lineId u) ∈ Q := Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩
    have hR : R.card = 3 := by rw [Finset.card_erase_of_mem hoQ, hQ]
    have hRsub : R ⊆ Q := Finset.erase_subset _ _
    have hPR : Disjoint P R := hdisj.mono_right hRsub
    have hcount : 30 ≤ (P ∪ R).card := by
      rw [Finset.card_union_of_disjoint hPR, hR]
      omega
    have hsub : P ∪ R ⊆ Finset.Ico 13 (13 + gs.length) :=
      Finset.union_subset hP (hRsub.trans hQsub)
    have hupper : (P ∪ R).card ≤ gs.length := by simpa using Finset.card_le_card hsub
    have hreads : Dead.NoReads 13 R gs := by
      intro j hj i hi hn hiR
      exact hsinks j hj i hi hn (hRsub hiR)
    have heq := Cut.essential_add_sinks (M := 13 + gs.length) 13 P R gs hreads
      (out (lineId u)) (by simp [R])
    have hb := Cut.essential_bound (M := 13 + gs.length) 13 (P ∪ R) gs (out (lineId u))
      (fun g hm => (hg g hm).2) hsub
    rw [heq] at hb
    change (E u).card ≤ _ at hb
    omega
  have hraw (u : Fin 4) (p : Fin 13) (hp : p ∈ Global.line (lineId u)) : Bridge.rawIndex gs p ∈ E u := by
    apply Bridge.raw_line_members9 gs (out (lineId u)) (lineId u) (fun g hm => (hg g hm).1)
      (hcorrect (lineId u)) P
      (fun i hi => (hPprops (lineId u) (hnotW u) i hi).1)
      (fun i hi => (hPprops (lineId u) (hnotW u) i hi).2)
      (fun z => Cut.cutVal 13 P gs z (out (lineId u))) (E u) (hE9 u)
    · exact Cut.essential_sources 13 P gs (out (lineId u))
    · intro x y hxy hx
      exact Cut.cutVal_mono 13 P gs (fun g hm => (hg g hm).1) x y hxy (out (lineId u)) hx
    · exact Cut.essential_supports 13 P gs (out (lineId u))
    · intro x
      exact Cut.factor P gs x (out (lineId u))
    · exact hp
  have hclamped (u : Fin 4) : ∀ x : Fin 13 → Bool, Support.Band x →
      Cut.cutVal 13 P gs (Dead.trueSources gs x) (out (lineId u)) = Support.target (lineId u) x := by
    apply (PaidClamp.correct_and_bounded gs (fun g hm => (hg g hm).1) (lineId u) P hPraw
      (fun i hi => (hPprops (lineId u) (hnotW u) i hi).1) (E u) (by have := hE9 u; omega)
      (Cut.essential_sources 13 P gs (out (lineId u))) (hraw u)
      (fun z => Cut.cutVal 13 P gs z (out (lineId u))) ?_ ?_ ?_).2
    · intro x y hxy hx
      exact Cut.cutVal_mono 13 P gs (fun g hm => (hg g hm).1) x y hxy (out (lineId u)) hx
    · exact Cut.essential_supports 13 P gs (out (lineId u))
    · intro x hx
      exact (Cut.factor P gs x (out (lineId u))).trans (hcorrect (lineId u) x hx)
  let C := Sink.transform 13 P gs
  have hCsize : C.length = gs.length := Sink.transform_length 13 P gs
  have hCallowed := Sink.transform_allowed 13 P gs hg
  have hCval (u : Fin 4) (x : Fin 13 → Bool) : Global.val C x (out (lineId u)) =
      Cut.cutVal 13 P gs (Dead.trueSources gs x) (out (lineId u)) :=
    Sink.transform_cut_output P gs (fun g hm => (hg g hm).1) hPraw x (Dead.trueSources gs x)
      (Dead.trueSources_input gs x) (fun i _ hn hi => Dead.trueSources_paid gs x i hn hi) _ (hnotP u)
  have hCcorrect (u : Fin 4) (x : Fin 13 → Bool) (hx : Support.Band x) :
      Global.val C x (out (lineId u)) = Support.target (lineId u) x := (hCval u x).trans (hclamped u x hx)
  have hCreads : Dead.NoReads 13 (P ∪ Q) C := Dead.noReads_union 13 P Q C
    (Dead.transform_noReads 13 P gs) (Sink.preserves_noReads 13 P Q gs hsinks)
  let I := Dead.code 13 (P ∪ Q) C
  have hPQ : P ∪ Q ⊆ Finset.Ico 13 (13 + C.length) := by
    rw [hCsize]
    exact Finset.union_subset hP hQsub
  have hPQcard : 31 ≤ (P ∪ Q).card := by
    rw [Finset.card_union_of_disjoint hdisj, hQ]
    omega
  have hPQupper : (P ∪ Q).card ≤ C.length := by simpa using Finset.card_le_card hPQ
  have hI : I.length ≤ 7 := by
    rw [Dead.code_length, Cut.unpaid_eq_sub 13 (P ∪ Q) C hPQ]
    omega
  have hIallowed := Dead.code_allowed 13 (P ∪ Q) C hCallowed
  have hpair : ∀ u : Fin 4, ∃ a b : ℕ, ∀ x : Fin 13 → Bool, Global.val C x (out (lineId u)) =
      (Global.val I x a || Global.val I x b) := by
    intro u
    obtain ⟨j, hj, hout, hOR⟩ := hor u
    have hjC : j < C.length := by rwa [hCsize]
    have hfalse : Global.val C (Support.row (lineId u)) (13 + j) = false := by
      rw [← hout]
      exact (hCcorrect u _ (Or.inr (Support.row_spec (lineId u)).1)).trans (Support.row_spec (lineId u)).2
    have hORC : C[j].op = GateOp.or := Sink.or_preserved_of_false P gs j hj hOR _ hfalse
    have hfan := (hCallowed C[j] (List.getElem_mem hjC)).2
    have hh := Dead.deleted_or_pair (P ∪ Q) C hCreads hI j hjC hORC hfan
    simpa only [← hout] using hh
  choose left right hpair using hpair
  let U := Dead.paidCode 13 P gs
  let outU : Fin 4 → ℕ := fun u => Dead.paidIndex 13 P gs (out (lineId u))
  have hUsize : U.length ≤ 11 := by
    rw [Dead.paid_length, Cut.unpaid_eq_sub 13 P gs hP]
    omega
  have hUallowed := Dead.paid_allowed 13 P gs hg
  have hUvalid (u : Fin 4) : outU u < 13 + U.length :=
    Dead.mapped_valid 13 P C (out (lineId u)) (by rw [hCsize]; exact (hindex (lineId u)).2) (hnotP u)
  have hUval (u : Fin 4) (x : Fin 13 → Bool) : Global.val U x (outU u) = Global.val C x (out (lineId u)) :=
    Dead.eval P C (Dead.transform_noReads 13 P gs) x (out (lineId u))
      (by rw [hCsize]; exact (hindex (lineId u)).2) (hnotP u)
  have hUnon := small_four_nonordinary U hUsize hUallowed lineId hinj outU hUvalid
    (fun u x hx => (hUval u x).trans (hCcorrect u x hx))
  have hcut (x : Fin 13 → Bool) (i : ℕ) : Cut.cutVal 13 ∅ I x i = Global.val I x i := Cut.cut_empty I x i
  apply FourOrSinks.four_pairs_impossible I hI hIallowed lineId hinj left right
  · intro u x hx
    rw [hcut, hcut, ← hpair u x]
    exact hCcorrect u x hx
  · intro u hexact
    apply hUnon u
    intro x
    rw [hUval, hpair u x, ← hcut, ← hcut]
    exact hexact x

end PEqualNP.Outside.L_meta_1024_aux.FourReduction

namespace PEqualNP.Outside.L_meta_1024_aux.TrueClamp

open PEqualNP.CircuitLowerBounds

noncomputable def constants (n : ℕ) (gs : List Gate) : Finset ℕ :=
  (Finset.Ico n (n + gs.length)).filter
    (fun i => Global.val gs (fun _ : Fin n => false) i = true)

lemma constant_value {n : ℕ} (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x : Fin n → Bool) (i : ℕ) (hi : i ∈ constants n gs) : Global.val gs x i = true := by
  have hz := (Finset.mem_filter.mp hi).2
  change Circuit.eval ⟨gs, i⟩ (List.ofFn (fun _ : Fin n => false)) = true at hz
  change Circuit.eval ⟨gs, i⟩ (List.ofFn x) = true
  rw [← Cut.cut_empty] at hz ⊢
  exact Cut.cutVal_mono n ∅ gs hg (fun _ => false) x (by intro p hp; cases hp) i hz

lemma constant_transform_eq {n : ℕ} (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x : Fin n → Bool) (i : ℕ) :
    Global.val (Sink.transform n (constants n gs) gs) x i = Global.val gs x i := by
  exact Sink.prefix_eq (constants n gs) gs hg x (n + gs.length) (by omega)
    (fun j hj _ _ => constant_value gs hg x j hj) i

lemma and_preserved (n : ℕ) (P : Finset ℕ) (gs : List Gate) (j : ℕ)
    (hj : j < gs.length) (hand : gs[j].op = GateOp.and) :
    ((Sink.transform n P gs)[j]'(by rw [Sink.transform_length]; exact hj)).op = GateOp.and := by
  rw [Sink.transform_get n P gs j hj]
  unfold Sink.gate
  split
  · rename_i h
    have he := h.1
    rw [hand] at he
  · exact hand

noncomputable def intermediate (n : ℕ) (S : Finset ℕ) (gs : List Gate) : List Gate :=
  Sink.transform n S gs

noncomputable def allDeleted (n : ℕ) (S : Finset ℕ) (gs : List Gate) : Finset ℕ :=
  S ∪ constants n (intermediate n S gs)

noncomputable def prepared (n : ℕ) (S : Finset ℕ) (gs : List Gate) : List Gate :=
  Sink.transform n (constants n (intermediate n S gs)) (intermediate n S gs)

noncomputable def clean (n : ℕ) (S : Finset ℕ) (gs : List Gate) : List Gate :=
  Dead.code n (allDeleted n S gs) (prepared n S gs)

noncomputable def cleanIndex (n : ℕ) (S : Finset ℕ) (gs : List Gate) (i : ℕ) : ℕ :=
  (Dead.indices n (allDeleted n S gs) (prepared n S gs)).getD i 0

lemma intermediate_length (n : ℕ) (S : Finset ℕ) (gs : List Gate) :
    (intermediate n S gs).length = gs.length := Sink.transform_length n S gs

lemma prepared_length (n : ℕ) (S : Finset ℕ) (gs : List Gate) :
    (prepared n S gs).length = gs.length := by
  simp only [prepared, intermediate, Sink.transform_length]

lemma prepared_noReads (n : ℕ) (S : Finset ℕ) (gs : List Gate) :
    Dead.NoReads n (allDeleted n S gs) (prepared n S gs) := by
  apply Dead.noReads_union
  · exact Sink.preserves_noReads n (constants n (intermediate n S gs)) S
      (intermediate n S gs) (Dead.transform_noReads n S gs)
  · exact Dead.transform_noReads n (constants n (intermediate n S gs)) _

lemma clean_eval {n : ℕ} (S : Finset ℕ) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x : Fin n → Bool) (i : ℕ) (hi : i < n + gs.length)
    (hkeep : i ∉ allDeleted n S gs) :
    Global.val (clean n S gs) x (cleanIndex n S gs i) =
      Global.val (intermediate n S gs) x i := by
  rw [clean, cleanIndex, Dead.eval (allDeleted n S gs) (prepared n S gs)
    (prepared_noReads n S gs) x i (by rwa [prepared_length]) hkeep]
  exact constant_transform_eq (intermediate n S gs)
    (fun g hm => (Sink.transform_allowed n S gs hg g hm).1) x i

lemma clean_allowed (n : ℕ) (S : Finset ℕ) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ g ∈ clean n S gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  exact Dead.code_allowed n (allDeleted n S gs) (prepared n S gs)
    (Sink.transform_allowed n _ _ (Sink.transform_allowed n S gs hg))

lemma clean_length_le (n : ℕ) (S : Finset ℕ) (gs : List Gate)
    (hS : S ⊆ Finset.Ico n (n + gs.length)) :
    (clean n S gs).length ≤ gs.length - S.card := by
  rw [clean, Dead.code_length]
  have hsub : Finset.Ico n (n + gs.length) \ allDeleted n S gs ⊆
      Finset.Ico n (n + gs.length) \ S := by
    intro i hi
    refine Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hi).1, ?_⟩
    intro hiS
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_union_left _ hiS)
  have hc := Finset.card_le_card hsub
  rw [Finset.card_sdiff_of_subset hS] at hc
  simpa only [Cut.unpaid, prepared_length, Nat.card_Ico, Nat.add_sub_cancel_left] using hc

lemma prepared_op_kept (n : ℕ) (S : Finset ℕ) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (j : ℕ) (hj : j < gs.length) (hkeep : n + j ∉ allDeleted n S gs) :
    ((prepared n S gs)[j]'(by rw [prepared_length]; exact hj)).op = gs[j].op := by
  have hjt : j < (intermediate n S gs).length := by rwa [intermediate_length]
  have hnotconst : n + j ∉ constants n (intermediate n S gs) :=
    fun h => hkeep (Finset.mem_union_right _ h)
  have hz : Global.val (intermediate n S gs) (fun _ : Fin n => false) (n + j) = false := by
    cases he : Global.val (intermediate n S gs) (fun _ : Fin n => false) (n + j) with
    | false => rfl
    | true =>
      apply False.elim
      apply hnotconst
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, he⟩
  have hmono : ∀ g ∈ intermediate n S gs, g.op = GateOp.and ∨ g.op = GateOp.or :=
    fun g hm => (Sink.transform_allowed n S gs hg g hm).1
  have huz : Global.val (prepared n S gs) (fun _ : Fin n => false) (n + j) = false :=
    (constant_transform_eq (intermediate n S gs) hmono _ _).trans hz
  rcases (hg gs[j] (List.getElem_mem hj)).1 with hand | hor
  · have ht := and_preserved n S gs j hj hand
    have hu := and_preserved n (constants n (intermediate n S gs))
      (intermediate n S gs) j hjt ht
    exact hu.trans hand.symm
  · have ht := Sink.or_preserved_of_false S gs j hj hor (fun _ : Fin n => false) hz
    have hu := Sink.or_preserved_of_false (constants n (intermediate n S gs))
      (intermediate n S gs) j hjt ht (fun _ : Fin n => false) huz
    exact hu.trans hor.symm

end PEqualNP.Outside.L_meta_1024_aux.TrueClamp

namespace PEqualNP.Outside.L_meta_1024_aux.TrueClamp

open PEqualNP.CircuitLowerBounds

def andGate (g : Gate) : Bool := match g.op with
  | GateOp.and => true
  | _ => false

def andCount (gs : List Gate) : ℕ := (gs.filter andGate).length

lemma andCount_snoc (gs : List Gate) (g : Gate) :
    andCount (gs ++ [g]) = andCount gs + if andGate g then 1 else 0 := by
  cases h : andGate g <;> simp [andCount, List.filter_append, h]

lemma code_and_count (n : ℕ) (P : Finset ℕ) (gs hs : List Gate)
    (hlen : hs.length = gs.length)
    (hop : ∀ j (hj : j < gs.length), n + j ∉ P →
      (hs[j]'(by omega)).op = gs[j].op) :
    andCount (Dead.code n P hs) ≤ andCount gs ∧
      (∀ j (hj : j < gs.length), n + j ∈ P → gs[j].op = GateOp.and →
        andCount (Dead.code n P hs) < andCount gs) := by
  induction gs using List.reverseRecOn generalizing hs with
  | nil =>
    have he : hs = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
    subst hs
    simp [andCount, Dead.code, Dead.compile]
  | append_singleton gs g ih =>
    cases hs using List.reverseRecOn with
    | nil => simp at hlen
    | append_singleton hs h ihs =>
      have hlen' : hs.length = gs.length := by
        simp only [List.length_append, List.length_singleton] at hlen
        omega
      have hop' : ∀ j (hj : j < gs.length), n + j ∉ P →
          (hs[j]'(by omega)).op = gs[j].op := by
        intro j hj hjP
        have hh := hop j (by simp; omega) hjP
        simpa only [List.getElem_append_left hj, List.getElem_append_left (show j < hs.length by omega)] using hh
      obtain ⟨hle, hstrict⟩ := ih hs hlen' hop'
      have hsource := andCount_snoc gs g
      by_cases hp : n + gs.length ∈ P
      · have hcode : Dead.code n P (hs ++ [h]) = Dead.code n P hs := by
          rw [Dead.code_snoc, hlen', if_pos hp]
        rw [hcode]
        constructor
        · omega
        · intro j hj hjP hjand
          by_cases hjlast : j = gs.length
          · subst j
            have hga : g.op = GateOp.and := by simpa using hjand
            have hbit : andGate g = true := by simp [andGate, hga]
            have hsource1 : andCount (gs ++ [g]) = andCount gs + 1 := by
              simpa [hbit] using hsource
            omega
          · have hjold : j < gs.length := by
              simp only [List.length_append, List.length_singleton] at hj
              omega
            have hja : gs[j].op = GateOp.and := by
              simpa only [List.getElem_append_left hjold] using hjand
            have hh := hstrict j hjold hjP hja
            omega
      · have hlast : h.op = g.op := by
          have hh := hop gs.length (by simp) hp
          simpa [hlen'] using hh
        have hcode : andCount (Dead.code n P (hs ++ [h])) =
            andCount (Dead.code n P hs) + if andGate g then 1 else 0 := by
          rw [Dead.code_snoc, hlen', if_neg hp, andCount_snoc]
          simp only [Dead.nextGate, andGate, hlast]
          rfl
        rw [hcode]
        constructor
        · omega
        · intro j hj hjP hjand
          have hjold : j < gs.length := by
            simp only [List.length_append, List.length_singleton] at hj
            have hjne : j ≠ gs.length := fun he => hp (he ▸ hjP)
            omega
          have hja : gs[j].op = GateOp.and := by
            simpa only [List.getElem_append_left hjold] using hjand
          have hh := hstrict j hjold hjP hja
          omega

lemma clean_and_count (n : ℕ) (S : Finset ℕ) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    andCount (clean n S gs) ≤ andCount gs := by
  exact (code_and_count n (allDeleted n S gs) gs (prepared n S gs)
    (prepared_length n S gs) (prepared_op_kept n S gs hg)).1

lemma clean_and_strict (n : ℕ) (S : Finset ℕ) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (j : ℕ) (hj : j < gs.length) (hjS : n + j ∈ S) (hand : gs[j].op = GateOp.and) :
    andCount (clean n S gs) < andCount gs := by
  exact (code_and_count n (allDeleted n S gs) gs (prepared n S gs)
    (prepared_length n S gs) (prepared_op_kept n S gs hg)).2 j hj
    (Finset.mem_union_left _ hjS) hand

end PEqualNP.Outside.L_meta_1024_aux.TrueClamp

namespace PEqualNP.Outside.L_meta_1024_aux.TrueClamp

open PEqualNP.CircuitLowerBounds

lemma intermediate_correct_other (gs : List Gate) (out : Fin 13 → ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ w x, Support.Band x → Global.val gs x (out w) = Support.target w x)
    (w : Fin 13) (S : Finset ℕ)
    (habove : ∀ i ∈ S, ∀ x, Support.Band x → Support.target w x = true → Global.val gs x i = true)
    (u : Fin 13) (huw : u ≠ w) (x : Fin 13 → Bool) (hx : Support.Band x) :
    Global.val (intermediate 13 S gs) x (out u) = Support.target u x := by
  cases hu : Support.target u x with
  | false =>
    have hw := Sink.other_target_true u w huw x hx hu
    have he := Sink.output_eq S gs (fun g hm => (hg g hm).1) x (out u)
      (Bridge.output_index gs (out u) u (hcorrect u))
      (fun i hi _ => habove i hi x hx hw)
    exact he.trans ((hcorrect u x hx).trans hu)
  | true =>
    apply Sink.val_ge S gs (fun g hm => (hg g hm).1) x (out u)
    exact (hcorrect u x hx).trans hu

lemma output_kept (gs : List Gate) (out : Fin 13 → ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ w x, Support.Band x → Global.val gs x (out w) = Support.target w x)
    (w : Fin 13) (S : Finset ℕ)
    (habove : ∀ i ∈ S, ∀ x, Support.Band x → Support.target w x = true → Global.val gs x i = true)
    (u : Fin 13) (huw : u ≠ w) : out u ∉ allDeleted 13 S gs := by
  let x := Support.row u
  have hx : Support.Band x := Or.inr (Support.row_spec u).1
  have hu : Support.target u x = false := (Support.row_spec u).2
  have hw := Sink.other_target_true u w huw x hx hu
  intro hm
  rcases Finset.mem_union.mp hm with hS | hP
  · have ht := habove (out u) hS x hx hw
    rw [hcorrect u x hx, hu] at ht
    cases ht
  · have ht := constant_value (intermediate 13 S gs)
      (fun g hgmem => (Sink.transform_allowed 13 S gs hg g hgmem).1) x (out u) hP
    rw [intermediate_correct_other gs out hg hcorrect w S habove u huw x hx, hu] at ht
    cases ht

lemma clean_correct_other (gs : List Gate) (out : Fin 13 → ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ w x, Support.Band x → Global.val gs x (out w) = Support.target w x)
    (w : Fin 13) (S : Finset ℕ)
    (habove : ∀ i ∈ S, ∀ x, Support.Band x → Support.target w x = true → Global.val gs x i = true)
    (u : Fin 13) (huw : u ≠ w) (x : Fin 13 → Bool) (hx : Support.Band x) :
    Global.val (clean 13 S gs) x (cleanIndex 13 S gs (out u)) = Support.target u x := by
  rw [clean_eval S gs hg x (out u) (Bridge.output_index gs (out u) u (hcorrect u)).2
    (output_kept gs out hg hcorrect w S habove u huw)]
  exact intermediate_correct_other gs out hg hcorrect w S habove u huw x hx

end PEqualNP.Outside.L_meta_1024_aux.TrueClamp

namespace PEqualNP.Outside.L_meta_1024_aux.TrueClamp

open PEqualNP.CircuitLowerBounds

lemma seed_extreme_true (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w u : Fin 13) (huw : u ≠ w) (S : Finset ℕ)
    (habove : ∀ i ∈ S, ∀ x, Support.Band x → Support.target w x = true → Global.val gs x i = true)
    (i : ℕ) (hi : i ∈ S) : Global.val gs (Global.Zof (Global.line u)) i = true := by
  have ht := habove i hi (Support.row u) (Or.inr (Support.row_spec u).1)
    (Bridge.row_targets u w huw)
  apply Bridge.val_mono gs hg (Support.row u) (Global.Zof (Global.line u)) _ i ht
  intro p hp
  have hn : p ∉ Support.line u := by
    intro hm
    rw [Clamp.row_line_false u p hm] at hp
    cases hp
  simpa [Global.Zof, Global.line, Support.line] using hn

lemma intermediate_ordinary (gs : List Gate) (out : Fin 13 → ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ v x, Support.Band x → Global.val gs x (out v) = Support.target v x)
    (w : Fin 13) (S : Finset ℕ)
    (habove : ∀ i ∈ S, ∀ x, Support.Band x → Support.target w x = true → Global.val gs x i = true)
    (u : Fin 13) (huw : u ≠ w)
    (hordinary : ∀ x, Global.val gs x (out u) = Support.target u x) :
    ∀ x, Global.val (intermediate 13 S gs) x (out u) = Support.target u x := by
  let Z := Global.Zof (Global.line u)
  have hZtarget : Support.target u Z = false := by
    simp [Support.target, Z, Global.Zof, Global.line, Support.line]
  have hZ : Global.val (intermediate 13 S gs) Z (out u) = false := by
    have he := Sink.output_eq S gs (fun g hm => (hg g hm).1) Z (out u)
      (Bridge.output_index gs (out u) u (hcorrect u))
      (fun i hi _ => seed_extreme_true gs (fun g hm => (hg g hm).1) w u huw S habove i hi)
    exact he.trans ((hordinary Z).trans hZtarget)
  intro x
  cases hx : Support.target u x with
  | true =>
    exact Sink.val_ge S gs (fun g hm => (hg g hm).1) x (out u) ((hordinary x).trans hx)
  | false =>
    have hxZ : ∀ p, x p = true → Z p = true := by
      intro p hp
      have hn : p ∉ Support.line u := by
        intro hm
        have ht : Support.target u x = true := decide_eq_true ⟨p, hm, hp⟩
        rw [hx] at ht
        cases ht
      simpa [Z, Global.Zof, Global.line, Support.line] using hn
    cases he : Global.val (intermediate 13 S gs) x (out u) with
    | false => rfl
    | true =>
      have ht := Bridge.val_mono (intermediate 13 S gs)
        (fun g hm => (Sink.transform_allowed 13 S gs hg g hm).1) x Z hxZ (out u) he
      rw [hZ] at ht
      cases ht

lemma clean_ordinary (gs : List Gate) (out : Fin 13 → ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ v x, Support.Band x → Global.val gs x (out v) = Support.target v x)
    (w : Fin 13) (S : Finset ℕ)
    (habove : ∀ i ∈ S, ∀ x, Support.Band x → Support.target w x = true → Global.val gs x i = true)
    (u : Fin 13) (huw : u ≠ w)
    (hordinary : ∀ x, Global.val gs x (out u) = Support.target u x) :
    ∀ x, Global.val (clean 13 S gs) x (cleanIndex 13 S gs (out u)) = Support.target u x := by
  intro x
  rw [clean_eval S gs hg x (out u) (Bridge.output_index gs (out u) u (hcorrect u)).2
    (output_kept gs out hg hcorrect w S habove u huw)]
  exact intermediate_ordinary gs out hg hcorrect w S habove u huw hordinary x

end PEqualNP.Outside.L_meta_1024_aux.TrueClamp

namespace PEqualNP.Outside.L_meta_1024_aux.TrueClamp

open PEqualNP.CircuitLowerBounds

lemma appendLine_andCount (gs : List Gate) (w : Fin 13) :
    andCount (AppendLine.appendLine gs w) = andCount gs := by
  simp [AppendLine.appendLine, andCount, andGate, AppendLine.pairGate, List.filter_append]

lemma seed_surgery (gs : List Gate) (out : Fin 13 → ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ w x, Support.Band x → Global.val gs x (out w) = Support.target w x)
    (w : Fin 13) (S : Finset ℕ)
    (hS : S ⊆ Finset.Ico 13 (13 + gs.length)) (hcard : 3 ≤ S.card)
    (habove : ∀ i ∈ S, ∀ x, Support.Band x → Support.target w x = true → Global.val gs x i = true)
    (j : ℕ) (hj : j < gs.length) (hjS : 13 + j ∈ S) (hand : gs[j].op = GateOp.and) :
    ∃ (gs' : List Gate) (out' : Fin 13 → ℕ),
      (∀ g ∈ gs', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ andCount gs' < andCount gs ∧
      (∀ u x, Support.Band x → Global.val gs' x (out' u) = Support.target u x) ∧
      (∀ x, Global.val gs' x (out' w) = Support.target w x) ∧
      ∀ u, (∀ x, Global.val gs x (out u) = Support.target u x) →
        ∀ x, Global.val gs' x (out' u) = Support.target u x := by
  let cs := clean 13 S gs
  let gs' := AppendLine.appendLine cs w
  let out' : Fin 13 → ℕ := fun u => if u = w then 15 + cs.length else cleanIndex 13 S gs (out u)
  refine ⟨gs', out', AppendLine.allowed cs w (clean_allowed 13 S gs hg), ?_, ?_, ?_, ?_, ?_⟩
  · have hlen := clean_length_le 13 S gs hS
    have hScard := Finset.card_le_card hS
    simp only [Nat.card_Ico, Nat.add_sub_cancel_left] at hScard
    change (AppendLine.appendLine cs w).length ≤ gs.length
    rw [AppendLine.length]
    change (clean 13 S gs).length + 3 ≤ gs.length
    omega
  · change andCount (AppendLine.appendLine cs w) < andCount gs
    rw [appendLine_andCount]
    exact clean_and_strict 13 S gs hg j hj hjS hand
  · intro u x hx
    by_cases huw : u = w
    · subst u
      simp only [out', if_pos rfl]
      exact AppendLine.eval cs w x
    · simp only [out', if_neg huw]
      change Global.val (AppendLine.appendLine cs w) x (cleanIndex 13 S gs (out u)) = _
      rw [AppendLine.old cs w x _ (by
        exact Dead.mapped_valid 13 (allDeleted 13 S gs) (prepared 13 S gs) (out u)
          (by rw [prepared_length]; exact (Bridge.output_index gs (out u) u (hcorrect u)).2)
          (output_kept gs out hg hcorrect w S habove u huw))]
      exact clean_correct_other gs out hg hcorrect w S habove u huw x hx

  · intro x
    simp only [out', if_pos rfl]
    exact AppendLine.eval cs w x
  · intro u hordinary x
    by_cases huw : u = w
    · subst u
      simp only [out', if_pos rfl]
      exact AppendLine.eval cs w x
    · simp only [out', if_neg huw]
      change Global.val (AppendLine.appendLine cs w) x (cleanIndex 13 S gs (out u)) = _
      rw [AppendLine.old cs w x _ (by
        exact Dead.mapped_valid 13 (allDeleted 13 S gs) (prepared 13 S gs) (out u)
          (by rw [prepared_length]; exact (Bridge.output_index gs (out u) u (hcorrect u)).2)
          (output_kept gs out hg hcorrect w S habove u huw))]
      exact clean_ordinary gs out hg hcorrect w S habove u huw hordinary x

end PEqualNP.Outside.L_meta_1024_aux.TrueClamp

namespace PEqualNP.Outside.L_meta_1024_aux.TrueClamp

open PEqualNP.CircuitLowerBounds

lemma first_and_parents (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : Fin 13) (k : ℕ) (hk : k < gs.length) (hand : gs[k].op = GateOp.and)
    (hcorrect : ∀ x, Support.Band x → Global.val gs x (13 + k) = Support.target w x)
    (hfirst : ∀ i, i < 13 + k → ¬ ∀ x, Support.Band x → Global.val gs x i = Support.target w x) :
    ∃ i j : ℕ, 13 ≤ i ∧ 13 ≤ j ∧ i < 13 + k ∧ j < 13 + k ∧ i ≠ j ∧
      ∀ x : Fin 13 → Bool, Global.val gs x (13 + k) = (Global.val gs x i && Global.val gs x j) := by
  have hlen := (hg gs[k] (List.getElem_mem hk)).2
  have hformula (x : Fin 13 → Bool) := Dead.wire_eq_gate gs x k hk
  have hnonempty : (Support.line w).Nonempty := Finset.card_pos.mp (by rw [Clamp.line_card]; decide)
  obtain ⟨p, hp⟩ := hnonempty
  let xp := Support.flip w p
  have hxp : Support.Band xp := Or.inl (Support.flip_spec w p hp).1
  have hrootp : Global.val gs xp (13 + k) = true :=
    (hcorrect xp hxp).trans (Support.flip_spec w p hp).2
  cases hins : gs[k].inputs with
  | nil =>
    have he := hformula (Support.row w)
    rw [hand, hins] at he
    simp only [GateOp.eval, List.map_nil, List.all_nil] at he
    rw [hcorrect _ (Or.inr (Support.row_spec w).1), (Support.row_spec w).2] at he
    cases he
  | cons i tail =>
    cases htail : tail with
    | nil =>
      have he (x : Fin 13 → Bool) : Global.val gs x (13 + k) =
          if i < 13 + k then Global.val gs x i else false := by
        simpa [hand, hins, htail, GateOp.eval] using hformula x
      have hi : i < 13 + k := by
        by_contra hn
        have hh := he xp
        rw [hrootp, if_neg hn] at hh
        cases hh
      apply False.elim
      apply hfirst i hi
      intro x hx
      have hh := he x
      rw [if_pos hi] at hh
      exact hh.symm.trans (hcorrect x hx)
    | cons j rest =>
      have hrest : rest = [] := by
        simp only [hins, htail, List.length_cons] at hlen
        exact List.length_eq_zero_iff.mp (by omega)
      have he (x : Fin 13 → Bool) : Global.val gs x (13 + k) =
          ((if i < 13 + k then Global.val gs x i else false) &&
            (if j < 13 + k then Global.val gs x j else false)) := by
        simpa [hand, hins, htail, hrest, GateOp.eval] using hformula x
      have hab := Bool.and_eq_true_iff.mp ((he xp).symm.trans hrootp)
      have hi : i < 13 + k := by
        by_contra hn
        simp [hn] at hab
      have hj : j < 13 + k := by
        by_contra hn
        simp [hn] at hab
      have heq (x : Fin 13 → Bool) : Global.val gs x (13 + k) =
          (Global.val gs x i && Global.val gs x j) := by simpa [hi, hj] using he x
      have habove (x : Fin 13 → Bool) (hx : Support.Band x) (ht : Support.target w x = true) :
          Global.val gs x i = true ∧ Global.val gs x j = true :=
        Bool.and_eq_true_iff.mp ((heq x).symm.trans ((hcorrect x hx).trans ht))
      have higen : 13 ≤ i := by
        by_contra! hn
        let q : Fin 13 := ⟨i, hn⟩
        obtain ⟨r, hrt, hrq⟩ := Charges.raw_not_above w q
        have hv := (habove (Support.row r) (Or.inr (Support.row_spec r).1) hrt).1
        have hf : Global.val gs (Support.row r) i = false :=
          (Bridge.val_input gs (Support.row r) q).trans hrq
        rw [hf] at hv
        cases hv
      have hjgen : 13 ≤ j := by
        by_contra! hn
        let q : Fin 13 := ⟨j, hn⟩
        obtain ⟨r, hrt, hrq⟩ := Charges.raw_not_above w q
        have hv := (habove (Support.row r) (Or.inr (Support.row_spec r).1) hrt).2
        have hf : Global.val gs (Support.row r) j = false :=
          (Bridge.val_input gs (Support.row r) q).trans hrq
        rw [hf] at hv
        cases hv
      have hij : i ≠ j := by
        intro hij
        apply hfirst i hi
        intro x hx
        have hh := heq x
        simpa [hij] using hh.symm.trans (hcorrect x hx)
      exact ⟨i, j, higen, hjgen, hi, hj, hij, heq⟩

end PEqualNP.Outside.L_meta_1024_aux.TrueClamp

namespace PEqualNP.Outside.L_meta_1024_aux.TrueClamp

open PEqualNP.CircuitLowerBounds

lemma first_and_improvement (gs : List Gate) (out : Fin 13 → ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ u x, Support.Band x → Global.val gs x (out u) = Support.target u x)
    (w : Fin 13) (k : ℕ) (hk : k < gs.length) (hand : gs[k].op = GateOp.and)
    (hroot : ∀ x, Support.Band x → Global.val gs x (13 + k) = Support.target w x)
    (hfirst : ∀ i, i < 13 + k → ¬ ∀ x, Support.Band x → Global.val gs x i = Support.target w x) :
    ∃ (gs' : List Gate) (out' : Fin 13 → ℕ),
      (∀ g ∈ gs', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ andCount gs' < andCount gs ∧
      (∀ u x, Support.Band x → Global.val gs' x (out' u) = Support.target u x) ∧
      (∀ x, Global.val gs' x (out' w) = Support.target w x) ∧
      ∀ u, (∀ x, Global.val gs x (out u) = Support.target u x) →
        ∀ x, Global.val gs' x (out' u) = Support.target u x := by
  obtain ⟨i, j, higen, hjgen, hi, hj, hij, heq⟩ :=
    first_and_parents gs hg w k hk hand hroot hfirst
  let S : Finset ℕ := {13 + k, i, j}
  have hS : S ⊆ Finset.Ico 13 (13 + gs.length) := by
    intro t ht
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl <;> apply Finset.mem_Ico.mpr <;> constructor <;> omega
  have hScard : S.card = 3 := by
    simp [S, (Nat.ne_of_lt hi).symm, (Nat.ne_of_lt hj).symm, hij]
  have habove : ∀ t ∈ S, ∀ x, Support.Band x → Support.target w x = true → Global.val gs x t = true := by
    intro t ht x hx hw
    have hr := (hroot x hx).trans hw
    have hp := Bool.and_eq_true_iff.mp ((heq x).symm.trans hr)
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · exact hr
    · exact hp.1
    · exact hp.2
  exact seed_surgery gs out hg hcorrect w S hS (by omega) habove k hk (by simp [S]) hand

end PEqualNP.Outside.L_meta_1024_aux.TrueClamp

namespace PEqualNP.Outside.L_meta_1024_aux.TrueClamp

open PEqualNP.CircuitLowerBounds

lemma normalize_or_sinks (gs : List Gate) (out : Fin 13 → ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ u x, Support.Band x → Global.val gs x (out u) = Support.target u x)
    (W : Finset (Fin 13))
    (hW : ∀ u ∈ W, ∀ x, Global.val gs x (out u) = Support.target u x) :
    ∃ (hs : List Gate) (ho : Fin 13 → ℕ),
      (∀ g ∈ hs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      hs.length ≤ gs.length ∧
      (∀ u x, Support.Band x → Global.val hs x (ho u) = Support.target u x) ∧
      (∀ u ∈ W, ∀ x, Global.val hs x (ho u) = Support.target u x) ∧
      Dead.NoReads 13 (Finset.univ.image ho) hs ∧
      ∀ u, u ∉ W → ∃ (k : ℕ) (hk : k < hs.length), ho u = 13 + k ∧ hs[k].op = GateOp.or := by
  classical
  let Candidate (cs : List Gate) (co : Fin 13 → ℕ) : Prop :=
    (∀ g ∈ cs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
    cs.length ≤ gs.length ∧
    (∀ u x, Support.Band x → Global.val cs x (co u) = Support.target u x) ∧
    ∀ u ∈ W, ∀ x, Global.val cs x (co u) = Support.target u x
  have hex : ∃ m : ℕ, ∃ cs co, Candidate cs co ∧ andCount cs = m :=
    ⟨andCount gs, gs, out, ⟨hg, le_rfl, hcorrect, hW⟩, rfl⟩
  obtain ⟨cs, co, hcand, hcount⟩ := Nat.find_spec hex
  obtain ⟨hcg, hclen, hccorrect, hcW⟩ := hcand
  have hminimal (ds : List Gate) (do' : Fin 13 → ℕ) (hd : Candidate ds do') :
      andCount cs ≤ andCount ds := by
    rw [hcount]
    exact Nat.find_min' hex ⟨ds, do', hd, rfl⟩
  have hexout (u : Fin 13) : ∃ i, ∀ x, Support.Band x → Global.val cs x i = Support.target u x :=
    ⟨co u, hccorrect u⟩
  let first : Fin 13 → ℕ := fun u => Nat.find (hexout u)
  have hfirstcorrect (u : Fin 13) : ∀ x, Support.Band x → Global.val cs x (first u) = Support.target u x :=
    Nat.find_spec (hexout u)
  have hfirstmin (u : Fin 13) (i : ℕ) (hi : i < first u) :
      ¬ ∀ x, Support.Band x → Global.val cs x i = Support.target u x := by
    intro he
    have hm := Nat.find_min' (hexout u) he
    change first u ≤ i at hm
    omega
  have hfirstor (u : Fin 13) : ∃ (k : ℕ) (hk : k < cs.length), first u = 13 + k ∧ cs[k].op = GateOp.or := by
    have hv := Bridge.output_index cs (first u) u (hfirstcorrect u)
    let k := first u - 13
    have hk : k < cs.length := by omega
    have he : first u = 13 + k := by omega
    rcases (hcg cs[k] (List.getElem_mem hk)).1 with hand | hor
    · have hr : ∀ x, Support.Band x → Global.val cs x (13 + k) = Support.target u x := by
        simpa only [← he] using hfirstcorrect u
      have hm : ∀ i, i < 13 + k → ¬ ∀ x, Support.Band x → Global.val cs x i = Support.target u x := by
        simpa only [← he] using hfirstmin u
      obtain ⟨ds, do', hdg, hdlen, hdand, hdcorrect, hdselected, hdpreserve⟩ :=
        first_and_improvement cs co hcg hccorrect u k hk hand hr hm
      have hdcand : Candidate ds do' :=
        ⟨hdg, hdlen.trans hclen, hdcorrect, fun v hvW => hdpreserve v (hcW v hvW)⟩
      have hle := hminimal ds do' hdcand
      omega
    · exact ⟨k, hk, he, hor⟩
  let ho : Fin 13 → ℕ := fun u => if u ∈ W then co u else first u
  have hretarget : ∀ u x, Support.Band x → Global.val cs x (ho u) = Support.target u x := by
    intro u x hx
    by_cases hu : u ∈ W
    · simpa [ho, hu] using hccorrect u x hx
    · simpa [ho, hu] using hfirstcorrect u x hx
  let O := Finset.univ.image ho
  let hs := Sink.transform 13 O cs
  have hfinal := Sink.band_correct cs ho (fun g hm => (hcg g hm).1) hretarget
  refine ⟨hs, ho, Sink.transform_allowed 13 O cs hcg, ?_, hfinal, ?_, ?_, ?_⟩
  · simpa only [hs, Sink.transform_length] using hclen
  · intro u hu
    apply Sink.preserves_ordinary cs ho hcg hretarget u
    intro x
    simpa [ho, hu] using hcW u hu x
  · exact Dead.transform_noReads 13 O cs
  · intro u hu
    obtain ⟨k, hk, he, hor⟩ := hfirstor u
    have hout : ho u = 13 + k := by simpa [ho, hu] using he
    have hknew : k < hs.length := by simpa only [hs, Sink.transform_length] using hk
    refine ⟨k, hknew, hout, ?_⟩
    have hf : Global.val hs (Support.row u) (13 + k) = false := by
      rw [← hout, hfinal u _ (Or.inr (Support.row_spec u).1), (Support.row_spec u).2]
    exact Sink.or_preserved_of_false O cs k hk hor (Support.row u) hf

end PEqualNP.Outside.L_meta_1024_aux.TrueClamp


namespace PEqualNP.Outside.L_meta_1024_aux.FourReduction
open PEqualNP.CircuitLowerBounds

lemma nine_ordinary_bound (gs : List Gate) (out : Fin 13 → ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ w (x : Fin 13 → Bool), Support.Band x →
      Global.val gs x (out w) = Support.target w x)
    (W : Finset (Fin 13)) (hW : 9 ≤ W.card)
    (hordinary : ∀ w ∈ W, ∀ x : Fin 13 → Bool,
      Global.val gs x (out w) = Support.target w x) : 39 ≤ gs.length := by
  classical
  obtain ⟨V, hVW, hVcard⟩ := Finset.exists_subset_card_eq hW
  obtain ⟨hs, ho, hhg, hhlen, hhcorrect, hhordinary, hhsinks, hhor⟩ :=
    TrueClamp.normalize_or_sinks gs out hg hcorrect V (fun w hw => hordinary w (hVW hw))
  let C := Finset.univ \ V
  have hC : C.card = 4 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), hVcard]
    decide
  let e : Fin 4 ≃ C := (Fintype.equivFinOfCardEq (by simpa using hC)).symm
  let lineId : Fin 4 → Fin 13 := fun u => (e u).val
  have hinj : Function.Injective lineId := Subtype.val_injective.comp e.injective
  have hmem (u : Fin 4) : lineId u ∈ C := (e u).property
  have hrange : Finset.univ.image lineId = C := by
    ext w
    constructor
    · intro hw
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hw
      exact hmem u
    · intro hw
      refine Finset.mem_image.mpr ⟨e.symm ⟨w, hw⟩, Finset.mem_univ _, ?_⟩
      simp [lineId]
  have hbound := four_or_sink_bound hs ho lineId hinj hhg hhcorrect
    (fun w hw => hhordinary w (by simpa [hrange, C] using hw))
    (by
      intro j hj i hi hn hiQ
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hiQ
      exact hhsinks j hj _ hi hn (Finset.mem_image.mpr ⟨lineId u, Finset.mem_univ _, rfl⟩))
    (fun u => hhor (lineId u) (Finset.mem_sdiff.mp (hmem u)).2)
  omega

lemma five_exotic_outputs (gs : List Gate) (out : Fin 13 → ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ w (x : Fin 13 → Bool), Support.Band x →
      Global.val gs x (out w) = Support.target w x)
    (hsmall : gs.length < 39) : 5 ≤ (Bridge.exoticSet gs out).card := by
  classical
  by_contra! hfew
  let W := Finset.univ \ Bridge.exoticSet gs out
  have hW : 9 ≤ W.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    have hu : (Finset.univ : Finset (Fin 13)).card = 13 := by decide
    rw [hu]
    omega
  have hord : ∀ w ∈ W, ∀ x : Fin 13 → Bool,
      Global.val gs x (out w) = Support.target w x := by
    intro w hw
    have hn := (Finset.mem_sdiff.mp hw).2
    change ∀ x : Fin 13 → Bool, Circuit.eval ⟨gs, out w⟩ (List.ofFn x) = Support.target w x
    simpa [Bridge.exoticSet] using hn
  have hh := nine_ordinary_bound gs out hg hcorrect W hW hord
  omega

end PEqualNP.Outside.L_meta_1024_aux.FourReduction

namespace PEqualNP.Outside.L_meta_1024_aux.FourReduction
open PEqualNP.CircuitLowerBounds

lemma residual_family_nonordinary (k : ℕ) (gs : List Gate) (hsize : gs.length < 3 * k)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (lineId : Fin k → Fin 13) (hinj : Function.Injective lineId) (out : Fin k → ℕ)
    (hcorrect : ∀ u (x : Fin 13 → Bool), Support.Band x →
      Global.val gs x (out u) = Support.target (lineId u) x)
    (hprevious : ∀ (cs : List Gate) (co : Fin 13 → ℕ),
      (∀ g ∈ cs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
      (∀ w (x : Fin 13 → Bool), Support.Band x → Global.val cs x (co w) = Support.target w x) →
      ∀ W : Finset (Fin 13), 14 - k ≤ W.card →
      (∀ w ∈ W, ∀ x : Fin 13 → Bool, Global.val cs x (co w) = Support.target w x) →
      39 ≤ cs.length) :
    ∀ u, ¬ ∀ x : Fin 13 → Bool, Global.val gs x (out u) = Support.target (lineId u) x := by
  classical
  intro u₀ hexact
  let A : Finset (Fin 13) := Finset.univ.image lineId
  let W := Finset.univ \ A
  have hA : A.card = k := by
    rw [Finset.card_image_of_injective _ hinj]
    simp
  have hk : k ≤ 13 := by
    have hh := Finset.card_le_univ A
    simpa [hA] using hh
  have hkpos : 0 < k := Nat.zero_lt_of_lt u₀.isLt
  have hW : W.card = 13 - k := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), hA]
    rfl
  have houtside (u : Fin k) : lineId u ∉ W := by
    intro hu
    exact (Finset.mem_sdiff.mp hu).2 (Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩)
  let cs := AppendLine.appendLines gs W.toList
  have hcs : cs.length < 39 := by
    rw [AppendLine.lines_length, Finset.length_toList, hW]
    omega
  have hallowed := AppendLine.lines_allowed gs W.toList hg
  have hwitness : ∀ w : Fin 13, ∃ i : ℕ,
      (∀ x : Fin 13 → Bool, Support.Band x → Global.val cs x i = Support.target w x) ∧
      ((w ∈ W ∨ w = lineId u₀) → ∀ x : Fin 13 → Bool, Global.val cs x i = Support.target w x) := by
    intro w
    by_cases hw : w ∈ W
    · obtain ⟨i, _, _, hi⟩ := AppendLine.lines_generated gs W.toList w (by simpa using hw)
      exact ⟨i, fun x _ => hi x, fun _ => hi⟩
    · have hwA : w ∈ A := by simpa [W] using hw
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hwA
      have hv := (Bridge.output_index gs (out u) (lineId u) (hcorrect u)).2
      have hold (x : Fin 13 → Bool) : Global.val cs x (out u) = Global.val gs x (out u) :=
        AppendLine.lines_old gs W.toList x (out u) hv
      refine ⟨out u, ?_, ?_⟩
      · intro x hx
        exact (hold x).trans (hcorrect u x hx)
      · rintro (hu | he)
        · exact False.elim (hw hu)
        · have huu : u = u₀ := hinj he
          subst u
          intro x
          exact (hold x).trans (hexact x)
  choose out' hband hord using hwitness
  have hcount : 14 - k ≤ (insert (lineId u₀) W).card := by
    rw [Finset.card_insert_of_notMem (houtside u₀), hW]
    omega
  have hord' : ∀ w ∈ insert (lineId u₀) W, ∀ x : Fin 13 → Bool,
      Global.val cs x (out' w) = Support.target w x := by
    intro w hw
    rcases Finset.mem_insert.mp hw with he | hw
    · exact hord w (Or.inr he)
    · exact hord w (Or.inl hw)
  have hh := hprevious cs out' hallowed hband (insert (lineId u₀) W) hcount hord'
  omega

lemma small_five_nonordinary (gs : List Gate) (hsize : gs.length ≤ 14)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (lineId : Fin 5 → Fin 13) (hinj : Function.Injective lineId) (out : Fin 5 → ℕ)
    (hcorrect : ∀ u (x : Fin 13 → Bool), Support.Band x →
      Global.val gs x (out u) = Support.target (lineId u) x) :
    ∀ u, ¬ ∀ x : Fin 13 → Bool, Global.val gs x (out u) = Support.target (lineId u) x := by
  apply residual_family_nonordinary 5 gs (by omega) hg lineId hinj out hcorrect
  intro cs co hcg hcc W hW hord
  exact nine_ordinary_bound cs co hcg hcc W hW hord

end PEqualNP.Outside.L_meta_1024_aux.FourReduction

namespace PEqualNP.Outside.L_meta_1024_aux.Dead
open PEqualNP.CircuitLowerBounds

lemma deleted_or_pair_all (P : Finset ℕ) (gs : List Gate) (hreads : NoReads 13 P gs)
    (j : ℕ) (hj : j < gs.length)
    (hor : gs[j].op = GateOp.or) (hfan : gs[j].inputs.length ≤ 2) :
    ∃ a b : ℕ, ∀ x : Fin 13 → Bool, Global.val gs x (13 + j) =
      (Global.val (code 13 P gs) x a || Global.val (code 13 P gs) x b) := by
  let d := 13 + gs.length
  let z := 13 + (code 13 P gs).length
  let ix : ℕ → ℕ := fun i => if i < 13 + j then (indices 13 P gs).getD i 0 else z
  refine ⟨ix (gs[j].inputs.getD 0 d), ix (gs[j].inputs.getD 1 d), ?_⟩
  intro x
  have hz : Global.val (code 13 P gs) x z = false := val_invalid _ _ _ (by exact le_rfl)
  have hmap : (fun i => if i < 13 + j then Global.val (code 13 P gs) x ((indices 13 P gs).getD i 0) else false) =
      (fun i => Global.val (code 13 P gs) x (ix i)) := by
    funext i
    by_cases hi : i < 13 + j <;> simp [ix, hi, hz]
  have hd : Global.val (code 13 P gs) x (ix d) = false := by
    have hn : ¬ d < 13 + j := by dsimp [d]; omega
    simp [ix, hn, hz]
  rw [deleted_formula P gs hreads x j hj, hor, hmap]
  exact or_two gs[j].inputs hfan (fun i => Global.val (code 13 P gs) x (ix i)) d hd

end PEqualNP.Outside.L_meta_1024_aux.Dead

namespace PEqualNP.Outside.L_meta_1024_aux.FourReduction
open PEqualNP.CircuitLowerBounds

lemma essential_other_sinks_bound {M : ℕ} (n : ℕ) (P Q : Finset ℕ) (gs : List Gate)
    (hg : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (hP : P ⊆ Finset.Ico n (n + gs.length)) (hQ : Q ⊆ Finset.Ico n (n + gs.length))
    (hdisj : Disjoint P Q) (hreads : Dead.NoReads n Q gs) (o : ℕ) (ho : o ∈ Q) :
    (Cut.essential (M := M) n P gs o).card ≤ gs.length - P.card - (Q.card - 1) + 1 := by
  let R := Q.erase o
  have hRsub : R ⊆ Q := Finset.erase_subset _ _
  have hRcard : R.card = Q.card - 1 := Finset.card_erase_of_mem ho
  have hPR : Disjoint P R := hdisj.mono_right hRsub
  have hsub : P ∪ R ⊆ Finset.Ico n (n + gs.length) :=
    Finset.union_subset hP (hRsub.trans hQ)
  have hr : Dead.NoReads n R gs := by
    intro j hj i hi hn hiR
    exact hreads j hj i hi hn (hRsub hiR)
  have heq := Cut.essential_add_sinks (M := M) n P R gs hr o (by simp [R])
  have hb := Cut.essential_bound (M := M) n (P ∪ R) gs o hg hsub
  rw [heq, Finset.card_union_of_disjoint hPR, hRcard] at hb
  omega

lemma essential_other_sinks_budget {M : ℕ} (n : ℕ) (P Q : Finset ℕ) (gs : List Gate)
    (hg : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (hP : P ⊆ Finset.Ico n (n + gs.length)) (hQ : Q ⊆ Finset.Ico n (n + gs.length))
    (hdisj : Disjoint P Q) (hreads : Dead.NoReads n Q gs) (o : ℕ) (ho : o ∈ Q) :
    (Cut.essential (M := M) n P gs o).card + P.card + Q.card ≤ gs.length + 2 := by
  have hb := essential_other_sinks_bound (M := M) n P Q gs hg hP hQ hdisj hreads o ho
  have hupper : P.card + Q.card ≤ gs.length := by
    have hh := Finset.card_le_card (Finset.union_subset hP hQ)
    simpa [Finset.card_union_of_disjoint hdisj] using hh
  have hqpos : 0 < Q.card := Finset.card_pos.mpr ⟨o, ho⟩
  omega

set_option maxHeartbeats 4000000 in
lemma five_or_sink_reduction (gs : List Gate) (out : Fin 13 → ℕ)
    (lineId : Fin 5 → Fin 13) (hinj : Function.Injective lineId)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hsmall : gs.length ≤ 38)
    (hcorrect : ∀ w (x : Fin 13 → Bool), Support.Band x →
      Global.val gs x (out w) = Support.target w x)
    (P : Finset ℕ) (hP : P ⊆ Finset.Ico 13 (13 + gs.length)) (hPcount : 24 ≤ P.card)
    (hnotP : ∀ u : Fin 5, out (lineId u) ∉ P)
    (hPoutside : ∀ u : Fin 5, ∀ i ∈ P, ∃ q : Fin 13,
      q ∉ Global.line (lineId u) ∧ Global.val gs (Global.eof q) i = true)
    (hsinks : Dead.NoReads 13 (Finset.univ.image (fun u : Fin 5 => out (lineId u))) gs)
    (hor : ∀ u : Fin 5, ∃ j : ℕ, ∃ hj : j < gs.length,
      out (lineId u) = 13 + j ∧ gs[j].op = GateOp.or)
    (hraw : ∀ u : Fin 5, ∀ p ∈ Global.line (lineId u), Bridge.rawIndex gs p ∈
      Cut.essential (M := 13 + gs.length) 13 P gs (out (lineId u))) :
    ∃ (I : List Gate) (left right : Fin 5 → ℕ), I.length ≤ 9 ∧
      (∀ g ∈ I, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      (∀ u (x : Fin 13 → Bool), Support.Band x →
        (Cut.cutVal 13 ∅ I x (left u) || Cut.cutVal 13 ∅ I x (right u)) = Support.target (lineId u) x) ∧
      (∀ u (x : Fin 13 → Bool), Support.target (lineId u) x = false →
        (Cut.cutVal 13 ∅ I x (left u) || Cut.cutVal 13 ∅ I x (right u)) = false) ∧
      ∀ u, ¬ ∀ x : Fin 13 → Bool,
        (Cut.cutVal 13 ∅ I x (left u) || Cut.cutVal 13 ∅ I x (right u)) = Support.target (lineId u) x := by
  classical
  let Q : Finset ℕ := Finset.univ.image (fun u : Fin 5 => out (lineId u))
  have houtinj := Bridge.output_distinct gs out hcorrect
  have hindex (w : Fin 13) := Bridge.output_index gs (out w) w (hcorrect w)
  have hQ : Q.card = 5 := by
    have hi : Function.Injective (fun u : Fin 5 => out (lineId u)) := houtinj.comp hinj
    change (Finset.univ.image (fun u : Fin 5 => out (lineId u))).card = 5
    rw [Finset.card_image_of_injective _ hi]
    decide
  have hPupper : P.card ≤ gs.length := by simpa using Finset.card_le_card hP
  have hPraw : ∀ i ∈ P, 13 ≤ i := fun i hi => (Finset.mem_Ico.mp (hP hi)).1
  have hdisj : Disjoint P Q := by
    rw [Finset.disjoint_left]
    intro i hiP hiQ
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hiQ
    exact hnotP u hiP
  have hQsub : Q ⊆ Finset.Ico 13 (13 + gs.length) := by
    intro i hi
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_Ico.mpr (hindex (lineId u))
  let E (u : Fin 5) := Cut.essential (M := 13 + gs.length) 13 P gs (out (lineId u))
  have hE11 (u : Fin 5) : (E u).card ≤ 11 := by
    have hb := essential_other_sinks_bound (M := 13 + gs.length) 13 P Q gs
      (fun g hm => (hg g hm).2) hP hQsub hdisj hsinks (out (lineId u))
      (Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩)
    rw [hQ] at hb
    change (E u).card ≤ _ at hb
    omega
  have hclamp (u : Fin 5) :
      (∀ x : Fin 13 → Bool, Support.target (lineId u) x = false →
        Cut.cutVal 13 P gs (Dead.trueSources gs x) (out (lineId u)) = false) ∧
      (∀ x : Fin 13 → Bool, Support.Band x →
        Cut.cutVal 13 P gs (Dead.trueSources gs x) (out (lineId u)) = Support.target (lineId u) x) := by
    apply PaidClamp.correct_and_bounded gs (fun g hm => (hg g hm).1) (lineId u) P hPraw
      (hPoutside u) (E u) (by have := hE11 u; omega)
      (Cut.essential_sources 13 P gs (out (lineId u))) (hraw u)
      (fun z => Cut.cutVal 13 P gs z (out (lineId u)))
    · intro x y hxy hx
      exact Cut.cutVal_mono 13 P gs (fun g hm => (hg g hm).1) x y hxy (out (lineId u)) hx
    · exact Cut.essential_supports 13 P gs (out (lineId u))
    · intro x hx
      exact (Cut.factor P gs x (out (lineId u))).trans (hcorrect (lineId u) x hx)
  have hclamped (u : Fin 5) := (hclamp u).2
  let C := Sink.transform 13 P gs
  have hCsize : C.length = gs.length := Sink.transform_length 13 P gs
  have hCallowed := Sink.transform_allowed 13 P gs hg
  have hCval (u : Fin 5) (x : Fin 13 → Bool) : Global.val C x (out (lineId u)) =
      Cut.cutVal 13 P gs (Dead.trueSources gs x) (out (lineId u)) :=
    Sink.transform_cut_output P gs (fun g hm => (hg g hm).1) hPraw x (Dead.trueSources gs x)
      (Dead.trueSources_input gs x) (fun i _ hn hi => Dead.trueSources_paid gs x i hn hi) _ (hnotP u)
  have hCcorrect (u : Fin 5) (x : Fin 13 → Bool) (hx : Support.Band x) :
      Global.val C x (out (lineId u)) = Support.target (lineId u) x := (hCval u x).trans (hclamped u x hx)
  have hCreads : Dead.NoReads 13 (P ∪ Q) C := Dead.noReads_union 13 P Q C
    (Dead.transform_noReads 13 P gs) (Sink.preserves_noReads 13 P Q gs hsinks)
  let I := Dead.code 13 (P ∪ Q) C
  have hPQ : P ∪ Q ⊆ Finset.Ico 13 (13 + C.length) := by
    rw [hCsize]
    exact Finset.union_subset hP hQsub
  have hPQcard : 29 ≤ (P ∪ Q).card := by
    rw [Finset.card_union_of_disjoint hdisj, hQ]
    omega
  have hPQupper : (P ∪ Q).card ≤ C.length := by simpa using Finset.card_le_card hPQ
  have hI : I.length ≤ 9 := by
    rw [Dead.code_length, Cut.unpaid_eq_sub 13 (P ∪ Q) C hPQ]
    omega
  have hIallowed := Dead.code_allowed 13 (P ∪ Q) C hCallowed
  have hpair : ∀ u : Fin 5, ∃ a b : ℕ, ∀ x : Fin 13 → Bool, Global.val C x (out (lineId u)) =
      (Global.val I x a || Global.val I x b) := by
    intro u
    obtain ⟨j, hj, hout, hOR⟩ := hor u
    have hjC : j < C.length := by rwa [hCsize]
    have hfalse : Global.val C (Support.row (lineId u)) (13 + j) = false := by
      rw [← hout]
      exact (hCcorrect u _ (Or.inr (Support.row_spec (lineId u)).1)).trans (Support.row_spec (lineId u)).2
    have hORC : C[j].op = GateOp.or := Sink.or_preserved_of_false P gs j hj hOR _ hfalse
    have hfan := (hCallowed C[j] (List.getElem_mem hjC)).2
    have hh := Dead.deleted_or_pair_all (P ∪ Q) C hCreads j hjC hORC hfan
    simpa only [← hout] using hh
  choose left right hpair using hpair
  let U := Dead.paidCode 13 P gs
  let outU : Fin 5 → ℕ := fun u => Dead.paidIndex 13 P gs (out (lineId u))
  have hUsize : U.length ≤ 14 := by
    rw [Dead.paid_length, Cut.unpaid_eq_sub 13 P gs hP]
    omega
  have hUallowed := Dead.paid_allowed 13 P gs hg
  have hUval (u : Fin 5) (x : Fin 13 → Bool) : Global.val U x (outU u) = Global.val C x (out (lineId u)) :=
    Dead.eval P C (Dead.transform_noReads 13 P gs) x (out (lineId u))
      (by rw [hCsize]; exact (hindex (lineId u)).2) (hnotP u)
  have hUnon := small_five_nonordinary U hUsize hUallowed lineId hinj outU
    (fun u x hx => (hUval u x).trans (hCcorrect u x hx))
  have hcut (x : Fin 13 → Bool) (i : ℕ) : Cut.cutVal 13 ∅ I x i = Global.val I x i := Cut.cut_empty I x i
  refine ⟨I, left, right, hI, hIallowed, ?_, ?_, ?_⟩
  · intro u x hx
    rw [hcut, hcut, ← hpair u x]
    exact hCcorrect u x hx
  · intro u x hx
    rw [hcut, hcut, ← hpair u x, hCval]
    exact (hclamp u).1 x hx
  · intro u hexact
    apply hUnon u
    intro x
    rw [hUval, hpair u x, ← hcut, ← hcut]
    exact hexact x

end PEqualNP.Outside.L_meta_1024_aux.FourReduction

namespace PEqualNP.Outside.L_meta_1024_aux
open PEqualNP.CircuitLowerBounds
lemma val_input {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : Fin n) :
    Global.val gs x i.val = x i := Bridge.val_input gs x i
lemma val_beyond {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ)
    (hi : n + gs.length ≤ i) : Global.val gs x i = false := Dead.val_invalid gs x i hi
end PEqualNP.Outside.L_meta_1024_aux

namespace PEqualNP.Outside.L_meta_1024_aux.PairSurcharge

open PEqualNP.CircuitLowerBounds

noncomputable def core {n : ℕ} (gs : List Gate) (i : ℕ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun p => Global.val gs (Global.eof p) i = true)

lemma mem_core {n : ℕ} (gs : List Gate) (i : ℕ) (p : Fin n) :
    p ∈ core gs i ↔ Global.val gs (Global.eof p) i = true := by
  classical
  simp [core]

lemma val_raw {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (p : Fin n) :
    Global.val gs x p.val = x p := by
  exact PEqualNP.Outside.L_meta_1024_aux.val_input gs x p

lemma val_invalid {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ)
    (hi : n + gs.length ≤ i) : Global.val gs x i = false := by
  exact PEqualNP.Outside.L_meta_1024_aux.val_beyond gs x i hi

lemma cnt_mem {n : ℕ} (gs : List Gate) (S : Finset (Fin n)) (i : ℕ)
    (hcnt : Global.Cnt S gs i) : i ∈ Global.D S gs := by
  classical
  obtain ⟨hz, u, v, huv, hu, hv⟩ := hcnt
  have hn : n ≤ i := by
    by_contra! hi
    have hu' : (⟨i, hi⟩ : Fin n) = u := by
      have he := val_raw gs (Global.eof u) ⟨i, hi⟩
      rw [he] at hu
      simpa [Global.eof] using hu
    have hv' : (⟨i, hi⟩ : Fin n) = v := by
      have he := val_raw gs (Global.eof v) ⟨i, hi⟩
      rw [he] at hv
      simpa [Global.eof] using hv
    exact huv (hu'.symm.trans hv')
  have hi : i < n + gs.length := by
    by_contra! hbad
    rw [val_invalid gs (Global.eof u) i hbad] at hu
    contradiction
  exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hn, hi⟩, hz, u, v, huv, hu, hv⟩

lemma core_large_mem {n : ℕ} (gs : List Gate) (S : Finset (Fin n)) (i : ℕ)
    (hz : Global.val gs (Global.Zof S) i = false) (hc : 1 < (core (n := n) gs i).card) :
    i ∈ Global.D S gs := by
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hc
  exact cnt_mem gs S i ⟨hz, u, v, huv, (mem_core gs i u).mp hu, (mem_core gs i v).mp hv⟩

lemma wire_eq_gate {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (j : ℕ) (hj : j < gs.length) :
    Global.val gs x (n + j) = gs[j].op.eval (gs[j].inputs.map
      (fun i => if i < n + j then Global.val gs x i else false)) := by
  induction gs using List.reverseRecOn generalizing j with
  | nil => simp at hj
  | append_singleton gs g ih =>
    by_cases hlast : j = gs.length
    · subst j
      rw [Global.val_snoc, ite_eq_left rfl]
      have hget : (gs ++ [g])[gs.length]'(by simp) = g := by simp
      rw [hget]
      apply congrArg g.op.eval
      apply List.map_congr_left
      intro i _
      by_cases hi : i < n + gs.length
      · rw [ite_eq_left hi, Global.val_snoc, ite_eq_right (by omega)]
      · rw [ite_eq_right hi, val_invalid _ _ _ (by omega)]
    · have hjold : j < gs.length := by simp only [List.length_append, List.length_singleton] at hj; omega
      rw [Global.val_snoc, ite_eq_right (by omega), List.getElem_append_left hjold, ih j hjold]
      apply congrArg gs[j].op.eval
      apply List.map_congr_left
      intro i _
      by_cases hi : i < n + j
      · simp only [ite_eq_left hi]
        rw [Global.val_snoc, ite_eq_right (by omega)]
      · simp only [ite_eq_right hi]

lemma overlapping_pair_charge {n : ℕ} (S : Finset (Fin n)) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hS : S.card = 4) (o i j : ℕ) (r q₁ q₂ : Fin n)
    (hz : Global.val gs (Global.Zof S) o = false) (ho : core gs o = S)
    (hi : i ∈ Global.D S gs) (hj : j ∈ Global.D S gs) (hij : i ≠ j)
    (hci : core gs i = {r, q₁}) (hcj : core gs j = {r, q₂}) :
    4 ≤ (Global.D S gs).card := by
  classical
  by_contra! hsmall
  have hoD : o ∈ Global.D S gs := core_large_mem gs S o hz (by rw [ho, hS]; decide)
  have hio : i ≠ o := by
    intro he
    have hh : (core (n := n) gs i).card ≤ 2 := by rw [hci]; exact Finset.card_le_two
    rw [he, ho, hS] at hh
    omega
  have hjo : j ≠ o := by
    intro he
    have hh : (core (n := n) gs j).card ≤ 2 := by rw [hcj]; exact Finset.card_le_two
    rw [he, ho, hS] at hh
    omega
  have hsub : ({i, j, o} : Finset ℕ) ⊆ Global.D S gs := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl <;> assumption
  have hthree : ({i, j, o} : Finset ℕ).card = 3 := by simp [hij, hio, hjo]
  have hD : Global.D S gs = {i, j, o} :=
    (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
  have hoi := (Finset.mem_filter.mp hoD).1
  have hon : n ≤ o := (Finset.mem_Ico.mp hoi).1
  have hob : o < n + gs.length := (Finset.mem_Ico.mp hoi).2
  let k := o - n
  have hk : k < gs.length := by dsimp [k]; omega
  have hok : n + k = o := by dsimp [k]; omega
  let f : (Fin n → Bool) → ℕ → Bool :=
    fun x a => if a < o then Global.val gs x a else false
  have hformula (x : Fin n → Bool) :
      gs[k].op.eval (gs[k].inputs.map (f x)) = Global.val gs x o := by
    simpa only [hok, f] using (wire_eq_gate gs x k hk).symm
  obtain ⟨hop, hlen⟩ := hg gs[k] (List.getElem_mem hk)
  rcases Global.gate_cases gs[k] hop hlen f (Global.Zof S) with hall | ⟨a, b, hab⟩
  · obtain ⟨p, hp⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
    have ht : Global.val gs (Global.eof p) o = true := (mem_core gs o p).mp (ho.symm ▸ hp)
    have hf := hall (Global.eof p)
    rw [hformula] at hf
    rw [hf] at ht
    contradiction
  · obtain ⟨ha, hb, hcover⟩ := hab (by rw [hformula]; exact hz)
    let C : ℕ → Finset (Fin n) := fun a => Finset.univ.filter (fun p => f (Global.eof p) a = true)
    have hclass (a : ℕ) (ha : f (Global.Zof S) a = false) :
        (C a = {r, q₁} ∨ C a = {r, q₂}) ∨ (C a).card ≤ 1 := by
      by_cases hcard : (C a).card ≤ 1
      · exact Or.inr hcard
      have hlt : a < o := by
        by_contra! hn
        have he : C a = ∅ := by ext p; simp [C, f, Nat.not_lt.mpr hn]
        simp [he] at hcard
      have hC : C a = core gs a := by ext p; simp [C, f, hlt, core]
      have haz : Global.val gs (Global.Zof S) a = false := by simpa only [f, ite_eq_left hlt] using ha
      have haD := core_large_mem gs S a haz (by rw [← hC]; omega)
      rw [hD] at haD
      simp only [Finset.mem_insert, Finset.mem_singleton] at haD
      rcases haD with rfl | rfl | he
      · exact Or.inl (Or.inl (hC.trans hci))
      · exact Or.inl (Or.inr (hC.trans hcj))
      · omega
    have hSC : S ⊆ C a ∪ C b := by
      intro p hp
      have ht : Global.val gs (Global.eof p) o = true := (mem_core gs o p).mp (ho.symm ▸ hp)
      have hh := hcover (Global.eof p) (by rw [hformula]; exact ht)
      simpa only [C, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] using hh
    have hunion : (C a ∪ C b).card ≤ 3 := by
      rcases hclass a ha with (hA | hA) | hA <;>
        rcases hclass b hb with (hB | hB) | hB
      · rw [hA, hB]
        simpa using (show ({r, q₁} : Finset (Fin n)).card ≤ 3 from Finset.card_le_two.trans (by decide))
      · rw [hA, hB]
        have hs : ({r, q₁} ∪ {r, q₂} : Finset (Fin n)) ⊆ {r, q₁, q₂} := by
          intro p hp
          simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hp ⊢
          tauto
        exact (Finset.card_le_card hs).trans Finset.card_le_three
      · have hh := Finset.card_union_le (C a) (C b)
        have hhA : (C a).card ≤ 2 := by rw [hA]; exact Finset.card_le_two
        omega
      · rw [hA, hB]
        have hs : ({r, q₂} ∪ {r, q₁} : Finset (Fin n)) ⊆ {r, q₁, q₂} := by
          intro p hp
          simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hp ⊢
          tauto
        exact (Finset.card_le_card hs).trans Finset.card_le_three
      · rw [hA, hB]
        simpa using (show ({r, q₂} : Finset (Fin n)).card ≤ 3 from Finset.card_le_two.trans (by decide))
      · have hh := Finset.card_union_le (C a) (C b)
        have hhA : (C a).card ≤ 2 := by rw [hA]; exact Finset.card_le_two
        omega
      · have hh := Finset.card_union_le (C a) (C b)
        have hhB : (C b).card ≤ 2 := by rw [hB]; exact Finset.card_le_two
        omega
      · have hh := Finset.card_union_le (C a) (C b)
        have hhB : (C b).card ≤ 2 := by rw [hB]; exact Finset.card_le_two
        omega
      · have hh := Finset.card_union_le (C a) (C b)
        omega
    have hh := Finset.card_le_card hSC
    omega

lemma ordinary_overlapping_pair_charge {n : ℕ} (S : Finset (Fin n)) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hS : S.card = 4) (o i j : ℕ) (r q₁ q₂ : Fin n)
    (hcorrect : ∀ x : Fin n → Bool,
      Global.val gs x o = decide (∃ p ∈ S, x p = true))
    (hi : i ∈ Global.D S gs) (hj : j ∈ Global.D S gs) (hij : i ≠ j)
    (hci : ∀ p : Fin n, Global.val gs (Global.eof p) i = true ↔ p = r ∨ p = q₁)
    (hcj : ∀ p : Fin n, Global.val gs (Global.eof p) j = true ↔ p = r ∨ p = q₂) :
    4 ≤ (Global.D S gs).card := by
  classical
  apply overlapping_pair_charge S gs hg hS o i j r q₁ q₂
  · rw [hcorrect]
    simp [Global.Zof]
  · ext p
    rw [mem_core, hcorrect]
    simp [Global.eof]
  · exact hi
  · exact hj
  · exact hij
  · ext p
    rw [mem_core, hci]
    simp
  · ext p
    rw [mem_core, hcj]
    simp

end PEqualNP.Outside.L_meta_1024_aux.PairSurcharge


namespace PEqualNP.Outside.L_meta_1024_aux.MissingRawWitness

open PEqualNP.CircuitLowerBounds

noncomputable def rawSet (gs : List Gate) (E : Finset (Fin (13 + gs.length))) : Finset (Fin 13) := by
  classical
  exact Finset.univ.filter (fun p => Bridge.rawIndex gs p ∈ E)

lemma mem_rawSet (gs : List Gate) (E : Finset (Fin (13 + gs.length))) (p : Fin 13) :
    p ∈ rawSet gs E ↔ Bridge.rawIndex gs p ∈ E := by
  classical
  simp [rawSet]

lemma raw_injective (gs : List Gate) : Function.Injective (Bridge.rawIndex gs) := by
  intro p q hpq
  apply Fin.ext
  exact congrArg (fun t : Fin (13 + gs.length) => t.val) hpq

lemma positive_avoiding (w p : Fin 13) (hp : p ∈ Support.line w)
    (R : Finset (Fin 13)) (hR : R.card ≤ 3) (hpR : p ∉ R) :
    ∃ x : Fin 13 → Bool, Support.Band x ∧ Support.target w x = true ∧
      x p = true ∧ (∀ q ∈ Support.line w, q ≠ p → x q = false) ∧
      ∀ q ∈ R, x q = false := by
  classical
  let O := Finset.univ \ Support.line w
  have hO : O.card = 9 := by
    dsimp [O]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Clamp.line_card]
    decide
  have havail : 6 ≤ (O \ R).card := by
    have hh := Finset.le_card_sdiff R O
    rw [hO] at hh
    omega
  obtain ⟨Y, hYsub, hYcard⟩ := Finset.exists_subset_card_eq havail
  have hYO : Y ⊆ O := fun q hq => (Finset.mem_sdiff.mp (hYsub hq)).1
  have hYR : ∀ q ∈ Y, q ∉ R := fun q hq => (Finset.mem_sdiff.mp (hYsub hq)).2
  have hpY : p ∉ Y := by
    intro hh
    exact (Finset.mem_sdiff.mp (hYO hh)).2 hp
  let U := insert p Y
  have hU : U.card = 7 := by simp [U, hpY, hYcard]
  let x := Clamp.fromTrue U
  have hxband : Support.Band x := by
    right
    have hzero : Support.zeroSet x = Finset.univ \ U := by
      ext q
      simp [Support.zeroSet, x, Clamp.fromTrue]
    rw [hzero, Finset.card_sdiff_of_subset (Finset.subset_univ _), hU]
    decide
  have hxp : x p = true := by simp [x, Clamp.fromTrue, U]
  refine ⟨x, hxband, ?_, hxp, ?_, ?_⟩
  · exact decide_eq_true_iff.mpr ⟨p, hp, hxp⟩
  · intro q hq hqp
    have hqY : q ∉ Y := by
      intro hh
      exact (Finset.mem_sdiff.mp (hYO hh)).2 hq
    simp [x, Clamp.fromTrue, U, hqp, hqY]
  · intro q hq
    have hqp : q ≠ p := fun he => hpR (he ▸ hq)
    have hqY : q ∉ Y := fun hy => hYR q hy hq
    simp [x, Clamp.fromTrue, U, hqp, hqY]

lemma true_foreign (gs : List Gate) (w p : Fin 13) (P : Finset ℕ)
    (E : Finset (Fin (13 + gs.length)))
    (hallowed : ∀ i ∈ E, i.val < 13 ∨ i.val ∈ P)
    (hpaid : ∀ i ∈ P, ∃ q : Fin 13,
      q ∉ Support.line w ∧ Global.val gs (Global.eof q) i = true)
    (hpnot : Bridge.rawIndex gs p ∉ E)
    (x : Fin 13 → Bool)
    (hline : ∀ q ∈ Support.line w, q ≠ p → x q = false) :
    ∀ i ∈ E, Global.val gs x i.val = true →
      ∃ q : Fin 13, q ∉ Support.line w ∧ Global.val gs (Clamp.singleton q) i.val = true := by
  intro i hi hit
  rcases hallowed i hi with hiraw | hipaid
  · let q : Fin 13 := ⟨i.val, hiraw⟩
    have hidx : Bridge.rawIndex gs q = i := by apply Fin.ext; rfl
    have hqtrue : x q = true := by
      rw [Bridge.val_input gs x q] at hit
      exact hit
    have hqout : q ∉ Support.line w := by
      intro hql
      by_cases hqp : q = p
      · subst p
        exact hpnot (hidx.symm ▸ hi)
      · rw [hline q hql hqp] at hqtrue
        contradiction
    refine ⟨q, hqout, ?_⟩
    have he := Bridge.val_input gs (Clamp.singleton q) q
    simpa [Clamp.singleton] using he
  · exact hpaid i.val hipaid

lemma raw_card_le_two (gs : List Gate) (w p : Fin 13) (hp : p ∈ Support.line w)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (P : Finset ℕ) (E : Finset (Fin (13 + gs.length)))
    (hE : E.card ≤ 11)
    (hallowed : ∀ i ∈ E, i.val < 13 ∨ i.val ∈ P)
    (hpaid : ∀ i ∈ P, ∃ q : Fin 13,
      q ∉ Support.line w ∧ Global.val gs (Global.eof q) i = true)
    (F : (Fin (13 + gs.length) → Bool) → Bool)
    (hmono : ∀ a b, (∀ i, a i = true → b i = true) → F a = true → F b = true)
    (hsupport : ∀ a b, (∀ i ∈ E, a i = b i) → F a = F b)
    (hcorrect : ∀ x : Fin 13 → Bool, Support.Band x →
      F (fun i => Global.val gs x i.val) = Support.target w x)
    (hpnot : Bridge.rawIndex gs p ∉ E) : (rawSet gs E).card ≤ 2 := by
  classical
  by_contra! hlarge
  have hthree : 3 ≤ (rawSet gs E).card := by omega
  obtain ⟨R, hRsub, hRcard⟩ := Finset.exists_subset_card_eq hthree
  have hpR : p ∉ R := fun h => hpnot ((mem_rawSet gs E p).mp (hRsub h))
  obtain ⟨x, hxband, hxpos, _, hxline, hxR⟩ := positive_avoiding w p hp R (by omega) hpR
  let K := R.image (Bridge.rawIndex gs)
  have hKcard : K.card = 3 := by
    rw [Finset.card_image_of_injective _ (raw_injective gs)]
    exact hRcard
  have hKE : K ⊆ E := by
    intro i hi
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hi
    exact (mem_rawSet gs E q).mp (hRsub hq)
  have hKfalse : ∀ i ∈ K, Global.val gs x i.val = false := by
    intro i hi
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hi
    change Global.val gs x q.val = false
    rw [Bridge.val_input gs x q]
    exact hxR q hq
  have hcount : (E.filter (fun i => Global.val gs x i.val = true)).card ≤ 8 := by
    have hs : E.filter (fun i => Global.val gs x i.val = true) ⊆ E \ K := by
      intro i hi
      obtain ⟨hiE, hit⟩ := Finset.mem_filter.mp hi
      refine Finset.mem_sdiff.mpr ⟨hiE, ?_⟩
      intro hiK
      rw [hKfalse i hiK] at hit
      contradiction
    have hh := Finset.card_le_card hs
    rw [Finset.card_sdiff_of_subset hKE, hKcard] at hh
    omega
  apply Clamp9.positive_frontier_impossible w E F (fun i x => Global.val gs x i.val)
    hmono hsupport _ hcorrect x hxband hxpos hcount
    (true_foreign gs w p P E hallowed hpaid hpnot x hxline)
  intro i _ a b hab ha
  exact Bridge.val_mono gs hg a b hab i.val ha

lemma positive_kills_raw (gs : List Gate) (w p : Fin 13) (hp : p ∈ Support.line w)
    (E : Finset (Fin (13 + gs.length))) (hraw : (rawSet gs E).card ≤ 2)
    (hpnot : Bridge.rawIndex gs p ∉ E) :
    ∃ x : Fin 13 → Bool, Support.Band x ∧ Support.target w x = true ∧
      ∀ i ∈ E, i.val < 13 → Global.val gs x i.val = false := by
  have hpR : p ∉ rawSet gs E := fun h => hpnot ((mem_rawSet gs E p).mp h)
  obtain ⟨x, hxband, hxpos, _, _, hxR⟩ := positive_avoiding w p hp (rawSet gs E) (by omega) hpR
  refine ⟨x, hxband, hxpos, ?_⟩
  intro i hi hiraw
  let q : Fin 13 := ⟨i.val, hiraw⟩
  have hidx : Bridge.rawIndex gs q = i := by apply Fin.ext; rfl
  have hqR : q ∈ rawSet gs E := (mem_rawSet gs E q).mpr (hidx.symm ▸ hi)
  rw [Bridge.val_input gs x q]
  exact hxR q hqR

def negative (w q : Fin 13) : Fin 13 → Bool :=
  Clamp.fromTrue ((Finset.univ \ Support.line w).erase q)

lemma negative_band (w q : Fin 13) (hq : q ∉ Support.line w) : Support.Band (negative w q) := by
  apply Clamp.fromTrue_band
  have hqO : q ∈ Finset.univ \ Support.line w := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hq⟩
  rw [Finset.card_erase_of_mem hqO, Finset.card_sdiff_of_subset (Finset.subset_univ _), Clamp.line_card]
  decide

lemma negative_false (w q : Fin 13) : Support.target w (negative w q) = false := by
  apply Clamp.fromTrue_misses
  exact Finset.erase_subset _ _

lemma paid_separator (gs : List Gate) (w q : Fin 13) (hq : q ∉ Support.line w)
    (P : Finset ℕ) (E : Finset (Fin (13 + gs.length)))
    (hallowed : ∀ i ∈ E, i.val < 13 ∨ i.val ∈ P)
    (F : (Fin (13 + gs.length) → Bool) → Bool)
    (hmono : ∀ a b, (∀ i, a i = true → b i = true) → F a = true → F b = true)
    (hsupport : ∀ a b, (∀ i ∈ E, a i = b i) → F a = F b)
    (hcorrect : ∀ x : Fin 13 → Bool, Support.Band x →
      F (fun i => Global.val gs x i.val) = Support.target w x)
    (x : Fin 13 → Bool) (hxband : Support.Band x) (hxpos : Support.target w x = true)
    (hxraw : ∀ i ∈ E, i.val < 13 → Global.val gs x i.val = false) :
    ∃ i ∈ E, i.val ∈ P ∧ Global.val gs x i.val = true ∧
      Global.val gs (negative w q) i.val = false := by
  classical
  have hpos : F (fun i => Global.val gs x i.val) = true := (hcorrect x hxband).trans hxpos
  have hneg : F (fun i => Global.val gs (negative w q) i.val) = false :=
    (hcorrect _ (negative_band w q hq)).trans (negative_false w q)
  have hex : ∃ i ∈ E, Global.val gs x i.val = true ∧
      Global.val gs (negative w q) i.val = false := by
    by_contra! hnone
    have hh := Clamp.supported_mono F E hmono hsupport
      (fun i => Global.val gs x i.val) (fun i => Global.val gs (negative w q) i.val)
      (by
        intro i hi hit
        have hn := hnone i hi hit
        cases he : Global.val gs (negative w q) i.val <;> simp_all) hpos
    rw [hneg] at hh
    contradiction
  obtain ⟨i, hi, hit, hif⟩ := hex
  refine ⟨i, hi, ?_, hit, hif⟩
  rcases hallowed i hi with hiraw | hipaid
  · rw [hxraw i hi hiraw] at hit
    contradiction
  · exact hipaid

lemma pair_core_of_negative (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w a q : Fin 13) (haw : a ≠ w) (hq : q ∉ Support.line w)
    (i : ℕ) (hi : i ∈ Global.D (Global.line a) gs)
    (hneg : Global.val gs (negative w q) i = false) :
    ∃ r : Fin 13, r ∈ Support.line w ∧ r ∈ Global.line a ∧
      ∀ p : Fin 13, Global.val gs (Global.eof p) i = true ↔ p = r ∨ p = q := by
  classical
  obtain ⟨label, hinv, _⟩ := Global.main_inv (Global.line a) gs hg
  obtain ⟨hz, u, v, huv, hu, hv⟩ := (Finset.mem_filter.mp hi).2
  obtain ⟨r, hrw, hra⟩ := (Bridge.pair_geometry w a haw.symm).2
  have hsub (p : Fin 13) (hp : Global.val gs (Global.eof p) i = true) : p = r ∨ p = q := by
    by_cases hpq : p = q
    · exact Or.inr hpq
    have hpa : p ∈ Global.line a := (hinv i p p hz hp hp).1
    have hpw : p ∈ Support.line w := by
      by_contra hpw
      have hrow : ∀ t : Fin 13, Global.eof p t = true → negative w q t = true := by
        intro t ht
        have htp : t = p := by simpa [Global.eof] using ht
        subst t
        simp [negative, Clamp.fromTrue, hpq, hpw]
      have hh := Bridge.val_mono gs (fun g hm => (hg g hm).1)
        (Global.eof p) (negative w q) hrow i hp
      rw [hneg] at hh
      contradiction
    exact Or.inl ((Finset.card_le_one.mp (Global.line_intersection a w haw))
      p (Finset.mem_inter.mpr ⟨hpa, hpw⟩) r (Finset.mem_inter.mpr ⟨hra, hrw⟩))
  have hboth : Global.val gs (Global.eof r) i = true ∧ Global.val gs (Global.eof q) i = true := by
    rcases hsub u hu with hur | huq <;> rcases hsub v hv with hvr | hvq
    · exact (huv (hur.trans hvr.symm)).elim
    · exact ⟨hur ▸ hu, hvq ▸ hv⟩
    · exact ⟨hvr ▸ hv, huq ▸ hu⟩
    · exact (huv (huq.trans hvq.symm)).elim
  refine ⟨r, hrw, hra, ?_⟩
  intro p
  constructor
  · exact hsub p
  · rintro (rfl | rfl)
    · exact hboth.1
    · exact hboth.2

lemma paid_pair_witnesses (gs : List Gate) (w p : Fin 13) (hp : p ∈ Support.line w)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (P : Finset ℕ) (E : Finset (Fin (13 + gs.length)))
    (hE : E.card ≤ 11)
    (hallowed : ∀ i ∈ E, i.val < 13 ∨ i.val ∈ P)
    (hpaid : ∀ i ∈ P, ∃ q : Fin 13,
      q ∉ Support.line w ∧ Global.val gs (Global.eof q) i = true)
    (howner : ∀ i ∈ P, ∃ a : Fin 13, a ≠ w ∧ i ∈ Global.D (Global.line a) gs)
    (F : (Fin (13 + gs.length) → Bool) → Bool)
    (hmono : ∀ a b, (∀ i, a i = true → b i = true) → F a = true → F b = true)
    (hsupport : ∀ a b, (∀ i ∈ E, a i = b i) → F a = F b)
    (hcorrect : ∀ x : Fin 13 → Bool, Support.Band x →
      F (fun i => Global.val gs x i.val) = Support.target w x)
    (hpnot : Bridge.rawIndex gs p ∉ E) :
    (rawSet gs E).card ≤ 2 ∧
      ∃ pick : {q : Fin 13 // q ∉ Support.line w} → Fin (13 + gs.length),
        Function.Injective pick ∧
        ∀ q, pick q ∈ E ∧ (pick q).val ∈ P ∧
          ∃ a r : Fin 13, a ≠ w ∧ r ∈ Support.line w ∧ r ∈ Global.line a ∧
            (pick q).val ∈ Global.D (Global.line a) gs ∧
            ∀ t : Fin 13, Global.val gs (Global.eof t) (pick q).val = true ↔
              t = r ∨ t = q.val := by
  classical
  have hraw := raw_card_le_two gs w p hp (fun g hm => (hg g hm).1) P E hE
    hallowed hpaid F hmono hsupport hcorrect hpnot
  obtain ⟨x, hxband, hxpos, hxraw⟩ := positive_kills_raw gs w p hp E hraw hpnot
  let Q := {q : Fin 13 // q ∉ Support.line w}
  have hwit (q : Q) : ∃ i : Fin (13 + gs.length), i ∈ E ∧ i.val ∈ P ∧
      ∃ a r : Fin 13, a ≠ w ∧ r ∈ Support.line w ∧ r ∈ Global.line a ∧
        i.val ∈ Global.D (Global.line a) gs ∧
        ∀ t : Fin 13, Global.val gs (Global.eof t) i.val = true ↔ t = r ∨ t = q.val := by
    obtain ⟨i, hi, hip, _, hif⟩ := paid_separator gs w q.val q.property P E hallowed F
      hmono hsupport hcorrect x hxband hxpos hxraw
    obtain ⟨a, haw, hia⟩ := howner i.val hip
    obtain ⟨r, hrw, hra, hcore⟩ := pair_core_of_negative gs hg w a q.val haw q.property i.val hia hif
    exact ⟨i, hi, hip, a, r, haw, hrw, hra, hia, hcore⟩
  let pick : Q → Fin (13 + gs.length) := fun q => Classical.choose (hwit q)
  have hspec (q : Q) : pick q ∈ E ∧ (pick q).val ∈ P ∧
      ∃ a r : Fin 13, a ≠ w ∧ r ∈ Support.line w ∧ r ∈ Global.line a ∧
        (pick q).val ∈ Global.D (Global.line a) gs ∧
        ∀ t : Fin 13, Global.val gs (Global.eof t) (pick q).val = true ↔ t = r ∨ t = q.val :=
    Classical.choose_spec (hwit q)
  refine ⟨hraw, pick, ?_, hspec⟩
  intro q₁ q₂ he
  obtain ⟨_, _, a₁, r₁, _, _, _, _, hc₁⟩ := hspec q₁
  obtain ⟨_, _, a₂, r₂, _, hr₂, _, _, hc₂⟩ := hspec q₂
  have ht : Global.val gs (Global.eof q₁.val) (pick q₁).val = true :=
    (hc₁ q₁.val).mpr (Or.inr rfl)
  rw [he] at ht
  rcases (hc₂ q₁.val).mp ht with hbad | hqeq
  · exact (q₁.property (hbad.symm ▸ hr₂)).elim
  · exact Subtype.ext hqeq

end PEqualNP.Outside.L_meta_1024_aux.MissingRawWitness


namespace PEqualNP.Outside.L_meta_1024_aux.Clamp11

open PEqualNP.CircuitLowerBounds

lemma fromTrue_seven (X : Finset (Fin 13)) (hX : X.card = 7) :
    Support.Band (Clamp.fromTrue X) := by
  right
  have he : Support.zeroSet (Clamp.fromTrue X) = Finset.univ \ X := by
    ext p
    simp [Support.zeroSet, Clamp.fromTrue]
  rw [he, Finset.card_sdiff_of_subset (Finset.subset_univ _), hX]
  decide

set_option maxHeartbeats 2000000 in
lemma missing_raw_impossible (gs : List Gate) (out : Fin 13 → ℕ) (w : Fin 13)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (W : Finset (Fin 13)) (hW : W.card = 8) (hw : w ∉ W)
    (hordinary : ∀ a ∈ W, ∀ x : Fin 13 → Bool,
      Global.val gs x (out a) = Support.target a x)
    (P : Finset ℕ) (hP : P = W.biUnion (fun a => Global.D (Global.line a) gs))
    (E : Finset (Fin (13 + gs.length))) (hbudget : E.card + P.card ≤ 35)
    (hallowed : ∀ i ∈ E, i.val < 13 ∨ i.val ∈ P)
    (F : (Fin (13 + gs.length) → Bool) → Bool)
    (hmono : ∀ a b, (∀ i, a i = true → b i = true) → F a = true → F b = true)
    (hsupport : ∀ a b, (∀ i ∈ E, a i = b i) → F a = F b)
    (hcorrect : ∀ x : Fin 13 → Bool, Support.Band x →
      F (fun i => Global.val gs x i.val) = Support.target w x)
    (p : Fin 13) (hp : p ∈ Support.line w) (hpnot : Bridge.rawIndex gs p ∉ E) : False := by
  classical
  have hown (i : ℕ) (hi : i ∈ P) : ∃ a ∈ W, i ∈ Global.D (Global.line a) gs := by
    rw [hP] at hi
    exact Finset.mem_biUnion.mp hi
  have howner (i : ℕ) (hi : i ∈ P) : ∃ a : Fin 13, a ≠ w ∧ i ∈ Global.D (Global.line a) gs := by
    obtain ⟨a, ha, hia⟩ := hown i hi
    exact ⟨a, fun he => hw (he ▸ ha), hia⟩
  have hpaid (i : ℕ) (hi : i ∈ P) : ∃ q : Fin 13,
      q ∉ Support.line w ∧ Global.val gs (Global.eof q) i = true := by
    obtain ⟨a, haw, hia⟩ := howner i hi
    exact Charges.charge_outside gs hg w a haw i hia
  have hcounts (a : Fin 13) (ha : a ∈ W) : 3 ≤ (Global.D (Global.line a) gs).card :=
    Charges.ordinary_charge_count gs (out a) a hg (hordinary a ha)
  have hdisj : ∀ a ∈ W, ∀ b ∈ W, a ≠ b →
      Disjoint (Global.D (Global.line a) gs) (Global.D (Global.line b) gs) := by
    intro a _ b _ hab
    exact Charges.disjoint_charges gs hg a b hab
  have hPsum : P.card = ∑ a ∈ W, (Global.D (Global.line a) gs).card := by
    rw [hP, Finset.card_biUnion hdisj]
  have hP24 : 24 ≤ P.card := by
    have hh := Finset.sum_le_sum hcounts
    rw [← hPsum] at hh
    simpa [hW] using hh
  have hE11 : E.card ≤ 11 := by omega
  obtain ⟨hraw, pick, hpick, hspec⟩ := MissingRawWitness.paid_pair_witnesses gs w p hp hg P E
    hE11 hallowed hpaid howner F hmono hsupport hcorrect hpnot
  let Q := {q : Fin 13 // q ∉ Support.line w}
  have hQ : Fintype.card Q = 9 := by
    dsimp [Q]
    rw [Fintype.card_subtype_compl]
    simp [Clamp.line_card]
  let owner : Q → {a : Fin 13 // a ∈ W} := fun q =>
    ⟨Classical.choose (hown (pick q).val (hspec q).2.1),
      (Classical.choose_spec (hown (pick q).val (hspec q).2.1)).1⟩
  have hownerD (q : Q) : (pick q).val ∈ Global.D (Global.line (owner q).val) gs :=
    (Classical.choose_spec (hown (pick q).val (hspec q).2.1)).2
  have hninj : ¬ Function.Injective owner := by
    intro hinj
    have hh := Fintype.card_le_of_injective owner hinj
    rw [hQ, Fintype.card_coe, hW] at hh
    omega
  change ¬ ∀ q₁ q₂, owner q₁ = owner q₂ → q₁ = q₂ at hninj
  push Not at hninj
  obtain ⟨q₁, q₂, hownerEq, hqne⟩ := hninj
  let a := (owner q₁).val
  have haW : a ∈ W := (owner q₁).property
  have haw : a ≠ w := fun he => hw (he ▸ haW)
  have hiD : (pick q₁).val ∈ Global.D (Global.line a) gs := hownerD q₁
  have hjD : (pick q₂).val ∈ Global.D (Global.line a) gs := by
    have hh := hownerD q₂
    rw [← hownerEq] at hh
    exact hh
  have hij : (pick q₁).val ≠ (pick q₂).val := by
    intro he
    exact hqne (hpick (Fin.ext he))
  obtain ⟨hiE, _, a₁, r₁, _, hr₁, _, _, hc₁⟩ := hspec q₁
  obtain ⟨hjE, _, a₂, r₂, _, hr₂, _, _, hc₂⟩ := hspec q₂
  obtain ⟨label, hinv, _⟩ := Global.main_inv (Global.line a) gs hg
  have hz₁ := (Finset.mem_filter.mp hiD).2.1
  have hz₂ := (Finset.mem_filter.mp hjD).2.1
  have ht₁ := (hc₁ r₁).mpr (Or.inl rfl)
  have ht₂ := (hc₂ r₂).mpr (Or.inl rfl)
  have hr₁a : r₁ ∈ Global.line a := (hinv _ r₁ r₁ hz₁ ht₁ ht₁).1
  have hr₂a : r₂ ∈ Global.line a := (hinv _ r₂ r₂ hz₂ ht₂ ht₂).1
  have hrEq : r₁ = r₂ := (Finset.card_le_one.mp (Global.line_intersection a w haw))
    r₁ (Finset.mem_inter.mpr ⟨hr₁a, hr₁⟩) r₂ (Finset.mem_inter.mpr ⟨hr₂a, hr₂⟩)
  have hDa : 4 ≤ (Global.D (Global.line a) gs).card := by
    apply PairSurcharge.ordinary_overlapping_pair_charge (Global.line a) gs hg
      (Global.line_card a) (out a) (pick q₁).val (pick q₂).val r₁ q₁.val q₂.val
      (hordinary a haW) hiD hjD hij hc₁
    intro t
    simpa only [hrEq] using hc₂ t
  have hP25 : 25 ≤ P.card := by
    have hh : (∑ b ∈ W, (3 + if b = a then 1 else 0 : ℕ)) ≤
        ∑ b ∈ W, (Global.D (Global.line b) gs).card := by
      apply Finset.sum_le_sum
      intro b hb
      by_cases hba : b = a
      · subst b
        simpa using hDa
      · simpa [hba] using hcounts b hb
    have hleft : (∑ b ∈ W, (3 + if b = a then 1 else 0 : ℕ)) = 25 := by
      simp [Finset.sum_add_distrib, hW, haW]
    rw [hleft, ← hPsum] at hh
    exact hh
  have hE10 : E.card ≤ 10 := by omega
  have hdiff : 3 ≤ (Support.line w \ Global.line a).card := by
    rw [Finset.card_sdiff, Clamp.line_card]
    have hh := Global.line_intersection a w haw
    change (Global.line a ∩ Support.line w).card ≤ 1 at hh
    omega
  obtain ⟨p', hp'diff, hp'raw⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show (MissingRawWitness.rawSet gs E).card < (Support.line w \ Global.line a).card by omega)
  have hp'w := (Finset.mem_sdiff.mp hp'diff).1
  have hp'a := (Finset.mem_sdiff.mp hp'diff).2
  have hp'not : Bridge.rawIndex gs p' ∉ E := fun h => hp'raw ((MissingRawWitness.mem_rawSet gs E p').mpr h)
  obtain ⟨hXcard, hp'X, hXa, hXonly⟩ := OneAnd.separating_row w a haw.symm p' hp'w hp'a
  let X := OneAnd.separatingRow w a p'
  let x := Clamp.fromTrue X
  have hxband : Support.Band x := fromTrue_seven X hXcard
  have hxpos : Support.target w x = true := by
    apply decide_eq_true_iff.mpr
    exact ⟨p', hp'w, by simpa [x, Clamp.fromTrue] using hp'X⟩
  have hxline : ∀ q ∈ Support.line w, q ≠ p' → x q = false := by
    intro q hqw hqp
    have hn : q ∉ X := fun hqX => hqp (hXonly q hqw hqX)
    simp [x, Clamp.fromTrue, hn]
  have hxZ : ∀ q : Fin 13, x q = true → Global.Zof (Global.line a) q = true := by
    intro q hq
    have hqX : q ∈ X := by simpa [x, Clamp.fromTrue] using hq
    have hqa : q ∉ Global.line a := fun hqa => Finset.disjoint_left.mp hXa hqa hqX
    simpa [Global.Zof] using hqa
  have hzraw (i : ℕ) (hi : i ∈ Global.D (Global.line a) gs) : Global.val gs x i = false := by
    have hzero := (Finset.mem_filter.mp hi).2.1
    cases he : Global.val gs x i
    · rfl
    · have hh := Bridge.val_mono gs (fun g hm => (hg g hm).1) x
        (Global.Zof (Global.line a)) hxZ i he
      rw [hzero] at hh
      contradiction
  have hKsub : ({pick q₁, pick q₂} : Finset (Fin (13 + gs.length))) ⊆ E := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact hiE
    · exact hjE
  have hKcard : ({pick q₁, pick q₂} : Finset (Fin (13 + gs.length))).card = 2 :=
    Finset.card_pair (fun he => hqne (hpick he))
  have hfront : (E.filter (fun i => Global.val gs x i.val = true)).card ≤ 8 := by
    have hs : E.filter (fun i => Global.val gs x i.val = true) ⊆ E \ {pick q₁, pick q₂} := by
      intro i hi
      obtain ⟨hiE', hit⟩ := Finset.mem_filter.mp hi
      refine Finset.mem_sdiff.mpr ⟨hiE', ?_⟩
      intro hiK
      simp only [Finset.mem_insert, Finset.mem_singleton] at hiK
      rcases hiK with rfl | rfl
      · rw [hzraw _ hiD] at hit
        contradiction
      · rw [hzraw _ hjD] at hit
        contradiction
    have hh := Finset.card_le_card hs
    rw [Finset.card_sdiff_of_subset hKsub, hKcard] at hh
    omega
  apply Clamp9.positive_frontier_impossible w E F (fun i x => Global.val gs x i.val)
    hmono hsupport _ hcorrect x hxband hxpos hfront
    (MissingRawWitness.true_foreign gs w p' P E hallowed hpaid hp'not x hxline)
  intro i _ y z hyz hy
  exact Bridge.val_mono gs (fun g hm => (hg g hm).1) y z hyz i.val hy

lemma raw_line_members (gs : List Gate) (out : Fin 13 → ℕ) (w : Fin 13)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (W : Finset (Fin 13)) (hW : W.card = 8) (hw : w ∉ W)
    (hordinary : ∀ a ∈ W, ∀ x : Fin 13 → Bool,
      Global.val gs x (out a) = Support.target a x)
    (P : Finset ℕ) (hP : P = W.biUnion (fun a => Global.D (Global.line a) gs))
    (E : Finset (Fin (13 + gs.length))) (hbudget : E.card + P.card ≤ 35)
    (hallowed : ∀ i ∈ E, i.val < 13 ∨ i.val ∈ P)
    (F : (Fin (13 + gs.length) → Bool) → Bool)
    (hmono : ∀ a b, (∀ i, a i = true → b i = true) → F a = true → F b = true)
    (hsupport : ∀ a b, (∀ i ∈ E, a i = b i) → F a = F b)
    (hcorrect : ∀ x : Fin 13 → Bool, Support.Band x →
      F (fun i => Global.val gs x i.val) = Support.target w x)
    (p : Fin 13) (hp : p ∈ Support.line w) : Bridge.rawIndex gs p ∈ E := by
  classical
  by_contra hpnot
  exact missing_raw_impossible gs out w hg W hW hw hordinary P hP E hbudget hallowed F
    hmono hsupport hcorrect p hp hpnot

end PEqualNP.Outside.L_meta_1024_aux.Clamp11

namespace PEqualNP.Outside.L_meta_1024_aux.Charges
open PEqualNP.CircuitLowerBounds

lemma owned_charge_properties (gs : List Gate) (out : Fin 13 → ℕ) (W : Finset (Fin 13))
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hordinary : ∀ a ∈ W, ∀ x : Fin 13 → Bool,
      Global.val gs x (out a) = Support.target a x) :
    let P := W.biUnion (fun a => Global.D (Global.line a) gs)
    P ⊆ Finset.Ico 13 (13 + gs.length) ∧ 3 * W.card ≤ P.card ∧
      ∀ w ∉ W, ∀ i ∈ P,
        (∃ q : Fin 13, q ∉ Global.line w ∧ Global.val gs (Global.eof q) i = true) ∧
        (∃ x : Fin 13 → Bool, Support.Band x ∧ Support.target w x = true ∧ Global.val gs x i = false) := by
  classical
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨a, _, hai⟩ := Finset.mem_biUnion.mp hi
    exact (Finset.mem_filter.mp hai).1
  · have hd : ∀ a ∈ W, ∀ b ∈ W, a ≠ b →
        Disjoint (Global.D (Global.line a) gs) (Global.D (Global.line b) gs) := by
      intro a _ b _ hab
      exact disjoint_charges gs hg a b hab
    have hsum : (∑ _a ∈ W, (3 : ℕ)) ≤ ∑ a ∈ W, (Global.D (Global.line a) gs).card := by
      apply Finset.sum_le_sum
      intro a ha
      exact ordinary_charge_count gs (out a) a hg (hordinary a ha)
    rw [← Finset.card_biUnion hd] at hsum
    simpa [Nat.mul_comm] using hsum
  · intro w hw i hi
    obtain ⟨a, ha, hai⟩ := Finset.mem_biUnion.mp hi
    have hne : a ≠ w := fun he => hw (he ▸ ha)
    exact ⟨charge_outside gs hg w a hne i hai,
      charge_not_above gs (fun g hm => (hg g hm).1) w a hne i hai⟩

end PEqualNP.Outside.L_meta_1024_aux.Charges

namespace PEqualNP.Outside.L_meta_1024_aux.FourReduction
open PEqualNP.CircuitLowerBounds

set_option maxHeartbeats 4000000 in
lemma eight_ordinary_reduction (gs : List Gate) (out : Fin 13 → ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hsmall : gs.length ≤ 38)
    (hcorrect : ∀ w (x : Fin 13 → Bool), Support.Band x →
      Global.val gs x (out w) = Support.target w x)
    (W : Finset (Fin 13)) (hW : 8 ≤ W.card)
    (hordinary : ∀ w ∈ W, ∀ x : Fin 13 → Bool,
      Global.val gs x (out w) = Support.target w x) :
    ∃ (I : List Gate) (lineId : Fin 5 → Fin 13) (left right : Fin 5 → ℕ),
      Function.Injective lineId ∧ I.length ≤ 9 ∧
      (∀ g ∈ I, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      (∀ u (x : Fin 13 → Bool), Support.Band x →
        (Cut.cutVal 13 ∅ I x (left u) || Cut.cutVal 13 ∅ I x (right u)) = Support.target (lineId u) x) ∧
      (∀ u (x : Fin 13 → Bool), Support.target (lineId u) x = false →
        (Cut.cutVal 13 ∅ I x (left u) || Cut.cutVal 13 ∅ I x (right u)) = false) ∧
      ∀ u, ¬ ∀ x : Fin 13 → Bool,
        (Cut.cutVal 13 ∅ I x (left u) || Cut.cutVal 13 ∅ I x (right u)) = Support.target (lineId u) x := by
  classical
  obtain ⟨V, hVW, hVcard⟩ := Finset.exists_subset_card_eq hW
  obtain ⟨hs, ho, hhg, hhlen, hhcorrect, hhordinary, hhsinks, hhor⟩ :=
    TrueClamp.normalize_or_sinks gs out hg hcorrect V (fun w hw => hordinary w (hVW hw))
  let C := Finset.univ \ V
  have hC : C.card = 5 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), hVcard]
    decide
  let e : Fin 5 ≃ C := (Fintype.equivFinOfCardEq (by simpa using hC)).symm
  let lineId : Fin 5 → Fin 13 := fun u => (e u).val
  have hinj : Function.Injective lineId := Subtype.val_injective.comp e.injective
  have hnotV (u : Fin 5) : lineId u ∉ V := (Finset.mem_sdiff.mp (e u).property).2
  let P := V.biUnion (fun a => Global.D (Global.line a) hs)
  obtain ⟨hP, hPcount, hPprops⟩ := Charges.owned_charge_properties hs ho V hhg hhordinary
  have hP24 : 24 ≤ P.card := by simpa [hVcard] using hPcount
  have hnotP (u : Fin 5) : ho (lineId u) ∉ P := by
    intro hu
    obtain ⟨x, hx, hxt, hxf⟩ := (hPprops (lineId u) (hnotV u) _ hu).2
    have hh := hhcorrect (lineId u) x hx
    rw [hxf, hxt] at hh
    exact Bool.noConfusion hh
  let Q : Finset ℕ := Finset.univ.image (fun u : Fin 5 => ho (lineId u))
  have houtinj := Bridge.output_distinct hs ho hhcorrect
  have hQ : Q.card = 5 := by
    have hi : Function.Injective (fun u : Fin 5 => ho (lineId u)) := houtinj.comp hinj
    change (Finset.univ.image (fun u : Fin 5 => ho (lineId u))).card = 5
    rw [Finset.card_image_of_injective _ hi]
    decide
  have hQsub : Q ⊆ Finset.Ico 13 (13 + hs.length) := by
    intro i hi
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_Ico.mpr (Bridge.output_index hs _ _ (hhcorrect (lineId u)))
  have hdisj : Disjoint P Q := by
    rw [Finset.disjoint_left]
    intro i hiP hiQ
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hiQ
    exact hnotP u hiP
  have hsinks : Dead.NoReads 13 Q hs := by
    intro j hj i hi hn hiQ
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hiQ
    exact hhsinks j hj _ hi hn (Finset.mem_image.mpr ⟨lineId u, Finset.mem_univ _, rfl⟩)
  let E (u : Fin 5) := Cut.essential (M := 13 + hs.length) 13 P hs (ho (lineId u))
  have hbudget (u : Fin 5) : (E u).card + P.card ≤ 35 := by
    have hb := essential_other_sinks_budget (M := 13 + hs.length) 13 P Q hs
      (fun g hm => (hhg g hm).2) hP hQsub hdisj hsinks (ho (lineId u))
      (Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩)
    rw [hQ] at hb
    change (E u).card + P.card + 5 ≤ _ at hb
    omega
  have hraw (u : Fin 5) (p : Fin 13) (hp : p ∈ Global.line (lineId u)) : Bridge.rawIndex hs p ∈ E u := by
    apply Clamp11.raw_line_members hs ho (lineId u) hhg V hVcard (hnotV u) hhordinary P rfl
      (E u) (hbudget u) (Cut.essential_sources 13 P hs (ho (lineId u)))
      (fun z => Cut.cutVal 13 P hs z (ho (lineId u)))
    · intro a b hab ha
      exact Cut.cutVal_mono 13 P hs (fun g hm => (hhg g hm).1) a b hab (ho (lineId u)) ha
    · exact Cut.essential_supports 13 P hs (ho (lineId u))
    · intro x hx
      exact (Cut.factor P hs x (ho (lineId u))).trans (hhcorrect (lineId u) x hx)
    · exact hp
  obtain ⟨I, left, right, hI, hIg, hIc, hIb, hIn⟩ := five_or_sink_reduction hs ho lineId hinj hhg
    (by omega) hhcorrect P hP hP24 hnotP
    (fun u i hi => (hPprops (lineId u) (hnotV u) i hi).1) hsinks
    (fun u => hhor (lineId u) (hnotV u)) hraw
  exact ⟨I, lineId, left, right, hinj, hI, hIg, hIc, hIb, hIn⟩

end PEqualNP.Outside.L_meta_1024_aux.FourReduction

namespace PEqualNP.Outside.L_meta_1024_aux.ParentRankGeometry

lemma pencil_card : ∀ p : Fin 13,
    (Finset.univ.filter (fun w : Fin 13 => p ∈ Global.line w)).card = 4 := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma avoid_three_card : ∀ a b c : Fin 13, a ≠ b → a ≠ c → b ≠ c →
    (Finset.univ.filter (fun w : Fin 13 =>
      a ∉ Global.line w ∧ b ∉ Global.line w ∧ c ∉ Global.line w)).card ≤ 4 := by
  decide +kernel

lemma five_lines_not_all_through (lineId : Fin 5 → Fin 13) (hinj : Function.Injective lineId)
    (p : Fin 13) : ∃ e : Fin 5, p ∉ Global.line (lineId e) := by
  classical
  by_contra! hall
  have hsub : Finset.univ.image lineId ⊆
      Finset.univ.filter (fun w : Fin 13 => p ∈ Global.line w) := by
    intro w hw
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hall e⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj, pencil_card] at hc
  have he : (Finset.univ : Finset (Fin 5)).card = 5 := by decide
  omega

lemma five_line_union_card (lineId : Fin 5 → Fin 13) (hinj : Function.Injective lineId) :
    11 ≤ (Finset.univ.biUnion (fun e : Fin 5 => Global.line (lineId e))).card := by
  classical
  let U := Finset.univ.biUnion (fun e : Fin 5 => Global.line (lineId e))
  change 11 ≤ U.card
  by_contra! hsmall
  have hcomp : 3 ≤ (Finset.univ \ U).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    have hu : (Finset.univ : Finset (Fin 13)).card = 13 := by decide
    rw [hu]
    omega
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hcomp
  obtain ⟨a, b, c, hab, hac, hbc, hT⟩ := Finset.card_eq_three.mp hTcard
  have hnot (p : Fin 13) (hp : p ∈ T) (e : Fin 5) : p ∉ Global.line (lineId e) := by
    intro he
    exact (Finset.mem_sdiff.mp (hTsub hp)).2
      (Finset.mem_biUnion.mpr ⟨e, Finset.mem_univ _, he⟩)
  have hsub : Finset.univ.image lineId ⊆ Finset.univ.filter (fun w : Fin 13 =>
      a ∉ Global.line w ∧ b ∉ Global.line w ∧ c ∉ Global.line w) := by
    intro w hw
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      hnot a (by simp [hT]) e, hnot b (by simp [hT]) e, hnot c (by simp [hT]) e⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj] at hc
  have hf := avoid_three_card a b c hab hac hbc
  have he : (Finset.univ : Finset (Fin 5)).card = 5 := by decide
  omega

end PEqualNP.Outside.L_meta_1024_aux.ParentRankGeometry

namespace PEqualNP.Outside.L_meta_1024_aux.ParentRankCore

def Shared (parent : Fin 5 → Bool → ℕ) (e f : Fin 5) : Prop :=
  ∃ a b : Bool, parent e a = parent f b

def Connected (parent : Fin 5 → Bool → ℕ) : Prop :=
  ∀ e f : Fin 5, Relation.ReflTransGen (Shared parent) e f

def DegreeTwo (parent : Fin 5 → Bool → ℕ) : Prop :=
  ∀ e : Fin 5, ∀ a : Bool, ∃ f : Fin 5, e ≠ f ∧ ∃ b : Bool, parent e a = parent f b

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma line_avoids_two : ∀ a b c : Fin 13, a ≠ b → a ≠ c →
    ∃ p ∈ Global.line a, p ∉ Global.line b ∧ p ∉ Global.line c := by
  decide +kernel

lemma connected_degree_two_rank
    (parent : Fin 5 → Bool → ℕ) (lineId : Fin 5 → Fin 13)
    (hinj : Function.Injective lineId) (hconn : Connected parent) (hdegree : DegreeTwo parent)
    (label : Fin 13 → ℕ) (wire : ℕ → ℕ)
    (hforce : ∀ e f : Fin 5, e ≠ f → ∀ a b : Bool, parent e a = parent f b →
      ∀ p ∈ Global.line (lineId e) \ Global.line (lineId f),
        label p = wire (parent e (!a))) :
    ∃ S : Finset (Fin 13), 10 + (S.image label).card ≤ S.card := by
  classical
  have hend (e : Fin 5) : wire (parent e false) = wire (parent e true) := by
    obtain ⟨f, hef, b, hfb⟩ := hdegree e false
    obtain ⟨g, heg, c, hgc⟩ := hdegree e true
    obtain ⟨p, hp, hpf, hpg⟩ := line_avoids_two (lineId e) (lineId f) (lineId g)
      (fun h => hef (hinj h)) (fun h => heg (hinj h))
    have h₁ := hforce e f hef false b hfb p (Finset.mem_sdiff.mpr ⟨hp, hpf⟩)
    have h₂ := hforce e g heg true c hgc p (Finset.mem_sdiff.mpr ⟨hp, hpg⟩)
    exact h₂.symm.trans h₁
  have hend' (e : Fin 5) (a : Bool) : wire (parent e a) = wire (parent e false) := by
    cases a
    · rfl
    · exact (hend e).symm
  have hadj (e f : Fin 5) (h : Shared parent e f) :
      wire (parent e false) = wire (parent f false) := by
    obtain ⟨a, b, hab⟩ := h
    exact (hend' e a).symm.trans ((congrArg wire hab).trans (hend' f b))
  have hpath (e f : Fin 5) (h : Relation.ReflTransGen (Shared parent) e f) :
      wire (parent e false) = wire (parent f false) := by
    induction h with
    | refl => rfl
    | tail hprev hlast ih => exact ih.trans (hadj _ _ hlast)
  let c := wire (parent 0 false)
  have hconst (e : Fin 5) (a : Bool) : wire (parent e a) = c :=
    (hend' e a).trans (hpath e 0 (hconn e 0))
  have hpoint (p : Fin 13) (e : Fin 5) (hp : p ∈ Global.line (lineId e)) : label p = c := by
    by_contra hn
    have hstep (e f : Fin 5) (h : Shared parent e f)
        (hp : p ∈ Global.line (lineId e)) : p ∈ Global.line (lineId f) := by
      by_cases hef : e = f
      · simpa [hef] using hp
      obtain ⟨a, b, hab⟩ := h
      by_contra hpf
      exact hn ((hforce e f hef a b hab p (Finset.mem_sdiff.mpr ⟨hp, hpf⟩)).trans (hconst e (!a)))
    have hall (f : Fin 5) : p ∈ Global.line (lineId f) := by
      have h := hconn e f
      induction h with
      | refl => exact hp
      | tail hprev hlast ih => exact hstep _ _ hlast ih
    obtain ⟨f, hpf⟩ := ParentRankGeometry.five_lines_not_all_through lineId hinj p
    exact hpf (hall f)
  let S := Finset.univ.biUnion (fun e : Fin 5 => Global.line (lineId e))
  have hS : 11 ≤ S.card := ParentRankGeometry.five_line_union_card lineId hinj
  have himage : S.image label ⊆ {c} := by
    intro v hv
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨e, _, hpe⟩ := Finset.mem_biUnion.mp hp
    exact Finset.mem_singleton.mpr (hpoint p e hpe)
  have hcard : (S.image label).card ≤ 1 := by simpa using Finset.card_le_card himage
  exact ⟨S, by omega⟩

lemma linewise_rank
    (lineId : Fin 5 → Fin 13) (hinj : Function.Injective lineId)
    (label : Fin 13 → ℕ) (value : Fin 5 → ℕ)
    (hline : ∀ e : Fin 5, ∀ p ∈ Global.line (lineId e), label p = value e) :
    ∃ S : Finset (Fin 13), 10 + (S.image label).card ≤ S.card := by
  classical
  have hvalue (e : Fin 5) : value e = value 0 := by
    by_cases he : e = 0
    · rw [he]
    obtain ⟨p, hpe, hp0⟩ := (Bridge.pair_geometry (lineId e) (lineId 0)
      (fun h => he (hinj h))).2
    exact (hline e p hpe).symm.trans (hline 0 p hp0)
  let S := Finset.univ.biUnion (fun e : Fin 5 => Global.line (lineId e))
  have hS : 11 ≤ S.card := ParentRankGeometry.five_line_union_card lineId hinj
  have himage : S.image label ⊆ {value 0} := by
    intro v hv
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨e, _, hpe⟩ := Finset.mem_biUnion.mp hp
    exact Finset.mem_singleton.mpr ((hline e p hpe).trans (hvalue e))
  have hcard : (S.image label).card ≤ 1 := by simpa using Finset.card_le_card himage
  exact ⟨S, by omega⟩

lemma star_rank
    (parent : Fin 5 → Bool → ℕ) (lineId : Fin 5 → Fin 13)
    (hinj : Function.Injective lineId) (label : Fin 13 → ℕ) (wire : ℕ → ℕ)
    (hforce : ∀ e f : Fin 5, e ≠ f → ∀ a b : Bool, parent e a = parent f b →
      ∀ p ∈ Global.line (lineId e) \ Global.line (lineId f),
        label p = wire (parent e (!a)))
    (center : ℕ) (side : Fin 5 → Bool) (hstar : ∀ e, parent e (side e) = center) :
    ∃ S : Finset (Fin 13), 10 + (S.image label).card ≤ S.card := by
  apply linewise_rank lineId hinj label (fun e => wire (parent e (!(side e))))
  intro e p hp
  obtain ⟨f, hpf⟩ := ParentRankGeometry.five_lines_not_all_through lineId hinj p
  have hef : e ≠ f := by
    intro he
    subst f
    exact hpf hp
  exact hforce e f hef (side e) (side f) ((hstar e).trans (hstar f).symm) p
    (Finset.mem_sdiff.mpr ⟨hp, hpf⟩)


def Nonleaf (parent : Fin 5 → Bool → ℕ) (v : ℕ) : Prop :=
  ∃ e f : Fin 5, e ≠ f ∧ ∃ a b : Bool, parent e a = v ∧ parent f b = v

def CoreEdge (parent : Fin 5 → Bool → ℕ) (e : Fin 5) : Prop :=
  Nonleaf parent (parent e false) ∧ Nonleaf parent (parent e true)

lemma nonleaf_other (parent : Fin 5 → Bool → ℕ) (e : Fin 5) (a : Bool)
    (h : Nonleaf parent (parent e a)) :
    ∃ f : Fin 5, e ≠ f ∧ ∃ b : Bool, parent e a = parent f b := by
  obtain ⟨f, g, hfg, b, c, hfb, hgc⟩ := h
  by_cases hef : e = f
  · subst f
    exact ⟨g, hfg, c, hgc.symm⟩
  · exact ⟨f, hef, b, hfb.symm⟩

lemma shared_nonleaf (parent : Fin 5 → Bool → ℕ) (e f : Fin 5)
    (hef : e ≠ f) (a b : Bool) (h : parent e a = parent f b) :
    Nonleaf parent (parent e a) :=
  ⟨e, f, hef, a, b, rfl, h.symm⟩

lemma edge_has_nonleaf (parent : Fin 5 → Bool → ℕ) (hconn : Connected parent)
    (e : Fin 5) : ∃ a : Bool, Nonleaf parent (parent e a) := by
  classical
  by_contra hn
  have hnone (a : Bool) : ¬ Nonleaf parent (parent e a) := by
    intro ha
    exact hn ⟨a, ha⟩
  have hadj (f : Fin 5) (h : Shared parent e f) : e = f := by
    by_contra hef
    obtain ⟨a, b, hab⟩ := h
    exact hnone a (shared_nonleaf parent e f hef a b hab)
  have hpath (f : Fin 5) (h : Relation.ReflTransGen (Shared parent) e f) : e = f := by
    induction h with
    | refl => rfl
    | tail hprev hlast ih =>
      apply hadj
      simpa only [ih] using hlast
  have h01 := (hpath 0 (hconn e 0)).symm.trans (hpath 1 (hconn e 1))
  exact (by decide : (0 : Fin 5) ≠ 1) h01

lemma core_end_equal
    (parent : Fin 5 → Bool → ℕ) (lineId : Fin 5 → Fin 13)
    (hinj : Function.Injective lineId) (label : Fin 13 → ℕ) (wire : ℕ → ℕ)
    (hforce : ∀ e f : Fin 5, e ≠ f → ∀ a b : Bool, parent e a = parent f b →
      ∀ p ∈ Global.line (lineId e) \ Global.line (lineId f),
        label p = wire (parent e (!a)))
    (e : Fin 5) (he : CoreEdge parent e) :
    wire (parent e false) = wire (parent e true) := by
  obtain ⟨f, hef, b, hfb⟩ := nonleaf_other parent e false he.1
  obtain ⟨g, heg, c, hgc⟩ := nonleaf_other parent e true he.2
  obtain ⟨p, hp, hpf, hpg⟩ := line_avoids_two (lineId e) (lineId f) (lineId g)
    (fun h => hef (hinj h)) (fun h => heg (hinj h))
  have h₁ := hforce e f hef false b hfb p (Finset.mem_sdiff.mpr ⟨hp, hpf⟩)
  have h₂ := hforce e g heg true c hgc p (Finset.mem_sdiff.mpr ⟨hp, hpg⟩)
  exact h₂.symm.trans h₁

lemma nonleaf_values_equal
    (parent : Fin 5 → Bool → ℕ) (lineId : Fin 5 → Fin 13)
    (hinj : Function.Injective lineId) (hconn : Connected parent)
    (label : Fin 13 → ℕ) (wire : ℕ → ℕ)
    (hforce : ∀ e f : Fin 5, e ≠ f → ∀ a b : Bool, parent e a = parent f b →
      ∀ p ∈ Global.line (lineId e) \ Global.line (lineId f),
        label p = wire (parent e (!a))) :
    ∃ c : ℕ, ∀ e : Fin 5, ∀ a : Bool, Nonleaf parent (parent e a) →
      wire (parent e a) = c := by
  classical
  choose anchor hanchor using edge_has_nonleaf parent hconn
  have hedge (e : Fin 5) (a : Bool) (ha : Nonleaf parent (parent e a)) :
      wire (parent e a) = wire (parent e (anchor e)) := by
    by_cases hea : a = anchor e
    · rw [hea]
    have hae := hanchor e
    have he : CoreEdge parent e := by
      cases a <;> cases h : anchor e <;> simp_all [CoreEdge]
    have heq := core_end_equal parent lineId hinj label wire hforce e he
    cases a <;> cases h : anchor e <;> simp_all
  have hadj (e f : Fin 5) (h : Shared parent e f) :
      wire (parent e (anchor e)) = wire (parent f (anchor f)) := by
    by_cases hef : e = f
    · rw [hef]
    obtain ⟨a, b, hab⟩ := h
    have hna := shared_nonleaf parent e f hef a b hab
    have hnb : Nonleaf parent (parent f b) := hab ▸ hna
    exact (hedge e a hna).symm.trans ((congrArg wire hab).trans (hedge f b hnb))
  have hpath (e f : Fin 5) (h : Relation.ReflTransGen (Shared parent) e f) :
      wire (parent e (anchor e)) = wire (parent f (anchor f)) := by
    induction h with
    | refl => rfl
    | tail hprev hlast ih => exact ih.trans (hadj _ _ hlast)
  exact ⟨wire (parent 0 (anchor 0)), fun e a ha =>
    (hedge e a ha).trans (hpath e 0 (hconn e 0))⟩

end PEqualNP.Outside.L_meta_1024_aux.ParentRankCore

namespace PEqualNP.Outside.L_meta_1024_aux.ParentRankCore

lemma core_points
    (parent : Fin 5 → Bool → ℕ) (lineId : Fin 5 → Fin 13)
    (hinj : Function.Injective lineId) (hconn : Connected parent)
    (label : Fin 13 → ℕ) (wire : ℕ → ℕ)
    (hforce : ∀ e f : Fin 5, e ≠ f → ∀ a b : Bool, parent e a = parent f b →
      ∀ p ∈ Global.line (lineId e) \ Global.line (lineId f),
        label p = wire (parent e (!a)))
    (c : ℕ) (hcommon : ∀ e : Fin 5, ∀ a : Bool, Nonleaf parent (parent e a) →
      wire (parent e a) = c)
    (e : Fin 5) (he : CoreEdge parent e) :
    ∀ p ∈ Global.line (lineId e), label p = c := by
  intro p hp
  by_contra hn
  let AllAt (v : ℕ) : Prop := ∀ f : Fin 5, ∀ b : Bool,
    parent f b = v → p ∈ Global.line (lineId f)
  have transfer (f : Fin 5) (a : Bool) (hf : p ∈ Global.line (lineId f))
      (hopp : Nonleaf parent (parent f (!a))) : AllAt (parent f a) := by
    intro g b hgb
    by_cases hfg : f = g
    · simpa [hfg] using hf
    by_contra hpg
    exact hn ((hforce f g hfg a b hgb.symm p
      (Finset.mem_sdiff.mpr ⟨hf, hpg⟩)).trans (hcommon f (!a) hopp))
  have hstart : ∀ a : Bool, Nonleaf parent (parent e a) → AllAt (parent e a) := by
    intro a ha
    apply transfer e a hp
    cases a
    · exact he.2
    · exact he.1
  have hstep (f g : Fin 5) (hfg : Shared parent f g)
      (hf : ∀ a : Bool, Nonleaf parent (parent f a) → AllAt (parent f a)) :
      ∀ b : Bool, Nonleaf parent (parent g b) → AllAt (parent g b) := by
    by_cases heq : f = g
    · simpa [heq] using hf
    obtain ⟨a, b, hab⟩ := hfg
    have hna := shared_nonleaf parent f g heq a b hab
    have hnb : Nonleaf parent (parent g b) := hab ▸ hna
    have hat : AllAt (parent g b) := hab ▸ hf a hna
    have hpg := hat g b rfl
    intro d hd
    by_cases hdb : d = b
    · simpa [hdb] using hat
    apply transfer g d hpg
    have hnot : (!d) = b := by cases d <;> cases b <;> simp_all
    simpa only [hnot] using hnb
  have hreach (f : Fin 5) : ∀ a : Bool,
      Nonleaf parent (parent f a) → AllAt (parent f a) := by
    have h := hconn e f
    induction h with
    | refl => exact hstart
    | tail hprev hlast ih => exact hstep _ _ hlast ih
  obtain ⟨f, hpf⟩ := ParentRankGeometry.five_lines_not_all_through lineId hinj p
  obtain ⟨a, ha⟩ := edge_has_nonleaf parent hconn f
  exact hpf (hreach f a ha f a rfl)


def Incident (parent : Fin 5 → Bool → ℕ) (v : ℕ) (e : Fin 5) : Prop :=
  ∃ a : Bool, parent e a = v

lemma star_of_no_core_neighbor (parent : Fin 5 → Bool → ℕ) (hconn : Connected parent)
    (v : ℕ) (hv : Nonleaf parent v)
    (hno : ∀ e : Fin 5, Incident parent v e → ¬ CoreEdge parent e) :
    ∃ side : Fin 5 → Bool, ∀ e : Fin 5, parent e (side e) = v := by
  classical
  have hstep (e f : Fin 5) (h : Shared parent e f) (he : Incident parent v e) :
      Incident parent v f := by
    by_cases hef : e = f
    · simpa [hef] using he
    obtain ⟨a, b, hab⟩ := h
    obtain ⟨d, hd⟩ := he
    by_cases hda : d = a
    · exact ⟨b, hab.symm.trans (hda ▸ hd)⟩
    have hna := shared_nonleaf parent e f hef a b hab
    have hnd : Nonleaf parent (parent e d) := hd.symm ▸ hv
    have hc : CoreEdge parent e := by
      cases d <;> cases a <;> simp_all [CoreEdge]
    exact False.elim (hno e ⟨d, hd⟩ hc)
  obtain ⟨e, f, hef, a, b, hea, hfb⟩ := hv
  have hall (g : Fin 5) : Incident parent v g := by
    have h := hconn e g
    induction h with
    | refl => exact ⟨a, hea⟩
    | tail hprev hlast ih => exact hstep _ _ hlast ih
  exact ⟨fun e => Classical.choose (hall e), fun e => Classical.choose_spec (hall e)⟩

lemma core_neighbor_of_not_star (parent : Fin 5 → Bool → ℕ) (hconn : Connected parent)
    (hstar : ¬ ∃ v : ℕ, ∃ side : Fin 5 → Bool, ∀ e : Fin 5, parent e (side e) = v)
    (v : ℕ) (hv : Nonleaf parent v) :
    ∃ e : Fin 5, Incident parent v e ∧ CoreEdge parent e := by
  by_contra! hno
  obtain ⟨side, hs⟩ := star_of_no_core_neighbor parent hconn v hv hno
  exact hstar ⟨v, side, hs⟩


lemma line_inter_unique (a b : Fin 13) (hab : a ≠ b) (p q : Fin 13)
    (hpa : p ∈ Global.line a) (hpb : p ∈ Global.line b)
    (hqa : q ∈ Global.line a) (hqb : q ∈ Global.line b) : p = q := by
  exact Finset.card_le_one.mp (Global.line_intersection a b hab) p
    (Finset.mem_inter.mpr ⟨hpa, hpb⟩) q (Finset.mem_inter.mpr ⟨hqa, hqb⟩)

lemma bad_endpoint_pencil
    (parent : Fin 5 → Bool → ℕ) (lineId : Fin 5 → Fin 13)
    (hinj : Function.Injective lineId) (hconn : Connected parent)
    (hstar : ¬ ∃ v : ℕ, ∃ side : Fin 5 → Bool, ∀ e : Fin 5, parent e (side e) = v)
    (label : Fin 13 → ℕ) (wire : ℕ → ℕ)
    (hforce : ∀ e f : Fin 5, e ≠ f → ∀ a b : Bool, parent e a = parent f b →
      ∀ p ∈ Global.line (lineId e) \ Global.line (lineId f),
        label p = wire (parent e (!a)))
    (c : ℕ) (hcommon : ∀ e : Fin 5, ∀ a : Bool, Nonleaf parent (parent e a) →
      wire (parent e a) = c)
    (e : Fin 5) (a : Bool) (hbad : wire (parent e a) ≠ c) :
    ∃ p ∈ Global.line (lineId e),
      (∀ f : Fin 5, CoreEdge parent f → p ∈ Global.line (lineId f)) ∧
      (∀ q ∈ Global.line (lineId e), q ≠ p → label q = wire (parent e a)) := by
  classical
  have hleaf : ¬ Nonleaf parent (parent e a) := fun h => hbad (hcommon e a h)
  have hne : ¬ CoreEdge parent e := by
    intro he
    apply hleaf
    cases a
    · exact he.1
    · exact he.2
  have hother : Nonleaf parent (parent e (!a)) := by
    obtain ⟨b, hb⟩ := edge_has_nonleaf parent hconn e
    cases a <;> cases b <;> simp_all
  obtain ⟨f, ⟨b, hfb⟩, hfc⟩ :=
    core_neighbor_of_not_star parent hconn hstar (parent e (!a)) hother
  have hef : e ≠ f := by intro h; exact hne (h.symm ▸ hfc)
  have hids : lineId e ≠ lineId f := fun h => hef (hinj h)
  obtain ⟨p, hpe, hpf⟩ := (Bridge.pair_geometry (lineId e) (lineId f) hids).2
  have hpartial (q : Fin 13) (hqe : q ∈ Global.line (lineId e)) (hqp : q ≠ p) :
      label q = wire (parent e a) := by
    have hqf : q ∉ Global.line (lineId f) := by
      intro hqf
      exact hqp (line_inter_unique (lineId e) (lineId f) hids q p hqe hqf hpe hpf)
    have h := hforce e f hef (!a) b hfb.symm q (Finset.mem_sdiff.mpr ⟨hqe, hqf⟩)
    simpa using h
  refine ⟨p, hpe, ?_, hpartial⟩
  intro g hgc
  have heg : e ≠ g := by intro h; exact hne (h.symm ▸ hgc)
  obtain ⟨q, hqe, hqg⟩ := (Bridge.pair_geometry (lineId e) (lineId g)
    (fun h => heg (hinj h))).2
  by_cases hqp : q = p
  · simpa only [hqp] using hqg
  have hqc := core_points parent lineId hinj hconn label wire hforce c hcommon g hgc q hqg
  exact False.elim (hbad ((hpartial q hqe hqp).symm.trans hqc))

lemma all_values_rank
    (parent : Fin 5 → Bool → ℕ) (lineId : Fin 5 → Fin 13)
    (hinj : Function.Injective lineId) (hconn : Connected parent)
    (label : Fin 13 → ℕ) (wire : ℕ → ℕ)
    (hforce : ∀ e f : Fin 5, e ≠ f → ∀ a b : Bool, parent e a = parent f b →
      ∀ p ∈ Global.line (lineId e) \ Global.line (lineId f),
        label p = wire (parent e (!a)))
    (c : ℕ) (hvalues : ∀ e : Fin 5, ∀ a : Bool, wire (parent e a) = c) :
    ∃ S : Finset (Fin 13), 10 + (S.image label).card ≤ S.card := by
  apply linewise_rank lineId hinj label (fun _ => c)
  intro e p hp
  by_contra hn
  have hstep (e f : Fin 5) (h : Shared parent e f)
      (hp : p ∈ Global.line (lineId e)) : p ∈ Global.line (lineId f) := by
    by_cases hef : e = f
    · simpa [hef] using hp
    obtain ⟨a, b, hab⟩ := h
    by_contra hpf
    exact hn ((hforce e f hef a b hab p (Finset.mem_sdiff.mpr ⟨hp, hpf⟩)).trans (hvalues e (!a)))
  have hall (f : Fin 5) : p ∈ Global.line (lineId f) := by
    have h := hconn e f
    induction h with
    | refl => exact hp
    | tail hprev hlast ih => exact hstep _ _ hlast ih
  obtain ⟨f, hpf⟩ := ParentRankGeometry.five_lines_not_all_through lineId hinj p
  exact hpf (hall f)

lemma two_core_edges_rank
    (parent : Fin 5 → Bool → ℕ) (lineId : Fin 5 → Fin 13)
    (hinj : Function.Injective lineId) (hconn : Connected parent)
    (label : Fin 13 → ℕ) (wire : ℕ → ℕ)
    (hforce : ∀ e f : Fin 5, e ≠ f → ∀ a b : Bool, parent e a = parent f b →
      ∀ p ∈ Global.line (lineId e) \ Global.line (lineId f),
        label p = wire (parent e (!a)))
    (f g : Fin 5) (hfg : f ≠ g) (hfc : CoreEdge parent f) (hgc : CoreEdge parent g) :
    ∃ S : Finset (Fin 13), 10 + (S.image label).card ≤ S.card := by
  classical
  by_cases hstar : ∃ v : ℕ, ∃ side : Fin 5 → Bool, ∀ e : Fin 5, parent e (side e) = v
  · obtain ⟨v, side, hs⟩ := hstar
    exact star_rank parent lineId hinj label wire hforce v side hs
  obtain ⟨c, hcommon⟩ := nonleaf_values_equal parent lineId hinj hconn label wire hforce
  apply all_values_rank parent lineId hinj hconn label wire hforce c
  intro e a
  by_contra hbad
  obtain ⟨p, hpe, hpall, hpartial⟩ :=
    bad_endpoint_pencil parent lineId hinj hconn hstar label wire hforce c hcommon e a hbad
  obtain ⟨n, hpn⟩ := ParentRankGeometry.five_lines_not_all_through lineId hinj p
  have hnwire (b : Bool) : wire (parent n b) = c := by
    by_contra hbadn
    obtain ⟨q, hqn, hqall, _⟩ :=
      bad_endpoint_pencil parent lineId hinj hconn hstar label wire hforce c hcommon n b hbadn
    have hqp := line_inter_unique (lineId f) (lineId g) (fun h => hfg (hinj h))
      q p (hqall f hfc) (hqall g hgc) (hpall f hfc) (hpall g hgc)
    exact hpn (hqp ▸ hqn)
  obtain ⟨b, hb⟩ := edge_has_nonleaf parent hconn n
  obtain ⟨k, ⟨d, hkd⟩, hkc⟩ :=
    core_neighbor_of_not_star parent hconn hstar (parent n b) hb
  have hnk : n ≠ k := by
    intro h
    exact hpn (h.symm ▸ hpall k hkc)
  have hen : e ≠ n := by intro h; exact hpn (h ▸ hpe)
  obtain ⟨q, hqe, hqn⟩ := (Bridge.pair_geometry (lineId e) (lineId n)
    (fun h => hen (hinj h))).2
  have hqp : q ≠ p := by intro h; exact hpn (h ▸ hqn)
  have hek : e ≠ k := by
    intro h
    have hec : CoreEdge parent e := h.symm ▸ hkc
    have hea : Nonleaf parent (parent e a) := by cases a; exact hec.1; exact hec.2
    exact hbad (hcommon e a hea)
  have hqk : q ∉ Global.line (lineId k) := by
    intro hqk
    exact hqp (line_inter_unique (lineId e) (lineId k) (fun h => hek (hinj h))
      q p hqe hqk hpe (hpall k hkc))
  have hqwire := hforce n k hnk b d hkd.symm q (Finset.mem_sdiff.mpr ⟨hqn, hqk⟩)
  exact hbad ((hpartial q hqe hqp).symm.trans (hqwire.trans (hnwire (!b))))

end PEqualNP.Outside.L_meta_1024_aux.ParentRankCore

namespace PEqualNP.Outside.L_meta_1024_aux.ParentRankCore

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma pencil_avoid_two : ∀ a q r : Fin 13, q ≠ r →
    let A := Finset.univ.filter (fun w : Fin 13 =>
      a ∈ Global.line w ∧ q ∉ Global.line w ∧ r ∉ Global.line w)
    A.card ≤ 3 ∧ (A.card ≤ 2 ∨ ∃ w : Fin 13,
      a ∈ Global.line w ∧ q ∈ Global.line w ∧ r ∈ Global.line w) := by
  decide +kernel

lemma line_eq_of_two (a b p q : Fin 13) (hpq : p ≠ q)
    (hpa : p ∈ Global.line a) (hpb : p ∈ Global.line b)
    (hqa : q ∈ Global.line a) (hqb : q ∈ Global.line b) : a = b := by
  by_contra hab
  exact hpq (line_inter_unique a b hab p q hpa hpb hqa hqb)

lemma pencil_pair_union_card
    (lineId : Fin 5 → Fin 13) (hinj : Function.Injective lineId)
    (d : Fin 5) (a b : Fin 13) (hab : a ≠ b)
    (had : a ∈ Global.line (lineId d)) (hbd : b ∈ Global.line (lineId d))
    (hfamily : ∀ e : Fin 5, a ∈ Global.line (lineId e) ∨ b ∈ Global.line (lineId e)) :
    12 ≤ (Finset.univ.biUnion (fun e : Fin 5 => Global.line (lineId e))).card := by
  classical
  let S := Finset.univ.biUnion (fun e : Fin 5 => Global.line (lineId e))
  change 12 ≤ S.card
  by_contra! hsmall
  have hcomp : 2 ≤ (Finset.univ \ S).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    have hu : (Finset.univ : Finset (Fin 13)).card = 13 := by decide
    omega
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hcomp
  obtain ⟨q, r, hqr, hT⟩ := Finset.card_eq_two.mp hTcard
  have hmissing (p : Fin 13) (hp : p ∈ T) (e : Fin 5) : p ∉ Global.line (lineId e) := by
    intro he
    exact (Finset.mem_sdiff.mp (hTsub hp)).2
      (Finset.mem_biUnion.mpr ⟨e, Finset.mem_univ _, he⟩)
  have hq (e : Fin 5) := hmissing q (by simp [hT]) e
  have hr (e : Fin 5) := hmissing r (by simp [hT]) e
  let A := Finset.univ.filter (fun w : Fin 13 =>
    a ∈ Global.line w ∧ q ∉ Global.line w ∧ r ∉ Global.line w)
  let B := Finset.univ.filter (fun w : Fin 13 =>
    b ∈ Global.line w ∧ q ∉ Global.line w ∧ r ∉ Global.line w)
  obtain ⟨hA3, hAcases⟩ := pencil_avoid_two a q r hqr
  obtain ⟨hB3, hBcases⟩ := pencil_avoid_two b q r hqr
  change A.card ≤ 3 at hA3
  change B.card ≤ 3 at hB3
  change A.card ≤ 2 ∨ _ at hAcases
  change B.card ≤ 2 ∨ _ at hBcases
  have hsum : A.card + B.card ≤ 5 := by
    rcases hAcases with hA2 | ⟨u, hau, hqu, hru⟩
    · omega
    rcases hBcases with hB2 | ⟨v, hbv, hqv, hrv⟩
    · omega
    have huv := line_eq_of_two u v q r hqr hqu hqv hru hrv
    have hbu : b ∈ Global.line u := huv.symm ▸ hbv
    have hdu := line_eq_of_two (lineId d) u a b hab had hau hbd hbu
    exact False.elim (hq d (hdu.symm ▸ hqu))
  have hboth : lineId d ∈ A ∩ B := by
    apply Finset.mem_inter.mpr
    exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, had, hq d, hr d⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbd, hq d, hr d⟩⟩
  have hinter : 1 ≤ (A ∩ B).card := Finset.one_le_card.mpr ⟨_, hboth⟩
  have hsub : Finset.univ.image lineId ⊆ A ∪ B := by
    intro w hw
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hw
    rcases hfamily e with hae | hbe
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hae, hq e, hr e⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbe, hq e, hr e⟩)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj] at hcard
  have hfive : (Finset.univ : Finset (Fin 5)).card = 5 := by decide
  have hu := Finset.card_union_add_card_inter A B
  omega


lemma grouped_rank
    (lineId : Fin 5 → Fin 13) (hinj : Function.Injective lineId)
    (d : Fin 5) (group : Fin 5 → Bool) (label : Fin 13 → ℕ)
    (value : Fin 5 → ℕ) (c : ℕ)
    (hcentral : ∀ p ∈ Global.line (lineId d), label p = c)
    (houtside : ∀ e : Fin 5, e ≠ d →
      ∀ p ∈ Global.line (lineId e) \ Global.line (lineId d), label p = value e)
    (hsame : ∀ e f : Fin 5, e ≠ f → group e = group f →
      ∀ p ∈ Global.line (lineId e) \ Global.line (lineId f), label p = value e) :
    ∃ S : Finset (Fin 13), 10 + (S.image label).card ≤ S.card := by
  classical
  by_cases hvalues : ∀ e : Fin 5, e ≠ d → value e = c
  · apply linewise_rank lineId hinj label (fun _ => c)
    intro e p hp
    by_cases hpd : p ∈ Global.line (lineId d)
    · exact hcentral p hpd
    have hed : e ≠ d := by intro h; exact hpd (h ▸ hp)
    exact (houtside e hed p (Finset.mem_sdiff.mpr ⟨hp, hpd⟩)).trans (hvalues e hed)
  push Not at hvalues
  obtain ⟨e, hed, hbad⟩ := hvalues
  have family_pencil (f : Fin 5) (hfd : f ≠ d) (hbadf : value f ≠ c) :
      ∃ p ∈ Global.line (lineId f), p ∈ Global.line (lineId d) ∧
        (∀ k : Fin 5, group k = group f → p ∈ Global.line (lineId k)) := by
    obtain ⟨p, hpf, hpd⟩ := (Bridge.pair_geometry (lineId f) (lineId d)
      (fun h => hfd (hinj h))).2
    refine ⟨p, hpf, hpd, ?_⟩
    intro k hgroup
    by_cases hfk : f = k
    · simpa [hfk] using hpf
    by_contra hpk
    have hv := hsame f k hfk hgroup.symm p (Finset.mem_sdiff.mpr ⟨hpf, hpk⟩)
    exact hbadf (hv.symm.trans (hcentral p hpd))
  obtain ⟨a, hae, had, hA⟩ := family_pencil e hed hbad
  obtain ⟨n, han⟩ := ParentRankGeometry.five_lines_not_all_through lineId hinj a
  have hnd : n ≠ d := by intro h; exact han (h.symm ▸ had)
  have hne : n ≠ e := by intro h; exact han (h.symm ▸ hae)
  have hgroups : group n ≠ group e := by intro h; exact han (hA n h)
  obtain ⟨q, hqe, hqn⟩ := (Bridge.pair_geometry (lineId e) (lineId n)
    (fun h => hne (hinj h).symm)).2
  have hqd : q ∉ Global.line (lineId d) := by
    intro hqd
    have hqa := line_inter_unique (lineId e) (lineId d) (fun h => hed (hinj h))
      q a hqe hqd hae had
    exact han (hqa ▸ hqn)
  have hvn : value n = value e :=
    (houtside n hnd q (Finset.mem_sdiff.mpr ⟨hqn, hqd⟩)).symm.trans
      (houtside e hed q (Finset.mem_sdiff.mpr ⟨hqe, hqd⟩))
  have hbadn : value n ≠ c := fun h => hbad (hvn.symm.trans h)
  obtain ⟨b, hbn, hbd, hB⟩ := family_pencil n hnd hbadn
  have hab : a ≠ b := by intro h; exact han (h.symm ▸ hbn)
  have hgroupcases (f : Fin 5) : group f = group e ∨ group f = group n := by
    cases hf : group f <;> cases he : group e <;> cases hn : group n <;> simp_all
  have hfamily (f : Fin 5) : a ∈ Global.line (lineId f) ∨ b ∈ Global.line (lineId f) := by
    rcases hgroupcases f with hf | hf
    · exact Or.inl (hA f hf)
    · exact Or.inr (hB f hf)
  have hval (f : Fin 5) (hfd : f ≠ d) : value f = value e := by
    have common (k : Fin 5) (hkd : k ≠ d) (x y : Fin 13) (hxy : x ≠ y)
        (hxf : x ∈ Global.line (lineId f)) (hxd : x ∈ Global.line (lineId d))
        (hyk : y ∈ Global.line (lineId k)) (hyd : y ∈ Global.line (lineId d)) :
        value f = value k := by
      have hfk : f ≠ k := by
        intro h
        have hxy' := line_inter_unique (lineId f) (lineId d) (fun h => hfd (hinj h))
          x y hxf hxd (h.symm ▸ hyk) hyd
        exact hxy hxy'
      obtain ⟨z, hzf, hzk⟩ := (Bridge.pair_geometry (lineId f) (lineId k)
        (fun h => hfk (hinj h))).2
      have hzd : z ∉ Global.line (lineId d) := by
        intro hzd
        have hzx := line_inter_unique (lineId f) (lineId d) (fun h => hfd (hinj h))
          z x hzf hzd hxf hxd
        have hzy := line_inter_unique (lineId k) (lineId d) (fun h => hkd (hinj h))
          z y hzk hzd hyk hyd
        exact hxy (hzx.symm.trans hzy)
      exact (houtside f hfd z (Finset.mem_sdiff.mpr ⟨hzf, hzd⟩)).symm.trans
        (houtside k hkd z (Finset.mem_sdiff.mpr ⟨hzk, hzd⟩))
    rcases hgroupcases f with hf | hf
    · exact (common n hnd a b hab (hA f hf) had hbn hbd).trans hvn
    · exact common e hed b a hab.symm (hB f hf) hbd hae had
  let S := Finset.univ.biUnion (fun f : Fin 5 => Global.line (lineId f))
  have hS : 12 ≤ S.card := pencil_pair_union_card lineId hinj d a b hab had hbd hfamily
  have himage : S.image label ⊆ {c, value e} := by
    intro v hv
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨f, _, hpf⟩ := Finset.mem_biUnion.mp hp
    by_cases hpd : p ∈ Global.line (lineId d)
    · exact Finset.mem_insert.mpr (Or.inl (hcentral p hpd))
    have hfd : f ≠ d := by intro h; exact hpd (h ▸ hpf)
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr
      ((houtside f hfd p (Finset.mem_sdiff.mpr ⟨hpf, hpd⟩)).trans (hval f hfd))))
  have hcard : (S.image label).card ≤ 2 := by
    have h := Finset.card_le_card himage
    have hpair : ({c, value e} : Finset ℕ).card ≤ 2 := by
      by_cases hce : c = value e
      · simp [hce]
      · rw [Finset.card_pair hce]
    omega
  exact ⟨S, by omega⟩


lemma unique_core_rank
    (parent : Fin 5 → Bool → ℕ) (lineId : Fin 5 → Fin 13)
    (hinj : Function.Injective lineId) (hconn : Connected parent)
    (label : Fin 13 → ℕ) (wire : ℕ → ℕ)
    (hforce : ∀ e f : Fin 5, e ≠ f → ∀ a b : Bool, parent e a = parent f b →
      ∀ p ∈ Global.line (lineId e) \ Global.line (lineId f),
        label p = wire (parent e (!a)))
    (d : Fin 5) (hd : CoreEdge parent d)
    (hunique : ∀ e : Fin 5, CoreEdge parent e → e = d) :
    ∃ S : Finset (Fin 13), 10 + (S.image label).card ≤ S.card := by
  classical
  by_cases hstar : ∃ v : ℕ, ∃ side : Fin 5 → Bool, ∀ e : Fin 5, parent e (side e) = v
  · obtain ⟨v, side, hs⟩ := hstar
    exact star_rank parent lineId hinj label wire hforce v side hs
  obtain ⟨c, hcommon⟩ := nonleaf_values_equal parent lineId hinj hconn label wire hforce
  choose anchor hanchor using edge_has_nonleaf parent hconn
  have hex (e : Fin 5) : ∃ b : Bool, parent e (anchor e) = parent d b := by
    obtain ⟨k, ⟨b, hkb⟩, hkc⟩ := core_neighbor_of_not_star parent hconn hstar
      (parent e (anchor e)) (hanchor e)
    exact ⟨b, hkb.symm.trans (congrArg (fun k => parent k b) (hunique k hkc))⟩
  choose arm harm using hex
  apply grouped_rank lineId hinj d arm label (fun e => wire (parent e (!(anchor e)))) c
  · exact core_points parent lineId hinj hconn label wire hforce c hcommon d hd
  · intro e hed p hp
    exact hforce e d hed (anchor e) (arm e) (harm e) p hp
  · intro e f hef hgroup p hp
    have hab : parent e (anchor e) = parent f (anchor f) :=
      (harm e).trans ((congrArg (fun b => parent d b) hgroup).trans (harm f).symm)
    exact hforce e f hef (anchor e) (anchor f) hab p hp

lemma connected_rank
    (parent : Fin 5 → Bool → ℕ) (lineId : Fin 5 → Fin 13)
    (hinj : Function.Injective lineId) (hconn : Connected parent)
    (label : Fin 13 → ℕ) (wire : ℕ → ℕ)
    (hforce : ∀ e f : Fin 5, e ≠ f → ∀ a b : Bool, parent e a = parent f b →
      ∀ p ∈ Global.line (lineId e) \ Global.line (lineId f),
        label p = wire (parent e (!a))) :
    ∃ S : Finset (Fin 13), 10 + (S.image label).card ≤ S.card := by
  classical
  by_cases hstar : ∃ v : ℕ, ∃ side : Fin 5 → Bool, ∀ e : Fin 5, parent e (side e) = v
  · obtain ⟨v, side, hs⟩ := hstar
    exact star_rank parent lineId hinj label wire hforce v side hs
  obtain ⟨a, ha⟩ := edge_has_nonleaf parent hconn 0
  obtain ⟨d, _, hd⟩ := core_neighbor_of_not_star parent hconn hstar (parent 0 a) ha
  by_cases htwo : ∃ e : Fin 5, e ≠ d ∧ CoreEdge parent e
  · obtain ⟨e, hed, he⟩ := htwo
    exact two_core_edges_rank parent lineId hinj hconn label wire hforce d e hed.symm hd he
  have hunique (e : Fin 5) (he : CoreEdge parent e) : e = d := by
    by_contra hed
    exact htwo ⟨e, hed, he⟩
  exact unique_core_rank parent lineId hinj hconn label wire hforce d hd hunique

end PEqualNP.Outside.L_meta_1024_aux.ParentRankCore

namespace PEqualNP.Outside.L_meta_1024_aux.ParentRankCore

open PEqualNP.CircuitLowerBounds

lemma rank_univ {M : ℕ} (label : Fin M → ℕ) (S : Finset (Fin M)) (k : ℕ)
    (hS : k + (S.image label).card ≤ S.card) :
    k + ((Finset.univ : Finset (Fin M)).image label).card ≤ M := by
  classical
  let T := Finset.univ \ S
  have hST : S ∪ T = Finset.univ := by
    ext p
    simp [T]
  have htotal : S.card + T.card = M := by
    have hle : S.card ≤ M := by
      simpa using Finset.card_le_card (Finset.subset_univ S)
    dsimp [T]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  have himage : ((Finset.univ : Finset (Fin M)).image label).card ≤
      (S.image label).card + T.card := by
    calc
      _ = (S.image label ∪ T.image label).card := by rw [← Finset.image_union, hST]
      _ ≤ (S.image label).card + (T.image label).card := Finset.card_union_le _ _
      _ ≤ (S.image label).card + T.card := Nat.add_le_add_left (Finset.card_image_le) _
  omega

lemma connected_gate_bound
    (gs : List Gate) (hg : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (parent : Fin 5 → Bool → ℕ) (lineId : Fin 5 → Fin 13)
    (hinj : Function.Injective lineId) (hconn : Connected parent)
    (hdepends : ∀ e f : Fin 5, e ≠ f → ∀ a b : Bool, parent e a = parent f b →
      ∀ p ∈ Global.line (lineId e) \ Global.line (lineId f),
        Cut.Depends 13 ∅ gs (parent e (!a)) p) :
    10 ≤ gs.length := by
  classical
  obtain ⟨label, wire, hcount, hdep⟩ :=
    Cut.components 13 ∅ (Finset.univ : Finset (Fin 13)) gs hg
  obtain ⟨S, hS⟩ := connected_rank parent lineId hinj hconn label wire
    (fun e f hef a b hab p hp => hdep _ _ (hdepends e f hef a b hab p hp))
  have hrank := rank_univ label S 10 hS
  have hcost : 13 ≤ ((Finset.univ : Finset (Fin 13)).image label).card + gs.length := by
    simpa [Cut.unpaid] using hcount
  omega

lemma connected_or_pairs_bound
    (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (parent : Fin 5 → Bool → ℕ) (lineId : Fin 5 → Fin 13)
    (hinj : Function.Injective lineId) (hconn : Connected parent)
    (hcorrect : ∀ e (x : Fin 13 → Bool), Support.Band x →
      (Cut.cutVal 13 ∅ gs x (parent e false) || Cut.cutVal 13 ∅ gs x (parent e true)) =
        Support.target (lineId e) x) :
    10 ≤ gs.length := by
  apply connected_gate_bound gs (fun g hgmem => (hg g hgmem).2) parent lineId hinj hconn
  intro e f hef a b hab p hp
  change p ∈ Support.line (lineId e) \ Support.line (lineId f) at hp
  apply FourOrSinks.shared_parent_cut_depends_band gs (parent e (!a))
    (fun g hgmem => (hg g hgmem).1) (lineId e) (lineId f) (fun h => hef (hinj h))
    (fun x => Cut.cutVal 13 ∅ gs x (parent e a))
  · intro x hx
    cases a
    · exact hcorrect e x hx
    · simpa only [Bool.not_true, Bool.or_comm] using hcorrect e x hx
  · intro x hx hh
    have hf := hcorrect f x hx
    have hfb : Cut.cutVal 13 ∅ gs x (parent f b) = true := by simpa only [hab] using hh
    cases b
    · simpa only [hfb, Bool.true_or] using hf.symm
    · simpa only [hfb, Bool.or_true] using hf.symm
  · exact hp

lemma or_pairs_disconnected
    (gs : List Gate) (hsmall : gs.length ≤ 9)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (parent : Fin 5 → Bool → ℕ) (lineId : Fin 5 → Fin 13)
    (hinj : Function.Injective lineId)
    (hcorrect : ∀ e (x : Fin 13 → Bool), Support.Band x →
      (Cut.cutVal 13 ∅ gs x (parent e false) || Cut.cutVal 13 ∅ gs x (parent e true)) =
        Support.target (lineId e) x) :
    ¬ Connected parent := by
  intro hconn
  have h := connected_or_pairs_bound gs hg parent lineId hinj hconn hcorrect
  omega


lemma left_right_disconnected
    (gs : List Gate) (hsmall : gs.length ≤ 9)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (lineId : Fin 5 → Fin 13) (hinj : Function.Injective lineId)
    (left right : Fin 5 → ℕ)
    (hcorrect : ∀ e (x : Fin 13 → Bool), Support.Band x →
      (Cut.cutVal 13 ∅ gs x (left e) || Cut.cutVal 13 ∅ gs x (right e)) =
        Support.target (lineId e) x) :
    ¬ Connected (fun e b => if b then right e else left e) := by
  apply or_pairs_disconnected gs hsmall hg
    (fun e b => if b then right e else left e) lineId hinj
  exact hcorrect

lemma eight_ordinary_disconnected_reduction (gs : List Gate) (out : Fin 13 → ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hsmall : gs.length ≤ 38)
    (hcorrect : ∀ w (x : Fin 13 → Bool), Support.Band x →
      Global.val gs x (out w) = Support.target w x)
    (W : Finset (Fin 13)) (hW : 8 ≤ W.card)
    (hordinary : ∀ w ∈ W, ∀ x : Fin 13 → Bool,
      Global.val gs x (out w) = Support.target w x) :
    ∃ (I : List Gate) (lineId : Fin 5 → Fin 13) (left right : Fin 5 → ℕ),
      Function.Injective lineId ∧ I.length ≤ 9 ∧
      (∀ g ∈ I, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      (∀ u (x : Fin 13 → Bool), Support.Band x →
        (Cut.cutVal 13 ∅ I x (left u) || Cut.cutVal 13 ∅ I x (right u)) = Support.target (lineId u) x) ∧
      (∀ u (x : Fin 13 → Bool), Support.target (lineId u) x = false →
        (Cut.cutVal 13 ∅ I x (left u) || Cut.cutVal 13 ∅ I x (right u)) = false) ∧
      (∀ u, ¬ ∀ x : Fin 13 → Bool,
        (Cut.cutVal 13 ∅ I x (left u) || Cut.cutVal 13 ∅ I x (right u)) = Support.target (lineId u) x) ∧
      ¬ Connected (fun e b => if b then right e else left e) := by
  obtain ⟨I, lineId, left, right, hinj, hI, hIg, hIc, hIb, hIn⟩ :=
    FourReduction.eight_ordinary_reduction gs out hg hsmall hcorrect W hW hordinary
  exact ⟨I, lineId, left, right, hinj, hI, hIg, hIc, hIb, hIn,
    left_right_disconnected I hI hIg lineId hinj left right hIc⟩

end PEqualNP.Outside.L_meta_1024_aux.ParentRankCore

namespace PEqualNP.Outside.L_meta_1024_aux.ParentRankCore

open PEqualNP.CircuitLowerBounds

def canonicalWire (gs : List Gate) (i : ℕ) : ℕ :=
  if i < 13 + gs.length then i else 22

def canonicalParent (gs : List Gate) (parent : Fin 5 → Bool → ℕ) (e : Fin 5) (b : Bool) : ℕ :=
  if b then
    if canonicalWire gs (parent e true) = canonicalWire gs (parent e false) then 22
    else canonicalWire gs (parent e true)
  else canonicalWire gs (parent e false)

lemma canonical_wire_value (gs : List Gate) (hsmall : gs.length ≤ 9)
    (x : Fin 13 → Bool) (i : ℕ) :
    Cut.cutVal 13 ∅ gs x (canonicalWire gs i) = Cut.cutVal 13 ∅ gs x i := by
  by_cases hi : i < 13 + gs.length
  · simp [canonicalWire, hi]
  · simp only [canonicalWire, hi, ite_false]
    rw [Cut.cutVal_invalid _ _ _ _ _ (by omega), Cut.cutVal_invalid _ _ _ _ _ (by omega)]

lemma canonical_pair_value (gs : List Gate) (hsmall : gs.length ≤ 9)
    (parent : Fin 5 → Bool → ℕ) (e : Fin 5) (x : Fin 13 → Bool) :
    (Cut.cutVal 13 ∅ gs x (canonicalParent gs parent e false) ||
      Cut.cutVal 13 ∅ gs x (canonicalParent gs parent e true)) =
    (Cut.cutVal 13 ∅ gs x (parent e false) || Cut.cutVal 13 ∅ gs x (parent e true)) := by
  have hz : Cut.cutVal 13 ∅ gs x 22 = false := Cut.cutVal_invalid _ _ _ _ _ (by omega)
  have hl := canonical_wire_value gs hsmall x (parent e false)
  have hr := canonical_wire_value gs hsmall x (parent e true)
  by_cases h : canonicalWire gs (parent e true) = canonicalWire gs (parent e false)
  · simp [canonicalParent, h, hz, ← hl, ← hr]
  · simp [canonicalParent, h, hl, hr]

lemma canonical_parent_bound (gs : List Gate) (hsmall : gs.length ≤ 9)
    (parent : Fin 5 → Bool → ℕ) (e : Fin 5) (b : Bool) :
    canonicalParent gs parent e b ≤ 22 := by
  have hw (i : ℕ) : canonicalWire gs i ≤ 22 := by
    unfold canonicalWire
    split_ifs <;> omega
  cases b
  · exact hw _
  · dsimp only [canonicalParent]
    split_ifs
    · exact Nat.le_refl _
    · exact hw _
    · exact hw _

lemma canonical_parent_valid (gs : List Gate) (parent : Fin 5 → Bool → ℕ)
    (e : Fin 5) (b : Bool) (h : canonicalParent gs parent e b ≠ 22) :
    canonicalParent gs parent e b < 13 + gs.length := by
  have hw (i : ℕ) (hi : canonicalWire gs i ≠ 22) : canonicalWire gs i < 13 + gs.length := by
    unfold canonicalWire at *
    split_ifs at * <;> omega
  cases b
  · exact hw _ h
  · dsimp only [canonicalParent] at *
    split_ifs at *
    · exact False.elim (h rfl)
    · exact hw _ h
    · exact hw _ h

lemma canonical_pair_distinct (gs : List Gate) (hsmall : gs.length ≤ 9)
    (parent : Fin 5 → Bool → ℕ) (lineId : Fin 5 → Fin 13)
    (hcorrect : ∀ e (x : Fin 13 → Bool), Support.Band x →
      (Cut.cutVal 13 ∅ gs x (parent e false) || Cut.cutVal 13 ∅ gs x (parent e true)) =
        Support.target (lineId e) x) (e : Fin 5) :
    canonicalParent gs parent e false ≠ canonicalParent gs parent e true := by
  intro heq
  have hzleft : canonicalParent gs parent e false = 22 := by
    dsimp [canonicalParent] at heq ⊢
    split_ifs at heq with h
    · exact heq
    · exact False.elim (h heq.symm)
  have hzright : canonicalParent gs parent e true = 22 := heq.symm.trans hzleft
  have hne : (Support.line (lineId e)).Nonempty := by
    apply Finset.card_pos.mp
    change 0 < (Global.line (lineId e)).card
    rw [Global.line_card]
    decide
  obtain ⟨p, hp⟩ := hne
  let x := Support.flip (lineId e) p
  have hx : Support.Band x := Or.inl (Support.flip_spec (lineId e) p hp).1
  have ht : Support.target (lineId e) x = true := (Support.flip_spec (lineId e) p hp).2
  have hf := (canonical_pair_value gs hsmall parent e x).trans (hcorrect e x hx)
  rw [hzleft, hzright, Cut.cutVal_invalid _ _ _ _ _ (by omega), ht] at hf
  exact Bool.noConfusion hf

lemma target_pairs_distinct (gs : List Gate)
    (parent : Fin 5 → Bool → ℕ) (lineId : Fin 5 → Fin 13)
    (hinj : Function.Injective lineId)
    (hcorrect : ∀ e (x : Fin 13 → Bool), Support.Band x →
      (Cut.cutVal 13 ∅ gs x (parent e false) || Cut.cutVal 13 ∅ gs x (parent e true)) =
        Support.target (lineId e) x)
    (e f : Fin 5) (hef : e ≠ f) :
    ¬ ((parent e false = parent f false ∧ parent e true = parent f true) ∨
      (parent e false = parent f true ∧ parent e true = parent f false)) := by
  intro hpairs
  let x := Support.row (lineId e)
  have hx : Support.Band x := Or.inr (Support.row_spec (lineId e)).1
  have he := hcorrect e x hx
  have hf := hcorrect f x hx
  have hxe : Support.target (lineId e) x = false := (Support.row_spec (lineId e)).2
  have hxf : Support.target (lineId f) x = true :=
    Bridge.row_targets (lineId e) (lineId f) (fun h => hef (hinj h))
  have heq : (Cut.cutVal 13 ∅ gs x (parent e false) || Cut.cutVal 13 ∅ gs x (parent e true)) =
      (Cut.cutVal 13 ∅ gs x (parent f false) || Cut.cutVal 13 ∅ gs x (parent f true)) := by
    rcases hpairs with ⟨hl, hr⟩ | ⟨hl, hr⟩
    · rw [hl, hr]
    · rw [hl, hr, Bool.or_comm]
  rw [he, hf, hxe, hxf] at heq
  exact Bool.noConfusion heq

lemma canonical_correct (gs : List Gate) (hsmall : gs.length ≤ 9)
    (parent : Fin 5 → Bool → ℕ) (lineId : Fin 5 → Fin 13)
    (hcorrect : ∀ e (x : Fin 13 → Bool), Support.Band x →
      (Cut.cutVal 13 ∅ gs x (parent e false) || Cut.cutVal 13 ∅ gs x (parent e true)) =
        Support.target (lineId e) x) :
    ∀ e (x : Fin 13 → Bool), Support.Band x →
      (Cut.cutVal 13 ∅ gs x (canonicalParent gs parent e false) ||
        Cut.cutVal 13 ∅ gs x (canonicalParent gs parent e true)) = Support.target (lineId e) x := by
  intro e x hx
  exact (canonical_pair_value gs hsmall parent e x).trans (hcorrect e x hx)

lemma canonical_disconnected (gs : List Gate) (hsmall : gs.length ≤ 9)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (parent : Fin 5 → Bool → ℕ) (lineId : Fin 5 → Fin 13)
    (hinj : Function.Injective lineId)
    (hcorrect : ∀ e (x : Fin 13 → Bool), Support.Band x →
      (Cut.cutVal 13 ∅ gs x (parent e false) || Cut.cutVal 13 ∅ gs x (parent e true)) =
        Support.target (lineId e) x) :
    ¬ Connected (canonicalParent gs parent) :=
  or_pairs_disconnected gs hsmall hg (canonicalParent gs parent) lineId hinj
    (canonical_correct gs hsmall parent lineId hcorrect)

end PEqualNP.Outside.L_meta_1024_aux.ParentRankCore

namespace PEqualNP.Outside.L_meta_1024_aux.Ancestry

open PEqualNP.CircuitLowerBounds

def step (w : List (Finset ℕ)) (g : Gate) : List (Finset ℕ) :=
  w ++ [insert w.length (g.inputs.toFinset.biUnion fun i => w.getD i ∅)]

def run (gs : List Gate) : List (Finset ℕ) :=
  gs.foldl step (List.ofFn fun i : Fin 13 => ({i.val} : Finset ℕ))

def anc (gs : List Gate) (i : ℕ) : Finset ℕ := (run gs).getD i ∅

lemma fold_length (gs : List Gate) (w : List (Finset ℕ)) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp only [List.foldl_cons, ih, List.length_cons, step,
      List.length_append, List.length_cons, List.length_nil]; omega

lemma run_length (gs : List Gate) : (run gs).length = 13 + gs.length := by
  simp [run, fold_length]

lemma anc_nil (i : ℕ) : anc [] i = if i < 13 then {i} else ∅ := by
  have hgen {n : ℕ} (k : ℕ) :
      (List.ofFn fun p : Fin n => ({p.val} : Finset ℕ)).getD k ∅ =
        if k < n then {k} else ∅ := by
    by_cases hk : k < n <;> simp [List.getD_eq_getElem?_getD, hk]
  exact hgen i

lemma anc_snoc (gs : List Gate) (g : Gate) (i : ℕ) :
    anc (gs ++ [g]) i = if i = 13 + gs.length then
      insert i (g.inputs.toFinset.biUnion fun j => anc gs j) else anc gs i := by
  unfold anc run
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, step]
  have hl : (gs.foldl step (List.ofFn fun i : Fin 13 => ({i.val} : Finset ℕ))).length =
      13 + gs.length := by rw [fold_length]; simp
  rcases lt_trichotomy i (13 + gs.length) with h | h | h
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  · rw [if_pos h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp only [hl, h, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by rw [List.length_append, hl]; simp only [List.length_singleton]; omega),
      List.getElem?_eq_none (by omega)]

lemma anc_invalid (gs : List Gate) (i : ℕ) (hi : 13 + gs.length ≤ i) : anc gs i = ∅ := by
  exact List.getD_eq_default _ _ (by simpa only [run_length] using hi)

lemma anc_input (gs : List Gate) (i : ℕ) (hi : i < 13) : anc gs i = {i} := by
  induction gs using List.reverseRecOn with
  | nil => simp [anc_nil, hi]
  | append_singleton gs g ih => rw [anc_snoc, if_neg (by omega), ih]

lemma anc_bound (gs : List Gate) (i j : ℕ) (hj : j ∈ anc gs i) :
    j ≤ i ∧ j < 13 + gs.length := by
  induction gs using List.reverseRecOn generalizing i j with
  | nil =>
    rw [anc_nil] at hj
    split_ifs at hj with hi
    · have he : j = i := by simpa using hj
      subst j
      exact ⟨le_rfl, by simpa using hi⟩
    · simp at hj
  | append_singleton gs g ih =>
    rw [anc_snoc] at hj
    by_cases hi : i = 13 + gs.length
    · rw [if_pos hi] at hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · simp only [List.length_append, List.length_singleton]; omega
      · obtain ⟨k, hk, hj⟩ := Finset.mem_biUnion.mp hj
        have hb := ih k j hj
        simp only [List.length_append, List.length_singleton]
        omega
    · rw [if_neg hi] at hj
      have hb := ih i j hj
      simp only [List.length_append, List.length_singleton]
      omega

lemma ancestor_trans (gs : List Gate) (i j : ℕ) (hj : j ∈ anc gs i) :
    anc gs j ⊆ anc gs i := by
  induction gs using List.reverseRecOn generalizing i j with
  | nil =>
    have hb := anc_bound [] i j hj
    rw [anc_input [] j (by simpa using hb.2)]
    exact Finset.singleton_subset_iff.mpr hj
  | append_singleton gs g ih =>
    have hb := anc_bound (gs ++ [g]) i j hj
    by_cases hij : j = i
    · subst j; exact Finset.Subset.refl _
    by_cases hi : i = 13 + gs.length
    · rw [anc_snoc gs g i, if_pos hi] at hj ⊢
      have hjold : j < 13 + gs.length := by omega
      rw [anc_snoc, if_neg (by omega)]
      obtain ⟨k, hk, hjk⟩ := Finset.mem_biUnion.mp ((Finset.mem_insert.mp hj).resolve_left hij)
      intro p hp
      exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨k, hk, ih k j hjk hp⟩)
    · rw [anc_snoc gs g i, if_neg hi] at hj ⊢
      have hjold := (anc_bound gs i j hj).2
      rw [anc_snoc, if_neg (by omega)]
      exact ih i j hj

lemma depends_mem {M : ℕ} (P : Finset ℕ) (gs : List Gate) (i : ℕ) (t : Fin M)
    (ht : Cut.Depends 13 P gs i t) : t.val ∈ anc gs i := by
  induction gs using List.reverseRecOn generalizing i t with
  | nil =>
    obtain ⟨x, y, hxy, hne⟩ := ht
    rw [Cut.cutVal_nil, Cut.cutVal_nil] at hne
    by_cases hi : i < 13
    · simp only [hi, ite_true] at hne
      have he := Cut.source_dep x y i t hxy hne
      simp [anc_nil, hi, he]
    · simp [hi] at hne
  | append_singleton gs g ih =>
    obtain ⟨x, y, hxy, hne⟩ := ht
    rw [Cut.cutVal_snoc, Cut.cutVal_snoc] at hne
    by_cases hi : i = 13 + gs.length
    · rw [if_pos hi, if_pos hi] at hne
      rw [anc_snoc, if_pos hi]
      by_cases hp : i ∈ P
      · simp only [← hi, hp, ite_true] at hne
        have he := Cut.source_dep x y i t hxy hne
        simpa only [he] using Finset.mem_insert_self i (g.inputs.toFinset.biUnion fun j => anc gs j)
      · simp only [← hi, hp, ite_false] at hne
        have hex : ∃ j ∈ g.inputs,
            Cut.cutVal 13 P gs x j ≠ Cut.cutVal 13 P gs y j := by
          by_contra! hh
          apply hne
          congr 1
          exact List.map_congr_left hh
        obtain ⟨j, hj, hne⟩ := hex
        exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr
          ⟨j, by simpa using hj, ih j t ⟨x, y, hxy, hne⟩⟩)
    · rw [if_neg hi, if_neg hi] at hne
      rw [anc_snoc, if_neg hi]
      exact ih i t ⟨x, y, hxy, hne⟩

lemma components (S : Finset (Fin 13)) (gs : List Gate)
    (hg : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    ∃ (label : Fin 13 → ℕ) (wire : ℕ → ℕ),
      S.card ≤ (S.image label).card + gs.length ∧
      (∀ p : Fin 13, wire p.val = label p) ∧
      ∀ i j, j ∈ anc gs i → wire j = wire i := by
  classical
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨Fin.val, id, ?_, fun _ => rfl, ?_⟩
    · simp [Finset.card_image_of_injective _ Fin.val_injective]
    · intro i j hj
      rw [anc_nil] at hj
      split_ifs at hj with hi
      · simpa using hj
      · simp at hj
  | append_singleton gs g ih =>
    obtain ⟨label, wire, hc, hr, ha⟩ := ih (fun q hq => hg q (by simp [hq]))
    obtain ⟨a, b, hins⟩ := Cut.two_inputs g.inputs (hg g (by simp))
    let merge (k : ℕ) := if k = wire b then wire a else k
    have hma : merge (wire a) = wire a := by simp [merge]
    have hmb : merge (wire b) = wire a := by simp [merge]
    refine ⟨merge ∘ label, fun i => if i = 13 + gs.length then wire a else merge (wire i),
      ?_, ?_, ?_⟩
    · have hsub : S.image label ⊆ insert (wire b) (S.image (merge ∘ label)) := by
        intro v hv
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hv
        by_cases he : label t = wire b
        · simp [he]
        · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨t, ht, by simp [merge, he]⟩)
      have hcard := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
      simp only [List.length_append, List.length_singleton]
      omega
    · intro p
      change (if p.val = 13 + gs.length then wire a else merge (wire p.val)) = merge (label p)
      rw [if_neg (by omega), hr]
    · intro i j hj
      change (if j = 13 + gs.length then wire a else merge (wire j)) =
        (if i = 13 + gs.length then wire a else merge (wire i))
      rw [anc_snoc] at hj
      by_cases hi : i = 13 + gs.length
      · rw [if_pos hi] at hj ⊢
        rcases Finset.mem_insert.mp hj with rfl | hj
        · simp [hi]
        · obtain ⟨k, hk, hjk⟩ := Finset.mem_biUnion.mp hj
          have hjold := (anc_bound gs k j hjk).2
          rw [if_neg (by omega), ha k j hjk]
          rcases hins k (by simpa using hk) with rfl | rfl
          · exact hma
          · exact hmb
      · rw [if_neg hi] at hj ⊢
        have hjold := (anc_bound gs i j hj).2
        rw [if_neg (by omega), ha i j hj]

end PEqualNP.Outside.L_meta_1024_aux.Ancestry

namespace PEqualNP.Outside.L_meta_1024_aux.TwoPairs

open PEqualNP.CircuitLowerBounds

lemma pair_zero (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w : Fin 13) (i j : ℕ)
    (hc : ∀ x, Support.Band x →
      (Cut.cutVal 13 ∅ gs x i || Cut.cutVal 13 ∅ gs x j) = Support.target w x) :
    (Cut.cutVal 13 ∅ gs (fun _ : Fin 13 => false) i || Cut.cutVal 13 ∅ gs (fun _ : Fin 13 => false) j) = false := by
  have hr := Support.row_spec w
  have he := hc (Support.row w) (Or.inr hr.1)
  rw [hr.2] at he
  apply Bool.eq_false_iff.mpr
  intro ht
  rcases Bool.or_eq_true_iff.mp ht with ht | ht
  · have h := Cut.cutVal_mono 13 ∅ gs hg (fun _ : Fin 13 => false) (Support.row w)
      (by simp) i ht
    simp [h] at he
  · have h := Cut.cutVal_mono 13 ∅ gs hg (fun _ : Fin 13 => false) (Support.row w)
      (by simp) j ht
    simp [h] at he

lemma missing_gate_exact (gs : List Gate) (hlen : gs.length ≤ 6)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : Fin 13) (i j k : ℕ) (hk : 13 ≤ k ∧ k < 13 + gs.length)
    (hki : k ∉ Ancestry.anc gs i) (hkj : k ∉ Ancestry.anc gs j)
    (hc : ∀ x, Support.Band x →
      (Cut.cutVal 13 ∅ gs x i || Cut.cutVal 13 ∅ gs x j) = Support.target w x) :
    ∀ x, (Cut.cutVal 13 ∅ gs x i || Cut.cutVal 13 ∅ gs x j) = Support.target w x := by
  classical
  let g : Gate := ⟨GateOp.or, [i, j]⟩
  let code := gs ++ [g]
  let o := 13 + gs.length
  have hval (x : Fin 13 → Bool) : Cut.cutVal 13 ∅ code x o =
      (Cut.cutVal 13 ∅ gs x i || Cut.cutVal 13 ∅ gs x j) := by
    rw [Cut.cutVal_snoc]
    simp [o, g, GateOp.eval]
  have hcode : ∀ q ∈ code, (q.op = GateOp.and ∨ q.op = GateOp.or) ∧ q.inputs.length ≤ 2 := by
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hg q hq
    · have he : q = g := by simpa using hq
      subst q
      simp [g]
  let E := Cut.essential (M := 13 + code.length) 13 {k} code o
  have hraw : ∀ t ∈ E, t.val < 13 := by
    intro t ht
    rcases Cut.essential_sources 13 {k} code o t ht with h | h
    · exact h
    · have he : t.val = k := by simpa using h
      have ha := Ancestry.depends_mem {k} code o t (Finset.mem_filter.mp ht).2
      rw [he, Ancestry.anc_snoc, if_pos rfl] at ha
      simp [g, o, ne_of_lt hk.2, hki, hkj] at ha
  have hcard : E.card ≤ 7 := by
    have hb := Cut.essential_bound (M := 13 + code.length) 13 {k} code o
      (fun q hq => (hcode q hq).2) (by
        intro a ha
        have he : a = k := by simpa using ha
        subst a
        exact Finset.mem_Ico.mpr ⟨hk.1, by simp [code]; omega⟩)
    simp only [Finset.card_singleton] at hb
    have hl : code.length ≤ 7 := by simp [code]; omega
    change (Cut.essential (M := 13 + code.length) 13 {k} code o).card ≤ 7
    omega
  obtain ⟨S, hS, hs⟩ := Cut.raw_support_exists {k} code o 7 hraw hcard
  have hb : ∀ x, Support.Band x → Circuit.eval ⟨code, o⟩ (List.ofFn x) = Support.target w x := by
    intro x hx
    rw [← Cut.cut_empty, hval]
    exact hc x hx
  have he := Support.circuit_support_exact code o w (fun q hq => (hcode q hq).1) hb S hS hs
  intro x
  rw [← hval, Cut.cut_empty, he]

lemma all_ancestors (gs : List Gate) (hlen : gs.length ≤ 6)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : Fin 13) (i j : ℕ)
    (hc : ∀ x, Support.Band x →
      (Cut.cutVal 13 ∅ gs x i || Cut.cutVal 13 ∅ gs x j) = Support.target w x)
    (hne : ¬ ∀ x, (Cut.cutVal 13 ∅ gs x i || Cut.cutVal 13 ∅ gs x j) = Support.target w x)
    (k : ℕ) (hk : 13 ≤ k ∧ k < 13 + gs.length) :
    k ∈ Ancestry.anc gs i ∪ Ancestry.anc gs j := by
  by_contra hm
  simp only [Finset.mem_union, not_or] at hm
  exact hne (missing_gate_exact gs hlen hg w i j k hk hm.1 hm.2 hc)

lemma ancestor_pair_exact (gs : List Gate) (hlen : gs.length ≤ 6)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : Fin 13) (i j : ℕ) (hij : j ∈ Ancestry.anc gs i)
    (hc : ∀ x, Support.Band x →
      (Cut.cutVal 13 ∅ gs x i || Cut.cutVal 13 ∅ gs x j) = Support.target w x) :
    ∀ x, (Cut.cutVal 13 ∅ gs x i || Cut.cutVal 13 ∅ gs x j) = Support.target w x := by
  classical
  let E := Cut.essential (M := 13) 13 ∅ gs i ∪ Cut.essential (M := 13) 13 ∅ gs j
  obtain ⟨label, wire, hcard, hraw, ha⟩ := Ancestry.components E gs (fun q hq => (hg q hq).2)
  have heq : wire j = wire i := ha i j hij
  have hlabel : ∀ p ∈ E, label p = wire i := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact (hraw p).symm.trans (ha i p.val
        (Ancestry.depends_mem ∅ gs i p (Finset.mem_filter.mp hp).2))
    · exact (hraw p).symm.trans ((ha j p.val
        (Ancestry.depends_mem ∅ gs j p (Finset.mem_filter.mp hp).2)).trans heq)
  have himage : (E.image label).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hb
    exact (hlabel p hp).trans (hlabel q hq).symm
  have hE : E.card ≤ 7 := by omega
  apply Support.small_support_exact w _ hc (pair_zero gs (fun q hq => (hg q hq).1) w i j hc) E hE
  intro x y hxy
  have hi := Cut.essential_supports 13 ∅ gs i x y
    (fun p hp => hxy p (Finset.mem_union_left _ hp))
  have hj := Cut.essential_supports 13 ∅ gs j x y
    (fun p hp => hxy p (Finset.mem_union_right _ hp))
  change (Cut.cutVal 13 ∅ gs x i || Cut.cutVal 13 ∅ gs x j) =
    (Cut.cutVal 13 ∅ gs y i || Cut.cutVal 13 ∅ gs y j)
  rw [hi, hj]

lemma small_pair_exact (gs : List Gate) (hlen : gs.length ≤ 5)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : Fin 13) (i j : ℕ)
    (hc : ∀ x, Support.Band x →
      (Cut.cutVal 13 ∅ gs x i || Cut.cutVal 13 ∅ gs x j) = Support.target w x) :
    ∀ x, (Cut.cutVal 13 ∅ gs x i || Cut.cutVal 13 ∅ gs x j) = Support.target w x := by
  let ii := if i < 18 then i else 20
  let jj := if j < 18 then j else 20
  have hv (x : Fin 13 → Bool) (k : ℕ) :
      Cut.cutVal 13 ∅ gs x (if k < 18 then k else 20) = Cut.cutVal 13 ∅ gs x k := by
    split_ifs with hk
    · rfl
    · rw [FourOrSinks.cut_ge_false gs x 20 (by omega),
        FourOrSinks.cut_ge_false gs x k (by omega)]
  have hsmall := FourOrSinks.low_pair_exact gs (by omega) hg w ii jj
    (by dsimp [ii]; split_ifs <;> omega) (by dsimp [ii]; split_ifs <;> omega)
    (by dsimp [jj]; split_ifs <;> omega) (by dsimp [jj]; split_ifs <;> omega)
    (by intro x hx; simpa only [ii, jj, hv] using hc x hx)
  intro x
  simpa only [ii, jj, hv] using hsmall x

lemma last_member (gs : List Gate) (hlen : gs.length = 6) (i : ℕ)
    (hi : 18 ∈ Ancestry.anc gs i) : i = 18 := by
  have hle := (Ancestry.anc_bound gs i 18 hi).1
  by_contra hn
  have hbig : 13 + gs.length ≤ i := by omega
  rw [Ancestry.anc_invalid gs i hbig] at hi
  simp at hi

lemma two_pairs_impossible (gs : List Gate) (hlen : gs.length ≤ 6)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (u v : Fin 13) (huv : u ≠ v) (i j k l : ℕ)
    (hu : ∀ x, Support.Band x →
      (Cut.cutVal 13 ∅ gs x i || Cut.cutVal 13 ∅ gs x j) = Support.target u x)
    (hv : ∀ x, Support.Band x →
      (Cut.cutVal 13 ∅ gs x k || Cut.cutVal 13 ∅ gs x l) = Support.target v x)
    (hnu : ¬ ∀ x, (Cut.cutVal 13 ∅ gs x i || Cut.cutVal 13 ∅ gs x j) = Support.target u x)
    (hnv : ¬ ∀ x, (Cut.cutVal 13 ∅ gs x k || Cut.cutVal 13 ∅ gs x l) = Support.target v x) : False := by
  have hs : gs.length = 6 := by
    by_contra hn
    exact hnu (small_pair_exact gs (by omega) hg u i j hu)
  have hp (w : Fin 13) (a b : ℕ)
      (hc : ∀ x, Support.Band x →
        (Cut.cutVal 13 ∅ gs x a || Cut.cutVal 13 ∅ gs x b) = Support.target w x)
      (hn : ¬ ∀ x, (Cut.cutVal 13 ∅ gs x a || Cut.cutVal 13 ∅ gs x b) = Support.target w x) :
      ∃ r, (∀ x, Support.Band x →
        (Cut.cutVal 13 ∅ gs x 18 || Cut.cutVal 13 ∅ gs x r) = Support.target w x) ∧
        (¬ ∀ x, (Cut.cutVal 13 ∅ gs x 18 || Cut.cutVal 13 ∅ gs x r) = Support.target w x) := by
    have hh := all_ancestors gs hlen hg w a b hc hn 18 (by omega)
    rcases Finset.mem_union.mp hh with hh | hh
    · have he := last_member gs hs a hh
      subst a
      exact ⟨b, hc, hn⟩
    · have he := last_member gs hs b hh
      subst b
      exact ⟨a, by simpa only [Bool.or_comm] using hc, by simpa only [Bool.or_comm] using hn⟩
  obtain ⟨a, hua, hnua⟩ := hp u i j hu hnu
  obtain ⟨b, hvb, hnvb⟩ := hp v k l hv hnv
  have hna : a ∉ Ancestry.anc gs 18 := fun h => hnua (ancestor_pair_exact gs hlen hg u 18 a h hua)
  have hnb : b ∉ Ancestry.anc gs 18 := fun h => hnvb (ancestor_pair_exact gs hlen hg v 18 b h hvb)
  have hvalid (w z : Fin 13) (hwz : w ≠ z) (r s : ℕ)
      (hc : ∀ x, Support.Band x →
        (Cut.cutVal 13 ∅ gs x 18 || Cut.cutVal 13 ∅ gs x r) = Support.target w x)
      (hd : ∀ x, Support.Band x →
        (Cut.cutVal 13 ∅ gs x 18 || Cut.cutVal 13 ∅ gs x s) = Support.target z x) :
      13 ≤ r ∧ r < 13 + gs.length := by
    have hdep : ∀ p ∈ Support.line w \ Support.line z, p.val ∈ Ancestry.anc gs r := by
      intro p hp
      apply Ancestry.depends_mem ∅ gs r p
      apply FourOrSinks.shared_parent_cut_depends_band gs r (fun q hq => (hg q hq).1)
        w z hwz (fun x => Cut.cutVal 13 ∅ gs x 18) hc
      · intro x hx ht
        rw [← hd x hx, ht]
        simp
      · exact hp
    have hc3 : (Support.line w \ Support.line z).card = 3 := by
      have h := Bridge.pair_geometry w z hwz
      have hi := Global.line_intersection w z hwz
      have hw := Global.line_card w
      have hz := Global.line_card z
      have hu := Finset.card_union_add_card_inter (Global.line w) (Global.line z)
      have he : (Global.line w ∩ Global.line z).card = 1 := by omega
      simpa only [Global.line, Support.line] using (show (Global.line w \ Global.line z).card = 3 by
        rw [Finset.card_sdiff, Finset.inter_comm]; omega)
    have hsub : (Support.line w \ Support.line z).image Fin.val ⊆ Ancestry.anc gs r := by
      intro q hq
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
      exact hdep p hp
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ Fin.val_injective, hc3] at hcard
    constructor
    · by_contra hn
      rw [Ancestry.anc_input gs r (by omega)] at hcard
      simp at hcard
    · by_contra hn
      rw [Ancestry.anc_invalid gs r (by omega)] at hcard
      simp at hcard
  have ha := hvalid u v huv a b hua hvb
  have hb := hvalid v u huv.symm b a hvb hua
  have hba := all_ancestors gs hlen hg u 18 a hua hnua b hb
  have hab := all_ancestors gs hlen hg v 18 b hvb hnvb a ha
  have hleba := (Ancestry.anc_bound gs a b ((Finset.mem_union.mp hba).resolve_left hnb)).1
  have hleab := (Ancestry.anc_bound gs b a ((Finset.mem_union.mp hab).resolve_left hna)).1
  have he : a = b := by omega
  subst b
  have heq := (hua (Support.row u) (Or.inr (Support.row_spec u).1)).symm.trans
    (hvb (Support.row u) (Or.inr (Support.row_spec u).1))
  rw [(Support.row_spec u).2, Bridge.row_targets u v huv] at heq
  cases heq

end PEqualNP.Outside.L_meta_1024_aux.TwoPairs

namespace PEqualNP.Outside.L_meta_1024_aux.TwoPairs

open PEqualNP.CircuitLowerBounds

lemma low_prefix_value (gs : List Gate) (hlen : gs.length ≤ 9) (i : ℕ)
    (hi : i ∉ ({19, 20, 21} : Finset ℕ)) (x : Fin 13 → Bool) :
    Cut.cutVal 13 ∅ gs x i = Cut.cutVal 13 ∅ (gs.take 6) x i := by
  by_cases hs : 6 ≤ gs.length
  · by_cases hil : i < 19
    · exact Cut.cutVal_take 13 ∅ gs x 6 i hs hil
    · have hbig : 22 ≤ i := by simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi; omega
      rw [FourOrSinks.cut_ge_false gs x i (by omega),
        FourOrSinks.cut_ge_false (gs.take 6) x i (by simp only [List.length_take]; omega)]
  · rw [List.take_of_length_le (show gs.length ≤ 6 by omega)]

lemma low_pair_unique (gs : List Gate) (hlen : gs.length ≤ 9)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    {m : ℕ} (lineId : Fin m → Fin 13) (hinj : Function.Injective lineId)
    (left right : Fin m → ℕ)
    (hc : ∀ w x, Support.Band x →
      (Cut.cutVal 13 ∅ gs x (left w) || Cut.cutVal 13 ∅ gs x (right w)) = Support.target (lineId w) x)
    (hn : ∀ w, ¬ ∀ x,
      (Cut.cutVal 13 ∅ gs x (left w) || Cut.cutVal 13 ∅ gs x (right w)) = Support.target (lineId w) x)
    (u v : Fin m)
    (hul : left u ∉ ({19, 20, 21} : Finset ℕ))
    (hur : right u ∉ ({19, 20, 21} : Finset ℕ))
    (hvl : left v ∉ ({19, 20, 21} : Finset ℕ))
    (hvr : right v ∉ ({19, 20, 21} : Finset ℕ)) : u = v := by
  by_contra huv
  have hvu (x : Fin 13 → Bool) :
      (Cut.cutVal 13 ∅ (gs.take 6) x (left u) || Cut.cutVal 13 ∅ (gs.take 6) x (right u)) =
      (Cut.cutVal 13 ∅ gs x (left u) || Cut.cutVal 13 ∅ gs x (right u)) := by
    rw [← low_prefix_value gs hlen (left u) hul x, ← low_prefix_value gs hlen (right u) hur x]
  have hvv (x : Fin 13 → Bool) :
      (Cut.cutVal 13 ∅ (gs.take 6) x (left v) || Cut.cutVal 13 ∅ (gs.take 6) x (right v)) =
      (Cut.cutVal 13 ∅ gs x (left v) || Cut.cutVal 13 ∅ gs x (right v)) := by
    rw [← low_prefix_value gs hlen (left v) hvl x, ← low_prefix_value gs hlen (right v) hvr x]
  exact two_pairs_impossible (gs.take 6) (by simp)
    (fun g hgm => hg g (List.mem_of_mem_take hgm)) (lineId u) (lineId v)
    (fun h => huv (hinj h)) (left u) (right u) (left v) (right v)
    (by intro x hx; rw [hvu]; exact hc u x hx)
    (by intro x hx; rw [hvv]; exact hc v x hx)
    (by intro h; apply hn u; intro x; rw [← hvu]; exact h x)
    (by intro h; apply hn v; intro x; rw [← hvv]; exact h x)

lemma four_use_last_three (gs : List Gate) (hlen : gs.length ≤ 9)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (lineId : Fin 5 → Fin 13) (hinj : Function.Injective lineId)
    (left right : Fin 5 → ℕ)
    (hc : ∀ w x, Support.Band x →
      (Cut.cutVal 13 ∅ gs x (left w) || Cut.cutVal 13 ∅ gs x (right w)) = Support.target (lineId w) x)
    (hn : ∀ w, ¬ ∀ x,
      (Cut.cutVal 13 ∅ gs x (left w) || Cut.cutVal 13 ∅ gs x (right w)) = Support.target (lineId w) x) :
    4 ≤ (Finset.univ.filter fun w : Fin 5 =>
      left w ∈ ({19, 20, 21} : Finset ℕ) ∨ right w ∈ ({19, 20, 21} : Finset ℕ)).card := by
  classical
  let low := Finset.univ.filter fun w : Fin 5 =>
    left w ∉ ({19, 20, 21} : Finset ℕ) ∧ right w ∉ ({19, 20, 21} : Finset ℕ)
  have hlow : low.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro u hu v hv
    exact low_pair_unique gs hlen hg lineId hinj left right hc hn u v
      (Finset.mem_filter.mp hu).2.1 (Finset.mem_filter.mp hu).2.2
      (Finset.mem_filter.mp hv).2.1 (Finset.mem_filter.mp hv).2.2
  have he : (Finset.univ.filter fun w : Fin 5 =>
      left w ∈ ({19, 20, 21} : Finset ℕ) ∨ right w ∈ ({19, 20, 21} : Finset ℕ)) =
      Finset.univ \ low := by
    ext w
    simp [low]
    tauto
  rw [he, Finset.card_sdiff, Finset.inter_univ]
  simp only [Finset.card_univ, Fintype.card_fin]
  omega

end PEqualNP.Outside.L_meta_1024_aux.TwoPairs

namespace PEqualNP.Outside.L_meta_1024_aux.EarlyCommon

open PEqualNP.CircuitLowerBounds

lemma pair_card_le {α : Type} [DecidableEq α] (a b : α) : ({a, b} : Finset α).card ≤ 2 := by
  have h := Finset.card_insert_le a ({b} : Finset α)
  simpa using h

def op (a : Bool) (x y : Bool) : Bool := if a then x && y else x || y

def output (gs : List Gate) (a : Bool) (c d e : ℕ) (x : Fin 13 → Bool) : Bool :=
  Cut.cutVal 13 ∅ gs x c || op a (Cut.cutVal 13 ∅ gs x d) (Cut.cutVal 13 ∅ gs x e)

lemma op_comm (a x y : Bool) : op a x y = op a y x := by
  cases a <;> simp [op, Bool.and_comm, Bool.or_comm]

lemma subset_rank {M : ℕ} (label : Fin M → ℕ) (s : ℕ)
    (h : M ≤ ((Finset.univ : Finset (Fin M)).image label).card + s)
    (S : Finset (Fin M)) : S.card ≤ (S.image label).card + s := by
  classical
  let T := Finset.univ \ S
  have hST : S ∪ T = Finset.univ := by ext p; simp [T]
  have htotal : S.card + T.card = M := by
    have hle : S.card ≤ M := by simpa using Finset.card_le_card (Finset.subset_univ S)
    dsimp [T]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  have himage : ((Finset.univ : Finset (Fin M)).image label).card ≤
      (S.image label).card + T.card := by
    calc
      _ = (S.image label ∪ T.image label).card := by rw [← Finset.image_union, hST]
      _ ≤ (S.image label).card + (T.image label).card := Finset.card_union_le _ _
      _ ≤ (S.image label).card + T.card := Nat.add_le_add_left Finset.card_image_le _
  omega

lemma difference_card (u v : Fin 13) (huv : u ≠ v) :
    (Support.line u \ Support.line v).card = 3 := by
  have h := Bridge.pair_geometry u v huv
  have hw := Global.line_card u
  have hz := Global.line_card v
  have hu := Finset.card_union_add_card_inter (Global.line u) (Global.line v)
  have he : (Global.line u ∩ Global.line v).card = 1 := by omega
  simpa only [Global.line, Support.line] using
    (show (Global.line u \ Global.line v).card = 3 by
      rw [Finset.card_sdiff, Finset.inter_comm]; omega)

lemma separating_raw (u v : Fin 13) (huv : u ≠ v) (q : Fin 13) :
    ∃ x : Fin 13 → Bool, Support.Band x ∧ Support.target u x = true ∧
      Support.target v x = false ∧ x q = false := by
  classical
  have hthree := difference_card u v huv
  have hex : ∃ p ∈ Support.line u \ Support.line v, p ≠ q := by
    by_contra! h
    have hs : Support.line u \ Support.line v ⊆ {q} := by
      intro p hp
      simpa using h p hp
    have hc := Finset.card_le_card hs
    simp only [Finset.card_singleton] at hc
    omega
  obtain ⟨p, hp, hpq⟩ := hex
  let Q := insert q (Support.line v)
  let U := Finset.univ.erase p
  have hQU : Q ⊆ U := by
    intro a ha
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_univ _⟩
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact hpq.symm
    · intro he
      subst a
      exact (Finset.mem_sdiff.mp hp).2 ha
  have hQ : Q.card ≤ 5 := by
    have h := Finset.card_insert_le q (Support.line v)
    rw [Clamp.line_card] at h
    exact h
  have hU : U.card = 12 := by simp [U]
  have havail : 6 - Q.card ≤ (U \ Q).card := by
    rw [Finset.card_sdiff_of_subset hQU, hU]
    omega
  obtain ⟨B, hB, hBc⟩ := Finset.exists_subset_card_eq havail
  have hd : Disjoint Q B := by
    rw [Finset.disjoint_left]
    intro a ha hb
    exact (Finset.mem_sdiff.mp (hB hb)).2 ha
  let Z := Q ∪ B
  have hZ : Z.card = 6 := by
    dsimp [Z]
    rw [Finset.card_union_of_disjoint hd, hBc]
    omega
  have hZU : Z ⊆ U := by
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · exact hQU ha
    · exact (Finset.mem_sdiff.mp (hB ha)).1
  refine ⟨Support.fromZeros Z, ?_, ?_, ?_, ?_⟩
  · exact Or.inr ((congrArg Finset.card (Support.zeroSet_fromZeros Z)).trans hZ)
  · apply decide_eq_true
    refine ⟨p, (Finset.mem_sdiff.mp hp).1, ?_⟩
    have hn : p ∉ Z := fun h => (Finset.mem_erase.mp (hZU h)).1 rfl
    simp [Support.fromZeros, hn]
  · apply decide_eq_false_iff_not.mpr
    rintro ⟨a, ha, hx⟩
    have hz : a ∈ Z := Finset.mem_union_left _ (Finset.mem_insert_of_mem ha)
    simp [Support.fromZeros, hz] at hx
  · have hz : q ∈ Z := Finset.mem_union_left _ (Finset.mem_insert_self _ _)
    simp [Support.fromZeros, hz]

lemma target_not_le (u v : Fin 13) (huv : u ≠ v) :
    ¬ ∀ x, Support.Band x → Support.target u x = true → Support.target v x = true := by
  intro h
  have he := h (Support.row v) (Or.inr (Support.row_spec v).1)
    (Bridge.row_targets v u huv.symm)
  rw [(Support.row_spec v).2] at he
  cases he

lemma output_zero (gs : List Gate) (a : Bool) (c d e : ℕ) (w : Fin 13)
    (hu : ∀ x, Support.target w x = false → output gs a c d e x = false) :
    output gs a c d e (fun _ => false) = false := by
  exact hu _ (by simp [Support.target])

lemma distinct_labels (gs : List Gate) (hlen : gs.length ≤ 5)
    (label : Fin 13 → ℕ) (wire : ℕ → ℕ)
    (hcount : 13 ≤ ((Finset.univ : Finset (Fin 13)).image label).card + gs.length)
    (hraw : ∀ p : Fin 13, wire p.val = label p)
    (ha : ∀ i j, j ∈ Ancestry.anc gs i → wire j = wire i)
    (a : Bool) (c d e : ℕ) (w : Fin 13)
    (hc : ∀ x, Support.Band x → output gs a c d e x = Support.target w x)
    (hu : ∀ x, Support.target w x = false → output gs a c d e x = false)
    (hn : ¬ ∀ x, output gs a c d e x = Support.target w x) :
    wire c ≠ wire d ∧ wire c ≠ wire e ∧ wire d ≠ wire e := by
  classical
  let E := (Cut.essential (M := 13) 13 ∅ gs c ∪ Cut.essential (M := 13) 13 ∅ gs d) ∪
    Cut.essential (M := 13) 13 ∅ gs e
  have hlabel (i : ℕ) (p : Fin 13) (hp : p ∈ Cut.essential (M := 13) 13 ∅ gs i) :
      label p = wire i :=
    (hraw p).symm.trans (ha i p.val (Ancestry.depends_mem ∅ gs i p (Finset.mem_filter.mp hp).2))
  have him : E.image label ⊆ {wire c, wire d, wire e} := by
    intro z hz
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
    rcases Finset.mem_union.mp hp with hp | hp
    · rcases Finset.mem_union.mp hp with hp | hp
      · simp [hlabel c p hp]
      · simp [hlabel d p hp]
    · simp [hlabel e p hp]
  have hnot : ¬ (wire c = wire d ∨ wire c = wire e ∨ wire d = wire e) := by
    intro he
    have htwo : (E.image label).card ≤ 2 := by
      have hset : ({wire c, wire d, wire e} : Finset ℕ).card ≤ 2 := by
        rcases he with he | he | he
        · simpa [he] using pair_card_le (wire d) (wire e)
        · simpa [he, Finset.insert_comm] using pair_card_le (wire d) (wire e)
        · simpa [he] using pair_card_le (wire c) (wire e)
      exact (Finset.card_le_card him).trans hset
    have hE : E.card ≤ 7 := by
      have hr := subset_rank label gs.length hcount E
      omega
    apply hn
    apply Support.small_support_exact w _ hc (output_zero gs a c d e w hu) E hE
    intro x y hxy
    have hc' := Cut.essential_supports 13 ∅ gs c x y
      (fun p hp => hxy p (Finset.mem_union_left _ (Finset.mem_union_left _ hp)))
    have hd' := Cut.essential_supports 13 ∅ gs d x y
      (fun p hp => hxy p (Finset.mem_union_left _ (Finset.mem_union_right _ hp)))
    have he' := Cut.essential_supports 13 ∅ gs e x y
      (fun p hp => hxy p (Finset.mem_union_right _ hp))
    simp only [output, hc', hd', he']
  simpa only [not_or] using hnot

lemma fork_other_inputs (gs : List Gate) (wire : ℕ → ℕ)
    (ha : ∀ i j, j ∈ Ancestry.anc gs i → wire j = wire i)
    (c d a b : ℕ) (hav : a < 13 + gs.length) (hbv : b < 13 + gs.length)
    (hac : wire a ≠ wire c) (had : wire a ≠ wire d)
    (hbc : wire b ≠ wire c) (hbd : wire b ≠ wire d)
    (hca : ∀ k, 13 ≤ k → k < 13 + gs.length →
      k ∈ (Ancestry.anc gs c ∪ Ancestry.anc gs d) ∪ Ancestry.anc gs a)
    (hcb : ∀ k, 13 ≤ k → k < 13 + gs.length →
      k ∈ (Ancestry.anc gs c ∪ Ancestry.anc gs d) ∪ Ancestry.anc gs b) :
    a = b ∨ (a < 13 ∧ b < 13) := by
  have hab : 13 ≤ a → a ≤ b := by
    intro hal
    rcases Finset.mem_union.mp (hcb a hal hav) with hh | hh
    · rcases Finset.mem_union.mp hh with hh | hh
      · exact (hac (ha c a hh)).elim
      · exact (had (ha d a hh)).elim
    · exact (Ancestry.anc_bound gs b a hh).1
  have hba : 13 ≤ b → b ≤ a := by
    intro hbl
    rcases Finset.mem_union.mp (hca b hbl hbv) with hh | hh
    · rcases Finset.mem_union.mp hh with hh | hh
      · exact (hbc (ha c b hh)).elim
      · exact (hbd (ha d b hh)).elim
    · exact (Ancestry.anc_bound gs a b hh).1
  by_cases hal : 13 ≤ a
  · left; have h₁ := hab hal; have h₂ := hba (by omega); omega
  · by_cases hbl : 13 ≤ b
    · have hh := hba hbl; omega
    · exact Or.inr ⟨by omega, by omega⟩

end PEqualNP.Outside.L_meta_1024_aux.EarlyCommon

namespace PEqualNP.Outside.L_meta_1024_aux.EarlyCommon

open PEqualNP.CircuitLowerBounds

lemma raw_value (gs : List Gate) (x : Fin 13 → Bool) (i : ℕ) (hi : i < 13) :
    Cut.cutVal 13 ∅ gs x i = x ⟨i, hi⟩ := by
  have h := Cut.cutVal_append_old 13 ∅ [] gs x i (by simpa using hi)
  simpa [Cut.cutVal_nil, Cut.source_eq, hi] using h

lemma raw_and_impossible (gs : List Gate) (c d a b e : ℕ) (ha : a < 13)
    (ob : Bool) (u v : Fin 13) (huv : u ≠ v)
    (hu : ∀ x, Support.Band x → output gs true c d a x = Support.target u x)
    (hv : ∀ x, Support.Band x → output gs ob c b e x = Support.target v x) : False := by
  obtain ⟨x, hx, hux, hvx, hax⟩ := separating_raw u v huv ⟨a, ha⟩
  have hcv : Cut.cutVal 13 ∅ gs x c = false := by
    have he := hv x hx
    rw [hvx] at he
    exact (Bool.or_eq_false_iff.mp he).1
  have he := hu x hx
  simp [output, op, hcv, raw_value gs x a ha, hax, hux] at he

lemma same_private_impossible (gs : List Gate) (oa ob : Bool) (c d a : ℕ)
    (u v : Fin 13) (huv : u ≠ v)
    (hu : ∀ x, Support.Band x → output gs oa c d a x = Support.target u x)
    (hv : ∀ x, Support.Band x → output gs ob c d a x = Support.target v x) : False := by
  cases oa <;> cases ob
  · apply target_not_le u v huv
    intro x hx ht
    exact (hv x hx).symm.trans ((hu x hx).trans ht)
  · apply target_not_le v u huv.symm
    intro x hx ht
    rw [← hv x hx] at ht
    rw [← hu x hx]
    cases hc : Cut.cutVal 13 ∅ gs x c <;>
      cases hd : Cut.cutVal 13 ∅ gs x d <;>
      cases he : Cut.cutVal 13 ∅ gs x a <;> simp_all [output, op]
  · apply target_not_le u v huv
    intro x hx ht
    rw [← hu x hx] at ht
    rw [← hv x hx]
    cases hc : Cut.cutVal 13 ∅ gs x c <;>
      cases hd : Cut.cutVal 13 ∅ gs x d <;>
      cases he : Cut.cutVal 13 ∅ gs x a <;> simp_all [output, op]
  · apply target_not_le u v huv
    intro x hx ht
    exact (hv x hx).symm.trans ((hu x hx).trans ht)

lemma raw_or_impossible (gs : List Gate) (c d a b : ℕ) (ha : a < 13) (hb : b < 13)
    (u v : Fin 13) (huv : u ≠ v)
    (hu : ∀ x, Support.Band x → output gs false c d a x = Support.target u x)
    (hv : ∀ x, Support.Band x → output gs false c d b x = Support.target v x) : False := by
  classical
  let H (x : Fin 13 → Bool) := Cut.cutVal 13 ∅ gs x c || Cut.cutVal 13 ∅ gs x d
  have hcu : ∀ x, Support.Band x → (H x || x ⟨a, ha⟩) = Support.target u x := by
    intro x hx
    simpa [output, op, H, raw_value gs x a ha, Bool.or_assoc] using hu x hx
  have hcv : ∀ x, Support.Band x → (H x || x ⟨b, hb⟩) = Support.target v x := by
    intro x hx
    simpa [output, op, H, raw_value gs x b hb, Bool.or_assoc] using hv x hx
  have hsub : Support.line u \ Support.line v ⊆ {⟨a, ha⟩} := by
    intro p hp
    obtain ⟨x, y, hxy, hne⟩ := FourOrSinks.shared_parent_essential_band u v huv H
      (fun x => x ⟨a, ha⟩) hcu (by
        intro x hx ht
        rw [← hcv x hx, ht]
        simp) (by intro x y hxy ht; exact hxy _ ht) p hp
    have he : p = ⟨a, ha⟩ := by
      by_contra hn
      exact hne (hxy _ (Ne.symm hn))
    simpa using he
  have hcard := Finset.card_le_card hsub
  rw [difference_card u v huv, Finset.card_singleton] at hcard
  omega

lemma shared_generated_impossible (gs : List Gate) (wire : ℕ → ℕ)
    (ha : ∀ i j, j ∈ Ancestry.anc gs i → wire j = wire i)
    (oa ob : Bool) (c d a b : ℕ)
    (hav : a < 13 + gs.length) (hbv : b < 13 + gs.length)
    (hac : wire a ≠ wire c) (had : wire a ≠ wire d)
    (hbc : wire b ≠ wire c) (hbd : wire b ≠ wire d)
    (hca : ∀ k, 13 ≤ k → k < 13 + gs.length →
      k ∈ (Ancestry.anc gs c ∪ Ancestry.anc gs d) ∪ Ancestry.anc gs a)
    (hcb : ∀ k, 13 ≤ k → k < 13 + gs.length →
      k ∈ (Ancestry.anc gs c ∪ Ancestry.anc gs d) ∪ Ancestry.anc gs b)
    (u v : Fin 13) (huv : u ≠ v)
    (hu : ∀ x, Support.Band x → output gs oa c d a x = Support.target u x)
    (hv : ∀ x, Support.Band x → output gs ob c d b x = Support.target v x) : False := by
  rcases fork_other_inputs gs wire ha c d a b hav hbv hac had hbc hbd hca hcb with he | hh
  · subst b
    exact same_private_impossible gs oa ob c d a u v huv hu hv
  · cases oa with
    | true => exact raw_and_impossible gs c d a d b hh.1 ob u v huv hu hv
    | false =>
      cases ob with
      | true => exact raw_and_impossible gs c d b d a hh.2 false v u huv.symm hv hu
      | false => exact raw_or_impossible gs c d a b hh.1 hh.2 u v huv hu hv

end PEqualNP.Outside.L_meta_1024_aux.EarlyCommon

namespace PEqualNP.Outside.L_meta_1024_aux.EarlyCommon

open PEqualNP.CircuitLowerBounds

lemma private_not_raw (gs : List Gate) (oa ob : Bool) (c r s t z : ℕ)
    (u v : Fin 13) (huv : u ≠ v)
    (hu : ∀ x, Support.Band x → output gs oa c r s x = Support.target u x)
    (hv : ∀ x, Support.Band x → output gs ob c t z x = Support.target v x) :
    13 ≤ r ∨ 13 ≤ s := by
  classical
  by_contra! hh
  have hcu : ∀ x, Support.Band x →
      (Cut.cutVal 13 ∅ gs x c || op oa (x ⟨r, hh.1⟩) (x ⟨s, hh.2⟩)) = Support.target u x := by
    intro x hx
    simpa only [output, raw_value gs x r hh.1, raw_value gs x s hh.2] using hu x hx
  have hmono : ∀ x y : Fin 13 → Bool, (∀ p, x p = true → y p = true) →
      op oa (x ⟨r, hh.1⟩) (x ⟨s, hh.2⟩) = true →
      op oa (y ⟨r, hh.1⟩) (y ⟨s, hh.2⟩) = true := by
    intro x y hxy ht
    cases oa with
    | false =>
      rcases Bool.or_eq_true_iff.mp ht with h | h
      · exact Bool.or_eq_true_iff.mpr (Or.inl (hxy _ h))
      · exact Bool.or_eq_true_iff.mpr (Or.inr (hxy _ h))
    | true =>
      obtain ⟨hr, hs⟩ := Bool.and_eq_true_iff.mp ht
      exact Bool.and_eq_true_iff.mpr ⟨hxy _ hr, hxy _ hs⟩
  have hsub : Support.line u \ Support.line v ⊆ {⟨r, hh.1⟩, ⟨s, hh.2⟩} := by
    intro p hp
    obtain ⟨x, y, hxy, hne⟩ := FourOrSinks.shared_parent_essential_band u v huv
      (fun x => Cut.cutVal 13 ∅ gs x c) (fun x => op oa (x ⟨r, hh.1⟩) (x ⟨s, hh.2⟩))
      hcu (by intro x hx ht; rw [← hv x hx]; simp [output, ht]) hmono p hp
    by_contra hm
    have hpr : (⟨r, hh.1⟩ : Fin 13) ≠ p := by
      intro he; apply hm; simp [← he]
    have hps : (⟨s, hh.2⟩ : Fin 13) ≠ p := by
      intro he; apply hm; simp [← he]
    exact hne (by rw [hxy _ hpr, hxy _ hps])
  have hcard := (Finset.card_le_card hsub).trans (pair_card_le _ _)
  rw [difference_card u v huv] at hcard
  omega

lemma full_prefix_ancestors (gs : List Gate) (hlen : gs.length ≤ 5)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (oa : Bool) (c r s : ℕ) (w : Fin 13)
    (hc : ∀ x, Support.Band x → output gs oa c r s x = Support.target w x)
    (hn : ¬ ∀ x, output gs oa c r s x = Support.target w x) :
    ∀ k, 13 ≤ k → k < 13 + gs.length →
      k ∈ (Ancestry.anc gs c ∪ Ancestry.anc gs r) ∪ Ancestry.anc gs s := by
  let g : Gate := ⟨if oa then GateOp.and else GateOp.or, [r, s]⟩
  let code := gs ++ [g]
  let n := 13 + gs.length
  let cc := if c < n then c else n + 1
  have hcc : cc ≠ n := by dsimp [cc]; split_ifs <;> omega
  have hread (x : Fin 13 → Bool) : Cut.cutVal 13 ∅ code x cc = Cut.cutVal 13 ∅ gs x c := by
    rw [Cut.cutVal_snoc, if_neg hcc]
    dsimp [cc]
    split_ifs with hc'
    · rfl
    · rw [FourOrSinks.cut_ge_false gs x (n + 1) (by omega),
        FourOrSinks.cut_ge_false gs x c (by omega)]
  have hval (x : Fin 13 → Bool) :
      (Cut.cutVal 13 ∅ code x cc || Cut.cutVal 13 ∅ code x n) = output gs oa c r s x := by
    rw [hread, Cut.cutVal_snoc]
    cases oa <;> simp [g, n, op, output, GateOp.eval]
  have hcode : ∀ q ∈ code, (q.op = GateOp.and ∨ q.op = GateOp.or) ∧ q.inputs.length ≤ 2 := by
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hg q hq
    · have he : q = g := by simpa using hq
      subst q
      cases oa <;> simp [g]
  have hac : Ancestry.anc code cc = Ancestry.anc gs c := by
    rw [Ancestry.anc_snoc, if_neg hcc]
    dsimp [cc]
    split_ifs with hc'
    · rfl
    · rw [Ancestry.anc_invalid gs (n + 1) (by omega), Ancestry.anc_invalid gs c (by omega)]
  intro k hkl hku
  have he := TwoPairs.all_ancestors code (by simp [code]; omega) hcode w cc n
    (by intro x hx; rw [hval]; exact hc x hx)
    (by intro he; apply hn; intro x; rw [← hval]; exact he x)
    k ⟨hkl, by simp [code]; omega⟩
  rw [hac, Ancestry.anc_snoc, if_pos rfl] at he
  have hkn : k ≠ n := by omega
  simpa [g, hkn, Finset.mem_union, or_assoc] using he

lemma parallel_binary_impossible (gs : List Gate) (hlen : gs.length ≤ 5)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (oa ob : Bool) (c r s t z : ℕ)
    (hr : r < 13 + gs.length) (hs : s < 13 + gs.length)
    (ht : t < 13 + gs.length) (hz : z < 13 + gs.length)
    (u v : Fin 13) (huv : u ≠ v)
    (hu : ∀ x, Support.Band x → output gs oa c r s x = Support.target u x)
    (hv : ∀ x, Support.Band x → output gs ob c t z x = Support.target v x)
    (hupperu : ∀ x, Support.target u x = false → output gs oa c r s x = false)
    (hupperv : ∀ x, Support.target v x = false → output gs ob c t z x = false)
    (hnu : ¬ ∀ x, output gs oa c r s x = Support.target u x)
    (hnv : ¬ ∀ x, output gs ob c t z x = Support.target v x) : False := by
  classical
  obtain ⟨label, wire, hcard, hraw, ha⟩ := Ancestry.components Finset.univ gs
    (fun q hq => (hg q hq).2)
  simp only [Finset.card_univ, Fintype.card_fin] at hcard
  have hdu := distinct_labels gs hlen label wire hcard hraw ha oa c r s u hu hupperu hnu
  have hdv := distinct_labels gs hlen label wire hcard hraw ha ob c t z v hv hupperv hnv
  have hfu := full_prefix_ancestors gs hlen hg oa c r s u hu hnu
  have hfv := full_prefix_ancestors gs hlen hg ob c t z v hv hnv
  let d := max (max r s) (max t z)
  have hrd : r ≤ d := le_trans (Nat.le_max_left r s) (Nat.le_max_left _ _)
  have hsd : s ≤ d := le_trans (Nat.le_max_right r s) (Nat.le_max_left _ _)
  have htd : t ≤ d := le_trans (Nat.le_max_left t z) (Nat.le_max_right _ _)
  have hzd : z ≤ d := le_trans (Nat.le_max_right t z) (Nat.le_max_right _ _)
  have hd : d = r ∨ d = s ∨ d = t ∨ d = z := by dsimp [d]; omega
  have hdlo : 13 ≤ d := by
    rcases private_not_raw gs oa ob c r s t z u v huv hu hv with h | h <;> omega
  have hdhi : d < 13 + gs.length := by dsimp [d]; omega
  have hdnot : d ∉ Ancestry.anc gs c := by
    intro hm
    have he := ha c d hm
    rcases hd with heq | heq | heq | heq
    · rw [heq] at he; exact hdu.1 he.symm
    · rw [heq] at he; exact hdu.2.1 he.symm
    · rw [heq] at he; exact hdv.1 he.symm
    · rw [heq] at he; exact hdv.2.1 he.symm
  have hdu' : d = r ∨ d = s := by
    rcases Finset.mem_union.mp (hfu d hdlo hdhi) with hm | hm
    · rcases Finset.mem_union.mp hm with hm | hm
      · exact (hdnot hm).elim
      · have hh := (Ancestry.anc_bound gs r d hm).1; exact Or.inl (by omega)
    · have hh := (Ancestry.anc_bound gs s d hm).1; exact Or.inr (by omega)
  have hdv' : d = t ∨ d = z := by
    rcases Finset.mem_union.mp (hfv d hdlo hdhi) with hm | hm
    · rcases Finset.mem_union.mp hm with hm | hm
      · exact (hdnot hm).elim
      · have hh := (Ancestry.anc_bound gs t d hm).1; exact Or.inl (by omega)
    · have hh := (Ancestry.anc_bound gs z d hm).1; exact Or.inr (by omega)
  have reorient (o : Bool) (i j : ℕ) (w : Fin 13)
      (hi : i < 13 + gs.length) (hj : j < 13 + gs.length)
      (hdi : d = i ∨ d = j)
      (hlabels : wire c ≠ wire i ∧ wire c ≠ wire j ∧ wire i ≠ wire j)
      (hfull : ∀ k, 13 ≤ k → k < 13 + gs.length →
        k ∈ (Ancestry.anc gs c ∪ Ancestry.anc gs i) ∪ Ancestry.anc gs j)
      (hcorrect : ∀ x, Support.Band x → output gs o c i j x = Support.target w x) :
      ∃ a, a < 13 + gs.length ∧ wire a ≠ wire c ∧ wire a ≠ wire d ∧
        (∀ k, 13 ≤ k → k < 13 + gs.length →
          k ∈ (Ancestry.anc gs c ∪ Ancestry.anc gs d) ∪ Ancestry.anc gs a) ∧
        (∀ x, Support.Band x → output gs o c d a x = Support.target w x) := by
    rcases hdi with he | he
    · subst i
      exact ⟨j, hj, hlabels.2.1.symm, hlabels.2.2.symm, hfull, hcorrect⟩
    · subst j
      refine ⟨i, hi, hlabels.1.symm, hlabels.2.2, ?_, ?_⟩
      · intro k hkl hku
        simpa only [Finset.union_assoc, Finset.union_comm, Finset.union_left_comm] using hfull k hkl hku
      · intro x hx
        simpa only [output, op_comm] using hcorrect x hx
  obtain ⟨a, hav, hac, had, hca, hua⟩ := reorient oa r s u hr hs hdu' hdu hfu hu
  obtain ⟨b, hbv, hbc, hbd, hcb, hvb⟩ := reorient ob t z v ht hz hdv' hdv hfv hv
  exact shared_generated_impossible gs wire ha oa ob c d a b hav hbv hac had hbc hbd hca hcb
    u v huv hua hvb

end PEqualNP.Outside.L_meta_1024_aux.EarlyCommon

namespace PEqualNP.Outside.L_meta_1024_aux.EarlyCommon

open PEqualNP.CircuitLowerBounds

def gateOutput (gs : List Gate) (g : Gate) (c : ℕ) (x : Fin 13 → Bool) : Bool :=
  Cut.cutVal 13 ∅ gs x c || g.op.eval (g.inputs.map fun i => Cut.cutVal 13 ∅ gs x i)

lemma private_binary (gs : List Gate) (hlen : gs.length ≤ 5)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hfanin : g.inputs.length ≤ 2)
    (c : ℕ) (w : Fin 13)
    (hc : ∀ x, Support.Band x → gateOutput gs g c x = Support.target w x)
    (hn : ¬ ∀ x, gateOutput gs g c x = Support.target w x) :
    ∃ a r s, r < 13 + gs.length ∧ s < 13 + gs.length ∧
      ∀ x, gateOutput gs g c x = output gs a c r s x := by
  have hsmall (i j : ℕ) (he : ∀ x, gateOutput gs g c x =
      (Cut.cutVal 13 ∅ gs x i || Cut.cutVal 13 ∅ gs x j)) : False := by
    apply hn
    have hh := TwoPairs.small_pair_exact gs hlen hg w i j
      (by intro x hx; rw [← he]; exact hc x hx)
    intro x
    rw [he, hh]
  cases hins : g.inputs with
  | nil =>
    rcases hop with hop | hop
    · have hh := hc (Support.row w) (Or.inr (Support.row_spec w).1)
      simp [gateOutput, hop, hins, GateOp.eval, (Support.row_spec w).2] at hh
    · exact (hsmall c c (by intro x; simp [gateOutput, hop, hins, GateOp.eval])).elim
  | cons r tail =>
    cases htail : tail with
    | nil =>
      apply False.elim
      apply hsmall c r
      intro x
      rcases hop with hop | hop <;> simp [gateOutput, hop, hins, htail, GateOp.eval]
    | cons s rest =>
      have hrest : rest = [] := by
        simp only [hins, htail, List.length_cons] at hfanin
        exact List.length_eq_zero_iff.mp (by omega)
      have hvalid (i j : ℕ) (hins' : g.inputs = [i, j]) : i < 13 + gs.length := by
        by_contra! hbad
        have hz (x : Fin 13 → Bool) : Cut.cutVal 13 ∅ gs x i = false :=
          FourOrSinks.cut_ge_false gs x i hbad
        rcases hop with hop | hop
        · apply hsmall c c
          intro x
          simp [gateOutput, hins', hop, GateOp.eval, hz]
        · apply hsmall c j
          intro x
          simp [gateOutput, hins', hop, GateOp.eval, hz]
      have hr := hvalid r s (by simp [hins, htail, hrest])
      have hs : s < 13 + gs.length := by
        by_contra! hbad
        have hz (x : Fin 13 → Bool) : Cut.cutVal 13 ∅ gs x s = false :=
          FourOrSinks.cut_ge_false gs x s hbad
        rcases hop with hop | hop
        · apply hsmall c c
          intro x
          simp [gateOutput, hins, htail, hrest, hop, GateOp.eval, hz]
        · apply hsmall c r
          intro x
          simp [gateOutput, hins, htail, hrest, hop, GateOp.eval, hz]
      rcases hop with hop | hop
      · refine ⟨true, r, s, hr, hs, ?_⟩
        intro x
        simp [gateOutput, output, op, hins, htail, hrest, hop, GateOp.eval]
      · refine ⟨false, r, s, hr, hs, ?_⟩
        intro x
        simp [gateOutput, output, op, hins, htail, hrest, hop, GateOp.eval]

lemma parallel_gates_impossible (gs : List Gate) (hlen : gs.length ≤ 5)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (ga gb : Gate)
    (hga : (ga.op = GateOp.and ∨ ga.op = GateOp.or) ∧ ga.inputs.length ≤ 2)
    (hgb : (gb.op = GateOp.and ∨ gb.op = GateOp.or) ∧ gb.inputs.length ≤ 2)
    (c : ℕ) (u v : Fin 13) (huv : u ≠ v)
    (hu : ∀ x, Support.Band x → gateOutput gs ga c x = Support.target u x)
    (hv : ∀ x, Support.Band x → gateOutput gs gb c x = Support.target v x)
    (hupperu : ∀ x, Support.target u x = false → gateOutput gs ga c x = false)
    (hupperv : ∀ x, Support.target v x = false → gateOutput gs gb c x = false)
    (hnu : ¬ ∀ x, gateOutput gs ga c x = Support.target u x)
    (hnv : ¬ ∀ x, gateOutput gs gb c x = Support.target v x) : False := by
  obtain ⟨oa, r, s, hr, hs, hea⟩ := private_binary gs hlen hg ga hga.1 hga.2 c u hu hnu
  obtain ⟨ob, t, z, ht, hz, heb⟩ := private_binary gs hlen hg gb hgb.1 hgb.2 c v hv hnv
  exact parallel_binary_impossible gs hlen hg oa ob c r s t z hr hs ht hz u v huv
    (by intro x hx; rw [← hea]; exact hu x hx)
    (by intro x hx; rw [← heb]; exact hv x hx)
    (by intro x hx; rw [← hea]; exact hupperu x hx)
    (by intro x hx; rw [← heb]; exact hupperv x hx)
    (by intro h; apply hnu; intro x; rw [hea]; exact h x)
    (by intro h; apply hnv; intro x; rw [heb]; exact h x)

lemma early_common_impossible (gs : List Gate) (hlen : gs.length = 5)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (ga gb : Gate)
    (hga : (ga.op = GateOp.and ∨ ga.op = GateOp.or) ∧ ga.inputs.length ≤ 2)
    (hgb : (gb.op = GateOp.and ∨ gb.op = GateOp.or) ∧ gb.inputs.length ≤ 2)
    (c : ℕ) (hc18 : c ≠ 18) (hc19 : c ≠ 19) (u v : Fin 13) (huv : u ≠ v)
    (hu : ∀ x, Support.Band x →
      (Cut.cutVal 13 ∅ ((gs ++ [ga]) ++ [gb]) x c ||
        Cut.cutVal 13 ∅ ((gs ++ [ga]) ++ [gb]) x 18) = Support.target u x)
    (hv : ∀ x, Support.Band x →
      (Cut.cutVal 13 ∅ ((gs ++ [ga]) ++ [gb]) x c ||
        Cut.cutVal 13 ∅ ((gs ++ [ga]) ++ [gb]) x 19) = Support.target v x)
    (hupperu : ∀ x, Support.target u x = false →
      (Cut.cutVal 13 ∅ ((gs ++ [ga]) ++ [gb]) x c ||
        Cut.cutVal 13 ∅ ((gs ++ [ga]) ++ [gb]) x 18) = false)
    (hupperv : ∀ x, Support.target v x = false →
      (Cut.cutVal 13 ∅ ((gs ++ [ga]) ++ [gb]) x c ||
        Cut.cutVal 13 ∅ ((gs ++ [ga]) ++ [gb]) x 19) = false)
    (hnu : ¬ ∀ x,
      (Cut.cutVal 13 ∅ ((gs ++ [ga]) ++ [gb]) x c ||
        Cut.cutVal 13 ∅ ((gs ++ [ga]) ++ [gb]) x 18) = Support.target u x)
    (hnv : ¬ ∀ x,
      (Cut.cutVal 13 ∅ ((gs ++ [ga]) ++ [gb]) x c ||
        Cut.cutVal 13 ∅ ((gs ++ [ga]) ++ [gb]) x 19) = Support.target v x) : False := by
  have hcommon (x : Fin 13 → Bool) : Cut.cutVal 13 ∅ ((gs ++ [ga]) ++ [gb]) x c =
      Cut.cutVal 13 ∅ gs x c := by
    rw [Cut.cutVal_snoc, if_neg (by simpa [hlen] using hc19),
      Cut.cutVal_snoc, if_neg (by simpa [hlen] using hc18)]
  have hfirst (x : Fin 13 → Bool) : Cut.cutVal 13 ∅ ((gs ++ [ga]) ++ [gb]) x 18 =
      Cut.cutVal 13 ∅ (gs ++ [ga]) x 18 := by
    rw [Cut.cutVal_snoc, if_neg (by simp [hlen])]
  have hsecond (x : Fin 13 → Bool) : Cut.cutVal 13 ∅ ((gs ++ [ga]) ++ [gb]) x 19 =
      gb.op.eval (gb.inputs.map fun i => Cut.cutVal 13 ∅ (gs ++ [ga]) x i) := by
    rw [Cut.cutVal_snoc]
    simp [hlen]
  have hnread : 18 ∉ gb.inputs := by
    intro hmem
    rcases hgb.1 with hop | hop
    · apply target_not_le v u huv.symm
      intro x hx htv
      rw [← hv x hx] at htv
      rw [← hu x hx]
      rcases Bool.or_eq_true_iff.mp htv with h | h
      · exact Bool.or_eq_true_iff.mpr (Or.inl h)
      · rw [hsecond, hop] at h
        have hall : ∀ i ∈ gb.inputs, Cut.cutVal 13 ∅ (gs ++ [ga]) x i = true := by
          simpa [GateOp.eval, List.all_eq_true, List.mem_map] using h
        exact Bool.or_eq_true_iff.mpr (Or.inr ((hfirst x).trans (hall 18 hmem)))
    · apply target_not_le u v huv
      intro x hx htu
      rw [← hu x hx] at htu
      rw [← hv x hx]
      rcases Bool.or_eq_true_iff.mp htu with h | h
      · exact Bool.or_eq_true_iff.mpr (Or.inl h)
      · apply Bool.or_eq_true_iff.mpr
        right
        rw [hsecond, hop]
        simp only [GateOp.eval, List.any_eq_true, List.mem_map, exists_exists_and_eq_and, id_eq]
        exact ⟨18, hmem, (hfirst x).symm.trans h⟩
  have hA (x : Fin 13 → Bool) :
      (Cut.cutVal 13 ∅ ((gs ++ [ga]) ++ [gb]) x c ||
        Cut.cutVal 13 ∅ ((gs ++ [ga]) ++ [gb]) x 18) = gateOutput gs ga c x := by
    rw [hcommon, hfirst, Cut.cutVal_snoc]
    simp [hlen, gateOutput]
  have hB (x : Fin 13 → Bool) :
      (Cut.cutVal 13 ∅ ((gs ++ [ga]) ++ [gb]) x c ||
        Cut.cutVal 13 ∅ ((gs ++ [ga]) ++ [gb]) x 19) = gateOutput gs gb c x := by
    rw [hcommon, hsecond]
    unfold gateOutput
    congr 2
    apply List.map_congr_left
    intro i hi
    rw [Cut.cutVal_snoc, if_neg (by
      intro he
      apply hnread
      have he' : i = 18 := by omega
      exact he' ▸ hi)]
  exact parallel_gates_impossible gs (by omega) hg ga gb hga hgb c u v huv
    (by intro x hx; rw [← hA]; exact hu x hx)
    (by intro x hx; rw [← hB]; exact hv x hx)
    (by intro x hx; rw [← hA]; exact hupperu x hx)
    (by intro x hx; rw [← hB]; exact hupperv x hx)
    (by intro h; apply hnu; intro x; rw [hA]; exact h x)
    (by intro h; apply hnv; intro x; rw [hB]; exact h x)

end PEqualNP.Outside.L_meta_1024_aux.EarlyCommon

namespace PEqualNP.Outside.L_meta_1024_aux.EarlyCommon

open PEqualNP.CircuitLowerBounds

lemma prefix_value (gs : List Gate) (hlen : gs.length ≤ 9) (hseven : 7 ≤ gs.length)
    (i : ℕ) (hi20 : i ≠ 20) (hi21 : i ≠ 21) (x : Fin 13 → Bool) :
    Cut.cutVal 13 ∅ gs x i = Cut.cutVal 13 ∅ (gs.take 7) x i := by
  by_cases hi : i < 20
  · exact Cut.cutVal_take 13 ∅ gs x 7 i hseven hi
  · rw [FourOrSinks.cut_ge_false gs x i (by omega),
      FourOrSinks.cut_ge_false (gs.take 7) x i (by simp only [List.length_take]; omega)]

lemma early_common_prefix_impossible (gs : List Gate) (hlen : gs.length ≤ 9)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (c : ℕ) (hc : c ∉ ({18, 19, 20, 21} : Finset ℕ))
    (u v : Fin 13) (huv : u ≠ v)
    (hu : ∀ x, Support.Band x →
      (Cut.cutVal 13 ∅ gs x c || Cut.cutVal 13 ∅ gs x 18) = Support.target u x)
    (hv : ∀ x, Support.Band x →
      (Cut.cutVal 13 ∅ gs x c || Cut.cutVal 13 ∅ gs x 19) = Support.target v x)
    (hupperu : ∀ x, Support.target u x = false →
      (Cut.cutVal 13 ∅ gs x c || Cut.cutVal 13 ∅ gs x 18) = false)
    (hupperv : ∀ x, Support.target v x = false →
      (Cut.cutVal 13 ∅ gs x c || Cut.cutVal 13 ∅ gs x 19) = false)
    (hnu : ¬ ∀ x, (Cut.cutVal 13 ∅ gs x c || Cut.cutVal 13 ∅ gs x 18) = Support.target u x)
    (hnv : ¬ ∀ x, (Cut.cutVal 13 ∅ gs x c || Cut.cutVal 13 ∅ gs x 19) = Support.target v x) : False := by
  have hs : 7 ≤ gs.length := by
    by_contra! hn
    exact TwoPairs.two_pairs_impossible gs (by omega) hg u v huv c 18 c 19 hu hv hnu hnv
  have h5 : 5 < gs.length := by omega
  have h6 : 6 < gs.length := by omega
  have heq : ((gs.take 5 ++ [gs[5]]) ++ [gs[6]]) = gs.take 7 := by
    rw [List.take_concat_get' gs 5 h5, List.take_concat_get' gs 6 h6]
  have hc' : c ≠ 18 ∧ c ≠ 19 ∧ c ≠ 20 ∧ c ≠ 21 := by simpa using hc
  have hp (x : Fin 13 → Bool) (i : ℕ) (hi20 : i ≠ 20) (hi21 : i ≠ 21) :
      Cut.cutVal 13 ∅ ((gs.take 5 ++ [gs[5]]) ++ [gs[6]]) x i = Cut.cutVal 13 ∅ gs x i := by
    rw [heq, ← prefix_value gs hlen hs i hi20 hi21 x]
  exact early_common_impossible (gs.take 5) (by simp only [List.length_take]; omega)
    (fun q hq => hg q (List.mem_of_mem_take hq)) gs[5] gs[6]
    (hg gs[5] (List.getElem_mem h5)) (hg gs[6] (List.getElem_mem h6)) c hc'.1 hc'.2.1 u v huv
    (by intro x hx; rw [hp x c hc'.2.2.1 hc'.2.2.2, hp x 18 (by decide) (by decide)]; exact hu x hx)
    (by intro x hx; rw [hp x c hc'.2.2.1 hc'.2.2.2, hp x 19 (by decide) (by decide)]; exact hv x hx)
    (by intro x hx; rw [hp x c hc'.2.2.1 hc'.2.2.2, hp x 18 (by decide) (by decide)]; exact hupperu x hx)
    (by intro x hx; rw [hp x c hc'.2.2.1 hc'.2.2.2, hp x 19 (by decide) (by decide)]; exact hupperv x hx)
    (by intro h; apply hnu; intro x; rw [← hp x c hc'.2.2.1 hc'.2.2.2, ← hp x 18 (by decide) (by decide)]; exact h x)
    (by intro h; apply hnv; intro x; rw [← hp x c hc'.2.2.1 hc'.2.2.2, ← hp x 19 (by decide) (by decide)]; exact h x)

end PEqualNP.Outside.L_meta_1024_aux.EarlyCommon

namespace PEqualNP.Outside.L_meta_1024_aux.OneAndCircuit
open PEqualNP.CircuitLowerBounds
def isAnd (g : Gate) : Bool := match g.op with
  | GateOp.and => true
  | _ => false
end PEqualNP.Outside.L_meta_1024_aux.OneAndCircuit

namespace PEqualNP.Outside.L_meta_1024_aux.PositiveCertificate

open PEqualNP.CircuitLowerBounds

def andCount (gs : List Gate) : ℕ := (gs.filter OneAndCircuit.isAnd).length

lemma andCount_snoc_and (gs : List Gate) (g : Gate) (hg : g.op = GateOp.and) :
    andCount (gs ++ [g]) = andCount gs + 1 := by
  simp [andCount, List.filter_append, OneAndCircuit.isAnd, hg]

lemma andCount_snoc_or (gs : List Gate) (g : Gate) (hg : g.op = GateOp.or) :
    andCount (gs ++ [g]) = andCount gs := by
  simp [andCount, List.filter_append, OneAndCircuit.isAnd, hg]

lemma positive_components {n : ℕ} (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x : Fin n → Bool) :
    ∃ (label : Fin n → ℕ) (wire : ℕ → ℕ),
      (∀ S : Finset (Fin n), S.card ≤ (S.image label).card + andCount gs) ∧
      ∀ i, Cut.cutVal n ∅ gs x i = true → ∀ y : Fin n → Bool,
        (∀ t, label t = wire i → x t = true → y t = true) →
        Cut.cutVal n ∅ gs y i = true := by
  classical
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨Fin.val, id, ?_, ?_⟩
    · intro S
      simp [andCount, Finset.card_image_of_injective _ Fin.val_injective]
    · intro i hi y hy
      rw [Cut.cutVal_nil] at hi ⊢
      by_cases hin : i < n
      · simp only [ite_true, Cut.source_eq, hin, dite_true] at hi ⊢
        exact hy ⟨i, hin⟩ rfl hi
      · simp [hin] at hi
  | append_singleton gs g ih =>
    have hgg := hg g (by simp)
    obtain ⟨label, wire, hcount, htrue⟩ := ih (fun h hh => hg h (by simp [hh]))
    rcases hgg.1 with hand | hor
    · obtain ⟨a, b, hinputs⟩ := Cut.two_inputs g.inputs hgg.2
      let merge (k : ℕ) := if k = wire b then wire a else k
      have ha : merge (wire a) = wire a := by simp [merge]
      have hb : merge (wire b) = wire a := by simp [merge]
      refine ⟨merge ∘ label, fun i => if i = n + gs.length then wire a else merge (wire i), ?_, ?_⟩
      · intro S
        have hsub : S.image label ⊆ insert (wire b) (S.image (merge ∘ label)) := by
          intro v hv
          obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hv
          by_cases he : label t = wire b
          · simp [he]
          · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨t, ht, by simp [merge, he]⟩)
        have hc := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
        have hs := hcount S
        rw [andCount_snoc_and gs g hand]
        omega
      · intro i hi y hy
        rw [Cut.cutVal_snoc] at hi ⊢
        by_cases hie : i = n + gs.length
        · simp only [hie, ite_true, Finset.notMem_empty, ite_false, hand, GateOp.eval,
            List.all_eq_true, List.mem_map, id_eq] at hi ⊢
          intro v hv
          obtain ⟨j, hj, rfl⟩ := hv
          apply htrue j (hi _ ⟨j, hj, rfl⟩) y
          intro t ht htx
          apply hy t
          · simp only [Function.comp_apply, hie, ite_true]
            rw [ht]
            rcases hinputs j hj with rfl | rfl
            · exact ha
            · exact hb
          · exact htx
        · simp only [hie, ite_false] at hi ⊢
          apply htrue i hi y
          intro t ht htx
          apply hy t
          · simp only [Function.comp_apply, hie, ite_false]
            rw [ht]
          · exact htx
    · by_cases hnew : g.op.eval (g.inputs.map fun j => Cut.cutVal n ∅ gs x j) = true
      · have hget : ∃ a ∈ g.inputs, Cut.cutVal n ∅ gs x a = true := by
          have he := hnew
          simp only [hor, GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at he
          obtain ⟨v, ⟨a, ha, rfl⟩, ht⟩ := he
          exact ⟨a, ha, ht⟩
        obtain ⟨a, ha, hax⟩ := hget
        refine ⟨label, fun i => if i = n + gs.length then wire a else wire i, ?_, ?_⟩
        · intro S
          rw [andCount_snoc_or gs g hor]
          exact hcount S
        · intro i hi y hy
          rw [Cut.cutVal_snoc] at hi ⊢
          by_cases hie : i = n + gs.length
          · simp only [hie, ite_true, Finset.notMem_empty, ite_false, hor, GateOp.eval,
              List.any_eq_true, List.mem_map, id_eq]
            have hay := htrue a hax y (by
              intro t ht htx
              exact hy t (by simpa [hie] using ht) htx)
            exact ⟨true, ⟨a, ha, hay⟩, rfl⟩
          · simp only [hie, ite_false] at hi ⊢
            exact htrue i hi y (fun t ht htx => hy t (by simpa [hie] using ht) htx)
      · refine ⟨label, fun i => if i = n + gs.length then 0 else wire i, ?_, ?_⟩
        · intro S
          rw [andCount_snoc_or gs g hor]
          exact hcount S
        · intro i hi y hy
          rw [Cut.cutVal_snoc] at hi ⊢
          by_cases hie : i = n + gs.length
          · simp only [hie, ite_true, Finset.notMem_empty, ite_false] at hi
            exact (hnew hi).elim
          · simp only [hie, ite_false] at hi ⊢
            exact htrue i hi y (fun t ht htx => hy t (by simpa [hie] using ht) htx)

lemma small_positive_certificate {n : ℕ} (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x : Fin n → Bool) (o : ℕ) (hx : Global.val gs x o = true) :
    ∃ T : Finset (Fin n),
      (∀ p ∈ T, x p = true) ∧ T.card ≤ andCount gs + 1 ∧
      Global.val gs (fun p => decide (p ∈ T)) o = true := by
  classical
  obtain ⟨label, wire, hcount, htrue⟩ := positive_components gs hg x
  let T := Finset.univ.filter (fun p => label p = wire o ∧ x p = true)
  have hT : ∀ p ∈ T, label p = wire o ∧ x p = true := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have hsmall : (T.image label).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hb
    exact (hT p hp).1.trans (hT q hq).1.symm
  refine ⟨T, fun p hp => (hT p hp).2, ?_, ?_⟩
  · have hc := hcount T
    omega
  · change Circuit.eval ⟨gs, o⟩ (List.ofFn (fun p => decide (p ∈ T))) = true
    rw [← Cut.cut_empty]
    apply htrue o
    · change Circuit.eval ⟨gs, o⟩ (List.ofFn x) = true at hx
      simpa only [Cut.cut_empty] using hx
    · intro p hp hpx
      apply decide_eq_true
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp, hpx⟩

end PEqualNP.Outside.L_meta_1024_aux.PositiveCertificate

namespace PEqualNP.Outside.L_meta_1024_aux.PositiveCertificate

open PEqualNP.CircuitLowerBounds

lemma abnormal_and_lower (gs : List Gate) (o : ℕ) (w : Fin 13)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ x, Support.Band x → Global.val gs x o = Support.target w x)
    (habnormal : Global.val gs (Global.Zof (Global.line w)) o = true) :
    8 ≤ andCount gs := by
  by_contra! hsmall
  obtain ⟨T, hT, hcard, htrue⟩ := small_positive_certificate gs hg
    (Global.Zof (Global.line w)) o habnormal
  have hTsub : T ⊆ Finset.univ \ Support.line w := by
    intro p hp
    have hn : p ∉ Support.line w := by
      have hpZ := hT p hp
      change decide (p ∉ Global.line w) = true at hpZ
      have hpnot : p ∉ Global.line w := of_decide_eq_true hpZ
      simpa only [Global.line, Support.line] using hpnot
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hn⟩
  obtain ⟨Y, hTY, hYsub, hYcard⟩ := Clamp.extend_eight w T hTsub (by omega)
  have hy := Bridge.val_mono gs (fun g hm => (hg g hm).1)
    (fun p => decide (p ∈ T)) (Clamp.fromTrue Y) (by
      intro p hp
      have hpT : p ∈ T := by simpa using hp
      exact decide_eq_true (hTY hpT)) o htrue
  rw [hcorrect _ (Clamp.fromTrue_band Y hYcard), Clamp.fromTrue_misses w Y hYsub] at hy
  cases hy

end PEqualNP.Outside.L_meta_1024_aux.PositiveCertificate

namespace PEqualNP.Outside.L_meta_1024_aux.Excess

open PEqualNP.CircuitLowerBounds

lemma support_univ (w : Fin 13) (f : (Fin 13 → Bool) → Bool)
    (hcorrect : ∀ x, Support.Band x → f x = Support.target w x)
    (hhigh : f (Support.fromZeros (Support.line w)) = true)
    (S : Finset (Fin 13)) (hsupport : Support.Supports f S) :
    S = Finset.univ := by
  classical
  apply Finset.eq_univ_of_forall
  intro p
  by_cases hp : p ∈ Support.line w
  · exact Support.support_contains_line w f hcorrect S hsupport hp
  · by_contra hnot
    have hband : Support.Band (Support.fromZeros (insert p (Support.line w))) := by
      left
      rw [Support.zeroSet_fromZeros, Finset.card_insert_of_notMem hp, Clamp.line_card]
    have htarget : Support.target w
        (Support.fromZeros (insert p (Support.line w))) = false := by
      have hn : ¬ ∃ q ∈ Support.line w,
          Support.fromZeros (insert p (Support.line w)) q = true := by
        rintro ⟨q, hq, hh⟩
        simp [Support.fromZeros, hq] at hh
      simp only [Support.target, hn, decide_false]
    have heq : f (Support.fromZeros (Support.line w)) =
        f (Support.fromZeros (insert p (Support.line w))) := by
      apply hsupport
      intro q hq
      have hqp : q ≠ p := by
        intro he
        subst q
        exact hnot hq
      simp [Support.fromZeros, hqp]
    rw [hhigh, hcorrect _ hband, htarget] at heq
    exact Bool.noConfusion heq

lemma mem_support (w : Fin 13) (f : (Fin 13 → Bool) → Bool)
    (hcorrect : ∀ x, Support.Band x → f x = Support.target w x)
    (hhigh : f (Support.fromZeros (Support.line w)) = true)
    (S : Finset (Fin 13)) (hsupport : Support.Supports f S) (p : Fin 13) : p ∈ S := by
  rw [support_univ w f hcorrect hhigh S hsupport]
  exact Finset.mem_univ p

lemma support_card (w : Fin 13) (f : (Fin 13 → Bool) → Bool)
    (hcorrect : ∀ x, Support.Band x → f x = Support.target w x)
    (hhigh : f (Support.fromZeros (Support.line w)) = true)
    (S : Finset (Fin 13)) (hsupport : Support.Supports f S) : S.card = 13 := by
  rw [support_univ w f hcorrect hhigh S hsupport]
  simp

lemma complement_false_of_support (w : Fin 13) (f : (Fin 13 → Bool) → Bool)
    (hcorrect : ∀ x, Support.Band x → f x = Support.target w x)
    (S : Finset (Fin 13)) (hsupport : Support.Supports f S) (hsmall : S.card ≤ 12) :
    f (Support.fromZeros (Support.line w)) = false := by
  cases hh : f (Support.fromZeros (Support.line w)) with
  | false => rfl
  | true =>
    have hc := support_card w f hcorrect hh S hsupport
    omega

lemma bounded_of_complement_false (w : Fin 13) (f : (Fin 13 → Bool) → Bool)
    (hmono : ∀ x y, (∀ p, x p = true → y p = true) → f x = true → f y = true)
    (hfalse : f (Support.fromZeros (Support.line w)) = false) :
    ∀ x, f x = true → Support.target w x = true := by
  intro x hx
  by_contra ht
  have hline : ∀ p ∈ Support.line w, x p ≠ true := by
    intro p hp hxp
    apply ht
    simp only [Support.target, decide_eq_true_eq]
    exact ⟨p, hp, hxp⟩
  have hle : ∀ p, x p = true → Support.fromZeros (Support.line w) p = true := by
    intro p hp
    have hn : p ∉ Support.line w := fun hm => hline p hm hp
    simp [Support.fromZeros, hn]
  have hh := hmono x (Support.fromZeros (Support.line w)) hle hx
  rw [hfalse] at hh
  exact Bool.noConfusion hh

lemma bounded_of_support (w : Fin 13) (f : (Fin 13 → Bool) → Bool)
    (hcorrect : ∀ x, Support.Band x → f x = Support.target w x)
    (hmono : ∀ x y, (∀ p, x p = true → y p = true) → f x = true → f y = true)
    (S : Finset (Fin 13)) (hsupport : Support.Supports f S) (hsmall : S.card ≤ 12) :
    ∀ x, f x = true → Support.target w x = true := by
  exact bounded_of_complement_false w f hmono
    (complement_false_of_support w f hcorrect S hsupport hsmall)

lemma raw_essential (gs : List Gate) (o : ℕ) (w : Fin 13)
    (hcorrect : ∀ x, Support.Band x →
      Circuit.eval ⟨gs, o⟩ (List.ofFn x) = Support.target w x)
    (hhigh : Circuit.eval ⟨gs, o⟩
      (List.ofFn (Support.fromZeros (Support.line w))) = true) (p : Fin 13) :
    p ∈ Cut.essential (M := 13) 13 ∅ gs o := by
  apply mem_support w (fun x => Circuit.eval ⟨gs, o⟩ (List.ofFn x))
    hcorrect hhigh (Cut.essential (M := 13) 13 ∅ gs o) ?_ p
  intro x y hxy
  change Circuit.eval ⟨gs, o⟩ (List.ofFn x) = Circuit.eval ⟨gs, o⟩ (List.ofFn y)
  rw [← Cut.cut_empty, ← Cut.cut_empty]
  exact Cut.essential_supports 13 ∅ gs o x y hxy

lemma circuit_length (gs : List Gate) (o : ℕ) (w : Fin 13)
    (hg : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (hcorrect : ∀ x, Support.Band x →
      Circuit.eval ⟨gs, o⟩ (List.ofFn x) = Support.target w x)
    (hhigh : Circuit.eval ⟨gs, o⟩
      (List.ofFn (Support.fromZeros (Support.line w))) = true) :
    12 ≤ gs.length := by
  have hraw : ∀ t ∈ Cut.essential (M := 13 + gs.length) 13 ∅ gs o, t.val < 13 := by
    intro t ht
    rcases Cut.essential_sources 13 ∅ gs o t ht with h | h
    · exact h
    · exact False.elim (Finset.notMem_empty _ h)
  have hc : (Cut.essential (M := 13 + gs.length) 13 ∅ gs o).card ≤ gs.length + 1 := by
    simpa using Cut.essential_bound (M := 13 + gs.length) 13 ∅ gs o hg
      (Finset.empty_subset _)
  obtain ⟨S, hS, hs⟩ := Cut.raw_support_exists (n := 13) ∅ gs o (gs.length + 1) hraw hc
  have hcard := support_card w (fun x => Circuit.eval ⟨gs, o⟩ (List.ofFn x))
    hcorrect hhigh S hs
  omega

lemma complement_false_of_short (gs : List Gate) (o : ℕ) (w : Fin 13)
    (hg : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (hcorrect : ∀ x, Support.Band x →
      Circuit.eval ⟨gs, o⟩ (List.ofFn x) = Support.target w x)
    (hsmall : gs.length ≤ 11) :
    Circuit.eval ⟨gs, o⟩ (List.ofFn (Support.fromZeros (Support.line w))) = false := by
  cases hh : Circuit.eval ⟨gs, o⟩
      (List.ofFn (Support.fromZeros (Support.line w))) with
  | false => rfl
  | true =>
    have hb := circuit_length gs o w hg hcorrect hh
    omega

lemma prefix_length (gs : List Gate) (o k : ℕ) (w : Fin 13)
    (hg : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (hcorrect : ∀ x, Support.Band x →
      Circuit.eval ⟨gs, o⟩ (List.ofFn x) = Support.target w x)
    (hhigh : Circuit.eval ⟨gs, o⟩
      (List.ofFn (Support.fromZeros (Support.line w))) = true)
    (hk : k ≤ gs.length) (ho : o < 13 + k) : 12 ≤ k := by
  have heq : ∀ x : Fin 13 → Bool,
      Circuit.eval ⟨gs.take k, o⟩ (List.ofFn x) =
        Circuit.eval ⟨gs, o⟩ (List.ofFn x) := by
    intro x
    rw [← Cut.cut_empty, ← Cut.cut_empty]
    exact (Cut.cutVal_take 13 ∅ gs x k o hk ho).symm
  have hb := circuit_length (gs.take k) o w
    (fun g hm => hg g (List.mem_of_mem_take hm))
    (fun x hx => (heq x).trans (hcorrect x hx))
    ((heq _).trans hhigh)
  simpa only [List.length_take, Nat.min_eq_left hk] using hb

end PEqualNP.Outside.L_meta_1024_aux.Excess

namespace PEqualNP.Outside.L_meta_1024_aux.Minterms
lemma avoid_extension (S : Finset (Fin 13)) (p : Fin 13) (hp : p ∉ S)
    (hs : S.card ≤ 6) :
    ∃ T : Finset (Fin 13), S ⊆ T ∧ T.card = 6 ∧ p ∉ T := by
  have hsub : S ⊆ Finset.univ.erase p := by
    intro q hq
    exact Finset.mem_erase.mpr ⟨fun h => hp (h ▸ hq), Finset.mem_univ q⟩
  have hc : 6 ≤ (Finset.univ.erase p).card := by simp
  obtain ⟨T, hST, hT, hcard⟩ := Finset.exists_subsuperset_card_eq hsub hs hc
  exact ⟨T, hST, hcard, fun h => (Finset.mem_erase.mp (hT h)).1 rfl⟩

end PEqualNP.Outside.L_meta_1024_aux.Minterms

namespace PEqualNP.Outside.L_meta_1024_aux.FalsePruning

open PEqualNP.CircuitLowerBounds

abbrev Entry := ℕ × Finset (Fin 13)

def emptyEntry : Entry := (0, ∅)

def hit (S : Finset (Fin 13)) (x : Fin 13 → Bool) : Bool :=
  decide (∃ p ∈ S, x p = true)

lemma hit_empty (x : Fin 13 → Bool) : hit ∅ x = false := by simp [hit]

lemma hit_union (S T : Finset (Fin 13)) (x : Fin 13 → Bool) :
    hit (S ∪ T) x = (hit S x || hit T x) := by
  apply Bool.eq_iff_iff.mpr
  simp [hit, Finset.mem_union, or_and_right, exists_or]

def readEntry (es : List Entry) (i : ℕ) : Entry := es.getD i emptyEntry

def selected (e : ℕ → Entry) (ins : List ℕ) : List ℕ :=
  match ins with
  | [] => []
  | [a] => [a]
  | a :: b :: _ => if (e a).1 ≤ (e b).1 then [a] else [b]

def profile (e : ℕ → Entry) (g : Gate) : Entry :=
  match g.op with
  | GateOp.and => match g.inputs with
    | [] => (5, ∅)
    | [a] => e a
    | a :: b :: _ => if (e a).1 ≤ (e b).1 then e a else e b
  | _ =>
    (min 5 ((g.inputs.map fun i => (e i).1).sum),
      g.inputs.foldr (fun i S => (e i).2 ∪ S) ∅)

def rewritten (e : ℕ → Entry) (g : Gate) : Gate :=
  match g.op with
  | GateOp.and => match g.inputs with
    | [] => g
    | _ :: _ => ⟨GateOp.or, selected e g.inputs⟩
  | _ => g

lemma gate_spec (e : ℕ → Entry) (g : Gate)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x : Fin 13 → Bool) (old new : ℕ → Bool)
    (hdom : ∀ i, old i = true → new i = true)
    (he : ∀ i, (e i).1 ≤ 4 → (e i).2.card ≤ (e i).1 ∧ new i = hit (e i).2 x) :
    ((rewritten e g).op = GateOp.and ∨ (rewritten e g).op = GateOp.or) ∧
    (rewritten e g).inputs.length ≤ 2 ∧
    (g.op.eval (g.inputs.map old) = true →
      (rewritten e g).op.eval ((rewritten e g).inputs.map new) = true) ∧
    ((profile e g).1 ≤ 4 →
      (profile e g).2.card ≤ (profile e g).1 ∧
      (rewritten e g).op.eval ((rewritten e g).inputs.map new) = hit (profile e g).2 x) := by
  rcases g with ⟨op, ins⟩
  rcases hg with ⟨hop, hlen⟩
  simp only at hop hlen ⊢
  rcases hop with rfl | rfl
  · match ins, hlen with
    | [], _ => simp [rewritten, profile, GateOp.eval]
    | [a], _ =>
      simpa [rewritten, selected, profile, GateOp.eval] using
        (show (GateOp.or = GateOp.and ∨ GateOp.or = GateOp.or) ∧
          1 ≤ 2 ∧ (old a = true → new a = true) ∧
          ((e a).1 ≤ 4 → (e a).2.card ≤ (e a).1 ∧ new a = hit (e a).2 x) from
          ⟨Or.inr rfl, by omega, hdom a, he a⟩)
    | [a, b], _ =>
      by_cases hab : (e a).1 ≤ (e b).1
      · simp only [rewritten, profile, selected, if_pos hab]
        refine ⟨by simp, by simp, ?_, ?_⟩
        · simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
            List.all_nil, List.any_cons, List.any_nil, id_eq, Bool.and_true, Bool.or_false]
          intro hh
          have hboth : old a = true ∧ old b = true := by simpa using hh
          exact hdom a hboth.1
        · simpa [GateOp.eval] using he a
      · simp only [rewritten, profile, selected, if_neg hab]
        refine ⟨by simp, by simp, ?_, ?_⟩
        · simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
            List.all_nil, List.any_cons, List.any_nil, id_eq, Bool.and_true, Bool.or_false]
          intro hh
          have hboth : old a = true ∧ old b = true := by simpa using hh
          exact hdom b hboth.2
        · simpa [GateOp.eval] using he b
    | _ :: _ :: _ :: _, hh => simp at hh
  · match ins, hlen with
    | [], _ => simp [rewritten, profile, GateOp.eval, hit_empty]
    | [a], _ =>
      simp only [rewritten, profile,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
        List.foldr_cons, List.foldr_nil, Finset.union_empty]
      refine ⟨by simp, by simp, ?_, ?_⟩
      · simpa [GateOp.eval] using hdom a
      · intro hc
        have ha : (e a).1 ≤ 4 := by omega
        have hm : min 5 (e a).1 = (e a).1 := Nat.min_eq_right (by omega)
        rw [hm]
        simpa [GateOp.eval] using he a ha
    | [a, b], _ =>
      simp only [rewritten, profile,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
        List.foldr_cons, List.foldr_nil, Finset.union_empty]
      refine ⟨by simp, by simp, ?_, ?_⟩
      · simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
          List.any_nil, id_eq, Bool.or_false, Bool.or_eq_true]
        exact Or.imp (hdom a) (hdom b)
      · intro hc
        have hab : (e a).1 + (e b).1 ≤ 4 := by omega
        have ha := he a (by omega)
        have hb := he b (by omega)
        have hm : min 5 ((e a).1 + (e b).1) = (e a).1 + (e b).1 :=
          Nat.min_eq_right (by omega)
        refine ⟨?_, ?_⟩
        · rw [hm]
          exact (Finset.card_union_le _ _).trans (Nat.add_le_add ha.1 hb.1)
        · simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
            List.any_nil, id_eq, Bool.or_false, ha.2, hb.2, hit_union]
    | _ :: _ :: _ :: _, hh => simp at hh

structure State where
  entries : List Entry
  gates : List Gate

def initial : State := ⟨List.ofFn (fun p : Fin 13 => (1, {p})), []⟩

def step (s : State) (g : Gate) : State :=
  ⟨s.entries ++ [profile (readEntry s.entries) g],
    s.gates ++ [rewritten (readEntry s.entries) g]⟩

def build (gs : List Gate) : State := gs.foldl step initial

def cost (gs : List Gate) (o : ℕ) : ℕ := (readEntry (build gs).entries o).1

lemma read_append (es : List Entry) (e : Entry) (i : ℕ) :
    readEntry (es ++ [e]) i = if i = es.length then e else readEntry es i := by
  unfold readEntry
  rcases lt_trichotomy i es.length with h | h | h
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left h]
  · rw [if_pos h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [h]
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

lemma build_snoc (gs : List Gate) (g : Gate) : build (gs ++ [g]) = step (build gs) g := by
  simp [build, List.foldl_append]

lemma build_lengths (gs : List Gate) :
    (build gs).entries.length = 13 + gs.length ∧ (build gs).gates.length = gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [build, initial]
  | append_singleton gs g ih =>
    rw [build_snoc]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma rewritten_allowed (e : ℕ → Entry) (g : Gate)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ((rewritten e g).op = GateOp.and ∨ (rewritten e g).op = GateOp.or) ∧
      (rewritten e g).inputs.length ≤ 2 := by
  rcases g with ⟨op, ins⟩
  rcases hg with ⟨hop, hlen⟩
  simp only at hop hlen ⊢
  rcases hop with rfl | rfl
  · match ins, hlen with
    | [], _ => simp [rewritten]
    | [a], _ => simp [rewritten, selected]
    | [a,b], _ =>
      by_cases h : (e a).1 ≤ (e b).1 <;> simp [rewritten, selected, h]
    | _ :: _ :: _ :: _, hh => simp at hh
  · simpa [rewritten] using hlen

lemma build_allowed (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ g ∈ (build gs).gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  induction gs using List.reverseRecOn with
  | nil => simp [build, initial]
  | append_singleton gs g ih =>
    rw [build_snoc]
    intro a ha
    simp only [step, List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | rfl
    · exact ih (fun b hb => hg b (by simp [hb])) a ha
    · exact rewritten_allowed _ g (hg g (by simp))

lemma wire_spec (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x : Fin 13 → Bool) (i : ℕ) :
    (Global.val gs x i = true → Global.val (build gs).gates x i = true) ∧
    ((readEntry (build gs).entries i).1 ≤ 4 →
      (readEntry (build gs).entries i).2.card ≤ (readEntry (build gs).entries i).1 ∧
      Global.val (build gs).gates x i = hit (readEntry (build gs).entries i).2 x) := by
  induction gs using List.reverseRecOn generalizing i with
  | nil =>
    by_cases hi : i < 13
    · have hr : readEntry initial.entries i = (1, {⟨i, hi⟩}) := by
        simp only [readEntry, initial, List.getD_eq_getElem?_getD,
          List.getElem?_ofFn, hi, ↓reduceDIte, Option.getD_some]
      change (Global.val [] x i = true → Global.val [] x i = true) ∧ _
      simp only [build, List.foldl_nil, hr]
      simp [initial, Global.val_nil, hi, hit]
    · simp [build, initial, readEntry, emptyEntry, Global.val_nil, hit,
        Nat.le_of_not_lt hi, hi]
  | append_singleton gs g ih =>
    have hgs : ∀ a ∈ gs,
        (a.op = GateOp.and ∨ a.op = GateOp.or) ∧ a.inputs.length ≤ 2 := by
      intro a ha
      exact hg a (by simp [ha])
    have hi := ih hgs
    have hs := gate_spec (readEntry (build gs).entries) g (hg g (by simp)) x
      (Global.val gs x) (Global.val (build gs).gates x)
      (fun j => (hi j).1) (fun j => (hi j).2)
    simp only [build_snoc, step, read_append, Global.val_snoc,
      (build_lengths gs).1, (build_lengths gs).2]
    by_cases he : i = 13 + gs.length
    · simp only [if_pos he]
      exact ⟨hs.2.2.1, hs.2.2.2⟩
    · simp only [if_neg he]
      exact hi i

lemma support_eq_line (w : Fin 13) (f : (Fin 13 → Bool) → Bool)
    (hcorrect : ∀ x, Support.Band x → f x = Support.target w x)
    (S : Finset (Fin 13)) (hS : S.card ≤ 4)
    (hdom : ∀ x, f x = true → hit S x = true) : S = Support.line w := by
  classical
  have hsub : Support.line w ⊆ S := by
    intro p hp
    by_contra hn
    obtain ⟨T, hST, hT, hpT⟩ := Minterms.avoid_extension S p hn (by omega)
    have hb : Support.Band (Support.fromZeros T) := by
      right
      rw [Support.zeroSet_fromZeros, hT]
    have ht : Support.target w (Support.fromZeros T) = true := by
      simp only [Support.target, decide_eq_true_eq]
      exact ⟨p, hp, by simp [Support.fromZeros, hpT]⟩
    have hh := hdom (Support.fromZeros T) ((hcorrect _ hb).trans ht)
    simp only [hit, decide_eq_true_eq] at hh
    obtain ⟨q, hq, hxq⟩ := hh
    have hqT := hST hq
    simp [Support.fromZeros, hqT] at hxq
  apply (Finset.eq_of_subset_of_card_le hsub ?_).symm
  rw [Clamp.line_card]
  exact hS

lemma low_cost_bound (gs : List Gate) (out : Fin 13 → ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ (w : Fin 13) (x : Fin 13 → Bool), Support.Band x →
      Circuit.eval ⟨gs, out w⟩ (List.ofFn x) = Support.target w x)
    (hcost : ∀ w, cost gs (out w) ≤ 4) : 39 ≤ gs.length := by
  have hglob : ∀ (w : Fin 13) (x : Fin 13 → Bool),
      Circuit.eval ⟨(build gs).gates, out w⟩ (List.ofFn x) =
        decide (∃ p ∈ Global.line w, x p = true) := by
    intro w x
    let S := (readEntry (build gs).entries (out w)).2
    have hc : (readEntry (build gs).entries (out w)).1 ≤ 4 := hcost w
    have hw := wire_spec gs hg x (out w)
    have hcard : S.card ≤ 4 := (hw.2 hc).1.trans hc
    have hdom : ∀ y, Circuit.eval ⟨gs, out w⟩ (List.ofFn y) = true → hit S y = true := by
      intro y hy
      have hh := wire_spec gs hg y (out w)
      exact (hh.2 hc).2.symm.trans (hh.1 hy)
    have hline := support_eq_line w (fun y => Circuit.eval ⟨gs, out w⟩ (List.ofFn y))
      (hcorrect w) S hcard hdom
    change Global.val (build gs).gates x (out w) = Support.target w x
    rw [(hw.2 hc).2]
    change hit S x = Support.target w x
    rw [hline]
    rfl
  have hb := Global.global_bound (build gs).gates out (build_allowed gs hg) hglob
  simpa only [(build_lengths gs).2] using hb

lemma some_large_cost (gs : List Gate) (out : Fin 13 → ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ (w : Fin 13) (x : Fin 13 → Bool), Support.Band x →
      Circuit.eval ⟨gs, out w⟩ (List.ofFn x) = Support.target w x)
    (hsmall : gs.length < 39) : ∃ w, 5 ≤ cost gs (out w) := by
  by_contra! hn
  have hc : ∀ w, cost gs (out w) ≤ 4 := fun w => by have h := hn w; omega
  have hb := low_cost_bound gs out hg hcorrect hc
  omega

end PEqualNP.Outside.L_meta_1024_aux.FalsePruning

namespace PEqualNP.Outside.L_meta_1024_aux.Collective

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_1024.OrOnly

abbrev V (C : Circuit) (x : Fin 13 → Bool) (i : ℕ) : Bool := value C x i

def readAt (C : Circuit) (x : Fin 13 → Bool) (k r : ℕ) : Bool :=
  if r < 13 + k then V C x r else false

def Good (C : Circuit) (z : Fin 13 → Bool) (pick : ℕ → ℕ) : Prop :=
  ∀ k (hk : k < C.gates.length), C.gates[k].op = GateOp.and →
    V C z (13 + k) = false →
    pick k ∈ C.gates[k].inputs ∧ readAt C z k (pick k) = false

lemma good_exists (C : Circuit) (z : Fin 13 → Bool) : ∃ pick, Good C z pick := by
  classical
  have choice : ∀ k, ∃ r, ∀ (hk : k < C.gates.length),
      C.gates[k].op = GateOp.and → V C z (13 + k) = false →
      r ∈ C.gates[k].inputs ∧ readAt C z k r = false := by
    intro k
    by_cases hk : k < C.gates.length
    · by_cases hop : C.gates[k].op = GateOp.and
      · by_cases hz : V C z (13 + k) = false
        · have hn : ¬ ∀ r ∈ C.gates[k].inputs, r < 13 + k ∧ V C z r = true := by
            intro hh
            have ht := (and_value C k hk hop z).mpr hh
            change V C z (13 + k) = true at ht
            rw [hz] at ht
            exact Bool.noConfusion ht
          push_neg at hn
          obtain ⟨r, hr, hbad⟩ := hn
          refine ⟨r, fun _ _ _ => ⟨hr, ?_⟩⟩
          unfold readAt
          by_cases hlt : r < 13 + k
          · simp only [hlt, ite_true]
            have hnt : V C z r ≠ true := hbad hlt
            cases hv : V C z r <;> simp_all
          · simp [hlt]
        · exact ⟨0, fun _ _ h => (hz h).elim⟩
      · exact ⟨0, fun _ h _ => (hop h).elim⟩
    · exact ⟨0, fun h => (hk h).elim⟩
  choose pick hp using choice
  exact ⟨pick, hp⟩

def Edge (C : Circuit) (z : Fin 13 → Bool) (pick : ℕ → ℕ) (a b : ℕ) : Prop :=
  ∃ (k : ℕ) (hk : k < C.gates.length), b = 13 + k ∧ a < b ∧ a ∈ C.gates[k].inputs ∧
    (C.gates[k].op = GateOp.or ∨ (C.gates[k].op = GateOp.and ∧ a = pick k)) ∧
    V C z a = false ∧ V C z b = false

def cone (C : Circuit) (z : Fin 13 → Bool) (pick : ℕ → ℕ) (o : ℕ) : Set ℕ :=
  {i | Relation.ReflTransGen (Edge C z pick) i o}

lemma edge_lt {C : Circuit} {z : Fin 13 → Bool} {pick : ℕ → ℕ} {a b : ℕ}
    (h : Edge C z pick a b) : a < b := by
  obtain ⟨k, hk, he, hlt, hrest⟩ := h
  exact hlt

lemma edge_false {C : Circuit} {z : Fin 13 → Bool} {pick : ℕ → ℕ} {a b : ℕ}
    (h : Edge C z pick a b) : V C z a = false ∧ V C z b = false := by
  obtain ⟨k, hk, he, hlt, hm, hop, ha, hb⟩ := h
  exact ⟨ha, hb⟩

lemma cone_false (C : Circuit) (z : Fin 13 → Bool) (pick : ℕ → ℕ) (o : ℕ)
    (ho : V C z o = false) {i : ℕ} (hi : i ∈ cone C z pick o) : V C z i = false := by
  rcases Relation.ReflTransGen.cases_head hi with rfl | ⟨j, hij, hjo⟩
  · exact ho
  · exact (edge_false hij).1

lemma positive_parent (C : Circuit) (z x : Fin 13 → Bool) (pick : ℕ → ℕ)
    (hpick : Good C z pick)
    (hg : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (i : ℕ) (hi : 13 ≤ i) (hz : V C z i = false) (hx : V C x i = true) :
    ∃ j, Edge C z pick j i ∧ V C x j = true := by
  have hil : i < 13 + C.gates.length := by
    by_contra hn
    have hf := missing_value C x i (by unfold Circuit.size; omega)
    change V C x i = false at hf
    rw [hf] at hx
    exact Bool.noConfusion hx
  let k := i - 13
  have hk : k < C.gates.length := by omega
  have he : i = 13 + k := by omega
  obtain hop | hop := hg C.gates[k] (List.getElem_mem hk)
  · have hz' : V C z (13 + k) = false := he ▸ hz
    have hx' : V C x (13 + k) = true := he ▸ hx
    obtain ⟨hm, hfalse⟩ := hpick k hk hop hz'
    obtain ⟨hlt, htrue⟩ := (and_value C k hk hop x).mp hx' (pick k) hm
    have hf : V C z (pick k) = false := by simpa [readAt, hlt] using hfalse
    exact ⟨pick k, ⟨k, hk, he, by omega, hm, Or.inr ⟨hop, rfl⟩, hf, hz⟩, htrue⟩
  · have hx' : V C x (13 + k) = true := he ▸ hx
    obtain ⟨j, hm, hlt, ht⟩ := (or_value C k hk hop x).mp hx'
    have hf : V C z j = false := by
      cases hv : V C z j
      · rfl
      · have hz' := (or_value C k hk hop z).mpr ⟨j, hm, hlt, hv⟩
        change V C z (13 + k) = true at hz'
        rw [← he, hz] at hz'
        exact Bool.noConfusion hz'
    exact ⟨j, ⟨k, hk, he, by omega, hm, Or.inl hop, hf, hz⟩, ht⟩

def Within (C : Circuit) (z : Fin 13 → Bool) (pick : ℕ → ℕ)
    (o : ℕ) (B : Set ℕ) (a b : ℕ) : Prop :=
  Edge C z pick a b ∧ a ∈ cone C z pick o ∧ b ∈ cone C z pick o ∧ a ∉ B ∧ b ∉ B

lemma path_avoiding (C : Circuit) (z x : Fin 13 → Bool) (pick : ℕ → ℕ)
    (hpick : Good C z pick)
    (hg : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (o : ℕ) (hz : V C z o = false) (hx : V C x o = true)
    (B : Set ℕ) (hB : ∀ i ∈ B, V C x i = false)
    (p : Fin 13) (hunique : ∀ q : Fin 13, z q = false → x q = true → q = p) :
    p.val ∈ cone C z pick o ∧ p.val ∉ B ∧
      Relation.ReflTransGen (Within C z pick o B) p.val o := by
  have walk : ∀ i, i ∈ cone C z pick o → V C x i = true →
      p.val ∈ cone C z pick o ∧ p.val ∉ B ∧
        Relation.ReflTransGen (Within C z pick o B) p.val i := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hic hix
      have hib : i ∉ B := by
        intro hb
        rw [hB i hb] at hix
        exact Bool.noConfusion hix
      have hiz := cone_false C z pick o hz hic
      by_cases hir : i < 13
      · let q : Fin 13 := ⟨i, hir⟩
        have hqz : z q = false := by simpa only [← input_value C z q] using hiz
        have hqx : x q = true := by simpa only [← input_value C x q] using hix
        have hqp := hunique q hqz hqx
        have hip : i = p.val := congrArg Fin.val hqp
        subst i
        exact ⟨hic, hib, Relation.ReflTransGen.refl⟩
      · obtain ⟨j, hji, hjx⟩ := positive_parent C z x pick hpick hg i (by omega) hiz hix
        have hjc : j ∈ cone C z pick o :=
          (Relation.ReflTransGen.single hji).trans hic
        obtain ⟨hpc, hpb, hpj⟩ := ih j (edge_lt hji) hjc hjx
        have hjb : j ∉ B := by
          intro hb
          rw [hB j hb] at hjx
          exact Bool.noConfusion hjx
        exact ⟨hpc, hpb, hpj.tail ⟨hji, hjc, hic, hjb, hib⟩⟩
  exact walk o Relation.ReflTransGen.refl hx

lemma line_inter_nonempty : ∀ w v : Fin 13, (Global.line w ∩ Global.line v).Nonempty := by
  decide +kernel

lemma separating_card (w v p : Fin 13) (hwv : w ≠ v)
    (hp : p ∈ Global.line w) (hpv : p ∉ Global.line v) :
    (Global.line v ∪ (Global.line w).erase p).card = 6 := by
  have hcL : (Global.line w).card = 4 := Clamp.line_card w
  have hcM : (Global.line v).card = 4 := Clamp.line_card v
  have hi : (Global.line v ∩ Global.line w).card = 1 := by
    have hu := Global.line_intersection v w (Ne.symm hwv)
    have hl := Finset.card_pos.mpr (line_inter_nonempty v w)
    omega
  have he : Global.line v ∩ (Global.line w).erase p = Global.line v ∩ Global.line w := by
    ext q
    simp only [Finset.mem_inter, Finset.mem_erase]
    constructor
    · intro h
      exact ⟨h.1, h.2.2⟩
    · intro h
      exact ⟨h.1, fun hqp => hpv (hqp ▸ h.1), h.2⟩
  have hc := Finset.card_union_add_card_inter (Global.line v) ((Global.line w).erase p)
  rw [he, hi, hcM, Finset.card_erase_of_mem hp, hcL] at hc
  omega

lemma collective_avoidance (C : Circuit) (w v : Fin 13) (oL oM : ℕ)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ x, Support.Band x → V C x oL = Support.target w x)
    (hL : V C (Global.Zof (Global.line w)) oL = false)
    (hM : V C (Global.Zof (Global.line v)) oM = false)
    (pickL pickM : ℕ → ℕ)
    (hpickL : Good C (Global.Zof (Global.line w)) pickL)
    (hwv : w ≠ v) (p : Fin 13) (hp : p ∈ Global.line w) (hpv : p ∉ Global.line v) :
    p.val ∈ cone C (Global.Zof (Global.line w)) pickL oL ∧
    p.val ∉ cone C (Global.Zof (Global.line v)) pickM oM ∧
    Relation.ReflTransGen
      (Within C (Global.Zof (Global.line w)) pickL oL
        (cone C (Global.Zof (Global.line v)) pickM oM)) p.val oL := by
  let S := Global.line v ∪ (Global.line w).erase p
  let x := Support.fromZeros S
  have hcard : S.card = 6 := separating_card w v p hwv hp hpv
  have hb : Support.Band x := by
    right
    simpa only [x, Support.zeroSet_fromZeros] using hcard
  have hpx : x p = true := by simp [x, S, Support.fromZeros, hpv]
  have ht : Support.target w x = true := by
    exact decide_eq_true (show ∃ q ∈ Support.line w, x q = true from ⟨p, hp, hpx⟩)
  have hout : V C x oL = true := (hcorrect x hb).trans ht
  have hxy : ∀ q, x q = true → Global.Zof (Global.line v) q = true := by
    intro q hq
    simp only [x, Support.fromZeros, decide_eq_true_eq] at hq
    simp only [Global.Zof, decide_eq_true_eq]
    intro hqv
    exact hq (Finset.mem_union_left _ hqv)
  have hblocked : ∀ i ∈ cone C (Global.Zof (Global.line v)) pickM oM,
      V C x i = false := by
    intro i hi
    have hm := cone_false C _ pickM oM hM hi
    cases hv : V C x i
    · rfl
    · have hmt := mono C hg x (Global.Zof (Global.line v)) hxy i hv
      change V C (Global.Zof (Global.line v)) i = true at hmt
      rw [hm] at hmt
      exact Bool.noConfusion hmt
  apply path_avoiding C _ x pickL hpickL (fun g hg' => (hg g hg').1) oL hL hout
    _ hblocked p
  intro q hqz hqx
  have hqL : q ∈ Global.line w := by
    simpa only [Global.Zof, decide_eq_false_iff_not, not_not] using hqz
  have hqS : q ∉ S := by simpa only [x, Support.fromZeros, decide_eq_true_eq] using hqx
  by_contra hqp
  exact hqS (Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hqp, hqL⟩))

end PEqualNP.Outside.L_meta_1024_aux.Collective

namespace PEqualNP.Outside.L_meta_1024_aux.PrivateSurgery
open PEqualNP.CircuitLowerBounds

lemma context_private (gs : List Gate) (o i : ℕ) (w : Fin 13)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hcorrect : ∀ x : Fin 13 → Bool, Support.Band x →
      Global.val gs x o = Support.target w x)
    (C : Finset (Fin 13)) (hC : C ⊆ Global.line w) (hc : C.card ≤ 2)
    (hcontext : ∀ x : Fin 13 → Bool, (∀ p ∈ C, x p = false) →
      Global.val gs x i = false → Global.val gs x o = false) :
    ∀ v : Fin 13, v ≠ w → Global.val gs (Global.Zof (Global.line v)) i = true := by
  classical
  intro v hv
  have hmeet := Global.line_intersection w v hv.symm
  have hcover : ¬ Global.line w ⊆ C ∪ Global.line v := by
    intro hh
    have hs : Global.line w ⊆ C ∪ (Global.line w ∩ Global.line v) := by
      intro p hp
      rcases Finset.mem_union.mp (hh hp) with hpC | hpv
      · exact Finset.mem_union_left _ hpC
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hp, hpv⟩)
    have hcard := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
    rw [Global.line_card] at hcard
    omega
  obtain ⟨p, hp, hpnot⟩ := Finset.not_subset.mp hcover
  have hsub : C ∪ Global.line v ⊆ Finset.univ.erase p := by
    intro q hq
    exact Finset.mem_erase.mpr ⟨by intro he; subst q; exact hpnot hq, Finset.mem_univ _⟩
  have hsmall : (C ∪ Global.line v).card ≤ 6 := by
    have hh := Finset.card_union_le C (Global.line v)
    rw [Global.line_card] at hh
    omega
  obtain ⟨T, hCT, hT, hTcard⟩ := Finset.exists_subsuperset_card_eq hsub hsmall
    (show 6 ≤ (Finset.univ.erase p : Finset (Fin 13)).card by simp)
  let x := Global.Zof T
  have hxband : Support.Band x := by
    have he : Support.zeroSet x = T := by
      ext q
      simp [Support.zeroSet, x, Global.Zof]
    right
    rw [he]
    exact hTcard
  have hxC : ∀ q ∈ C, x q = false := by
    intro q hq
    simp [x, Global.Zof, hCT (Finset.mem_union_left _ hq)]
  have hxv : ∀ q, x q = true → Global.Zof (Global.line v) q = true := by
    intro q hq
    have hqn : q ∉ T := by simpa [x, Global.Zof] using hq
    simp only [Global.Zof, decide_eq_true_eq]
    exact fun hqv => hqn (hCT (Finset.mem_union_right _ hqv))
  cases hi : Global.val gs (Global.Zof (Global.line v)) i with
  | true => rfl
  | false =>
    have hxi : Global.val gs x i = false := by
      cases he : Global.val gs x i
      · rfl
      · have hh := Bridge.val_mono gs hg x (Global.Zof (Global.line v)) hxv i he
        rw [hi] at hh
        exact Bool.noConfusion hh
    have hxo := hcontext x hxC hxi
    have htarget : Support.target w x = true := by
      apply decide_eq_true_iff.mpr
      refine ⟨p, hp, ?_⟩
      simp only [x, Global.Zof, decide_eq_true_eq]
      exact fun hpt => (Finset.mem_erase.mp (hT hpt)).1 rfl
    rw [hcorrect x hxband, htarget] at hxo
    exact Bool.noConfusion hxo

lemma normal_clamp (gs : List Gate) (o : ℕ) (w : Fin 13) (P : Finset ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ x : Fin 13 → Bool, Support.Band x →
      Global.val gs x o = Support.target w x)
    (hnormal : Global.val gs (Global.Zof (Global.line w)) o = false)
    (hprivate : ∀ i ∈ P, Global.val gs (Global.Zof (Global.line w)) i = true) :
    Global.val (Sink.transform 13 P gs) (Global.Zof (Global.line w)) o = false ∧
    ∀ x : Fin 13 → Bool, Support.Band x →
      Global.val (Sink.transform 13 P gs) x o = Support.target w x := by
  have hop := fun g hg' => (hg g hg').1
  have hn := (Sink.output_eq P gs hop (Global.Zof (Global.line w)) o
    (Bridge.output_index gs o w hcorrect) (fun i hi _ => hprivate i hi)).trans hnormal
  refine ⟨hn, ?_⟩
  intro x hx
  cases ht : Support.target w x
  · have hxz : ∀ p, x p = true → Global.Zof (Global.line w) p = true := by
      intro p hp
      simp only [Global.Zof, decide_eq_true_eq]
      intro hpl
      have hh : Support.target w x = true := decide_eq_true_iff.mpr ⟨p, hpl, hp⟩
      rw [ht] at hh
      exact Bool.noConfusion hh
    cases he : Global.val (Sink.transform 13 P gs) x o
    · rfl
    · have hh := Bridge.val_mono (Sink.transform 13 P gs)
        (fun g hm => (Sink.transform_allowed 13 P gs hg g hm).1)
        x (Global.Zof (Global.line w)) hxz o he
      rw [hn] at hh
      exact Bool.noConfusion hh
  · exact Sink.val_ge P gs hop x o ((hcorrect x hx).trans ht)

lemma rebuild (k : ℕ) (gs : List Gate) (out : Fin k → ℕ)
    (lineId : Fin k → Fin 13) (u₀ : Fin k)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ u (x : Fin 13 → Bool), Support.Band x →
      Global.val gs x (out u) = Support.target (lineId u) x)
    (hnormal : ∀ u, Global.val gs (Global.Zof (Global.line (lineId u))) (out u) = false)
    (P : Finset ℕ) (hP : P ⊆ Finset.Ico 13 (13 + gs.length)) (hcard : 3 ≤ P.card)
    (hprivate : ∀ i ∈ P, ∀ u, u ≠ u₀ →
      Global.val gs (Global.Zof (Global.line (lineId u))) i = true) :
    ∃ (cs : List Gate) (co : Fin k → ℕ),
      cs.length ≤ gs.length ∧
      (∀ g ∈ cs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      (∀ u (x : Fin 13 → Bool), Support.Band x →
        Global.val cs x (co u) = Support.target (lineId u) x) ∧
      (∀ x : Fin 13 → Bool, Global.val cs x (co u₀) = Support.target (lineId u₀) x) := by
  classical
  let T := Sink.transform 13 P gs
  let U := Dead.paidCode 13 P gs
  let cs := AppendLine.appendLine U (lineId u₀)
  let co : Fin k → ℕ := fun u => if u = u₀ then 15 + U.length else Dead.paidIndex 13 P gs (out u)
  have hkept (u : Fin k) (hu : u ≠ u₀) : out u ∉ P := by
    intro hp
    have hh := hprivate (out u) hp u hu
    rw [hnormal u] at hh
    exact Bool.noConfusion hh
  have heval (u : Fin k) (hu : u ≠ u₀) (x : Fin 13 → Bool) :
      Global.val U x (Dead.paidIndex 13 P gs (out u)) = Global.val T x (out u) := by
    apply Dead.eval P T (Dead.transform_noReads 13 P gs) x (out u)
      (by simpa [T, Sink.transform_length] using (Bridge.output_index gs (out u) (lineId u) (hcorrect u)).2)
      (hkept u hu)
  have hvalid (u : Fin k) (hu : u ≠ u₀) : Dead.paidIndex 13 P gs (out u) < 13 + U.length :=
    Dead.mapped_valid 13 P T (out u)
      (by simpa [T, Sink.transform_length] using (Bridge.output_index gs (out u) (lineId u) (hcorrect u)).2)
      (hkept u hu)
  refine ⟨cs, co, ?_, AppendLine.allowed U (lineId u₀) (Dead.paid_allowed 13 P gs hg), ?_, ?_⟩
  · have hpbound : P.card ≤ gs.length := by simpa using Finset.card_le_card hP
    change (AppendLine.appendLine U (lineId u₀)).length ≤ gs.length
    rw [AppendLine.length]
    have hu : U.length = gs.length - P.card := by
      exact (Dead.paid_length 13 P gs).trans (Cut.unpaid_eq_sub 13 P gs hP)
    rw [hu]
    omega
  · intro u x hx
    by_cases hu : u = u₀
    · subst u
      simpa only [co, if_pos rfl] using AppendLine.eval U (lineId u₀) x
    · change Global.val cs x (if u = u₀ then _ else _) = _
      rw [if_neg hu, AppendLine.old U (lineId u₀) x _ (hvalid u hu), heval u hu x]
      exact (normal_clamp gs (out u) (lineId u) P hg (hcorrect u) (hnormal u)
        (fun i hi => hprivate i hi u hu)).2 x hx
  · intro x
    simpa only [co, if_pos rfl] using AppendLine.eval U (lineId u₀) x

lemma three_private_impossible (gs : List Gate) (hsize : gs.length ≤ 14)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (lineId : Fin 5 → Fin 13) (hinj : Function.Injective lineId) (out : Fin 5 → ℕ)
    (hcorrect : ∀ u (x : Fin 13 → Bool), Support.Band x →
      Global.val gs x (out u) = Support.target (lineId u) x)
    (hnormal : ∀ u, Global.val gs (Global.Zof (Global.line (lineId u))) (out u) = false)
    (u₀ : Fin 5) (P : Finset ℕ) (hP : P ⊆ Finset.Ico 13 (13 + gs.length)) (hcard : 3 ≤ P.card)
    (hprivate : ∀ i ∈ P, ∀ u, u ≠ u₀ →
      Global.val gs (Global.Zof (Global.line (lineId u))) i = true) : False := by
  obtain ⟨cs, co, hlen, hcg, hcc, he⟩ := rebuild 5 gs out lineId u₀ hg hcorrect hnormal P hP hcard hprivate
  exact FourReduction.small_five_nonordinary cs (by omega) hcg lineId hinj co hcc u₀ he

end PEqualNP.Outside.L_meta_1024_aux.PrivateSurgery

namespace PEqualNP.Outside.L_meta_1024_aux.Certificate

open PEqualNP.CircuitLowerBounds
open FalsePruning

abbrev entry (gs : List Gate) (i : ℕ) : Entry := readEntry (build gs).entries i

lemma entry_snoc (gs : List Gate) (g : Gate) (i : ℕ) :
    entry (gs ++ [g]) i =
      if i = 13 + gs.length then profile (entry gs) g else entry gs i := by
  simp only [entry, build_snoc, FalsePruning.step, read_append, (build_lengths gs).1]

lemma entry_beyond (gs : List Gate) (i : ℕ) (hi : 13 + gs.length ≤ i) :
    entry gs i = emptyEntry := by
  unfold entry readEntry
  apply List.getD_eq_default
  simpa only [(build_lengths gs).1] using hi

lemma positive_valid (gs : List Gate) (i : ℕ) (hi : 0 < (entry gs i).1) :
    i < 13 + gs.length := by
  by_contra hn
  rw [entry_beyond gs i (by omega)] at hi
  simp [emptyEntry] at hi

lemma support_bound (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (i : ℕ) (hc : (entry gs i).1 ≤ 4) : (entry gs i).2.card ≤ (entry gs i).1 :=
  ((wire_spec gs hg (fun _ => false) i).2 hc).1

lemma certificate_false (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (i : ℕ) (hc : (entry gs i).1 ≤ 4) (x : Fin 13 → Bool)
    (hx : ∀ p ∈ (entry gs i).2, x p = false) : Global.val gs x i = false := by
  cases hv : Global.val gs x i
  · rfl
  · have hs := wire_spec gs hg x i
    have ht := (hs.2 hc).2.symm.trans (hs.1 hv)
    simp only [hit, decide_eq_true_eq] at ht
    obtain ⟨p, hp, hpt⟩ := ht
    rw [hx p hp] at hpt
    exact Bool.noConfusion hpt

def Cert (gs : List Gate) (i : ℕ) (Q : Finset ℕ) : Prop :=
  Q ⊆ Finset.Ico 13 (13 + gs.length) ∧
  ∀ q ∈ Q, q ≤ i ∧ (entry gs q).2 ⊆ (entry gs i).2 ∧ 2 ≤ (entry gs q).2.card ∧
    ∀ x : Fin 13 → Bool, Global.val gs x q = false →
      (∀ p ∈ (entry gs i).2 \ (entry gs q).2, x p = false) → Global.val gs x i = false

lemma cert_empty (gs : List Gate) (i : ℕ) : Cert gs i ∅ := by simp [Cert]

lemma cert_old (gs : List Gate) (g : Gate) (i : ℕ) (Q : Finset ℕ)
    (hQ : Cert gs i Q) (hi : i ≠ 13 + gs.length) : Cert (gs ++ [g]) i Q := by
  refine ⟨?_, ?_⟩
  · intro q hq
    have h := hQ.1 hq
    simp only [Finset.mem_Ico, List.length_append, List.length_cons, List.length_nil] at h ⊢
    omega
  · intro q hq
    have hqrange := hQ.1 hq
    have hqn : q ≠ 13 + gs.length := by simp only [Finset.mem_Ico] at hqrange; omega
    have hh := hQ.2 q hq
    simp only [entry_snoc, hi, hqn, ite_false, Global.val_snoc]
    exact hh

lemma cert_inherit (gs : List Gate) (g : Gate) (j : ℕ) (Q : Finset ℕ)
    (hQ : Cert gs j Q) (hj : j < 13 + gs.length)
    (hsub : (entry gs j).2 ⊆ (entry (gs ++ [g]) (13 + gs.length)).2)
    (hstep : ∀ x : Fin 13 → Bool, Global.val gs x j = false →
      (∀ p ∈ (entry (gs ++ [g]) (13 + gs.length)).2 \ (entry gs j).2, x p = false) →
      Global.val (gs ++ [g]) x (13 + gs.length) = false) :
    Cert (gs ++ [g]) (13 + gs.length) Q := by
  refine ⟨?_, ?_⟩
  · intro q hq
    have h := hQ.1 hq
    simp only [Finset.mem_Ico, List.length_append, List.length_cons, List.length_nil] at h ⊢
    omega
  · intro q hq
    obtain ⟨hqi, hqs, hqc, hctx⟩ := hQ.2 q hq
    have hqn : q ≠ 13 + gs.length := by omega
    have heq : entry (gs ++ [g]) q = entry gs q := by simp [entry_snoc, hqn]
    refine ⟨by omega, ?_, ?_, ?_⟩
    · simpa only [heq] using hqs.trans hsub
    · simpa only [heq] using hqc
    · intro x hx hzero
      have hxq : Global.val gs x q = false := by
        simpa only [Global.val_snoc, hqn, ite_false] using hx
      apply hstep x
      · apply hctx x hxq
        intro p hp
        apply hzero p
        rw [heq]
        exact Finset.mem_sdiff.mpr ⟨hsub (Finset.mem_sdiff.mp hp).1,
          (Finset.mem_sdiff.mp hp).2⟩
      · intro p hp
        apply hzero p
        rw [heq]
        obtain ⟨hpin, hpnot⟩ := Finset.mem_sdiff.mp hp
        exact Finset.mem_sdiff.mpr ⟨hpin, fun h => hpnot (hqs h)⟩

lemma cert_union (gs : List Gate) (i : ℕ) (A B : Finset ℕ)
    (hA : Cert gs i A) (hB : Cert gs i B) : Cert gs i (A ∪ B) := by
  refine ⟨Finset.union_subset hA.1 hB.1, ?_⟩
  intro q hq
  rcases Finset.mem_union.mp hq with hq | hq
  · exact hA.2 q hq
  · exact hB.2 q hq

lemma cert_insert (gs : List Gate) (g : Gate) (Q : Finset ℕ)
    (hQ : Cert (gs ++ [g]) (13 + gs.length) Q)
    (hc : 2 ≤ (entry (gs ++ [g]) (13 + gs.length)).2.card) :
    Cert (gs ++ [g]) (13 + gs.length) (insert (13 + gs.length) Q) := by
  refine ⟨?_, ?_⟩
  · intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · simp only [Finset.mem_Ico, List.length_append, List.length_cons, List.length_nil]
      omega
    · exact hQ.1 hq
  · intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact ⟨le_rfl, Finset.Subset.refl _, hc, fun x hx _ => hx⟩
    · exact hQ.2 q hq

lemma cert_disjoint (gs : List Gate) (a b : ℕ) (A B : Finset ℕ)
    (hA : Cert gs a A) (hB : Cert gs b B)
    (hd : Disjoint (entry gs a).2 (entry gs b).2) : Disjoint A B := by
  apply Finset.disjoint_left.mpr
  intro q hqa hqb
  have ha := hA.2 q hqa
  have hb := hB.2 q hqb
  obtain ⟨p, hp⟩ := Finset.card_pos.mp (show 0 < (entry gs q).2.card by omega)
  exact Finset.disjoint_left.mp hd (ha.2.1 hp) (hb.2.1 hp)

lemma and_false (g : Gate) (hop : g.op = GateOp.and) (f : ℕ → Bool)
    (j : ℕ) (hj : j ∈ g.inputs) (hf : f j = false) :
    g.op.eval (g.inputs.map f) = false := by
  cases hv : g.op.eval (g.inputs.map f)
  · rfl
  · simp only [hop, GateOp.eval, List.all_eq_true, id_eq] at hv
    have ht := hv (f j) (List.mem_map.mpr ⟨j, hj, rfl⟩)
    rw [hf] at ht
    exact Bool.noConfusion ht

lemma inherit_and (gs : List Gate) (g : Gate) (j : ℕ) (Q : Finset ℕ)
    (hop : g.op = GateOp.and) (hj : j ∈ g.inputs)
    (hQ : Cert gs j Q) (hvalid : j < 13 + gs.length)
    (he : entry (gs ++ [g]) (13 + gs.length) = entry gs j) :
    Cert (gs ++ [g]) (13 + gs.length) Q := by
  apply cert_inherit gs g j Q hQ hvalid
  · rw [he]
  · intro x hx _
    simp only [Global.val_snoc, ite_true]
    exact and_false g hop (Global.val gs x) j hj hx

lemma sharp_union (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (a b : ℕ) (hc : (entry gs a).1 + (entry gs b).1 ≤ 4)
    (hs : ((entry gs a).2 ∪ (entry gs b).2).card = (entry gs a).1 + (entry gs b).1) :
    (entry gs a).2.card = (entry gs a).1 ∧ (entry gs b).2.card = (entry gs b).1 ∧
      Disjoint (entry gs a).2 (entry gs b).2 := by
  have ha := support_bound gs hg a (by omega)
  have hb := support_bound gs hg b (by omega)
  have hu := Finset.card_union_le (entry gs a).2 (entry gs b).2
  have he := Finset.card_union_add_card_inter (entry gs a).2 (entry gs b).2
  refine ⟨by omega, by omega, ?_⟩
  apply Finset.disjoint_iff_inter_eq_empty.mpr
  apply Finset.card_eq_zero.mp
  omega

lemma inherit_or_left (gs : List Gate) (a b : ℕ) (Q : Finset ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hQ : Cert gs a Q) (ha : a < 13 + gs.length)
    (hb : (entry gs b).1 ≤ 4)
    (hd : Disjoint (entry gs a).2 (entry gs b).2) :
    Cert (gs ++ [⟨GateOp.or, [a,b]⟩]) (13 + gs.length) Q := by
  have he : (entry (gs ++ [⟨GateOp.or, [a,b]⟩]) (13 + gs.length)).2 =
      (entry gs a).2 ∪ (entry gs b).2 := by simp [entry_snoc, profile]
  apply cert_inherit gs _ a Q hQ ha
  · rw [he]
    exact Finset.subset_union_left
  · intro x hxa hzero
    have hxb : Global.val gs x b = false := by
      apply certificate_false gs hg b hb x
      intro p hp
      apply hzero p
      rw [he]
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ hp,
        fun h => Finset.disjoint_left.mp hd h hp⟩
    simp [Global.val_snoc, GateOp.eval, hxa, hxb]

lemma inherit_or_right (gs : List Gate) (a b : ℕ) (Q : Finset ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hQ : Cert gs b Q) (hb : b < 13 + gs.length)
    (ha : (entry gs a).1 ≤ 4)
    (hd : Disjoint (entry gs a).2 (entry gs b).2) :
    Cert (gs ++ [⟨GateOp.or, [a,b]⟩]) (13 + gs.length) Q := by
  have he : (entry (gs ++ [⟨GateOp.or, [a,b]⟩]) (13 + gs.length)).2 =
      (entry gs a).2 ∪ (entry gs b).2 := by simp [entry_snoc, profile]
  apply cert_inherit gs _ b Q hQ hb
  · rw [he]
    exact Finset.subset_union_right
  · intro x hxb hzero
    have hxa : Global.val gs x a = false := by
      apply certificate_false gs hg a ha x
      intro p hp
      apply hzero p
      rw [he]
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ hp,
        fun h => Finset.disjoint_left.mp hd hp h⟩
    simp [Global.val_snoc, GateOp.eval, hxa, hxb]

lemma entry_nil (i : ℕ) : entry [] i =
    if h : i < 13 then (1, {⟨i,h⟩}) else emptyEntry := by
  by_cases hi : i < 13
  · simp only [entry, build, List.foldl_nil, readEntry, initial,
      List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, dite_true, Option.getD_some]
  · simp [entry, build, initial, readEntry, emptyEntry, hi]

lemma extract (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (i : ℕ) (hc : (entry gs i).1 ≤ 4) (hs : (entry gs i).2.card = (entry gs i).1) :
    ∃ Q : Finset ℕ, (entry gs i).1 ≤ Q.card + 1 ∧ Cert gs i Q := by
  induction gs using List.reverseRecOn generalizing i with
  | nil =>
    refine ⟨∅, ?_, cert_empty _ _⟩
    by_cases hi : i < 13 <;> simp [entry_nil, hi, emptyEntry]
  | append_singleton gs g ih =>
    have hgs : ∀ a ∈ gs, (a.op = GateOp.and ∨ a.op = GateOp.or) ∧ a.inputs.length ≤ 2 := by
      intro a ha
      exact hg a (by simp [ha])
    by_cases hsmall : (entry (gs ++ [g]) i).1 ≤ 1
    · exact ⟨∅, by simpa using hsmall, cert_empty _ _⟩
    by_cases hi : i = 13 + gs.length
    · subst i
      have hgate := hg g (by simp)
      rcases g with ⟨op, ins⟩
      rcases hgate with ⟨hop, hlen⟩
      simp only at hop hlen
      rcases hop with rfl | rfl
      · have take_parent (j : ℕ) (hj : j ∈ ins)
            (he : entry (gs ++ [⟨GateOp.and, ins⟩]) (13 + gs.length) = entry gs j) :
            ∃ Q : Finset ℕ,
              (entry (gs ++ [⟨GateOp.and, ins⟩]) (13 + gs.length)).1 ≤ Q.card + 1 ∧
              Cert (gs ++ [⟨GateOp.and, ins⟩]) (13 + gs.length) Q := by
          have hcj : (entry gs j).1 ≤ 4 := he ▸ hc
          have hsj : (entry gs j).2.card = (entry gs j).1 := he ▸ hs
          obtain ⟨Q, hcount, hQ⟩ := ih hgs j hcj hsj
          have hjpos : 0 < (entry gs j).1 := by rw [he] at hsmall; omega
          exact ⟨Q, by simpa only [he] using hcount,
            inherit_and gs _ j Q rfl hj hQ (positive_valid gs j hjpos) he⟩
        rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, tl⟩⟩⟩
        · simp [entry_snoc, profile] at hc
        ·
          apply take_parent a (by simp)
          simp [entry_snoc, profile]
        ·
          by_cases hab : (entry gs a).1 ≤ (entry gs b).1
          · apply take_parent a (by simp)
            simp [entry_snoc, profile, hab]
          · apply take_parent b (by simp)
            simp [entry_snoc, profile, hab]
        · simp at hlen
      · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, tl⟩⟩⟩
        · simp [entry_snoc, profile] at hsmall
        ·
          have he0 : entry (gs ++ [⟨GateOp.or, [a]⟩]) (13 + gs.length) =
              (min 5 (entry gs a).1, (entry gs a).2) := by simp [entry_snoc, profile]
          rw [he0] at hc hs hsmall
          have ha : (entry gs a).1 ≤ 4 := by omega
          have hm : min 5 (entry gs a).1 = (entry gs a).1 := Nat.min_eq_right (by omega)
          have he : entry (gs ++ [⟨GateOp.or, [a]⟩]) (13 + gs.length) = entry gs a := by
            rw [he0, hm]
          obtain ⟨Q, hcount, hQ⟩ := ih hgs a ha (by simpa only [hm] using hs)
          refine ⟨Q, by simpa only [he] using hcount, ?_⟩
          apply cert_inherit gs _ a Q hQ (positive_valid gs a (by omega))
          · rw [he]
          · intro x hx _
            simp [Global.val_snoc, GateOp.eval, hx]
        ·
          have he : entry (gs ++ [⟨GateOp.or, [a,b]⟩]) (13 + gs.length) =
              (min 5 ((entry gs a).1 + (entry gs b).1), (entry gs a).2 ∪ (entry gs b).2) := by
            simp [entry_snoc, profile]
          rw [he] at hc hs hsmall
          have hab : (entry gs a).1 + (entry gs b).1 ≤ 4 := by omega
          have hm : min 5 ((entry gs a).1 + (entry gs b).1) =
              (entry gs a).1 + (entry gs b).1 := Nat.min_eq_right (by omega)
          have hUnion : ((entry gs a).2 ∪ (entry gs b).2).card =
              (entry gs a).1 + (entry gs b).1 := by simpa only [hm] using hs
          obtain ⟨hsa, hsb, hd⟩ := sharp_union gs hgs a b hab hUnion
          obtain ⟨A, hca, hA⟩ := ih hgs a (by omega) hsa
          obtain ⟨B, hcb, hB⟩ := ih hgs b (by omega) hsb
          by_cases ha0 : (entry gs a).1 = 0
          · refine ⟨B, ?_, inherit_or_right gs a b B hgs hB
                (positive_valid gs b (by omega)) (by omega) hd⟩
            rw [he]
            change min 5 ((entry gs a).1 + (entry gs b).1) ≤ B.card + 1
            rw [hm, ha0, Nat.zero_add]
            exact hcb
          by_cases hb0 : (entry gs b).1 = 0
          · refine ⟨A, ?_, inherit_or_left gs a b A hgs hA
                (positive_valid gs a (by omega)) (by omega) hd⟩
            rw [he]
            change min 5 ((entry gs a).1 + (entry gs b).1) ≤ A.card + 1
            rw [hm, hb0, Nat.add_zero]
            exact hca
          have hIA := inherit_or_left gs a b A hgs hA
            (positive_valid gs a (by omega)) (by omega) hd
          have hIB := inherit_or_right gs a b B hgs hB
            (positive_valid gs b (by omega)) (by omega) hd
          have hdisj := cert_disjoint gs a b A B hA hB hd
          have hn : 13 + gs.length ∉ A ∪ B := by
            intro hh
            rcases Finset.mem_union.mp hh with hh | hh
            · have hr := hA.1 hh
              simp at hr
            · have hr := hB.1 hh
              simp at hr
          refine ⟨insert (13 + gs.length) (A ∪ B), ?_,
            cert_insert gs _ _ (cert_union _ _ _ _ hIA hIB) ?_⟩
          · rw [Finset.card_insert_of_notMem hn, Finset.card_union_of_disjoint hdisj, he]
            simp only [Prod.fst, hm]
            omega
          · rw [he]
            simp only [Prod.snd]
            rw [hUnion]
            omega
        · simp at hlen
    · have he : entry (gs ++ [g]) i = entry gs i := by simp [entry_snoc, hi]
      obtain ⟨Q, hcount, hQ⟩ := ih hgs i (he ▸ hc) (he ▸ hs)
      exact ⟨Q, by simpa only [he] using hcount, cert_old gs g i Q hQ hi⟩

lemma global_line_card (w : Fin 13) : (Global.line w).card = 4 := Clamp.line_card w

lemma line_profile (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : Fin 13) (o : ℕ)
    (hcorrect : ∀ x, Support.Band x → Global.val gs x o = Support.target w x)
    (hc : (entry gs o).1 ≤ 4) : (entry gs o).2 = Global.line w ∧ (entry gs o).1 = 4 := by
  have hcard := support_bound gs hg o hc
  have hline : (entry gs o).2 = Global.line w := by
    apply support_eq_line w (fun x => Global.val gs x o) hcorrect _ (hcard.trans hc)
    intro x hx
    have h := wire_spec gs hg x o
    exact (h.2 hc).2.symm.trans (h.1 hx)
  refine ⟨hline, ?_⟩
  rw [hline, global_line_card] at hcard
  omega

lemma three_contexts (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : Fin 13) (o : ℕ)
    (hcorrect : ∀ x, Support.Band x → Global.val gs x o = Support.target w x)
    (hc : (entry gs o).1 ≤ 4) :
    ∃ Q : Finset ℕ, 3 ≤ Q.card ∧ Q ⊆ Finset.Ico 13 (13 + gs.length) ∧
      ∀ q ∈ Q, ∃ C : Finset (Fin 13), C ⊆ Global.line w ∧ C.card ≤ 2 ∧
        ∀ x : Fin 13 → Bool, Global.val gs x q = false →
          (∀ p ∈ C, x p = false) → Global.val gs x o = false := by
  obtain ⟨hline, hcost⟩ := line_profile gs hg w o hcorrect hc
  have hsharp : (entry gs o).2.card = (entry gs o).1 := by rw [hline, hcost, global_line_card]
  obtain ⟨Q, hcount, hQ⟩ := extract gs hg o hc hsharp
  refine ⟨Q, by omega, hQ.1, ?_⟩
  intro q hq
  obtain ⟨hqo, hsub, hcard, hctx⟩ := hQ.2 q hq
  refine ⟨(entry gs o).2 \ (entry gs q).2, ?_, ?_, hctx⟩
  · rw [hline]
    exact Finset.sdiff_subset
  · rw [Finset.card_sdiff_of_subset hsub, hline, global_line_card]
    omega

end PEqualNP.Outside.L_meta_1024_aux.Certificate

namespace PEqualNP.Outside.L_meta_1024_aux.PrivateSurgery
open PEqualNP.CircuitLowerBounds

lemma every_cost_large (gs : List Gate) (hsize : gs.length ≤ 14)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (lineId : Fin 5 → Fin 13) (hinj : Function.Injective lineId) (out : Fin 5 → ℕ)
    (hcorrect : ∀ u (x : Fin 13 → Bool), Support.Band x →
      Global.val gs x (out u) = Support.target (lineId u) x)
    (hnormal : ∀ u, Global.val gs (Global.Zof (Global.line (lineId u))) (out u) = false) :
    ∀ u, 5 ≤ FalsePruning.cost gs (out u) := by
  intro u₀
  by_contra hcost
  have hc : FalsePruning.cost gs (out u₀) ≤ 4 := by omega
  obtain ⟨P, hcard, hP, hcontexts⟩ := Certificate.three_contexts gs hg (lineId u₀)
    (out u₀) (hcorrect u₀) hc
  apply three_private_impossible gs hsize hg lineId hinj out hcorrect hnormal u₀ P hP hcard
  intro i hi u hu
  obtain ⟨C, hC, hc, hcontext⟩ := hcontexts i hi
  apply context_private gs (out u₀) i (lineId u₀) (fun g hm => (hg g hm).1)
    (hcorrect u₀) C hC hc (fun x hx hf => hcontext x hf hx) (lineId u)
  exact fun he => hu (hinj he)

end PEqualNP.Outside.L_meta_1024_aux.PrivateSurgery

namespace PEqualNP.Outside.L_meta_1024_aux.PrivateSurgery
open PEqualNP.CircuitLowerBounds

lemma normal_clamp_ordinary (gs : List Gate) (o : ℕ) (w : Fin 13) (P : Finset ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ x : Fin 13 → Bool, Support.Band x →
      Global.val gs x o = Support.target w x)
    (hordinary : ∀ x : Fin 13 → Bool, Global.val gs x o = Support.target w x)
    (hprivate : ∀ i ∈ P, Global.val gs (Global.Zof (Global.line w)) i = true) :
    ∀ x : Fin 13 → Bool,
      Global.val (Sink.transform 13 P gs) x o = Support.target w x := by
  have hop := fun g hm => (hg g hm).1
  obtain ⟨hz, he⟩ := (Bridge.ordinary_iff_extremes gs o w hop).mp hordinary
  apply (Bridge.ordinary_iff_extremes (Sink.transform 13 P gs) o w
    (fun g hm => (Sink.transform_allowed 13 P gs hg g hm).1)).mpr
  exact ⟨(normal_clamp gs o w P hg hcorrect hz hprivate).1,
    fun p hp => Sink.val_ge P gs hop (Global.eof p) o (he p hp)⟩

lemma rebuild_ordinary (k : ℕ) (gs : List Gate) (out : Fin k → ℕ)
    (lineId : Fin k → Fin 13) (u₀ : Fin k)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ u (x : Fin 13 → Bool), Support.Band x →
      Global.val gs x (out u) = Support.target (lineId u) x)
    (P : Finset ℕ)
    (hprivate : ∀ i ∈ P, ∀ u, u ≠ u₀ →
      Global.val gs (Global.Zof (Global.line (lineId u))) i = true)
    (u : Fin k) (hordinary : ∀ x : Fin 13 → Bool,
      Global.val gs x (out u) = Support.target (lineId u) x) :
    ∀ x : Fin 13 → Bool,
      Global.val (AppendLine.appendLine (Dead.paidCode 13 P gs) (lineId u₀)) x
        (if u = u₀ then 15 + (Dead.paidCode 13 P gs).length else Dead.paidIndex 13 P gs (out u)) =
      Support.target (lineId u) x := by
  classical
  intro x
  by_cases hu : u = u₀
  · subst u
    simpa using AppendLine.eval (Dead.paidCode 13 P gs) (lineId u₀) x
  · rw [if_neg hu]
    have hz := ((Bridge.ordinary_iff_extremes gs (out u) (lineId u)
      (fun g hm => (hg g hm).1)).mp hordinary).1
    have hkeep : out u ∉ P := by
      intro hm
      have hh := hprivate (out u) hm u hu
      rw [hz] at hh
      exact Bool.noConfusion hh
    have hvalid := (Bridge.output_index gs (out u) (lineId u) (hcorrect u)).2
    have hmapped : Dead.paidIndex 13 P gs (out u) < 13 + (Dead.paidCode 13 P gs).length :=
      Dead.mapped_valid 13 P (Sink.transform 13 P gs) (out u)
        (by simpa only [Sink.transform_length] using hvalid) hkeep
    rw [AppendLine.old _ _ x _ hmapped]
    have heq := Dead.eval P (Sink.transform 13 P gs) (Dead.transform_noReads 13 P gs) x
      (out u) (by simpa only [Sink.transform_length] using hvalid) hkeep
    exact heq.trans (normal_clamp_ordinary gs (out u) (lineId u) P hg (hcorrect u)
      hordinary (fun i hi => hprivate i hi u hu) x)

end PEqualNP.Outside.L_meta_1024_aux.PrivateSurgery
