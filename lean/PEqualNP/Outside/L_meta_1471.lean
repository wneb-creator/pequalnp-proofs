import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1471

open PEqualNP.CircuitLowerBounds


def p1461_run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma p1461_run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    p1461_run (g :: gs) x = p1461_run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma p1461_run_length (gs : List Gate) (x : List Bool) :
    (p1461_run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [p1461_run]
  | cons g gs ih => rw [p1461_run_cons, ih]; simp; omega

lemma p1461_run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (p1461_run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [p1461_run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma p1461_run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    p1461_run gs x = p1461_run (gs.drop j) (p1461_run (gs.take j) x) := by
  simpa only [p1461_run, List.foldl_append] using
    congrArg (fun l : List Gate => p1461_run l x) (List.take_append_drop j gs).symm

def p1461_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma p1461_input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    p1461_value C x p = x p := by
  change (p1461_run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [p1461_run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma p1461_missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : p1461_value C x w = false := by
  change (p1461_run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [p1461_run_length, Circuit.size] using hw)

lemma p1461_gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    p1461_value C x w = g.op.eval (g.inputs.map fun r => if r < w then p1461_value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := p1461_run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, p1461_run_length, Nat.min_eq_left hj.le, j]; omega
  have split : p1461_run C.gates (List.ofFn x) = p1461_run (g :: C.gates.drop (j + 1)) earlier := by
    rw [p1461_run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then p1461_value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (p1461_run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (p1461_run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (p1461_run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then p1461_value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [p1461_run_cons]
  rw [p1461_run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

lemma p1461_gate_mono {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or)
    (x y : Fin n → Bool)
    (h : ∀ r ∈ C.gates[k].inputs, r < n + k → p1461_value C x r = true → p1461_value C y r = true) :
    p1461_value C x (n + k) = true → p1461_value C y (n + k) = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := p1461_gate_value C x (n + k) (by omega) hw
  have hy := p1461_gate_value C y (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx hy
  rw [hx, hy]
  have hr (r : ℕ) (hm : r ∈ C.gates[k].inputs) :
      (if r < n + k then p1461_value C x r else false) = true →
      (if r < n + k then p1461_value C y r else false) = true := by
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

lemma p1461_or_value {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.or) (x : Fin n → Bool) :
    p1461_value C x (n + k) = true ↔ ∃ r ∈ C.gates[k].inputs, r < n + k ∧ p1461_value C x r = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := p1461_gate_value C x (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx
  rw [hx, hop]
  simp [GateOp.eval]

lemma p1461_and_value {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and) (x : Fin n → Bool) :
    p1461_value C x (n + k) = true ↔ ∀ r ∈ C.gates[k].inputs, r < n + k ∧ p1461_value C x r = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := p1461_gate_value C x (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx
  rw [hx, hop]
  simp [GateOp.eval]

lemma p1461_not_value {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.not) :
    ∃ r, ∀ x : Fin n → Bool, p1461_value C x (n + k) = false → r < n + k ∧ p1461_value C x r = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  refine ⟨C.gates[k].inputs.headD 0, fun x h => ?_⟩
  have hx := p1461_gate_value C x (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx
  rw [hx, hop] at h
  rcases hin : C.gates[k].inputs with _ | ⟨a, tl⟩
  · rw [hin] at h
    simp [GateOp.eval] at h
  · rw [hin] at h
    by_cases ha : a < n + k
    · simpa [GateOp.eval, ha] using h
    · simp [GateOp.eval, ha] at h

lemma p1461_mono {n : ℕ} (C : Circuit) (x y : Fin n → Bool) (h : ∀ v, x v = true → y v = true)
    (hN : ∀ k, ∀ hk : k < C.gates.length,
      ¬ (C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or) →
      p1461_value C x (n + k) = true → p1461_value C y (n + k) = true) (w : ℕ) :
    p1461_value C x w = true → p1461_value C y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change p1461_value C x p = true → p1461_value C y p = true
      simpa only [p1461_input_value] using h p
    by_cases hw : w < n + C.gates.length
    · have hk : w - n < C.gates.length := by omega
      have hwk : w = n + (w - n) := by omega
      rw [hwk]
      by_cases hop : C.gates[w - n].op = GateOp.and ∨ C.gates[w - n].op = GateOp.or
      · exact p1461_gate_mono C (w - n) hk hop x y fun r _ hlt => ih r (by omega)
      · exact hN (w - n) hk hop
    · simp [p1461_missing_value C x w (by unfold Circuit.size; omega)]

def p1461_Sv {n : ℕ} {ι : Type*} (C : Circuit) (l : ι → Fin n → Bool) (y : Fin n → Bool)
    (p : ι) (w : ℕ) : Prop :=
  p1461_value C (l p) w = true ∧ p1461_value C y w = false

def p1461_Multi {n : ℕ} {ι : Type*} (C : Circuit) (T : Finset ι) (l : ι → Fin n → Bool)
    (y : Fin n → Bool) (w : ℕ) : Prop :=
  ∃ p ∈ T, ∃ p' ∈ T, p ≠ p' ∧ p1461_Sv C l y p w ∧ p1461_Sv C l y p' w

lemma p1461_list_cases (L : List ℕ) (hL : L.length ≤ 2) (Q : ℕ → Prop) :
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

lemma p1461_step_cases {n : ℕ} {ι : Type*} (C : Circuit) (T : Finset ι) (l : ι → Fin n → Bool)
    (y : Fin n → Bool)
    (k : ℕ) (hk : k < C.gates.length)
    (hopk : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or)
    (hfank : C.gates[k].inputs.length ≤ 2) (hm : p1461_Multi C T l y (n + k)) :
    (∃ r ∈ C.gates[k].inputs, r < n + k ∧ ∀ p ∈ T, p1461_Sv C l y p (n + k) → p1461_Sv C l y p r) ∨
    (C.gates[k].op = GateOp.or ∧ C.gates[k].inputs.length = 2 ∧
      (∀ r ∈ C.gates[k].inputs, ∃ p ∈ T, p1461_value C (l p) r = true) ∧
      ∀ p ∈ T, p1461_Sv C l y p (n + k) → ∃ r ∈ C.gates[k].inputs, r < n + k ∧ p1461_Sv C l y p r) := by
  obtain ⟨p0, hp0, _, _, _, hs0, _⟩ := hm
  rcases hopk with hop | hop
  · left
    have hy := hs0.2
    by_contra hcon
    have hall : ∀ r ∈ C.gates[k].inputs, r < n + k ∧ p1461_value C y r = true := by
      intro r hr
      by_contra hr2
      apply hcon
      have hlt := ((p1461_and_value C k hk hop (l p0)).mp hs0.1 r hr).1
      refine ⟨r, hr, hlt, fun p _ hsp => ⟨((p1461_and_value C k hk hop (l p)).mp hsp.1 r hr).2, ?_⟩⟩
      by_contra hne
      exact hr2 ⟨hlt, by simpa using hne⟩
    rw [(p1461_and_value C k hk hop y).mpr hall] at hy
    exact Bool.noConfusion hy
  · have hyall : ∀ r ∈ C.gates[k].inputs, r < n + k → p1461_value C y r = false := by
      intro r hr hlt
      by_contra h
      have h2 : p1461_value C y (n + k) = true :=
        (p1461_or_value C k hk hop y).mpr ⟨r, hr, hlt, by simpa using h⟩
      rw [hs0.2] at h2
      exact Bool.noConfusion h2
    have hsv : ∀ p ∈ T, p1461_Sv C l y p (n + k) →
        ∃ r ∈ C.gates[k].inputs, r < n + k ∧ p1461_value C (l p) r = true ∧ p1461_Sv C l y p r := by
      intro p _ hsp
      obtain ⟨r, hr, hlt, hv⟩ := (p1461_or_value C k hk hop (l p)).mp hsp.1
      exact ⟨r, hr, hlt, hv, hv, hyall r hr hlt⟩
    rcases p1461_list_cases C.gates[k].inputs hfank
      (fun r => ∃ p ∈ T, r < n + k ∧ p1461_value C (l p) r = true) with ⟨hlen, hQ⟩ | ⟨c, hc⟩
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

lemma p1461_frontier {n : ℕ} {ι : Type*} (C : Circuit) (T : Finset ι) (l : ι → Fin n → Bool)
    (y : Fin n → Bool)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hopM : ∀ k, ∀ hk : k < C.gates.length, p1461_Multi C T l y (n + k) →
      C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or)
    (W : Finset ℕ)
    (hW : ∀ k, ∀ hk : k < C.gates.length, p1461_Multi C T l y (n + k) →
      C.gates[k].op = GateOp.or → C.gates[k].inputs.length = 2 →
      (∀ r ∈ C.gates[k].inputs, ∃ p ∈ T, p1461_value C (l p) r = true) → n + k ∈ W)
    (hlen : ∀ w, p1461_Multi C T l y w → n ≤ w ∧ w < n + C.gates.length)
    (t : ℕ) (F : Finset ℕ) (hF : ∀ w ∈ F, p1461_Multi C T l y w → w < t)
    (T' : Finset ι) (hT' : T' ⊆ T) (hs : ∀ p ∈ T', ∃ w ∈ F, p1461_Sv C l y p w) :
    T'.card ≤ F.card + (W.filter (· < t)).card := by
  classical
  induction t generalizing F with
  | zero =>
    choose! f hfF hfs using hs
    have hinj : Set.InjOn f T' := by
      intro p hp p' hp' e
      by_contra hne
      have hc : p1461_Multi C T l y (f p) :=
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
    by_cases hex : t ∈ F ∧ p1461_Multi C T l y t
    · obtain ⟨h1, h2⟩ := hlen t hex.2
      have hk : t - n < C.gates.length := by omega
      have htk : t = n + (t - n) := by omega
      have hm : p1461_Multi C T l y (n + (t - n)) := by rw [← htk]; exact hex.2
      have he := Finset.card_erase_add_one hex.1
      rcases p1461_step_cases C T l y (t - n) hk (hopM _ hk hm)
          (hfan _ (List.getElem_mem hk)) hm with ⟨r, hr, hlt, hall⟩ | ⟨hop, hlen2, hQ, hsv⟩
      · rw [← htk] at hlt hall
        let F' := insert r (F.erase t)
        have hF' : ∀ w ∈ F', p1461_Multi C T l y w → w < t := by
          intro w hw hg
          rcases Finset.mem_insert.mp hw with hw | hw
          · rw [hw]; exact hlt
          · have hne := (Finset.mem_erase.mp hw).1
            have hlt := hF w (Finset.mem_erase.mp hw).2 hg
            omega
        have hs' : ∀ p ∈ T', ∃ w ∈ F', p1461_Sv C l y p w := by
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
        have hF' : ∀ w ∈ F', p1461_Multi C T l y w → w < t := by
          intro w hw hg
          rcases Finset.mem_union.mp hw with hw | hw
          · have hne := (Finset.mem_erase.mp hw).1
            have hlt := hF w (Finset.mem_erase.mp hw).2 hg
            omega
          · have := (List.mem_filter.mp (List.mem_toFinset.mp hw)).2
            simpa using this
        have hs' : ∀ p ∈ T', ∃ w ∈ F', p1461_Sv C l y p w := by
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
    · have hF' : ∀ w ∈ F, p1461_Multi C T l y w → w < t := by
        intro w hw hg
        have hne : w ≠ t := fun e => hex ⟨e ▸ hw, e ▸ hg⟩
        have hlt := hF w hw hg
        omega
      have := ih F hF' hs
      omega

lemma p1461_family {n : ℕ} {ι : Type*} (gates : List Gate)
    (hfan : ∀ g ∈ gates, g.inputs.length ≤ 2)
    (T : Finset ι) (l : ι → Fin n → Bool) (y : Fin n → Bool) (o : ℕ)
    (hopM : ∀ k, ∀ hk : k < gates.length, p1461_Multi ⟨gates, 0⟩ T l y (n + k) →
      gates[k].op = GateOp.and ∨ gates[k].op = GateOp.or)
    (ho : ∀ p ∈ T, p1461_Sv ⟨gates, 0⟩ l y p o)
    (hin : ∀ w, w < n → ¬ p1461_Multi ⟨gates, 0⟩ T l y w)
    (K : Finset (Fin gates.length))
    (hK : ∀ g : Fin gates.length, p1461_Multi ⟨gates, 0⟩ T l y (n + (g : ℕ)) →
      gates[(g : ℕ)].op = GateOp.or → gates[(g : ℕ)].inputs.length = 2 →
      (∀ r ∈ gates[(g : ℕ)].inputs, ∃ p ∈ T, p1461_value ⟨gates, 0⟩ (l p) r = true) → g ∈ K) :
    T.card ≤ K.card + 1 := by
  classical
  let C : Circuit := ⟨gates, 0⟩
  let W : Finset ℕ := Finset.image (fun g : Fin gates.length => n + (g : ℕ)) K
  have hlen : ∀ w, p1461_Multi C T l y w → n ≤ w ∧ w < n + C.gates.length := by
    intro w hc
    refine ⟨Nat.le_of_not_lt fun h => hin w h hc, ?_⟩
    by_contra hge
    obtain ⟨p, _, _, _, _, hsv, _⟩ := hc
    have hm := p1461_missing_value C (l p) w (by unfold Circuit.size; omega)
    have h1 := hsv.1
    rw [hm] at h1
    exact Bool.noConfusion h1
  have h := p1461_frontier C T l y hfan hopM W
    (fun k hk hm hop hl hQ => Finset.mem_image.mpr ⟨(⟨k, hk⟩ : Fin gates.length), hK ⟨k, hk⟩ hm hop hl hQ, rfl⟩)
    hlen (n + C.gates.length) {o}
    (fun w _ hc => (hlen w hc).2) T (Finset.Subset.refl T)
    (fun p hp => ⟨o, Finset.mem_singleton_self o, ho p hp⟩)
  have h1 := Finset.card_filter_le W (· < n + C.gates.length)
  have h2 : W.card ≤ K.card := Finset.card_image_le
  rw [Finset.card_singleton] at h
  omega

def p1461_rowL {n m : ℕ} (R : Fin m → Fin n → Finset (Fin n)) (i : Fin m) (p : Fin n) :
    Fin n → Bool :=
  fun v => decide (v ∈ R i p)

def p1461_coY {n m : ℕ} (S : Fin m → Finset (Fin n)) (i : Fin m) : Fin n → Bool :=
  fun v => decide (v ∉ S i)

lemma p1461_kill {n m : ℕ} (gates : List Gate)
    (S : Fin m → Finset (Fin n)) (R : Fin m → Fin n → Finset (Fin n)) (i j : Fin m)
    (hN : ∀ k, ∀ hk : k < gates.length, ¬ (gates[k].op = GateOp.and ∨ gates[k].op = GateOp.or) →
      ∀ a ∈ S i, p1461_value ⟨gates, 0⟩ (p1461_rowL R i a) (n + k) = false)
    (hint : (S i ∩ S j).card ≤ 1)
    (hnA : ¬ ∃ p ∈ S i \ S j, (R i p ∩ S j).Nonempty) (w : ℕ)
    (hi : p1461_Multi ⟨gates, 0⟩ (S i) (p1461_rowL R i) (p1461_coY S i) w)
    (hj : p1461_value ⟨gates, 0⟩ (p1461_coY S j) w = false) : False := by
  obtain ⟨p, hp, p', hp', hne, hs, hs'⟩ := hi
  have key : ∀ a ∈ S i, a ∉ S j → p1461_value ⟨gates, 0⟩ (p1461_rowL R i a) w = true → False := by
    intro a ha haj hv
    have := p1461_mono ⟨gates, 0⟩ (p1461_rowL R i a) (p1461_coY S j) (fun v hv => ?_)
      (fun k hk hop h => by rw [hN k hk hop a ha] at h; exact Bool.noConfusion h) w hv
    · rw [hj] at this
      exact Bool.noConfusion this
    · simp only [p1461_rowL, p1461_coY, decide_eq_true_eq] at hv ⊢
      intro hvj
      exact hnA ⟨a, Finset.mem_sdiff.mpr ⟨ha, haj⟩, ⟨v, Finset.mem_inter.mpr ⟨hv, hvj⟩⟩⟩
  by_cases hpj : p ∈ S j
  · by_cases hpj' : p' ∈ S j
    · exact hne (Finset.card_le_one.mp hint p (Finset.mem_inter.mpr ⟨hp, hpj⟩) p'
        (Finset.mem_inter.mpr ⟨hp', hpj'⟩))
    · exact key p' hp' hpj' hs'.1
  · exact key p hp hpj hs.1

def p1461_InK {n m : ℕ} (gates : List Gate) (S : Fin m → Finset (Fin n))
    (R : Fin m → Fin n → Finset (Fin n)) (i : Fin m) (g : Fin gates.length) : Prop :=
  p1461_Multi ⟨gates, 0⟩ (S i) (p1461_rowL R i) (p1461_coY S i) (n + (g : ℕ)) ∧
    gates[(g : ℕ)].op = GateOp.or ∧ gates[(g : ℕ)].inputs.length = 2 ∧
    ∀ r ∈ gates[(g : ℕ)].inputs, ∃ p ∈ S i, p1461_value ⟨gates, 0⟩ (p1461_rowL R i p) r = true


theorem engine_main : ∀ (q n m : ℕ) (S : Fin m → Finset (Fin n))
    (R : Fin m → Fin n → Finset (Fin n)),
    1 ≤ q → 1 ≤ m → (∀ i : Fin m, (S i).card = q + 1) →
    (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ v : Fin n, ∃ i : Fin m, v ∈ S i) →
    (∀ (i : Fin m) (p : Fin n), p ∈ S i → R i p ∩ S i = {p}) →
    (∀ i j : Fin m, i ≠ j → ¬ ((∃ p ∈ S i \ S j, (R i p ∩ S j).Nonempty) ∧
      (∃ s ∈ S j \ S i, (R j s ∩ S i).Nonempty))) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ) (j : Fin gates.length),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      g.inputs.length ≤ 2) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    (∀ (w : Fin m) (x : Fin n → Bool),
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)) →
    (∀ i : Fin m, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (j : ℕ)⟩ (List.ofFn (fun v : Fin n => decide (v ∉ S i))) = false) →
    (∀ (i : Fin m) (p : Fin n), p ∈ S i →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (j : ℕ)⟩ (List.ofFn (fun v : Fin n => decide (v ∈ R i p))) = false) →
    m * q + (Finset.univ.filter (fun i : Fin gates.length => j < i ∧ n + (j : ℕ) ∈ (gates.get i).inputs)).card + 2 ≤ gates.length := by
  intro q n m S R hq hm hcard hint hcov hR hno gates out j hg hj hone hout hNco hNrow
  set Rd := Finset.univ.filter
    (fun i : Fin gates.length => j < i ∧ n + (j : ℕ) ∈ (gates.get i).inputs) with hRd
  classical
  have hnv : ∀ (k : ℕ) (hk : k < gates.length),
      ¬ (gates[k].op = GateOp.and ∨ gates[k].op = GateOp.or) → k = (j : ℕ) := by
    intro k hk hop
    have hn : (gates.get ⟨k, hk⟩).op = GateOp.not := by
      rcases (hg _ (List.getElem_mem hk)).1 with h | h | h
      · exact absurd (Or.inl h) hop
      · exact absurd (Or.inr h) hop
      · exact h
    exact congrArg Fin.val (hone ⟨k, hk⟩ hn)
  have hrow : ∀ (k : ℕ) (hk : k < gates.length),
      ¬ (gates[k].op = GateOp.and ∨ gates[k].op = GateOp.or) → ∀ (i : Fin m), ∀ a ∈ S i,
      PEqualNP.Outside.L_meta_1471.p1461_value ⟨gates, 0⟩ (PEqualNP.Outside.L_meta_1471.p1461_rowL R i a) (n + k) = false := by
    intro k hk hop i a ha
    rw [hnv k hk hop]
    exact hNrow i a ha
  have hopM : ∀ (i : Fin m) (k : ℕ) (hk : k < gates.length),
      PEqualNP.Outside.L_meta_1471.p1461_Multi ⟨gates, 0⟩ (S i) (PEqualNP.Outside.L_meta_1471.p1461_rowL R i) (PEqualNP.Outside.L_meta_1471.p1461_coY S i) (n + k) →
      gates[k].op = GateOp.and ∨ gates[k].op = GateOp.or := by
    intro i k hk hmu
    by_contra hop
    obtain ⟨p, hp, _, _, _, hs, _⟩ := hmu
    have h1 := hs.1
    rw [hrow k hk hop i p hp] at h1
    exact Bool.noConfusion h1
  let K : Fin m → Finset (Fin gates.length) := fun i => Finset.univ.filter fun g =>
    PEqualNP.Outside.L_meta_1471.p1461_InK gates S R i g
  have hKq : ∀ i, q ≤ (K i).card := by
    intro i
    have h := PEqualNP.Outside.L_meta_1471.p1461_family (n := n) gates (fun g hgm => (hg g hgm).2) (S i)
      (PEqualNP.Outside.L_meta_1471.p1461_rowL R i) (PEqualNP.Outside.L_meta_1471.p1461_coY S i) (out i) (hopM i)
      (fun p hp => ⟨(hout i (PEqualNP.Outside.L_meta_1471.p1461_rowL R i p)).trans (decide_eq_true ⟨p, hp, by
          have h3 : p ∈ R i p ∩ S i := by rw [hR i p hp]; exact Finset.mem_singleton_self p
          simpa [PEqualNP.Outside.L_meta_1471.p1461_rowL] using (Finset.mem_inter.mp h3).1⟩),
        (hout i (PEqualNP.Outside.L_meta_1471.p1461_coY S i)).trans (decide_eq_false (by
          rintro ⟨v, hv, h⟩
          simp [PEqualNP.Outside.L_meta_1471.p1461_coY, hv] at h))⟩)
      (fun w hw hc => by
        obtain ⟨p, hp, p', hp', hne, hs1, hs2⟩ := hc
        have e : ∀ a ∈ S i, PEqualNP.Outside.L_meta_1471.p1461_Sv ⟨gates, 0⟩
            (PEqualNP.Outside.L_meta_1471.p1461_rowL R i) (PEqualNP.Outside.L_meta_1471.p1461_coY S i) a w →
            (⟨w, hw⟩ : Fin n) = a := by
          intro a ha hsa
          have h1 : PEqualNP.Outside.L_meta_1471.p1461_value ⟨gates, 0⟩
            (PEqualNP.Outside.L_meta_1471.p1461_rowL R i a) ((⟨w, hw⟩ : Fin n) : ℕ) = true := hsa.1
          have h2 : PEqualNP.Outside.L_meta_1471.p1461_value ⟨gates, 0⟩
            (PEqualNP.Outside.L_meta_1471.p1461_coY S i) ((⟨w, hw⟩ : Fin n) : ℕ) = false := hsa.2
          rw [PEqualNP.Outside.L_meta_1471.p1461_input_value] at h1 h2
          simp only [PEqualNP.Outside.L_meta_1471.p1461_rowL, PEqualNP.Outside.L_meta_1471.p1461_coY,
            decide_eq_true_eq, decide_eq_false_iff_not, not_not] at h1 h2
          have h3 : (⟨w, hw⟩ : Fin n) ∈ R i a ∩ S i := Finset.mem_inter.mpr ⟨h1, h2⟩
          rw [hR i a ha] at h3
          exact Finset.mem_singleton.mp h3
        exact hne ((e p hp hs1).symm.trans (e p' hp' hs2)))
      (K i)
      (fun g hmu hop hl hQ => Finset.mem_filter.mpr ⟨Finset.mem_univ g, hmu, hop, hl, hQ⟩)
    have := hcard i
    omega
  have hdisj : ∀ i ∈ (Finset.univ : Finset (Fin m)), ∀ j' ∈ (Finset.univ : Finset (Fin m)),
      i ≠ j' → Disjoint (K i) (K j') := by
    intro i _ j' _ hij
    refine Finset.disjoint_left.mpr fun g hgi hgj => ?_
    have hmi := (Finset.mem_filter.mp hgi).2.1
    have hmj := (Finset.mem_filter.mp hgj).2.1
    have hyi : PEqualNP.Outside.L_meta_1471.p1461_value ⟨gates, 0⟩ (PEqualNP.Outside.L_meta_1471.p1461_coY S i) (n + (g : ℕ)) = false := by
      obtain ⟨p, _, _, _, _, hs, _⟩ := hmi
      exact hs.2
    have hyj : PEqualNP.Outside.L_meta_1471.p1461_value ⟨gates, 0⟩ (PEqualNP.Outside.L_meta_1471.p1461_coY S j') (n + (g : ℕ)) = false := by
      obtain ⟨p, _, _, _, _, hs, _⟩ := hmj
      exact hs.2
    by_cases hA : ∃ p ∈ S i \ S j', (R i p ∩ S j').Nonempty
    · have hB : ¬ ∃ s ∈ S j' \ S i, (R j' s ∩ S i).Nonempty := fun hB => hno i j' hij ⟨hA, hB⟩
      exact PEqualNP.Outside.L_meta_1471.p1461_kill gates S R j' i (fun k hk hop => hrow k hk hop j')
        (by rw [Finset.inter_comm]; exact hint i j' hij) hB _ hmj hyi
    · exact PEqualNP.Outside.L_meta_1471.p1461_kill gates S R i j' (fun k hk hop => hrow k hk hop i) (hint i j' hij) hA _ hmi hyj
  obtain ⟨r, hr⟩ := PEqualNP.Outside.L_meta_1471.p1461_not_value (n := n) ⟨gates, 0⟩ (j : ℕ) j.isLt hj
  have hrco : ∀ i : Fin m, r < n + (j : ℕ) ∧ PEqualNP.Outside.L_meta_1471.p1461_value ⟨gates, 0⟩ (PEqualNP.Outside.L_meta_1471.p1461_coY S i) r = true :=
    fun i => hr (PEqualNP.Outside.L_meta_1471.p1461_coY S i) (hNco i)
  have hrn : n ≤ r := by
    by_contra hlt
    have hlt' : r < n := by omega
    obtain ⟨i, hi⟩ := hcov ⟨r, hlt'⟩
    have h1 : PEqualNP.Outside.L_meta_1471.p1461_value ⟨gates, 0⟩ (PEqualNP.Outside.L_meta_1471.p1461_coY S i) ((⟨r, hlt'⟩ : Fin n) : ℕ) = true := (hrco i).2
    rw [PEqualNP.Outside.L_meta_1471.p1461_input_value] at h1
    simp [PEqualNP.Outside.L_meta_1471.p1461_coY, hi] at h1
  have hrj := (hrco ⟨0, hm⟩).1
  obtain ⟨g0, hg0⟩ : ∃ g0 : Fin gates.length, n + (g0 : ℕ) = r :=
    ⟨⟨r - n, by have := j.isLt; omega⟩, by simp only []; omega⟩
  have hg0j : g0 < j := Fin.lt_def.mpr (by omega)
  let N : Finset (Fin gates.length) := insert j (insert g0 Rd)
  have hNcard : N.card = Rd.card + 2 := by
    have h1 : g0 ∉ Rd := fun h => by
      have := (Finset.mem_filter.mp h).2.1
      exact absurd hg0j (not_lt.mpr this.le)
    have h2 : j ∉ insert g0 Rd := fun h => by
      rcases Finset.mem_insert.mp h with h | h
      · exact absurd hg0j (by rw [h]; exact lt_irrefl _)
      · exact absurd (Finset.mem_filter.mp h).2.1 (lt_irrefl _)
    rw [Finset.card_insert_of_notMem h2, Finset.card_insert_of_notMem h1]
  have hND : Disjoint (Finset.univ.biUnion K) N := by
    refine Finset.disjoint_left.mpr fun g hgK hgN => ?_
    obtain ⟨i, _, hgi⟩ := Finset.mem_biUnion.mp hgK
    obtain ⟨hmu, hop, hl, hQ⟩ := (Finset.mem_filter.mp hgi).2
    rcases Finset.mem_insert.mp hgN with h | h
    · rw [h] at hop
      have hj' : gates[(j : ℕ)].op = GateOp.not := hj
      rw [hj'] at hop
      exact GateOp.noConfusion hop
    rcases Finset.mem_insert.mp h with h | h
    · obtain ⟨p, _, _, _, _, hs, _⟩ := hmu
      have h2 := hs.2
      rw [h, hg0, (hrco i).2] at h2
      exact Bool.noConfusion h2
    · have hin := (Finset.mem_filter.mp h).2.2
      obtain ⟨p, hp, hv⟩ := hQ _ hin
      have h2 : PEqualNP.Outside.L_meta_1471.p1461_value ⟨gates, 0⟩ (PEqualNP.Outside.L_meta_1471.p1461_rowL R i p) (n + (j : ℕ)) = false := hNrow i p hp
      rw [h2] at hv
      exact Bool.noConfusion hv
  have h1 := Finset.card_le_card (Finset.subset_univ (Finset.univ.biUnion K ∪ N))
  rw [Finset.card_union_of_disjoint hND, Finset.card_biUnion hdisj, Finset.card_univ,
    Fintype.card_fin, hNcard] at h1
  have h2 : ∑ i : Fin m, q ≤ ∑ i : Fin m, (K i).card := Finset.sum_le_sum fun i _ => hKq i
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h2
  omega

theorem p1462_rowaux {n m : ℕ} (S : Fin m → Finset (Fin n)) (X : Finset (Fin n)) (f : Fin m → Fin n)
    (i j : Fin m) (p v : Fin n) (hp : p ∈ S i \ S j)
    (hv : v ∈ (if p ∈ X then ({p} : Finset (Fin n)) else {p, f i}) ∩ S j) :
    ¬ S i ⊆ X ∧ f i ∈ S j := by
  rw [Finset.mem_sdiff] at hp
  rw [Finset.mem_inter] at hv
  by_cases hpX : p ∈ X
  · simp only [hpX, ↓reduceIte, Finset.mem_singleton] at hv
    exact absurd (hv.1 ▸ hv.2) hp.2
  · simp only [hpX, ↓reduceIte, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv.1 with h | h
    · exact absurd (h ▸ hv.2) hp.2
    · exact ⟨fun hs => hpX (hs hp.1), h ▸ hv.2⟩


theorem rows_main : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (X B : Finset (Fin n))
    (r : Fin n → Fin n → Prop) (f : Fin m → Fin n),
    (∀ a b : Fin n, r a b → ¬ r b a) →
    (∀ i : Fin m, ¬ S i ⊆ X → f i ∈ B ∧ f i ∉ S i ∧ ∀ y ∈ S i ∩ B, r (f i) y) →
    (∀ (i : Fin m) (p : Fin n), p ∈ S i →
      (if p ∈ X then ({p} : Finset (Fin n)) else {p, f i}) ∩ S i = {p}) ∧
    (∀ i j : Fin m, i ≠ j → ¬ ((∃ p ∈ S i \ S j,
        ((if p ∈ X then ({p} : Finset (Fin n)) else {p, f i}) ∩ S j).Nonempty) ∧
      (∃ s ∈ S j \ S i, ((if s ∈ X then ({s} : Finset (Fin n)) else {s, f j}) ∩ S i).Nonempty))) := by
  intro n m S X B r f hr hf
  constructor
  · intro i p hp
    by_cases hpX : p ∈ X
    · simp only [hpX, ↓reduceIte]
      ext v
      simp only [Finset.mem_inter, Finset.mem_singleton]
      exact ⟨fun h => h.1, fun h => ⟨h, h ▸ hp⟩⟩
    · have hfi := (hf i (fun h => hpX (h hp))).2.1
      simp only [hpX, ↓reduceIte]
      ext v
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨h | h, hv⟩
        · exact h
        · exact absurd (h ▸ hv) hfi
      · intro h
        exact ⟨Or.inl h, h ▸ hp⟩
  · rintro i j hij ⟨⟨p, hp, v, hv⟩, ⟨s, hs, w, hw⟩⟩
    obtain ⟨a1, a2⟩ := PEqualNP.Outside.L_meta_1471.p1462_rowaux S X f i j p v hp hv
    obtain ⟨b1, b2⟩ := PEqualNP.Outside.L_meta_1471.p1462_rowaux S X f j i s w hs hw
    have h1 := hf i a1
    have h2 := hf j b1
    exact hr _ _ (h1.2.2 (f j) (Finset.mem_inter.2 ⟨b2, h2.1⟩)) (h2.2.2 (f i) (Finset.mem_inter.2 ⟨a2, h1.1⟩))

def p1463_T (x y : Fin 7) : Bool := decide (y - x = 1 ∨ y - x = 2 ∨ y - x = 4)

theorem p1463_T_anti : ∀ x y : Fin 7, PEqualNP.Outside.L_meta_1471.p1463_T x y = true → ¬ PEqualNP.Outside.L_meta_1471.p1463_T y x = true := by decide

theorem p1463_T_dom : ∀ a b : Fin 7, ∃ z : Fin 7, PEqualNP.Outside.L_meta_1471.p1463_T z a = true ∧ PEqualNP.Outside.L_meta_1471.p1463_T z b = true := by decide

theorem p1463_T_irr : ∀ a : Fin 7, ¬ PEqualNP.Outside.L_meta_1471.p1463_T a a = true := by decide

theorem p1463_T_set (U : Finset (Fin 7)) (hU : U.card ≤ 2) :
    ∃ z : Fin 7, z ∉ U ∧ ∀ y ∈ U, PEqualNP.Outside.L_meta_1471.p1463_T z y = true := by
  rcases Finset.eq_empty_or_nonempty U with h | ⟨a, ha⟩
  · subst h
    exact ⟨0, by simp, by simp⟩
  · by_cases hb : ∃ b ∈ U, b ≠ a
    · obtain ⟨b, hb, hba⟩ := hb
      obtain ⟨z, hz1, hz2⟩ := PEqualNP.Outside.L_meta_1471.p1463_T_dom a b
      have hab : ({a, b} : Finset (Fin 7)) = U := by
        apply Finset.eq_of_subset_of_card_le
        · intro v hv
          rw [Finset.mem_insert, Finset.mem_singleton] at hv
          rcases hv with h | h
          · exact h ▸ ha
          · exact h ▸ hb
        · rw [Finset.card_pair (Ne.symm hba)]
          exact hU
      have hall : ∀ y ∈ U, PEqualNP.Outside.L_meta_1471.p1463_T z y = true := by
        intro y hy
        rw [← hab, Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with h | h
        · exact h ▸ hz1
        · exact h ▸ hz2
      exact ⟨z, fun hz => PEqualNP.Outside.L_meta_1471.p1463_T_irr z (hall z hz), hall⟩
    · obtain ⟨z, hz1, _⟩ := PEqualNP.Outside.L_meta_1471.p1463_T_dom a a
      have hall : ∀ y ∈ U, PEqualNP.Outside.L_meta_1471.p1463_T z y = true := by
        intro y hy
        by_cases hya : y = a
        · exact hya ▸ hz1
        · exact absurd ⟨y, hy, hya⟩ hb
      exact ⟨z, fun hz => PEqualNP.Outside.L_meta_1471.p1463_T_irr z (hall z hz), hall⟩


theorem dom_main : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (A : Finset (Fin n)),
    A.card = 7 → (∀ i : Fin m, (S i ∩ A).card ≤ 2) →
    ∃ (r : Fin n → Fin n → Prop) (f : Fin m → Fin n), (∀ a b : Fin n, r a b → ¬ r b a) ∧
      ∀ i : Fin m, f i ∈ A ∧ f i ∉ S i ∧ ∀ y ∈ S i ∩ A, r (f i) y := by
  intro n m S A hA hA2
  have e : A ≃ Fin 7 := Finset.equivFinOfCardEq hA
  have key : ∀ i : Fin m, ∃ z : Fin 7, z ∉ (S i ∩ A).image (fun a => if h : a ∈ A then e ⟨a, h⟩ else 0) ∧
      ∀ y ∈ (S i ∩ A).image (fun a => if h : a ∈ A then e ⟨a, h⟩ else 0), PEqualNP.Outside.L_meta_1471.p1463_T z y = true :=
    fun i => PEqualNP.Outside.L_meta_1471.p1463_T_set _ (le_trans Finset.card_image_le (hA2 i))
  choose z hz1 hz2 using key
  have hg : ∀ i : Fin m, (if h : (e.symm (z i)).1 ∈ A then e ⟨(e.symm (z i)).1, h⟩ else 0) = z i := by
    intro i
    simp
  refine ⟨fun a b => PEqualNP.Outside.L_meta_1471.p1463_T (if h : a ∈ A then e ⟨a, h⟩ else 0) (if h : b ∈ A then e ⟨b, h⟩ else 0) = true,
    fun i => (e.symm (z i)).1, fun a b h => PEqualNP.Outside.L_meta_1471.p1463_T_anti _ _ h, fun i => ⟨(e.symm (z i)).2, ?_, ?_⟩⟩
  · intro hmem
    apply hz1 i
    rw [Finset.mem_image]
    exact ⟨(e.symm (z i)).1, Finset.mem_inter.2 ⟨hmem, (e.symm (z i)).2⟩, hg i⟩
  · intro y hy
    show PEqualNP.Outside.L_meta_1471.p1463_T _ _ = true
    rw [hg i]
    exact hz2 i _ (Finset.mem_image_of_mem _ hy)

theorem core : ∀ (q n m : ℕ) (S : Fin m → Finset (Fin n)) (X B : Finset (Fin n))
    (r : Fin n → Fin n → Prop) (f : Fin m → Fin n),
    1 ≤ q → 1 ≤ m → (∀ i : Fin m, (S i).card = q + 1) →
    (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ v : Fin n, ∃ i : Fin m, v ∈ S i) →
    (∀ a b : Fin n, r a b → ¬ r b a) →
    (∀ i : Fin m, ¬ S i ⊆ X → f i ∈ B ∧ f i ∉ S i ∧ ∀ y ∈ S i ∩ B, r (f i) y) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ) (j : Fin gates.length),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      g.inputs.length ≤ 2) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    (∀ (w : Fin m) (x : Fin n → Bool),
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)) →
    (∀ i : Fin m, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (j : ℕ)⟩ (List.ofFn (fun v : Fin n => decide (v ∉ S i))) = false) →
    (∀ (i : Fin m) (p : Fin n), p ∈ S i →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (j : ℕ)⟩ (List.ofFn (fun v : Fin n => decide (v ∈ (if p ∈ X then ({p} : Finset (Fin n)) else {p, f i})))) = false) →
    m * q + (Finset.univ.filter (fun i : Fin gates.length => j < i ∧ n + (j : ℕ) ∈ (gates.get i).inputs)).card + 2 ≤ gates.length := by
  intro q n m S X B r f hq hm hc hi hcov hr hf gates out j hb hn hu he hco hrow
  obtain ⟨h1, h2⟩ := PEqualNP.Outside.L_meta_1471.rows_main n m S X B r f hr hf
  exact PEqualNP.Outside.L_meta_1471.engine_main q n m S (fun i p => if p ∈ X then ({p} : Finset (Fin n)) else {p, f i})
    hq hm hc hi hcov h1 h2 gates out j hb hn hu he hco hrow

end PEqualNP.Outside.L_meta_1471

theorem PEqualNP.Outside.L_meta_1471 : ∀ (q n m : ℕ) (S : Fin m → Finset (Fin n)) (Y A : Finset (Fin n)),
    2 ≤ q → 1 ≤ m → (∀ i : Fin m, (S i).card = q + 1) →
    (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ v : Fin n, ∃ i : Fin m, v ∈ S i) →
    A ⊆ Y → A.card = 7 → (∀ i : Fin m, (S i ∩ A).card ≤ 2) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ) (j : Fin gates.length),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      g.inputs.length ≤ 2) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    (∀ (w : Fin m) (x : Fin n → Bool),
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)) →
    (∀ x : Fin n → Bool, (∃ v ∈ Y, x v = true) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (j : ℕ)⟩ (List.ofFn x) = false) →
    m * q + (Finset.univ.filter (fun i : Fin gates.length => j < i ∧ n + (j : ℕ) ∈ (gates.get i).inputs)).card + 2 ≤ gates.length := by
  intro q n m S Y A hq hm hc hi hcov hAY hA hA2 gates out j hb hn hu he hY
  obtain ⟨r, f, hr, hf⟩ := PEqualNP.Outside.L_meta_1471.dom_main n m S A hA hA2
  refine PEqualNP.Outside.L_meta_1471.core q n m S ∅ A r f (by omega) hm hc hi hcov hr (fun i _ => hf i)
    gates out j hb hn hu he ?_ ?_
  · intro i
    apply hY
    exact ⟨f i, hAY (hf i).1, by simpa using (hf i).2.1⟩
  · intro i p hp
    apply hY
    exact ⟨f i, hAY (hf i).1, by simp⟩
