import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1513

-- Circuit evaluator and frontier lemmas adapted from upstream L-meta-1460.

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


-- Gate reservation count adapted from upstream L-meta-1461.
theorem paid_card {n : ℕ} (gates : List Gate) (j h : Fin gates.length) (earlier : h < j)
    (paid : Finset (Fin gates.length)) (hj : j ∉ paid) (hh : h ∉ paid)
    (noReader : ∀ i ∈ paid, j < i → n+j.val ∉ (gates.get i).inputs) :
    paid.card + (Finset.univ.filter (fun i : Fin gates.length =>
      j < i ∧ n+j.val ∈ (gates.get i).inputs)).card + 2 ≤ gates.length := by
  classical
  let rs := Finset.univ.filter (fun i : Fin gates.length => j < i ∧ n+j.val∈(gates.get i).inputs)
  have dis : Disjoint paid rs := Finset.disjoint_left.mpr fun i hi hr =>
    noReader i hi (Finset.mem_filter.mp hr).2.1 (Finset.mem_filter.mp hr).2.2
  have outJ : j ∉ paid∪rs := by
    simp [rs,hj]
  have outH : h ∉ insert j (paid∪rs) := by
    simp [rs,hh,earlier.ne,not_lt_of_gt earlier]
  have cap := Finset.card_le_univ (insert h (insert j (paid∪rs)))
  rw [Finset.card_insert_of_notMem outH,Finset.card_insert_of_notMem outJ,
    Finset.card_union_of_disjoint dis,Fintype.card_fin] at cap
  change paid.card+rs.card+2 ≤ gates.length
  omega

-- The evaluation replacement argument adapts L-meta-1457.

def patchC (gates : List Gate) (j : ℕ) : Circuit :=
  ⟨gates.set j ⟨GateOp.or, []⟩, 0⟩

lemma patchC_size (gates : List Gate) (j : ℕ) : (patchC gates j).size = gates.length := by
  simp [patchC, Circuit.size]

lemma patchC_good (gates : List Gate) (j : Fin gates.length)
    (valid : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (unique : ∀ k : Fin gates.length, (gates.get k).op = GateOp.not → k = j) :
    ∀ g ∈ (patchC gates j.val).gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
  have hk' : k < gates.length := by simpa [patchC] using hk
  by_cases hkj : j.val = k
  · simp [patchC, hkj]
  · have same : (patchC gates j.val).gates[k] = gates[k] := by simp [patchC, hkj]
    rw [same]
    obtain ⟨hop, hfan⟩ := valid gates[k] (List.getElem_mem _)
    refine ⟨?_, hfan⟩
    rcases hop with hop | hop | hop
    · exact Or.inl hop
    · exact Or.inr hop
    · exact absurd (congrArg Fin.val (unique ⟨k, hk'⟩ hop)).symm hkj

lemma patchC_false {n : ℕ} (gates : List Gate) (j : Fin gates.length) (x : Fin n → Bool) :
    value (patchC gates j.val) x (n + j.val) = false := by
  have h := gate_value (patchC gates j.val) x (n + j.val) (by omega)
    (by rw [patchC_size]; omega)
  simp only at h
  rw [h]
  simp [patchC, GateOp.eval]

lemma patchC_other {n : ℕ} (gates : List Gate) (j : ℕ) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + gates.length) (hne : w ≠ n + j) :
    value (patchC gates j) x w = (gates[w - n]'(by omega)).op.eval
      ((gates[w - n]'(by omega)).inputs.map fun r =>
        if r < w then value (patchC gates j) x r else false) := by
  have h := gate_value (patchC gates j) x w hn (by rw [patchC_size]; exact hw)
  simp only at h
  rw [h]
  have same : (patchC gates j).gates[w - n]'(by simp [patchC]; omega) =
      gates[w - n]'(by omega) := by
    simp only [patchC, List.getElem_set]
    rw [ite_eq_right (by omega)]
  rw [same]

lemma originalGateValue {n : ℕ} (gates : List Gate) (o : ℕ) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + gates.length) :
    value ⟨gates, o⟩ x w = (gates[w - n]'(by omega)).op.eval
      ((gates[w - n]'(by omega)).inputs.map fun r =>
        if r < w then value ⟨gates, o⟩ x r else false) :=
  gate_value ⟨gates, o⟩ x w hn hw

lemma patchEvalCongr (g : Gate) (f f' : ℕ → Bool) (h : ∀ r ∈ g.inputs, f r = f' r) :
    g.op.eval (g.inputs.map f) = g.op.eval (g.inputs.map f') := by
  rw [List.map_congr_left h]

lemma patchC_eq {n : ℕ} (gates : List Gate) (j : Fin gates.length) (o : ℕ)
    (x : Fin n → Bool) (hjFalse : value ⟨gates, o⟩ x (n + j.val) = false) (w : ℕ) :
    value (patchC gates j.val) x w = value ⟨gates, o⟩ x w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · have h₁ := input_value ⟨gates, o⟩ x ⟨w, hn⟩
      have h₂ := input_value (patchC gates j.val) x ⟨w, hn⟩
      simp only at h₁ h₂
      rw [h₁, h₂]
    by_cases hw : w < n + gates.length
    · by_cases hne : w = n + j.val
      · rw [hne, hjFalse]
        exact patchC_false gates j x
      · rw [originalGateValue gates o x w (by omega) hw,
          patchC_other gates j.val x w (by omega) hw hne]
        apply patchEvalCongr
        intro r _
        by_cases hr : r < w
        · simpa [hr] using ih r hr
        · simp [hr]
    · rw [missing_value ⟨gates, o⟩ x w (by simp only [Circuit.size]; omega),
        missing_value (patchC gates j.val) x w (by rw [patchC_size]; omega)]

lemma not_false_of_input_true {n : ℕ} (gates : List Gate) (j h : Fin gates.length)
    (o : ℕ) (x : Fin n → Bool)
    (hop : (gates.get j).op = GateOp.not) (hlt : h < j)
    (hread : ∃ r : List ℕ, (gates.get j).inputs = (n + h.val) :: r)
    (hhTrue : value ⟨gates, o⟩ x (n + h.val) = true) :
    value ⟨gates, o⟩ x (n + j.val) = false := by
  obtain ⟨r, hr⟩ := hread
  have hj : n + j.val < n + gates.length := by omega
  have hw : n + h.val < n + j.val := by exact Nat.add_lt_add_left hlt n
  have he := originalGateValue gates o x (n + j.val) (by omega) hj
  simp only [Nat.add_sub_cancel_left] at he
  rw [he]
  change (gates.get j).op.eval ((gates.get j).inputs.map fun w =>
    if w < n + j.val then value ⟨gates, o⟩ x w else false) = false
  rw [hop, hr]
  simp [hw, hhTrue, GateOp.eval]

lemma patchC_co_set {n m : ℕ} (gates : List Gate) (j h : Fin gates.length)
    (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ) (i : Fin m)
    (hop : (gates.get j).op = GateOp.not) (hlt : h < j)
    (hread : ∃ r : List ℕ, (gates.get j).inputs = (n + h.val) :: r)
    (hhTrue : (Circuit.mk gates (n + h.val)).eval
      (List.ofFn (fun v : Fin n => decide (v ∉ S i))) = true)
    (hcorrect : ∀ x : Fin n → Bool, (Circuit.mk gates (out i)).eval (List.ofFn x) =
      decide (∃ v ∈ S i, x v = true)) :
    value (patchC gates j.val) (fun v : Fin n => decide (v ∉ S i)) (n + h.val) = true ∧
    value (patchC gates j.val) (fun v : Fin n => decide (v ∉ S i)) (out i) = false := by
  let x (v : Fin n) := decide (v ∉ S i)
  change value (patchC gates j.val) x (n + h.val) = true ∧
    value (patchC gates j.val) x (out i) = false
  have hx : value ⟨gates, out i⟩ x (n + h.val) = true := hhTrue
  have hjFalse := not_false_of_input_true gates j h (out i) x hop hlt hread hx
  rw [patchC_eq gates j (out i) x hjFalse (n + h.val),
    patchC_eq gates j (out i) x hjFalse (out i)]
  refine ⟨hx, ?_⟩
  change (Circuit.mk gates (out i)).eval (List.ofFn x) = false
  rw [hcorrect]
  apply decide_eq_false
  rintro ⟨v, hv, hvt⟩
  exact (of_decide_eq_true hvt) hv
def single1513 {n : ℕ} (p : Fin n) : Fin n → Bool :=
  fun v => decide (v = p)

def Join1513 {n : ℕ} (gs : List Gate) (T : Finset (Fin n)) (y : Fin n → Bool)
    (g : Fin gs.length) : Prop :=
  Multi ⟨gs, 0⟩ T single1513 y (n + g.val) ∧
  gs[g.val].op = GateOp.or ∧
  ∃ a b, gs[g.val].inputs = [a,b] ∧ ∃ p ∈ T, ∃ p' ∈ T, p ≠ p' ∧
    value ⟨gs, 0⟩ (single1513 p) a = true ∧ value ⟨gs, 0⟩ (single1513 p') b = true

lemma pair_of_length_two (L : List ℕ) (h : L.length = 2) :
    ∃ a b, L = [a,b] := by
  rcases L with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · simp at h
  · simp at h
  · exact ⟨a,b,rfl⟩
  · simp at h

lemma join_count1513 {n : ℕ} (gs : List Gate)
    (hC : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (T : Finset (Fin n)) (y : Fin n → Bool) (o : ℕ)
    (hfalse : value ⟨gs, 0⟩ y o = false)
    (htrue : ∀ p ∈ T, value ⟨gs, 0⟩ (single1513 p) o = true)
    (K : Finset (Fin gs.length)) (hK : ∀ g, Join1513 gs T y g → g ∈ K) :
    T.card ≤ K.card + 1 := by
  refine family gs hC T single1513 y o (fun p hp => ⟨htrue p hp, hfalse⟩) ?_ K ?_
  · intro w hw
    rintro ⟨p, _, p', _, hpne, hsv, hsv'⟩
    let v : Fin n := ⟨w,hw⟩
    have h1 := hsv.1
    have h2 := hsv'.1
    change value ⟨gs,0⟩ (single1513 p) v = true at h1
    change value ⟨gs,0⟩ (single1513 p') v = true at h2
    simp only [input_value, single1513, decide_eq_true_eq] at h1 h2
    exact hpne (h1.symm.trans h2)
  · intro g hm hop hlen hall
    apply hK
    obtain ⟨a,b,hab⟩ := pair_of_length_two _ hlen
    refine ⟨hm, hop, a, b, hab, ?_⟩
    obtain ⟨pa,hpa,hva⟩ := hall a (by simp [hab])
    obtain ⟨pb,hpb,hvb⟩ := hall b (by simp [hab])
    by_cases habp : pa = pb
    · subst pb
      obtain ⟨s,hs,t,ht,hst,hvs,hvt⟩ := hm
      have hnew : ∃ u ∈ T, u ≠ pa ∧ value ⟨gs, 0⟩ (single1513 u) (n + g.val) = true := by
        by_cases e : s = pa
        · exact ⟨t, ht, fun he => hst (e.trans he.symm), hvt.1⟩
        · exact ⟨s, hs, e, hvs.1⟩
      obtain ⟨u, hu, hne, hvu⟩ := hnew
      obtain ⟨r, hr, _, hvr⟩ := (or_value ⟨gs,0⟩ g.val g.isLt hop (single1513 u)).mp hvu
      change r ∈ gs[g.val].inputs at hr
      rw [hab] at hr
      rcases List.mem_pair.mp hr with rfl | rfl
      · exact ⟨u, hu, pa, hpa, hne, hvr, hvb⟩
      · exact ⟨pa, hpa, u, hu, Ne.symm hne, hva, hvr⟩
    · exact ⟨pa,hpa,pb,hpb,habp,hva,hvb⟩

lemma budget1513 {n m q : ℕ} (gs : List Gate) (j h : Fin gs.length) (hlt : h < j)
    (I : Finset (Fin gs.length)) (pay : Fin m → Finset (Fin gs.length))
    (loss : Fin m → ℕ) (per : ∀ i, q ≤ (pay i).card + loss i)
    (sep : ∀ i l, i ≠ l → Disjoint (pay i) (pay l))
    (eligible : ∀ i g, g ∈ pay i → g ≠ j ∧ g ≠ h ∧
      ¬ (j < g ∧ n + j.val ∈ (gs.get g).inputs) ∧ g ∉ I)
    (idle : ∀ g ∈ I, g ≠ j ∧ g ≠ h ∧ ¬ (j < g ∧ n + j.val ∈ (gs.get g).inputs)) :
    m * q + (Finset.univ.filter (fun g : Fin gs.length =>
      j < g ∧ n + j.val ∈ (gs.get g).inputs)).card + 2 + I.card ≤
      gs.length + ∑ i, loss i := by
  classical
  let P := Finset.univ.biUnion pay
  have cardP : P.card = ∑ i, (pay i).card :=
    Finset.card_biUnion (fun i _ l _ hd => sep i l hd)
  have bounds (g) (hg : g ∈ P) :
      g ≠ j ∧ g ≠ h ∧ ¬ (j < g ∧ n + j.val ∈ (gs.get g).inputs) ∧ g ∉ I := by
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hg
    exact eligible i g hi
  have dis : Disjoint P I := Finset.disjoint_left.mpr fun g hg => (bounds g hg).2.2.2
  have safe (g) (hg : g ∈ P ∪ I) :
      g ≠ j ∧ g ≠ h ∧ ¬ (j < g ∧ n + j.val ∈ (gs.get g).inputs) := by
    rcases Finset.mem_union.mp hg with hp | hi
    · exact ⟨(bounds g hp).1, (bounds g hp).2.1, (bounds g hp).2.2.1⟩
    · exact idle g hi
  have cap := paid_card (n := n) gs j h hlt (P ∪ I)
    (fun hj => (safe j hj).1 rfl) (fun hh => (safe h hh).2.1 rfl)
    (fun g hg hglt hr => (safe g hg).2.2 ⟨hglt, hr⟩)
  rw [Finset.card_union_of_disjoint dis] at cap
  have sum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => per i)
  rw [Finset.sum_add_distrib, ← cardP] at sum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at sum
  omega

lemma restrict_join1513 {n : ℕ} (gs : List Gate)
    (hgs : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (T U R : Finset (Fin n)) (w : ℕ) (hl : (T ∩ U).card ≤ 1) (hR : R ⊆ T)
    (hm : Multi ⟨gs,0⟩ R single1513 (fun v => decide (v ∉ T)) w)
    (off : value ⟨gs,0⟩ (fun v => decide (v ∉ U)) w = false) : False := by
  classical
  obtain ⟨p,hp,r,hr,hpr,hpval,hrval⟩ := hm
  have memU (v : Fin n) (hv : value ⟨gs,0⟩ (single1513 v) w = true) : v ∈ U := by
    by_contra hvU
    have inc : ∀ b, single1513 v b = true → decide (b ∉ U) = true := by
      intro b hb
      have hbv : b = v := by simpa [single1513] using hb
      simpa [hbv] using hvU
    have bad := mono ⟨gs,0⟩ hgs _ _ inc w hv
    exact Bool.noConfusion (off.symm.trans bad)
  have sub : ({p,r} : Finset (Fin n)) ⊆ T ∩ U := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact Finset.mem_inter.mpr ⟨hR hp, memU _ hpval.1⟩
    · exact Finset.mem_inter.mpr ⟨hR hr, memU _ hrval.1⟩
  have two := Finset.card_le_card sub
  simp [hpr] at two
  omega

end PEqualNP.Outside.L_meta_1513

open PEqualNP.Outside.L_meta_1513

theorem PEqualNP.Outside.L_meta_1513 : ∀ (q n m : ℕ) (S : Fin m → Finset (Fin n)),
    (∀ i : Fin m, (S i).card = q + 1) →
    (∀ i i' : Fin m, i ≠ i' → (S i ∩ S i').card ≤ 1) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ) (j h : Fin gates.length),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      g.inputs.length ≤ 2) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (n + (h : ℕ)) :: r) →
    (∀ (w : Fin m) (x : Fin n → Bool),
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)) →
    (∀ i : Fin m, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (h : ℕ)⟩ (List.ofFn (fun v : Fin n => decide (v ∉ S i))) = true) →
    ∀ I : Finset (Fin gates.length),
      (∀ g : Fin gates.length, g ∈ I ↔
        (g ≠ j ∧ g ≠ h ∧ ¬ (j < g ∧ n + (j : ℕ) ∈ (gates.get g).inputs) ∧
         ¬ ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∃ i : Fin m,
            PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩, n + (g : ℕ)⟩
              (List.ofFn (fun v : Fin n => decide (v ∉ S i))) = false ∧
            ∃ (w1 w2 : ℕ), (gates.get g).inputs = [w1, w2] ∧
            ∃ p ∈ S i, ∃ p' ∈ S i, p ≠ p' ∧
              PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩, out i⟩ (List.ofFn (fun v : Fin n => decide (v = p))) = true ∧
              PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩, out i⟩ (List.ofFn (fun v : Fin n => decide (v = p'))) = true ∧
              PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩, w1⟩ (List.ofFn (fun v : Fin n => decide (v = p))) = true ∧
              PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩, w2⟩ (List.ofFn (fun v : Fin n => decide (v = p'))) = true))) →
      m * q + (Finset.univ.filter (fun i : Fin gates.length => j < i ∧ n + (j : ℕ) ∈ (gates.get i).inputs)).card + 2 + I.card
        ≤ gates.length + ∑ i : Fin m, (q + 1 - ((S i).filter (fun p => PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩, out i⟩
            (List.ofFn (fun v : Fin n => decide (v = p))) = true)).card) := by
  classical
  intro q n m S hsize hthin gs out j h hgood hj huniq hlt hread hcorrect hhigh I hI
  let C := patchC gs j.val
  let D := C.gates
  have len : D.length = gs.length := by simp [D,C,patchC]
  let e : Fin D.length ≃ Fin gs.length := finCongr len
  let y (i : Fin m) (v : Fin n) := decide (v ∉ S i)
  let T (i : Fin m) := (S i).filter (fun p => value C (single1513 p) (out i) = true)
  let R (i : Fin m) : Finset (Fin D.length) := Finset.univ.filter (Join1513 D (T i) (y i))
  let pay (i : Fin m) := (R i).map e.toEmbedding
  let loss (i : Fin m) := q + 1 - (T i).card
  have hD := patchC_good gs j hgood huniq
  have hco (i : Fin m) : value C (y i) (n + h.val) = true ∧ value C (y i) (out i) = false :=
    patchC_co_set gs j h S out i hj hlt hread (hhigh i) (hcorrect i)
  have live (i : Fin m) (p : Fin n) (hp : p ∈ T i) :
      p ∈ S i ∧ value C (single1513 p) (out i) = true :=
    Finset.mem_filter.mp hp
  have mempay {i : Fin m} {g : Fin gs.length} (hg : g ∈ pay i) :
      Join1513 D (T i) (y i) (e.symm g) := by
    obtain ⟨a,ha,he⟩ := Finset.mem_map.mp hg
    change e a = g at he
    subst g
    simpa only [Equiv.symm_apply_apply] using
      (show Join1513 D (T i) (y i) a from (Finset.mem_filter.mp ha).2)
  have off {i : Fin m} {g : Fin gs.length} (hg : g ∈ pay i) :
      value C (y i) (n + g.val) = false := by
    obtain ⟨_,_,_,_,_,hv,_⟩ := (mempay hg).1
    exact hv.2
  apply budget1513 (n := n) gs j h hlt I pay loss
  · intro i
    have many := join_count1513 D hD (T i) (y i) (out i) (hco i).2
      (fun p hp => (live i p hp).2) (R i)
      (fun g hg => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩)
    have pc : (pay i).card = (R i).card := Finset.card_map _
    have tc : (T i).card ≤ q + 1 := by
      rw [← hsize i]
      exact Finset.card_filter_le _ _
    change q ≤ (pay i).card + (q + 1 - (T i).card)
    omega
  · intro i l hil
    apply Finset.disjoint_left.mpr
    intro g hi hl
    exact restrict_join1513 D hD (S i) (S l) (T i) (n + g.val) (hthin i l hil)
      (fun _ hp => (live i _ hp).1) (mempay hi).1 (off hl)
  · intro i g hg
    obtain ⟨hm,hop,a,b,hab,p,hp,r,hr,hpr,hap,hbr⟩ := mempay hg
    have ofalse := off hg
    have gj : g ≠ j := by
      intro he
      obtain ⟨v,_,_,_,_,hv,_⟩ := hm
      have high : value C (single1513 v) (n + g.val) = true := hv.1
      rw [he] at high
      exact Bool.noConfusion ((patchC_false gs j (single1513 v)).symm.trans high)
    have gh : g ≠ h := by
      intro he
      rw [he] at ofalse
      exact Bool.noConfusion (ofalse.symm.trans (hco i).1)
    have geteq : D[(e.symm g).val] = gs.get g := by
      have ne : j.val ≠ g.val := fun he => gj (Fin.ext he.symm)
      change (gs.set j.val ⟨GateOp.or, []⟩)[g.val] = gs[g.val]
      simp [ne]
    rw [geteq] at hop hab
    have noRead : ¬ (j < g ∧ n + j.val ∈ (gs.get g).inputs) := by
      rintro ⟨_, hmread⟩
      rw [hab] at hmread
      rcases List.mem_pair.mp hmread with he | he
      · rw [← he] at hap
        exact Bool.noConfusion ((patchC_false gs j (single1513 p)).symm.trans hap)
      · rw [← he] at hbr
        exact Bool.noConfusion ((patchC_false gs j (single1513 r)).symm.trans hbr)
    refine ⟨gj,gh,noRead,?_⟩
    intro idle
    apply ((hI g).mp idle).2.2.2
    exact ⟨hop,i,ofalse,a,b,hab,p,(live i p hp).1,r,(live i r hr).1,hpr,
      (live i p hp).2,(live i r hr).2,hap,hbr⟩
  · intro g hg
    obtain ⟨gj,gh,gn,_⟩ := (hI g).mp hg
    exact ⟨gj,gh,gn⟩
