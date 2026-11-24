import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1518

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

lemma main : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ D : (Fin 13 → Bool) → Prop,
    (∀ x y : Fin 13 → Bool, D x → (∀ v : Fin 13, x v = true → y v = true) → D y) →
    (∀ t : Fin 13, D (fun v => decide (v ∉ L t))) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin 13 → ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    (∀ (t : Fin 13) (x : Fin 13 → Bool), D x →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    ∀ (Lam : Finset (Fin 13)) (B : Fin 13 → Fin 13 → Finset (Fin 13)),
    (∀ t ∈ Lam, ∀ p ∈ L t, B t p ∩ L t = ∅ ∧ D (fun v => decide (v = p ∨ v ∈ B t p))) →
    (∀ t ∈ Lam, ∀ t' ∈ Lam, t ≠ t' → ¬ ((∃ p ∈ L t \ L t', (B t p ∩ L t').Nonempty) ∧
      (∃ p ∈ L t' \ L t, (B t' p ∩ L t).Nonempty))) →
    ∀ I : Finset (Fin gates.length), (∀ g ∈ I, (gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.and) →
      3 * Lam.card + max (13 - Lam.card) I.card ≤ gates.length := by
  intro L hL D hup hco gates o hg hout Lam B hB hno I hI
  classical
  let R : Fin 13 → Fin 13 → Finset (Fin 13) := fun t p => insert p (B t p)
  have hint : ∀ i j : Fin 13, i ≠ j → (L i ∩ L j).card ≤ 1 := by
    intro i j
    rw [hL i, hL j]
    revert i j
    decide
  have hcard : ∀ t : Fin 13, (L t).card = 4 := by
    intro t
    rw [hL t]
    revert t
    decide
  have hgeo1 : ∀ t t' : Fin 13, t ≠ t' → ∃ u ∈ L t, u ∉ L t' := by
    intro t t'
    rw [hL t, hL t']
    revert t t'
    decide
  have hgeo2 : ∀ t v : Fin 13, v ∈ L t → ∃ t' : Fin 13, t' ≠ t ∧ v ∈ L t' := by
    simp only [hL]
    decide +kernel
  have hsucc : ∀ t : Fin 13, t ≠ t + 1 := by decide
  have hval : ∀ (t : Fin 13) (x : Fin 13 → Bool), D x →
      value ⟨gates, 0⟩ x (o t) = decide (∃ v ∈ L t, x v = true) := fun t x hx => hout t x hx
  have hDco : ∀ t : Fin 13, D (coY L t) := hco
  have hfalse : ∀ t : Fin 13, value ⟨gates, 0⟩ (coY L t) (o t) = false := by
    intro t
    rw [hval t _ (hDco t)]
    refine decide_eq_false ?_
    rintro ⟨v, hv, h⟩
    exact (of_decide_eq_true h) hv
  have hA : ∀ t t' : Fin 13, t ≠ t' → value ⟨gates, 0⟩ (coY L t') (o t) = true := by
    intro t t' htt
    rw [hval t _ (hDco t')]
    obtain ⟨u, hu, hu'⟩ := hgeo1 t t' htt
    exact decide_eq_true ⟨u, hu, decide_eq_true hu'⟩
  have hrow : ∀ t ∈ Lam, ∀ p ∈ L t, rowL R t p = fun v => decide (v = p ∨ v ∈ B t p) := by
    intro t _ p _
    funext v
    simp only [rowL, R, Finset.mem_insert]
  have htrue : ∀ t ∈ Lam, ∀ p ∈ L t, value ⟨gates, 0⟩ (rowL R t p) (o t) = true := by
    intro t ht p hp
    have hd : D (rowL R t p) := by
      rw [hrow t ht p hp]
      exact (hB t ht p hp).2
    rw [hval t _ hd]
    exact decide_eq_true ⟨p, hp, decide_eq_true (Finset.mem_insert_self p _)⟩
  let K : Fin 13 → Finset (Fin gates.length) := fun i => Finset.univ.filter fun g =>
    InK gates L R i g
  have hK3 : ∀ t ∈ Lam, 3 ≤ (K t).card := by
    intro i hiL
    have h := family (n := 13) gates hg (L i) (rowL R i) (coY L i) (o i)
      (fun p hp => ⟨htrue i hiL p hp, hfalse i⟩)
      (fun w hw hc => by
        obtain ⟨p, hp, p', hp', hne, hs1, hs2⟩ := hc
        have e : ∀ a ∈ L i, Sv ⟨gates, 0⟩ (rowL R i) (coY L i) a w →
            (⟨w, hw⟩ : Fin 13) = a := by
          intro a ha hsa
          have h1 : value ⟨gates, 0⟩ (rowL R i a) ((⟨w, hw⟩ : Fin 13) : ℕ) = true := hsa.1
          have h2 : value ⟨gates, 0⟩ (coY L i) ((⟨w, hw⟩ : Fin 13) : ℕ) = false := hsa.2
          rw [input_value] at h1 h2
          simp only [rowL, coY, R, decide_eq_true_eq, decide_eq_false_iff_not, not_not] at h1 h2
          rcases Finset.mem_insert.mp h1 with h3 | h3
          · exact h3
          · have h4 : (⟨w, hw⟩ : Fin 13) ∈ B i a ∩ L i := Finset.mem_inter.mpr ⟨h3, h2⟩
            rw [(hB i hiL a ha).1] at h4
            exact absurd h4 (Finset.notMem_empty _)
        exact hne ((e p hp hs1).symm.trans (e p' hp' hs2)))
      (K i)
      (fun g hm hop hl hQ => Finset.mem_filter.mpr ⟨Finset.mem_univ g, hm, hop, hl, hQ⟩)
    have := hcard i
    omega
  have hKy : ∀ (i : Fin 13) (g : Fin gates.length), g ∈ K i →
      value ⟨gates, 0⟩ (coY L i) (13 + (g : ℕ)) = false := by
    intro i g hgi
    obtain ⟨p, _, _, _, _, hs, _⟩ := (Finset.mem_filter.mp hgi).2.1
    exact hs.2
  have hconv : ∀ i j : Fin 13, (¬ ∃ p ∈ L i \ L j, (B i p ∩ L j).Nonempty) →
      ¬ ∃ p ∈ L i \ L j, (R i p ∩ L j).Nonempty := by
    rintro i j hn ⟨p, hp, v, hv⟩
    refine hn ⟨p, hp, v, ?_⟩
    obtain ⟨hv1, hv2⟩ := Finset.mem_inter.mp hv
    rcases Finset.mem_insert.mp hv1 with h3 | h3
    · rw [h3] at hv2
      exact absurd hv2 (Finset.mem_sdiff.mp hp).2
    · exact Finset.mem_inter.mpr ⟨h3, hv2⟩
  have hdisj : ∀ i ∈ Lam, ∀ j ∈ Lam, i ≠ j → Disjoint (K i) (K j) := by
    intro i hi j hj hij
    refine Finset.disjoint_left.mpr fun g hgi hgj => ?_
    have hmi := (Finset.mem_filter.mp hgi).2.1
    have hmj := (Finset.mem_filter.mp hgj).2.1
    have hyi := hKy i g hgi
    have hyj := hKy j g hgj
    by_cases hA' : ∃ p ∈ L i \ L j, (B i p ∩ L j).Nonempty
    · have hB' : ¬ ∃ s ∈ L j \ L i, (B j s ∩ L i).Nonempty := fun hB' => hno i hi j hj hij ⟨hA', hB'⟩
      exact kill gates hg L R j i
        (by rw [Finset.inter_comm]; exact hint i j hij) (hconv j i hB') _ hmj hyi
    · exact kill gates hg L R i j (hint i j hij) (hconv i j hA') _ hmi hyj
  let U : Finset (Fin gates.length) := Lam.biUnion K
  have hU : 3 * Lam.card ≤ U.card := by
    have h1 : U.card = ∑ i ∈ Lam, (K i).card := Finset.card_biUnion hdisj
    have h2 : ∑ _i ∈ Lam, 3 ≤ ∑ i ∈ Lam, (K i).card := Finset.sum_le_sum fun i hi => hK3 i hi
    rw [Finset.sum_const, smul_eq_mul] at h2
    omega
  have hUor : ∀ g ∈ U, gates[(g : ℕ)].op = GateOp.or := by
    intro g hgU
    obtain ⟨i, _, hgi⟩ := Finset.mem_biUnion.mp hgU
    exact (Finset.mem_filter.mp hgi).2.2.1
  have hUI : Disjoint U I := by
    refine Finset.disjoint_left.mpr fun g hgU hgI => ?_
    have h1 := hUor g hgU
    have h2 : gates[(g : ℕ)].op = GateOp.and := hI g hgI
    rw [h1] at h2
    exact GateOp.noConfusion h2
  have hpart2 : 3 * Lam.card + I.card ≤ gates.length := by
    have h1 := Finset.card_union_of_disjoint hUI
    have h2 := Finset.card_le_univ (U ∪ I)
    rw [Fintype.card_fin] at h2
    omega
  have hrange : ∀ t : Fin 13, 13 ≤ o t ∧ o t < 13 + gates.length := by
    intro t
    constructor
    · by_contra hlt
      have hlt' : o t < 13 := by omega
      have hin : ∀ x : Fin 13 → Bool, value ⟨gates, 0⟩ x (o t) = x ⟨o t, hlt'⟩ := fun x =>
        input_value ⟨gates, 0⟩ x ⟨o t, hlt'⟩
      have h1 := hfalse t
      rw [hin] at h1
      have hv : (⟨o t, hlt'⟩ : Fin 13) ∈ L t := by
        simpa only [coY, decide_eq_false_iff_not, not_not] using h1
      obtain ⟨t', hne, hv'⟩ := hgeo2 t _ hv
      have h2 := hA t t' (Ne.symm hne)
      rw [hin] at h2
      simp only [coY, decide_eq_true_eq] at h2
      exact h2 hv'
    · by_contra hge
      have h2 := hA t (t + 1) (hsucc t)
      rw [missing_value ⟨gates, 0⟩ _ (o t) (by change 13 + gates.length ≤ o t; omega)] at h2
      exact Bool.noConfusion h2
  let Un : Finset ℕ := U.image (fun g : Fin gates.length => 13 + (g : ℕ))
  let On : Finset ℕ := (Finset.univ \ Lam).image o
  have hUn : Un.card = U.card := Finset.card_image_of_injective _ (by
    intro a b hab
    exact Fin.ext (by simpa using hab))
  have hOn : On.card = 13 - Lam.card := by
    have h1 : On.card = (Finset.univ \ Lam).card := Finset.card_image_of_injOn (by
      intro a _ b _ hab
      by_contra hne
      have h1 := hA a b hne
      have h2 := hfalse b
      rw [show o a = o b from hab] at h1
      rw [h1] at h2
      exact Bool.noConfusion h2)
    rw [h1, Finset.card_sdiff_of_subset (Finset.subset_univ Lam), Finset.card_univ, Fintype.card_fin]
  have hdis : Disjoint Un On := by
    refine Finset.disjoint_left.mpr fun w hwU hwO => ?_
    obtain ⟨g, hgU, rfl⟩ := Finset.mem_image.mp hwU
    obtain ⟨t, htL, hto⟩ := Finset.mem_image.mp hwO
    obtain ⟨i, hiL, hgi⟩ := Finset.mem_biUnion.mp hgU
    have hne : t ≠ i := fun e => (Finset.mem_sdiff.mp htL).2 (e ▸ hiL)
    have h1 := hA t i hne
    have h2 := hKy i g hgi
    rw [hto, h2] at h1
    exact Bool.noConfusion h1
  have hsub : Un ∪ On ⊆ Finset.Ico 13 (13 + gates.length) := by
    intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp hw
      exact Finset.mem_Ico.mpr ⟨by omega, by have := g.isLt; omega⟩
    · obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hw
      exact Finset.mem_Ico.mpr (hrange t)
  have hpart1 : 3 * Lam.card + (13 - Lam.card) ≤ gates.length := by
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdis, Nat.card_Ico] at h1
    omega
  rcases le_total (13 - Lam.card) I.card with h | h
  · rw [max_eq_right h]
    exact hpart2
  · rw [max_eq_left h]
    exact hpart1

lemma hmono (gates : List Gate) (j : Fin gates.length)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hone : ∀ i : Fin gates.length, (gates.get i).op = GateOp.not → i = j)
    (x y : Fin 13 → Bool) (hxy : ∀ v, x v = true → y v = true) (w : ℕ) (hw : w < 13 + (j : ℕ)) :
    value ⟨gates, 0⟩ x w = true → value ⟨gates, 0⟩ y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < 13
    · let p : Fin 13 := ⟨w, hn⟩
      change value ⟨gates, 0⟩ x p = true → value ⟨gates, 0⟩ y p = true
      simpa only [input_value] using hxy p
    · have hk : w - 13 < gates.length := by
        have := j.isLt
        omega
      have hwk : w = 13 + (w - 13) := by omega
      rw [hwk]
      have hop : gates[w - 13].op = GateOp.and ∨ gates[w - 13].op = GateOp.or := by
        rcases (hg _ (List.getElem_mem hk)).1 with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · have h1 := hone ⟨w - 13, hk⟩ h
          have h2 : w - 13 = (j : ℕ) := congrArg Fin.val h1
          omega
      exact gate_mono (n := 13) ⟨gates, 0⟩ (w - 13) hk hop x y fun r _ hlt => ih r (by omega) (by omega)

def drun (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma druncons (g : Gate) (gs : List Gate) (x : List Bool) :
    drun (g :: gs) x = drun gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma drunappend (A B : List Gate) (x : List Bool) : drun (A ++ B) x = drun B (drun A x) := by
  simp [drun, List.foldl_append]

lemma drunlength (gs : List Gate) (x : List Bool) :
    (drun gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [drun]
  | cons g gs ih => rw [druncons, ih]; simp; omega

lemma drungetD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (drun gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [druncons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma drunsplit (gs : List Gate) (x : List Bool) (j : ℕ) :
    drun gs x = drun (gs.drop j) (drun (gs.take j) x) := by
  simpa only [drun, List.foldl_append] using
    congrArg (fun l : List Gate => drun l x) (List.take_append_drop j gs).symm

def dvalue {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma dmissingvalue {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : dvalue C x w = false := by
  change (drun C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [drunlength, Circuit.size] using hw)

lemma dgatevalue {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    dvalue C x w = g.op.eval (g.inputs.map fun r => if r < w then dvalue C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := drun (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, drunlength, Nat.min_eq_left hj.le, j]; omega
  have split : drun C.gates (List.ofFn x) = drun (g :: C.gates.drop (j + 1)) earlier := by
    rw [drunsplit C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then dvalue C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (drun C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (drungetD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (drun C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then dvalue C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [druncons]
  rw [drungetD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

lemma dgatevalueP {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (k : ℕ) (hk : k < gs.length) :
    dvalue ⟨gs, 0⟩ x (n + k) =
      gs[k].op.eval (gs[k].inputs.map fun r => if r < n + k then dvalue ⟨gs, 0⟩ x r else false) := by
  have h := dgatevalue ⟨gs, 0⟩ x (n + k) (by omega) (by change n + k < n + gs.length; omega)
  simpa only [Nat.add_sub_cancel_left] using h

def isOr : GateOp → Bool
  | GateOp.or => true
  | _ => false

def isNot : GateOp → Bool
  | GateOp.not => true
  | _ => false

lemma eval_ao (op : GateOp) (l : List Bool) (h : op = GateOp.and ∨ op = GateOp.or) :
    op.eval l = if isOr op ∈ l then isOr op else !isOr op := by
  rcases h with rfl | rfl
  · simp only [GateOp.eval, isOr]
    induction l with
    | nil => rfl
    | cons b t ih => cases b <;> simp_all
  · simp only [GateOp.eval, isOr]
    induction l with
    | nil => rfl
    | cons b t ih => cases b <;> simp_all

def fin3 (a : Bool) (op : GateOp) (N : ℕ) : List ℕ → (Bool ⊕ ℕ) × List Gate
  | [] => (Sum.inl (!a), [])
  | [w] => (Sum.inr w, [])
  | w :: w2 :: t => (Sum.inr N, [⟨op, w :: w2 :: t⟩])

def gen (ρ : List (Bool ⊕ ℕ)) (N : ℕ) (g : Gate) : (Bool ⊕ ℕ) × List Gate :=
  if Sum.inl (isOr g.op) ∈ g.inputs.map (fun r => ρ.getD r (Sum.inl false)) then
    (Sum.inl (isOr g.op), [])
  else fin3 (isOr g.op) g.op N
    ((g.inputs.map (fun r => ρ.getD r (Sum.inl false))).filterMap Sum.getRight?)

def stp (n h k : ℕ) (g : Gate) (s : List (Bool ⊕ ℕ) × List Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  if k < h then (s.1 ++ [Sum.inr (n + s.2.length)], s.2 ++ [g])
  else if k = h then (s.1 ++ [Sum.inl true], s.2)
  else if isNot g.op = true then (s.1 ++ [Sum.inl false], s.2)
  else (s.1 ++ [(gen s.1 (n + s.2.length) g).1], s.2 ++ (gen s.1 (n + s.2.length) g).2)

def S (n h : ℕ) (gs : List Gate) : ℕ → List (Bool ⊕ ℕ) × List Gate
  | 0 => ((List.range n).map Sum.inr, [])
  | k + 1 => match gs[k]? with
    | none => S n h gs k
    | some g => stp n h k g (S n h gs k)

lemma S_succ (n h : ℕ) (gs : List Gate) (k : ℕ) (hk : k < gs.length) :
    S n h gs (k + 1) = stp n h k gs[k] (S n h gs k) := by
  rw [S]
  simp [hk]

lemma fin3_len (a : Bool) (op : GateOp) (N : ℕ) (l : List ℕ) : (fin3 a op N l).2.length ≤ 1 := by
  rcases l with _ | ⟨w, _ | ⟨w2, t⟩⟩ <;> simp [fin3]

lemma fin3_mem (a : Bool) (op : GateOp) (N : ℕ) (l : List ℕ) :
    ∀ g' ∈ (fin3 a op N l).2, g'.op = op ∧ g'.inputs = l := by
  rcases l with _ | ⟨w, _ | ⟨w2, t⟩⟩ <;> simp [fin3]

lemma fin3_short (a : Bool) (op : GateOp) (N : ℕ) (l : List ℕ) (h : l.length ≤ 1) :
    (fin3 a op N l).2 = [] := by
  rcases l with _ | ⟨w, _ | ⟨w2, t⟩⟩
  · rfl
  · rfl
  · simp at h

lemma gen_len (ρ : List (Bool ⊕ ℕ)) (N : ℕ) (g : Gate) : (gen ρ N g).2.length ≤ 1 := by
  unfold gen
  split_ifs
  · simp
  · exact fin3_len _ _ _ _

lemma gen_mem (ρ : List (Bool ⊕ ℕ)) (N : ℕ) (g : Gate) :
    ∀ g' ∈ (gen ρ N g).2, g'.op = g.op ∧ g'.inputs.length ≤ g.inputs.length := by
  unfold gen
  split_ifs
  · simp
  · intro g' hg'
    obtain ⟨h1, h2⟩ := fin3_mem _ _ _ _ g' hg'
    refine ⟨h1, ?_⟩
    rw [h2]
    exact (List.length_filterMap_le _ _).trans (by simp)

lemma filterMap_lt (l : List (Bool ⊕ ℕ)) (b : Bool) (h : Sum.inl b ∈ l) :
    (l.filterMap Sum.getRight?).length + 1 ≤ l.length := by
  induction l with
  | nil => simp at h
  | cons c t ih =>
    rcases List.mem_cons.mp h with h | h
    · subst h
      have := List.length_filterMap_le Sum.getRight? t
      change (t.filterMap Sum.getRight?).length + 1 ≤ t.length + 1
      omega
    · have := ih h
      rcases c with c | c
      · change (t.filterMap Sum.getRight?).length + 1 ≤ t.length + 1
        omega
      · change (t.filterMap Sum.getRight?).length + 1 + 1 ≤ t.length + 1
        omega

lemma gen_reader (ρ : List (Bool ⊕ ℕ)) (N : ℕ) (g : Gate) (hlen : g.inputs.length ≤ 2)
    (r : ℕ) (hr : r ∈ g.inputs) (hρ : ρ.getD r (Sum.inl false) = Sum.inl false) :
    (gen ρ N g).2 = [] := by
  unfold gen
  split_ifs
  · rfl
  · apply fin3_short
    have hm : Sum.inl false ∈ g.inputs.map (fun r => ρ.getD r (Sum.inl false)) :=
      List.mem_map.mpr ⟨r, hr, hρ⟩
    have := filterMap_lt _ false hm
    simp only [List.length_map] at this
    omega

lemma stp_fst (n h k : ℕ) (g : Gate) (s : List (Bool ⊕ ℕ) × List Gate) :
    ∃ d, (stp n h k g s).1 = s.1 ++ [d] := by
  unfold stp
  split_ifs <;> exact ⟨_, rfl⟩

lemma stp_snd (n h k : ℕ) (g : Gate) (s : List (Bool ⊕ ℕ) × List Gate) :
    ∃ e, (stp n h k g s).2 = s.2 ++ e ∧ e.length ≤ 1 := by
  unfold stp
  split_ifs
  · exact ⟨[g], rfl, by simp⟩
  · exact ⟨[], by simp, by simp⟩
  · exact ⟨[], by simp, by simp⟩
  · exact ⟨_, rfl, gen_len _ _ _⟩

lemma S_len (n h : ℕ) (gs : List Gate) : ∀ k, k ≤ gs.length → (S n h gs k).1.length = n + k := by
  intro k
  induction k with
  | zero => intro _; simp [S]
  | succ k ih =>
    intro hk
    rw [S_succ n h gs k (by omega)]
    obtain ⟨d, hd⟩ := stp_fst n h k gs[k] (S n h gs k)
    rw [hd, List.length_append, ih (by omega)]
    simp
    omega

lemma S_low (n h : ℕ) (gs : List Gate) : ∀ k, k ≤ gs.length → k ≤ h →
    (S n h gs k).2 = gs.take k ∧ (S n h gs k).1 = (List.range (n + k)).map Sum.inr := by
  intro k
  induction k with
  | zero => intro _ _; simp [S]
  | succ k ih =>
    intro hk hkh
    obtain ⟨h1, h2⟩ := ih (by omega) (by omega)
    rw [S_succ n h gs k (by omega)]
    have hlt : k < h := by omega
    unfold stp
    simp only [hlt, ↓reduceIte]
    rw [h1, h2]
    refine ⟨(List.take_succ_eq_append_getElem (by omega)).symm, ?_⟩
    have : (List.take k gs).length = k := by simp; omega
    rw [this, ← Nat.add_assoc, List.range_succ, List.map_append]
    rfl

lemma S_prefix (n h : ℕ) (gs : List Gate) : ∀ k, k ≤ gs.length → h ≤ k →
    gs.take h <+: (S n h gs k).2 := by
  intro k
  induction k with
  | zero =>
    intro _ hh
    have : h = 0 := by omega
    subst this
    simp
  | succ k ih =>
    intro hk hh
    by_cases he : h = k + 1
    · rw [he, (S_low n (k + 1) gs (k + 1) hk le_rfl).1]
    · rw [S_succ n h gs k (by omega)]
      obtain ⟨e, he2, _⟩ := stp_snd n h k gs[k] (S n h gs k)
      rw [he2]
      exact (ih (by omega) (by omega)).trans (List.prefix_append _ _)

lemma S_ops (n h j : ℕ) (gs : List Gate) (hhj : h < j)
    (hops : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (huniq : ∀ i (hi : i < gs.length), gs[i].op = GateOp.not → i = j) :
    ∀ k, k ≤ gs.length → ∀ g' ∈ (S n h gs k).2,
      (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length ≤ 2 := by
  intro k
  induction k with
  | zero => intro _ g' hg'; simp [S] at hg'
  | succ k ih =>
    intro hk g' hg'
    have hkl : k < gs.length := by omega
    rw [S_succ n h gs k hkl] at hg'
    have hg := hops gs[k] (List.getElem_mem hkl)
    unfold stp at hg'
    split_ifs at hg' with h1 h2 h3
    · rcases List.mem_append.mp hg' with hm | hm
      · exact ih (by omega) g' hm
      · rw [List.mem_singleton.mp hm]
        refine ⟨?_, hg.2⟩
        rcases hg.1 with ho | ho | ho
        · exact Or.inl ho
        · exact Or.inr ho
        · have := huniq k hkl ho
          omega
    · exact ih (by omega) g' hg'
    · exact ih (by omega) g' hg'
    · rcases List.mem_append.mp hg' with hm | hm
      · exact ih (by omega) g' hm
      · obtain ⟨e1, e2⟩ := gen_mem _ _ _ g' hm
        refine ⟨?_, e2.trans hg.2⟩
        rw [e1]
        rcases hg.1 with ho | ho | ho
        · exact Or.inl ho
        · exact Or.inr ho
        · rw [ho] at h3
          exact absurd rfl h3

lemma S_j (n h j : ℕ) (gs : List Gate) (hhj : h < j) (hj : j < gs.length)
    (hjn : gs[j].op = GateOp.not) :
    ∀ k, k ≤ gs.length → j < k → (S n h gs k).1.getD (n + j) (Sum.inl false) = Sum.inl false := by
  intro k
  induction k with
  | zero => intro _ h0; omega
  | succ k ih =>
    intro hk hjk
    have hkl : k < gs.length := by omega
    have hl := S_len n h gs k (by omega)
    by_cases he : k = j
    · subst he
      rw [S_succ n h gs k hkl]
      unfold stp
      have h1 : ¬ k < h := by omega
      have h2 : ¬ k = h := by omega
      have h3 : isNot gs[k].op = true := by rw [hjn]; rfl
      simp only [h1, h2, h3, ↓reduceIte]
      rw [List.getD_append_right _ _ _ _ (by omega)]
      simp [hl]
    · rw [S_succ n h gs k hkl]
      obtain ⟨d, hd⟩ := stp_fst n h k gs[k] (S n h gs k)
      rw [hd, List.getD_append _ _ _ _ (by omega)]
      exact ih (by omega) (by omega)

def bad (n h j : ℕ) (gs : List Gate) (i : ℕ) : Bool :=
  decide (i = h ∨ i = j ∨ (j < i ∧ n + j ∈ (gs.getD i ⟨GateOp.and, []⟩).inputs))

lemma S_bad (n h j : ℕ) (gs : List Gate) (hhj : h < j) (hj : j < gs.length)
    (hjn : gs[j].op = GateOp.not) (hlen : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (k : ℕ) (hk : k < gs.length) (hb : bad n h j gs k = true) :
    (S n h gs (k + 1)).2 = (S n h gs k).2 := by
  rw [S_succ n h gs k hk]
  unfold bad at hb
  simp only [decide_eq_true_eq] at hb
  unfold stp
  rcases hb with hb | hb | ⟨hb1, hb2⟩
  · subst hb
    simp only [lt_irrefl, ↓reduceIte]
  · have h1 : ¬ k < h := by omega
    have h2 : ¬ k = h := by omega
    have h3 : isNot gs[k].op = true := by subst hb; rw [hjn]; rfl
    simp only [h1, h2, h3, ↓reduceIte]
  · have h1 : ¬ k < h := by omega
    have h2 : ¬ k = h := by omega
    simp only [h1, h2, ↓reduceIte]
    split_ifs
    · rfl
    · rw [List.getD_eq_getElem _ _ hk] at hb2
      rw [gen_reader _ _ gs[k] (hlen _ (List.getElem_mem hk)) (n + j) hb2
        (S_j n h j gs hhj hj hjn k (by omega) hb1)]
      simp

lemma S_count (n h j : ℕ) (gs : List Gate) (hhj : h < j) (hj : j < gs.length)
    (hjn : gs[j].op = GateOp.not) (hlen : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    ∀ k, k ≤ gs.length →
      (S n h gs k).2.length + ((Finset.range k).filter (fun i => bad n h j gs i = true)).card ≤ k := by
  intro k
  induction k with
  | zero => intro _; simp [S]
  | succ k ih =>
    intro hk
    have hkl : k < gs.length := by omega
    have ih' := ih (by omega)
    rw [Finset.range_add_one, Finset.filter_insert]
    by_cases hb : bad n h j gs k = true
    · rw [S_bad n h j gs hhj hj hjn hlen k hkl hb]
      simp only [hb, ↓reduceIte]
      rw [Finset.card_insert_of_notMem (by simp)]
      omega
    · simp only [hb]
      rw [S_succ n h gs k hkl]
      obtain ⟨e, he, hel⟩ := stp_snd n h k gs[k] (S n h gs k)
      rw [he, List.length_append]
      have : (false = true) = False := by simp
      simp only [this, ↓reduceIte]
      omega

def Rp (W' : List Bool) (v : Bool) : Bool ⊕ ℕ → Prop
  | Sum.inl b => v = b
  | Sum.inr w => w < W'.length ∧ W'.getD w false = v

lemma Rp_mono (W' : List Bool) (e : List Gate) (v : Bool) (r : Bool ⊕ ℕ) (hr : Rp W' v r) :
    Rp (drun e W') v r := by
  rcases r with b | w
  · exact hr
  · exact ⟨by rw [drunlength]; exact Nat.lt_add_right _ hr.1, by rw [drungetD _ _ _ hr.1]; exact hr.2⟩

lemma ext (ρ : List (Bool ⊕ ℕ)) (W' : List Bool) (e : List Gate) (d : Bool ⊕ ℕ) (V : ℕ → Bool)
    (N : ℕ) (hlen : ρ.length = N)
    (ih : ∀ i, Rp W' (if i < N then V i else false) (ρ.getD i (Sum.inl false)))
    (hd : Rp (drun e W') (V N) d) (i : ℕ) :
    Rp (drun e W') (if i < N + 1 then V i else false) ((ρ ++ [d]).getD i (Sum.inl false)) := by
  rcases lt_trichotomy i N with hi | hi | hi
  · rw [List.getD_append _ _ _ _ (by omega)]
    have := Rp_mono W' e _ _ (ih i)
    have h1 : i < N + 1 := by omega
    simpa only [hi, h1, ↓reduceIte] using this
  · subst hi
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simpa [hlen] using hd
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    have h1 : ¬ i < N + 1 := by omega
    simp only [h1, ↓reduceIte]
    exact rfl

lemma gen_sem (ρ : List (Bool ⊕ ℕ)) (W' : List Bool) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (vals : ℕ → Bool)
    (hr : ∀ r ∈ g.inputs, Rp W' (vals r) (ρ.getD r (Sum.inl false))) :
    Rp (drun (gen ρ W'.length g).2 W') (g.op.eval (g.inputs.map vals)) (gen ρ W'.length g).1 := by
  rw [eval_ao g.op _ hop]
  unfold gen
  by_cases hin : Sum.inl (isOr g.op) ∈ g.inputs.map (fun r => ρ.getD r (Sum.inl false))
  · simp only [hin, ↓reduceIte]
    obtain ⟨r, hrm, hre⟩ := List.mem_map.mp hin
    have h1 := hr r hrm
    rw [hre] at h1
    have h2 : vals r = isOr g.op := h1
    have hmem : isOr g.op ∈ g.inputs.map vals := List.mem_map.mpr ⟨r, hrm, h2⟩
    simp only [hmem, ↓reduceIte]
    exact rfl
  · simp only [hin, ↓reduceIte]
    have key1 : ∀ w ∈ (g.inputs.map (fun r => ρ.getD r (Sum.inl false))).filterMap Sum.getRight?,
        w < W'.length ∧ ∃ r ∈ g.inputs, W'.getD w false = vals r := by
      intro w hw
      obtain ⟨c, hc, hcw⟩ := List.mem_filterMap.mp hw
      obtain ⟨r, hrm, hre⟩ := List.mem_map.mp hc
      have hc' : c = Sum.inr w := Sum.getRight?_eq_some_iff.mp hcw
      have h1 := hr r hrm
      rw [hre, hc'] at h1
      exact ⟨h1.1, r, hrm, h1.2⟩
    have key2 : isOr g.op ∈ g.inputs.map vals ↔ isOr g.op ∈
        ((g.inputs.map (fun r => ρ.getD r (Sum.inl false))).filterMap Sum.getRight?).map
          (fun w => W'.getD w false) := by
      constructor
      · intro hm
        obtain ⟨r, hrm, hre⟩ := List.mem_map.mp hm
        have h1 := hr r hrm
        rcases hc : ρ.getD r (Sum.inl false) with b | w
        · rw [hc] at h1
          have h2 : vals r = b := h1
          exact absurd (List.mem_map.mpr ⟨r, hrm, by rw [hc, ← h2, hre]⟩) hin
        · rw [hc] at h1
          refine List.mem_map.mpr ⟨w, List.mem_filterMap.mpr ⟨Sum.inr w, List.mem_map.mpr ⟨r, hrm, hc⟩, rfl⟩, ?_⟩
          rw [h1.2, hre]
      · intro hm
        obtain ⟨w, hw, hwe⟩ := List.mem_map.mp hm
        obtain ⟨_, r, hrm, hre⟩ := key1 w hw
        exact List.mem_map.mpr ⟨r, hrm, by rw [← hre, hwe]⟩
    simp only [key2]
    generalize (g.inputs.map (fun r => ρ.getD r (Sum.inl false))).filterMap Sum.getRight? = l at key1
    rcases l with _ | ⟨w, _ | ⟨w2, t⟩⟩
    · simp [fin3, Rp]
    · have hw := (key1 w (by simp)).1
      refine ⟨hw, ?_⟩
      change W'.getD w false = _
      simp only [List.map_cons, List.map_nil, List.mem_singleton]
      generalize W'.getD w false = c
      cases isOr g.op <;> cases c <;> simp
    · refine ⟨by simp [fin3, drun], ?_⟩
      simp only [fin3, drun, List.foldl_cons, List.foldl_nil]
      rw [List.getD_append_right _ _ _ _ (by omega)]
      simp only [Nat.sub_self, List.getD_cons_zero]
      exact eval_ao g.op _ hop

lemma sem (n h j : ℕ) (gs : List Gate) (x : Fin n → Bool)
    (hops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (huniq : ∀ i (hi : i < gs.length), gs[i].op = GateOp.not → i = j)
    (hh : dvalue ⟨gs, 0⟩ x (n + h) = true) (hjv : dvalue ⟨gs, 0⟩ x (n + j) = false) :
    ∀ k, k ≤ gs.length → ∀ i, Rp (drun (S n h gs k).2 (List.ofFn x))
      (if i < n + k then dvalue ⟨gs, 0⟩ x i else false)
      ((S n h gs k).1.getD i (Sum.inl false)) := by
  intro k
  induction k with
  | zero =>
    intro _ i
    change Rp (List.ofFn x) (if i < n + 0 then dvalue ⟨gs, 0⟩ x i else false)
      (((List.range n).map Sum.inr).getD i (Sum.inl false))
    by_cases hi : i < n
    · have e1 : ((List.range n).map (Sum.inr : ℕ → Bool ⊕ ℕ)).getD i (Sum.inl false) = Sum.inr i := by
        rw [List.getD_eq_getElem _ _ (by simpa using hi)]
        simp
      rw [e1]
      simp only [Nat.add_zero, hi, ↓reduceIte]
      refine ⟨by simpa using hi, ?_⟩
      exact (drungetD gs _ i (by simpa using hi)).symm
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      simp only [Nat.add_zero, hi, ↓reduceIte]
      exact rfl
  | succ k ih =>
    intro hk
    have hkl : k < gs.length := by omega
    have ih' := ih (by omega)
    have hl := S_len n h gs k (by omega)
    have hWl : (drun (S n h gs k).2 (List.ofFn x)).length = n + (S n h gs k).2.length := by
      rw [drunlength]; simp
    have hgv := dgatevalueP gs x k hkl
    rw [S_succ n h gs k hkl]
    unfold stp
    split_ifs with h1 h2 h3
    · simp only [drunappend, ← Nat.add_assoc]
      apply ext _ _ _ _ (fun i => dvalue ⟨gs, 0⟩ x i) (n + k) hl ih'
      obtain ⟨l1, l2⟩ := S_low n h gs k (by omega) (by omega)
      have hk2 : (S n h gs k).2.length = k := by rw [l1]; simp; omega
      refine ⟨by rw [drunlength, hWl]; simp, ?_⟩
      change ((drun (S n h gs k).2 (List.ofFn x)) ++ [_]).getD _ false = _
      rw [List.getD_append_right _ _ _ _ (by omega), hWl, Nat.sub_self, List.getD_cons_zero, hgv]
      congr 1
      apply List.map_congr_left
      intro r _
      by_cases hr : r < n + k
      · have h4 := ih' r
        have e1 : (S n h gs k).1.getD r (Sum.inl false) = Sum.inr r := by
          rw [l2, List.getD_eq_getElem _ _ (by simpa using hr)]
          simp
        rw [e1] at h4
        simp only [hr, ↓reduceIte] at h4 ⊢
        exact h4.2
      · simp only [hr, ↓reduceIte]
        exact List.getD_eq_default _ _ (by omega)
    · simp only [← Nat.add_assoc]
      have := ext _ _ [] (Sum.inl true) (fun i => dvalue ⟨gs, 0⟩ x i) (n + k) hl ih'
        (by subst h2; exact hh)
      exact this
    · simp only [← Nat.add_assoc]
      have hkj : k = j := by
        apply huniq k hkl
        rcases hops gs[k] (List.getElem_mem hkl) with ho | ho | ho
        · rw [ho] at h3; exact absurd h3 (by simp [isNot])
        · rw [ho] at h3; exact absurd h3 (by simp [isNot])
        · exact ho
      have := ext _ _ [] (Sum.inl false) (fun i => dvalue ⟨gs, 0⟩ x i) (n + k) hl ih'
        (by subst hkj; exact hjv)
      exact this
    · simp only [drunappend, ← Nat.add_assoc]
      apply ext _ _ _ _ (fun i => dvalue ⟨gs, 0⟩ x i) (n + k) hl ih'
      have hop : gs[k].op = GateOp.and ∨ gs[k].op = GateOp.or := by
        rcases hops gs[k] (List.getElem_mem hkl) with ho | ho | ho
        · exact Or.inl ho
        · exact Or.inr ho
        · rw [ho] at h3; exact absurd rfl h3
      change Rp _ (dvalue ⟨gs, 0⟩ x (n + k)) _
      rw [hgv, ← hWl]
      exact gen_sem _ _ gs[k] hop _ (fun r _ => ih' r)

lemma dmain : ∀ (n m : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ) (j h : Fin gates.length),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      g.inputs.length ≤ 2) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (n + (h : ℕ)) :: r) →
    (∀ w : Fin m, ∃ x y : Fin n → Bool,
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (h : ℕ)⟩ (List.ofFn x) = true ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (h : ℕ)⟩ (List.ofFn y) = true ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = true ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn y) = false) →
    ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (out' : Fin m → ℕ),
      (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates.take (h : ℕ) <+: gates' ∧
      gates'.length + (Finset.univ.filter (fun i : Fin gates.length => j < i ∧ n + (j : ℕ) ∈ (gates.get i).inputs)).card + 2
        ≤ gates.length ∧
      ∀ (w : Fin m) (x : Fin n → Bool),
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (h : ℕ)⟩ (List.ofFn x) = true →
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', out' w⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) := by
  intro n m gates out j h hops hj huniq hhj hin hsep
  have hjl : (j : ℕ) < gates.length := j.2
  have hhj' : (h : ℕ) < (j : ℕ) := hhj
  have hjn : gates[(j : ℕ)].op = GateOp.not := hj
  have huniq' : ∀ i (hi : i < gates.length), gates[i].op = GateOp.not → i = (j : ℕ) :=
    fun i hi ho => congrArg Fin.val (huniq ⟨i, hi⟩ ho)
  have hops1 : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not :=
    fun g hg => (hops g hg).1
  have hlen : ∀ g ∈ gates, g.inputs.length ≤ 2 := fun g hg => (hops g hg).2
  have hjv : ∀ x : Fin n → Bool, dvalue ⟨gates, 0⟩ x (n + (h : ℕ)) = true →
      dvalue ⟨gates, 0⟩ x (n + (j : ℕ)) = false := by
    intro x hx
    obtain ⟨r, hr⟩ := hin
    have hr' : gates[(j : ℕ)].inputs = (n + (h : ℕ)) :: r := hr
    rw [dgatevalueP gates x j hjl, hjn, hr']
    have : n + (h : ℕ) < n + (j : ℕ) := by omega
    simp [GateOp.eval, this, hx]
  have hsem := fun (x : Fin n → Bool) (hx : dvalue ⟨gates, 0⟩ x (n + (h : ℕ)) = true) =>
    sem n h j gates x hops1 huniq' hx (hjv x hx) gates.length le_rfl
  have hSl := S_len n h gates gates.length le_rfl
  refine ⟨(S n h gates gates.length).2,
    fun w => ((S n h gates gates.length).1.getD (out w) (Sum.inl false)).elim (fun _ => 0) id,
    S_ops n h j gates hhj' hops huniq' gates.length le_rfl,
    S_prefix n h gates gates.length le_rfl (by omega), ?_, ?_⟩
  · have hc := S_count n h j gates hhj' hjl hjn hlen gates.length le_rfl
    have hsub : insert (h : ℕ) (insert (j : ℕ)
        ((Finset.univ.filter (fun i : Fin gates.length =>
          j < i ∧ n + (j : ℕ) ∈ (gates.get i).inputs)).image (fun i : Fin gates.length => (i : ℕ)))) ⊆
        (Finset.range gates.length).filter (fun i => bad n h j gates i = true) := by
      intro i hi
      rw [Finset.mem_filter, Finset.mem_range]
      unfold bad
      simp only [decide_eq_true_eq]
      rcases Finset.mem_insert.mp hi with hi | hi
      · exact ⟨by omega, Or.inl hi⟩
      rcases Finset.mem_insert.mp hi with hi | hi
      · exact ⟨by omega, Or.inr (Or.inl hi)⟩
      obtain ⟨i', hi', rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨_, a, b⟩ := Finset.mem_filter.mp hi'
      refine ⟨i'.2, Or.inr (Or.inr ⟨a, ?_⟩)⟩
      rw [List.getD_eq_getElem _ _ i'.2]
      exact b
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_image_of_injective _ Fin.val_injective] at hcard
    · omega
    · intro hm
      obtain ⟨i', hi', he⟩ := Finset.mem_image.mp hm
      have := (Finset.mem_filter.mp hi').2.1
      have : (j : ℕ) < (i' : ℕ) := this
      omega
    · intro hm
      rcases Finset.mem_insert.mp hm with hm | hm
      · omega
      · obtain ⟨i', hi', he⟩ := Finset.mem_image.mp hm
        have := (Finset.mem_filter.mp hi').2.1
        have : (j : ℕ) < (i' : ℕ) := this
        omega
  · intro w x hx
    have hx' : dvalue ⟨gates, 0⟩ x (n + (h : ℕ)) = true := hx
    obtain ⟨x0, y0, hx0, hy0, ox, oy⟩ := hsep w
    have ox' : dvalue ⟨gates, 0⟩ x0 (out w) = true := ox
    have oy' : dvalue ⟨gates, 0⟩ y0 (out w) = false := oy
    have a1 := hsem x0 hx0 (out w)
    have a2 := hsem y0 hy0 (out w)
    have a3 := hsem x hx' (out w)
    change (drun (S n h gates gates.length).2 (List.ofFn x)).getD (Sum.elim (fun _ => 0) id ((S n h gates gates.length).1.getD (out w) (Sum.inl false))) false = dvalue ⟨gates, 0⟩ x (out w)
    rcases hc : (S n h gates gates.length).1.getD (out w) (Sum.inl false) with b | w'
    · rw [hc] at a1 a2
      exfalso
      by_cases hlt : out w < n + gates.length
      · simp only [hlt, ↓reduceIte] at a1 a2
        have e1 : dvalue ⟨gates, 0⟩ x0 (out w) = b := a1
        have e2 : dvalue ⟨gates, 0⟩ y0 (out w) = b := a2
        rw [ox'] at e1
        rw [oy'] at e2
        rw [← e1] at e2
        exact Bool.noConfusion e2
      · rw [dmissingvalue _ x0 (out w) (by change n + gates.length ≤ _; omega)] at ox'
        exact Bool.noConfusion ox'
    · rw [hc] at a3
      by_cases hlt : out w < n + gates.length
      · simp only [hlt, ↓reduceIte] at a3
        exact a3.2
      · simp only [hlt, ↓reduceIte] at a3
        rw [dmissingvalue _ x (out w) (by change n + gates.length ≤ _; omega)]
        exact a3.2

lemma glue (hdel : ∀ (n m : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ) (j h : Fin gates.length),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      g.inputs.length ≤ 2) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (n + (h : ℕ)) :: r) →
    (∀ w : Fin m, ∃ x y : Fin n → Bool,
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (h : ℕ)⟩ (List.ofFn x) = true ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (h : ℕ)⟩ (List.ofFn y) = true ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = true ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn y) = false) →
    ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (out' : Fin m → ℕ),
      (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates.take (h : ℕ) <+: gates' ∧
      gates'.length + (Finset.univ.filter (fun i : Fin gates.length => j < i ∧ n + (j : ℕ) ∈ (gates.get i).inputs)).card + 2
        ≤ gates.length ∧
      ∀ (w : Fin m) (x : Fin n → Bool),
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (h : ℕ)⟩ (List.ofFn x) = true →
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', out' w⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x)) :
    ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin 13 → ℕ) (j h : Fin gates.length),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      g.inputs.length ≤ 2) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (13 + (h : ℕ)) :: r) →
    (∀ (t : Fin 13) (x : Fin 13 → Bool),
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    (∀ t : Fin 13, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (h : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = true) →
    ∀ (Lam : Finset (Fin 13)) (B : Fin 13 → Fin 13 → Finset (Fin 13)),
    (∀ t ∈ Lam, ∀ p ∈ L t, B t p ∩ L t = ∅ ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (h : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ v ∈ B t p))) = true) →
    (∀ t ∈ Lam, ∀ t' ∈ Lam, t ≠ t' → ¬ ((∃ p ∈ L t \ L t', (B t p ∩ L t').Nonempty) ∧
      (∃ p ∈ L t' \ L t, (B t' p ∩ L t).Nonempty))) →
    ∀ I : Finset (Fin gates.length),
      (∀ g ∈ I, (gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        ∀ T : Finset (Fin gates.length), (∀ i g' : Fin gates.length, (i = h ∨ i ∈ T) →
          13 + (g' : ℕ) ∈ (gates.get i).inputs → g' < i → g' ∈ T) → g ∈ T) →
      (Finset.univ.filter (fun i : Fin gates.length => j < i ∧ 13 + (j : ℕ) ∈ (gates.get i).inputs)).card + 2 + 3 * Lam.card + max (13 - Lam.card) I.card ≤ gates.length := by
  intro L hL gates o j h hg hjop hone hhj hjin hout hco Lam B hB hno I hI
  classical
  have hLne : ∀ t t' : Fin 13, t ≠ t' → ∃ u ∈ L t, u ∉ L t' := by
    intro t t'
    rw [hL t, hL t']
    revert t t'
    decide
  have hsucc : ∀ t : Fin 13, t ≠ t + 1 := by decide
  obtain ⟨gates', out', hg', hpre, hlen, hagree⟩ := hdel 13 13 gates o j h hg hjop hone hhj hjin (by
    intro w
    refine ⟨fun v => decide (v ∉ L (w + 1)), fun v => decide (v ∉ L w), hco (w + 1), hco w, ?_, ?_⟩
    · rw [hout]
      obtain ⟨u, hu, hu'⟩ := hLne w (w + 1) (hsucc w)
      exact decide_eq_true ⟨u, hu, decide_eq_true hu'⟩
    · rw [hout]
      refine decide_eq_false ?_
      rintro ⟨v, hv, hh⟩
      exact (of_decide_eq_true hh) hv)
  let D : (Fin 13 → Bool) → Prop := fun x => Circuit.eval ⟨gates, 13 + (h : ℕ)⟩ (List.ofFn x) = true
  have hup : ∀ x y : Fin 13 → Bool, D x → (∀ v : Fin 13, x v = true → y v = true) → D y :=
    fun x y hx hxy => hmono gates j hg hone x y hxy (13 + (h : ℕ)) (by
      have : (h : ℕ) < (j : ℕ) := hhj
      omega) hx
  have hIlt : ∀ g ∈ I, (g : ℕ) < (h : ℕ) := by
    intro g hgI
    have h1 := (hI g hgI).2 (Finset.univ.filter fun i => i < h) (by
      intro i g' hi _ hlt
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rcases hi with rfl | hi
      · exact hlt
      · exact lt_trans hlt (Finset.mem_filter.mp hi).2)
    exact (Finset.mem_filter.mp h1).2
  obtain ⟨tl, htl⟩ := hpre
  have hget : ∀ (a : ℕ) (ha : a < gates.length) (ha' : a < gates'.length), a < (h : ℕ) →
      gates'[a] = gates[a] := by
    intro a ha ha' hah
    subst htl
    rw [List.getElem_append_left (by rw [List.length_take]; omega)]
    exact List.getElem_take
  have hhlen : (h : ℕ) ≤ gates'.length := by
    rw [← htl, List.length_append, List.length_take]
    have := h.isLt
    omega
  let I' : Finset (Fin gates'.length) := Finset.univ.filter fun g' => ∃ g ∈ I, (g : ℕ) = (g' : ℕ)
  have hI' : ∀ g' ∈ I', (gates'.get g').op = GateOp.and := by
    intro g' hgm
    obtain ⟨g, hgI, e⟩ := (Finset.mem_filter.mp hgm).2
    rcases g' with ⟨a, ha⟩
    simp only at e
    subst e
    change gates'[(g : ℕ)].op = _
    rw [hget g g.isLt ha (hIlt g hgI)]
    exact (hI g hgI).1
  have hcard : I.card ≤ I'.card := by
    have h1 : Finset.image (fun g : Fin gates.length => (g : ℕ)) I ⊆
        Finset.image (fun g : Fin gates'.length => (g : ℕ)) I' := by
      intro w hw
      obtain ⟨g, hgI, rfl⟩ := Finset.mem_image.mp hw
      have := hIlt g hgI
      exact Finset.mem_image.mpr ⟨⟨g, by omega⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, g, hgI, rfl⟩, rfl⟩
    have h2 := Finset.card_le_card h1
    rw [Finset.card_image_of_injective _ Fin.val_injective] at h2
    exact h2.trans Finset.card_image_le
  have key := main L hL D hup hco gates' out' hg'
    (fun t x hx => (hagree t x hx).trans (hout t x)) Lam B hB hno I' hI'
  have hmax : max (13 - Lam.card) I.card ≤ max (13 - Lam.card) I'.card := max_le_max le_rfl hcard
  linarith

lemma m17 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin 13 → ℕ) (j h : Fin gates.length),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      g.inputs.length ≤ 2) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (13 + (h : ℕ)) :: r) →
    (∀ (t : Fin 13) (x : Fin 13 → Bool),
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    (∀ t : Fin 13, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (h : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = true) →
    ∀ (Lam : Finset (Fin 13)) (B : Fin 13 → Fin 13 → Finset (Fin 13)),
    (∀ t ∈ Lam, ∀ p ∈ L t, B t p ∩ L t = ∅ ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (h : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ v ∈ B t p))) = true) →
    (∀ t ∈ Lam, ∀ t' ∈ Lam, t ≠ t' → ¬ ((∃ p ∈ L t \ L t', (B t p ∩ L t').Nonempty) ∧
      (∃ p ∈ L t' \ L t, (B t' p ∩ L t).Nonempty))) →
    ∀ I : Finset (Fin gates.length),
      (∀ g ∈ I, (gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        ∀ T : Finset (Fin gates.length), (∀ i g' : Fin gates.length, (i = h ∨ i ∈ T) →
          13 + (g' : ℕ) ∈ (gates.get i).inputs → g' < i → g' ∈ T) → g ∈ T) →
      (Finset.univ.filter (fun i : Fin gates.length => j < i ∧ 13 + (j : ℕ) ∈ (gates.get i).inputs)).card + 2 + 3 * Lam.card + max (13 - Lam.card) I.card ≤ gates.length := glue dmain

lemma m18 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin 13 → ℕ) (j h : Fin gates.length),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      g.inputs.length ≤ 2) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (13 + (h : ℕ)) :: r) →
    (∀ (t : Fin 13) (x : Fin 13 → Bool),
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    (∀ t : Fin 13, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (h : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = true) →
    ∀ (s t u v : Fin 13), t ∈ L s → u ∈ L s → v ∈ L s → t ≠ u → u ≠ v → t ≠ v →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (h : ℕ)⟩ (List.ofFn (fun y : Fin 13 => decide (y = t))) = true →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (h : ℕ)⟩ (List.ofFn (fun y : Fin 13 => decide (y = u))) = true →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (h : ℕ)⟩ (List.ofFn (fun y : Fin 13 => decide (y = v))) = true →
    ∀ I : Finset (Fin gates.length),
      (∀ g ∈ I, (gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        ∀ T : Finset (Fin gates.length), (∀ i g' : Fin gates.length, (i = h ∨ i ∈ T) →
          13 + (g' : ℕ) ∈ (gates.get i).inputs → g' < i → g' ∈ T) → g ∈ T) →
      38 + (Finset.univ.filter (fun i : Fin gates.length => j < i ∧ 13 + (j : ℕ) ∈ (gates.get i).inputs)).card + max 1 I.card ≤ gates.length := by
  intro L hL gates o j h hg hjop hone hhj hjin hout hco s t u v hts hus hvs htu huv htv ht hu hv I hI
  classical
  have hint : ∀ i j : Fin 13, i ≠ j → (L i ∩ L j).card ≤ 1 := by
    intro i j
    rw [hL i, hL j]
    revert i j
    decide
  have two : ∀ l a b : Fin 13, l ≠ s → a ∈ L s → b ∈ L s → a ≠ b → a ∈ L l → b ∉ L l := by
    intro l a b hl ha hb hab hal hbl
    exact hab (Finset.card_le_one.mp (hint l s hl) a (Finset.mem_inter.mpr ⟨hal, ha⟩) b
      (Finset.mem_inter.mpr ⟨hbl, hb⟩))
  let c : Fin 13 → Fin 13 := fun l => if t ∈ L l then u else if u ∈ L l then v else t
  have hcs : ∀ l : Fin 13, (t ∈ L l ∧ c l = u) ∨ (t ∉ L l ∧ u ∈ L l ∧ c l = v) ∨
      (t ∉ L l ∧ u ∉ L l ∧ c l = t) := by
    intro l
    by_cases h1 : t ∈ L l
    · exact Or.inl ⟨h1, by simp only [c, h1, ↓reduceIte]⟩
    · by_cases h2 : u ∈ L l
      · exact Or.inr (Or.inl ⟨h1, h2, by simp only [c, h1, h2, ↓reduceIte]⟩)
      · exact Or.inr (Or.inr ⟨h1, h2, by simp only [c, h1, h2, ↓reduceIte]⟩)
  have hc : ∀ l : Fin 13, l ≠ s → c l ∉ L l := by
    intro l hl
    rcases hcs l with ⟨h1, e⟩ | ⟨h1, h2, e⟩ | ⟨h1, h2, e⟩
    · rw [e]
      exact two l t u hl hts hus htu h1
    · rw [e]
      exact two l u v hl hus hvs huv h2
    · rw [e]
      exact h1
  have hct : ∀ l : Fin 13,
      Circuit.eval ⟨gates, 13 + (h : ℕ)⟩ (List.ofFn (fun y : Fin 13 => decide (y = c l))) = true := by
    intro l
    rcases hcs l with ⟨_, e⟩ | ⟨_, _, e⟩ | ⟨_, _, e⟩
    · rw [e]
      exact hu
    · rw [e]
      exact hv
    · rw [e]
      exact ht
  have hlt : 13 + (h : ℕ) < 13 + (j : ℕ) := by
    have : (h : ℕ) < (j : ℕ) := hhj
    omega
  let Lam : Finset (Fin 13) := Finset.univ.erase s
  let B : Fin 13 → Fin 13 → Finset (Fin 13) := fun l _ => {c l}
  have hB : ∀ l ∈ Lam, ∀ p ∈ L l, B l p ∩ L l = ∅ ∧
      Circuit.eval ⟨gates, 13 + (h : ℕ)⟩ (List.ofFn (fun y : Fin 13 => decide (y = p ∨ y ∈ B l p))) = true := by
    intro l hl p _
    refine ⟨Finset.singleton_inter_of_notMem (hc l (Finset.ne_of_mem_erase hl)), ?_⟩
    refine hmono gates j hg hone (fun y : Fin 13 => decide (y = c l)) _ (fun y hy => ?_) _ hlt (hct l)
    exact decide_eq_true (Or.inr (Finset.mem_singleton.mpr (of_decide_eq_true hy)))
  have hmem : ∀ l l' p : Fin 13, (B l p ∩ L l').Nonempty → c l ∈ L l' := by
    rintro l l' p ⟨z, hz⟩
    obtain ⟨hz1, hz2⟩ := Finset.mem_inter.mp hz
    rw [Finset.mem_singleton.mp hz1] at hz2
    exact hz2
  have hno : ∀ l ∈ Lam, ∀ l' ∈ Lam, l ≠ l' → ¬ ((∃ p ∈ L l \ L l', (B l p ∩ L l').Nonempty) ∧
      (∃ p ∈ L l' \ L l, (B l' p ∩ L l).Nonempty)) := by
    rintro l hl l' hl' _ ⟨⟨p, _, hn1⟩, ⟨p', _, hn2⟩⟩
    have a1 := hmem l l' p hn1
    have a2 := hmem l' l p' hn2
    have hls := Finset.ne_of_mem_erase hl
    have hls' := Finset.ne_of_mem_erase hl'
    rcases hcs l with ⟨h1, e⟩ | ⟨h1, h2, e⟩ | ⟨h1, h2, e⟩
    · rw [e] at a1
      rcases hcs l' with ⟨k1, e'⟩ | ⟨k1, k2, e'⟩ | ⟨k1, k2, e'⟩
      · exact two l' u t hls' hus hts (Ne.symm htu) a1 k1
      · rw [e'] at a2
        exact two l t v hls hts hvs htv h1 a2
      · exact k2 a1
    · rw [e] at a1
      rcases hcs l' with ⟨k1, e'⟩ | ⟨k1, k2, e'⟩ | ⟨k1, k2, e'⟩
      · exact two l' t v hls' hts hvs htv k1 a1
      · exact two l' u v hls' hus hvs huv k2 a1
      · rw [e'] at a2
        exact h1 a2
    · rw [e] at a1
      rcases hcs l' with ⟨k1, e'⟩ | ⟨k1, k2, e'⟩ | ⟨k1, k2, e'⟩
      · rw [e'] at a2
        exact h2 a2
      · exact k1 a1
      · exact k1 a1
  have key := m17 L hL gates o j h hg hjop hone hhj hjin hout hco Lam B hB hno I hI
  have e : Lam.card = 12 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ s), Finset.card_univ, Fintype.card_fin]
  rw [e] at key
  have e2 : (13 - 12 : ℕ) = 1 := rfl
  rw [e2] at key
  linarith

end PEqualNP.Outside.L_meta_1518

theorem PEqualNP.Outside.L_meta_1518 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin 13 → ℕ) (j h : Fin gates.length),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      g.inputs.length ≤ 2) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (13 + (h : ℕ)) :: r) →
    (∀ (t : Fin 13) (x : Fin 13 → Bool),
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    (∀ t : Fin 13, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (h : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = true) →
    ∀ (s t u v : Fin 13), t ∈ L s → u ∈ L s → v ∈ L s → t ≠ u → u ≠ v → t ≠ v →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (h : ℕ)⟩ (List.ofFn (fun y : Fin 13 => decide (y = t))) = true →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (h : ℕ)⟩ (List.ofFn (fun y : Fin 13 => decide (y = u))) = true →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (h : ℕ)⟩ (List.ofFn (fun y : Fin 13 => decide (y = v))) = true →
    ∀ I : Finset (Fin gates.length),
      (∀ g ∈ I, (gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        ∀ T : Finset (Fin gates.length), (∀ i g' : Fin gates.length, (i = h ∨ i ∈ T) →
          13 + (g' : ℕ) ∈ (gates.get i).inputs → g' < i → g' ∈ T) → g ∈ T) →
      38 + (Finset.univ.filter (fun i : Fin gates.length => j < i ∧ 13 + (j : ℕ) ∈ (gates.get i).inputs)).card + max 1 I.card ≤ gates.length :=
  PEqualNP.Outside.L_meta_1518.m18
