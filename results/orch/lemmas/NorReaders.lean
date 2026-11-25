import ReaderRename
import NorCompression
import CleanReader
import TwoNotSwap

namespace PEqualNP.Outside.L_meta_2592.NorReaders
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity ReaderDeletion NorCompression

lemma countP_unique {α : Type} (p : α → Bool) (xs : List α)
    (hc : xs.countP p ≤ 1) (a b : α) (ha : a ∈ xs) (hb : b ∈ xs)
    (pa : p a = true) (pb : p b = true) : a = b := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    simp only [List.mem_cons] at ha hb
    by_cases hp : p x = true
    · have hz : xs.countP p = 0 := by
        simp only [List.countP_cons,hp,ite_true] at hc
        omega
      have absent : ∀ t ∈ xs, p t ≠ true := by
        intro t ht hpt
        have hpos : 0 < xs.countP p := List.countP_pos_iff.mpr ⟨t,ht,hpt⟩
        omega
      rcases ha with rfl | ha
      · rcases hb with rfl | hb
        · rfl
        · exact False.elim (absent b hb pb)
      · exact False.elim (absent a ha pa)
    · have hx : p x = false := Bool.eq_false_iff.mpr hp
      have hc' : xs.countP p ≤ 1 := by simpa [List.countP_cons,hx] using hc
      rcases ha with rfl | ha
      · exact False.elim (hp pa)
      rcases hb with rfl | hb
      · exact False.elim (hp pb)
      exact ih hc' ha hb

lemma no_negative_reader {i n : Nat} {gs : List Gate}
    (hc : gs.countP (fun g => g.inputs.contains i || g.inputs.contains n) ≤ 1)
    (clean : ∃ g ∈ gs, i ∈ g.inputs ∧ n ∉ g.inputs) :
    ∀ g ∈ gs, n ∉ g.inputs := by
  obtain ⟨a,ha,hpos,hneg⟩ := clean
  intro b hb hbad
  have pa : (a.inputs.contains i || a.inputs.contains n) = true := by simp [hpos]
  have pb : (b.inputs.contains i || b.inputs.contains n) = true := by simp [hbad]
  have eq := countP_unique (fun g : Gate => g.inputs.contains i || g.inputs.contains n)
    gs hc a b ha hb pa pb
  exact hneg (eq.symm ▸ hbad)

lemma first_count (h15 : ¬ HasCircuitSize 9 p9 15)
    (i j : Fin 10) (hij : i ≠ j) (gs : List Gate) (out : Nat)
    (hf : FanInTwo (old i j gs out)) (hs : (old i j gs out).size ≤ 19)
    (hc : ∀ x : Fin 10 → Bool, (old i j gs out).eval (List.ofFn x) = p10 x)
    (mono : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) :
    gs.countP (fun g => g.inputs.contains i.val || g.inputs.contains 10) ≤ 1 := by
  have hb := first_not_readers_le_two_any h15 i
    (⟨.not,[j.val]⟩ :: ⟨.and,[10,11]⟩ :: gs) out hf hs hc
  have hijval : i.val ≠ j.val := fun h => hij (Fin.ext h)
  have hj10 : 10 ≠ j.val := by have := j.isLt;omega
  have hi10 : i.val ≠ 10 := by have := i.isLt;omega
  have hi11 : i.val ≠ 11 := by have := i.isLt;omega
  simp only [List.countP_cons,readsLiteral] at hb
  simp [hijval,hj10,hi10,hi11] at hb
  have eq : gs.countP (readsLiteral i) =
      gs.countP (fun g => g.inputs.contains i.val || g.inputs.contains 10) := by
    apply List.countP_congr
    intro g hg
    rcases mono g hg with h | h <;> simp [readsLiteral,h]

  rw [eq] at hb
  omega

lemma old_eval_seed (i j : Fin 10) (gs : List Gate) (out : Nat) (x : Fin 10 → Bool) :
    (old i j gs out).eval (List.ofFn x) =
      (CleanReader.wf gs (CleanReader.seed i j x)).getD out false := by
  change ((([⟨.not,[i.val]⟩,⟨.not,[j.val]⟩,⟨.and,[10,11]⟩] : List Gate) ++ gs).foldl
    NorCompression.step (List.ofFn x)).getD out false = _
  rw [List.foldl_append,old_prefix]
  rfl

lemma clean_readers (i j : Fin 10) (hij : i ≠ j) (gs : List Gate) (out : Nat)
    (hf : FanInTwo (old i j gs out))
    (hc : ∀ x : Fin 10 → Bool, (old i j gs out).eval (List.ofFn x) = p10 x)
    (mono : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) :
    (∃ g ∈ gs, i.val ∈ g.inputs ∧ 10 ∉ g.inputs) ∧
    (∃ g ∈ gs, j.val ∈ g.inputs ∧ 11 ∉ g.inputs) := by
  have hl : ∀ g ∈ gs, g.inputs.length ≤ 2 := fun g hg => (hf g (by simp [old,hg])).2
  have comp : ∀ x : Fin 10 → Bool,
      (CleanReader.wf gs (CleanReader.seed i j x)).getD out false = CleanReader.pet x := by
    intro x
    rw [← old_eval_seed]
    exact hc x
  exact ⟨CleanReader.clean_reader i j hij false gs out mono hl comp,
    CleanReader.clean_reader i j hij true gs out mono hl comp⟩

lemma unused_negative (h15 : ¬ HasCircuitSize 9 p9 15)
    (i j : Fin 10) (hij : i ≠ j) (gs : List Gate) (out : Nat)
    (hf : FanInTwo (old i j gs out)) (hs : (old i j gs out).size ≤ 19)
    (hc : ∀ x : Fin 10 → Bool, (old i j gs out).eval (List.ofFn x) = p10 x)
    (mono : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) :
    ∀ g ∈ gs, ∀ t ∈ g.inputs, t ≠ 10 ∧ t ≠ 11 := by
  obtain ⟨hci,hcj⟩ := clean_readers i j hij gs out hf hc mono
  have hfirst := first_count h15 i j hij gs out hf hs hc mono
  have hsecond := TwoNotSwap.second_count_binary h15 i j gs out hf hs hc
    (fun g hg => by rcases mono g hg with h | h <;> simp [h])
  have hn10 := no_negative_reader hfirst hci
  have hn11 := no_negative_reader hsecond hcj
  intro g hg t ht
  constructor
  · intro he
    exact hn10 g hg (he ▸ ht)
  · intro he
    exact hn11 g hg (he ▸ ht)

lemma output_not_negative (i j : Fin 10) (gs : List Gate) (out : Nat)
    (hc : ∀ x : Fin 10 → Bool, (old i j gs out).eval (List.ofFn x) = p10 x) :
    out ≠ 10 ∧ out ≠ 11 := by
  have h := hc (fun _ => false)
  rw [old_eval_seed] at h
  constructor <;> intro he <;> rw [he,CleanReader.wf_initial _ _ _ (by simp [CleanReader.seed])] at h
  all_goals simp [CleanReader.seed,p10,List.getD_eq_getElem?_getD] at h

lemma old_notCount (i j : Fin 10) (gs : List Gate) (out : Nat)
    (mono : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) :
    PEqualNP.NotBracket.notCount (old i j gs out) = 2 := by
  simp [PEqualNP.NotBracket.notCount,old]
  intro g hg
  rcases mono g hg with h | h <;> simp [h]

lemma compressed_one_not (h15 : ¬ HasCircuitSize 9 p9 15)
    (i j : Fin 10) (hij : i ≠ j) (gs : List Gate) (out : Nat)
    (hf : FanInTwo (old i j gs out)) (hs : (old i j gs out).size ≤ 19)
    (hc : ∀ x : Fin 10 → Bool, (old i j gs out).eval (List.ofFn x) = p10 x)
    (mono : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) :
    ∃ D : Circuit, FanInTwo D ∧ D.size ≤ 18 ∧ PEqualNP.NotBracket.notCount D = 1 ∧
      (∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = p10 x) := by
  obtain ⟨hout10,hout11⟩ := output_not_negative i j gs out hc
  have unused := unused_negative h15 i j hij gs out hf hs hc mono
  refine ⟨new i j gs out,NorCompression.fanInTwo i j gs out hf,?_,?_,?_⟩
  · have := size_equal i j gs out
    omega
  · have h := notCount_equal i j gs out
    rw [old_notCount i j gs out mono] at h
    omega
  · intro x
    rw [eval_equal i j gs out unused hout10 hout11]
    exact hc x

end PEqualNP.Outside.L_meta_2592.NorReaders
