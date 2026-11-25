import constant_sweep

namespace PEqualNP.Outside.L_meta_1886_aux.ConstantSweepMono

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2592_aux.ConstantSweep

def monoGood (g : Gate) : Prop := (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2

lemma monoGood_good {g : Gate} (h : monoGood g) : good g := by
  refine ⟨?_,h.2⟩
  rcases h.1 with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

lemma emit_mono (op : GateOp) (n : ℕ) (rs : List Ref) (hop : op = .and ∨ op = .or) :
    ∀ g ∈ (emit op n rs).2, monoGood g := by
  rcases rs with _ | ⟨a, _ | ⟨b, rs⟩⟩
  · rcases hop with rfl | rfl <;> simp [emit]
  · rcases hop with rfl | rfl <;> simp [emit]
  · rcases hop with rfl | rfl <;> rcases a with (a | a) <;> rcases b with (b | b) <;>
      simp [emit,binary,monoGood]

lemma sweep (marks : Finset ℕ) (gs : List Gate) (hg : ∀ g ∈ gs, monoGood g)
    (refs : List Ref) (n : ℕ)
    (within : ∀ i ∈ marks, i < refs.length)
    (constants : ∀ i ∈ marks, ∃ b : Bool, read refs i = .inl b) :
    ∃ (out : List Gate) (extraRefs : List Ref),
      (∀ g ∈ out, monoGood g) ∧ extraRefs.length = gs.length ∧
      out.length + (gs.filter (touched marks)).length ≤ gs.length ∧
      ∀ w old, w.length = n → related refs w old →
        related (refs ++ extraRefs) (run out w) (run gs old) := by
  induction gs generalizing refs n with
  | nil =>
    refine ⟨[],[],by simp,by simp,by simp,?_⟩
    intro w old hw hr
    simpa [run] using hr
  | cons g gs ih =>
    have hg' := hg g (by simp)
    have legal := monoGood_good hg'
    let rs := g.inputs.map (read refs)
    let e := emit g.op n rs
    have he : e.2.length ≤ 1 ∧ (∀ g ∈ e.2, good g) ∧
        (∀ b : Bool, Sum.inl b ∈ rs.take (width g.op) → e.2 = []) ∧
        ∀ w : List Bool, w.length = n → (∀ r ∈ rs, valid n r) →
          valid (run e.2 w).length e.1 ∧
            value (run e.2 w) e.1 = g.op.eval (rs.map (value w)) :=
      emit_ok _ _ _ (by simpa [Set.mem_insert_iff] using legal.1)
        (by simpa [rs] using legal.2)
    have em : ∀ q ∈ e.2, monoGood q := emit_mono _ _ _ hg'.1
    let nextRefs := refs ++ [e.1]
    obtain ⟨tail,extras,htail,hlen,hsize,hcorrect⟩ :=
      ih (fun q hq => hg q (by simp [hq])) nextRefs (n + e.2.length)
        (fun i hi => by have bound := within i hi; simp [nextRefs]; omega)
        (fun i hi => by
          obtain ⟨b,hb⟩ := constants i hi
          exact ⟨b,(List.getD_append _ _ _ _ (within i hi)).trans hb⟩)
    refine ⟨e.2 ++ tail,e.1 :: extras,?_,?_,?_,?_⟩
    · intro q hq
      exact (List.mem_append.mp hq).elim (em q) (htail q)
    · simpa only [List.length_cons] using congrArg Nat.succ hlen
    · have hone := he.1
      cases hc : touched marks g
      · simp only [List.length_append,List.filter_cons,hc,Bool.false_eq_true,ite_false,List.length_cons]
        omega
      · obtain ⟨i,hi,hmark⟩ := List.any_eq_true.mp hc
        have hiMark : i ∈ marks := of_decide_eq_true hmark
        obtain ⟨b,hb⟩ := constants i hiMark
        have hf : Sum.inl b ∈ rs.take (width g.op) := by
          dsimp only [rs]
          rw [← List.map_take,List.mem_map]
          exact ⟨i,hi,hb⟩
        have hz := he.2.2.1 b hf
        simp [hz,hc]
        omega
    · intro w old hw hr
      have hv : ∀ r ∈ rs, valid n r := by
        intro r hr'
        obtain ⟨i,_,rfl⟩ := List.mem_map.mp hr'
        rw [← hw]
        exact read_valid hr i
      obtain ⟨hv',he'⟩ := he.2.2.2 w hw hv
      have hm : rs.map (value w) = g.inputs.map (fun i => old.getD i false) := by
        dsimp only [rs]
        rw [List.map_map]
        exact List.map_congr_left (fun i _ => read_value hr i)
      rw [hm] at he'
      rw [run_append]
      change related (refs ++ e.1 :: extras) (run tail (run e.2 w)) (run gs (step old g))
      have hc := hcorrect _ _ (by rw [run_length,hw]) (related_extend hr _ _ _ hv' he')
      simpa only [nextRefs,List.append_assoc,List.singleton_append,
        PEqualNP.Outside.L_meta_2592_aux.ConstantSweep.step] using hc

end PEqualNP.Outside.L_meta_1886_aux.ConstantSweepMono
