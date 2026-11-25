namespace PEqualNP.Outside.L_meta_6659_aux

lemma empty_opposite_rejects_other_nonedge {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (budget : totalSurplus 14 D ≤ (eligSet 14 D).card)
    (twoW : ∀ x, (sem_W 14 D x).card ≤ 2)
    (andEmpty : ∀ j, j < D.length → tag D j = true → supp 14 D (14+j) = ∅)
    (x : Fin 14) (e : Nat × Bool) (he : e ∈ sem_W 14 D x)
    (empty : supp 14 D (src D (sem_bar e)) = ∅) :
    ∃ f, f ≠ e ∧ sem_W 14 D x = {e,f} ∧
      ∀ u v : Fin 14, ¬ Adj u v →
        val D (sem_ind ({u,v} : Finset (Fin 14))) (14+f.1) = true →
        val D (sem_ind ({u,v} : Finset (Fin 14))) (14+e.1) = false := by
  classical
  have ev := (sem_mem_W.mp he).1
  obtain ⟨f,different,code,neighbors⟩ := empty_opposite_other_exit h hD twoW e ev
    (andEmpty e.1 ev (sem_W_and h.1 he)) empty (sem_mem_W.mp he).2.1
  refine ⟨f,different,code,?_⟩
  intro u v nonedge signal
  have hf : f ∈ sem_W 14 D x := by rw [code]; simp
  have fv := (sem_mem_W.mp hf).1
  have fEmpty := andEmpty f.1 fv (sem_W_and h.1 hf)
  obtain ⟨j,s,hj,chain,value,hand,_,last⟩ :=
    fano_nonedge_first_filter h hD budget u v nonedge (14+f.1) fEmpty signal
  have upper := fano_nonedge_true_cone_unbranched h.1 hD budget u v nonedge
    (14+f.1) fEmpty signal (src D (j,s))
    (sem_rtg_mono (fun _ _ step => step.1) chain) value
  have one : fanout D (src D (j,s)) = 1 :=
    Nat.le_antisymm upper (sem_step_fanout (sem_step_src (n := 14) hj s))
  have same := and_on_fullstar_chain_is_other h hD twoW andEmpty x e f he empty
    code neighbors j s hj hand chain one
  simpa only [same] using last

end PEqualNP.Outside.L_meta_6659_aux
