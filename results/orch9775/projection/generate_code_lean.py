from pathlib import Path
import json
out=['import CompactFramework','','namespace PEqualNP.Outside.L_meta_9775.UpstreamCore','open DagTools']
for I in[111,4757,2213]:
 d=json.loads(Path(f'results/orch9775/projection/code-{I}-minimal.json').read_text());k=d['k'];rs=d['relations'];vs=d['variables'];n=I.bit_count()
 out += ['','set_option maxHeartbeats 0 in','set_option maxRecDepth 100000 in','set_option synthInstance.maxSize 8192 in',f'theorem residual_exclude{I} {{D : Dag}} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)',f'    (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask {I}=ineligSet 14 D) : False := by','  classical','  obtain ⟨b,hb⟩ := sem_exists_pureBranch graph_ok h.1 hc','  have card := card_residual h.1 b hb','  have el := inelig_card_add 14 D','  rw [←eq] at el',f'  have count : (mask {I}).card={n} := by decide +kernel',f'  have res : Fintype.card ↥(residualUnits 14 D b)={k} := by rw [Fintype.card_coe]; omega','  let f := (Fintype.equivFinOfCardEq res).symm']
 mem=lambda i:f'(eq ▸ (by decide +kernel : ({i}:V)∈mask {I}))'
 for idx,r in enumerate(rs):
  x,c=r['x'],r['c'];w=r['witness'];kind=w[0]
  if kind=='two':
   _,P,i,j,xx,cc,y=w;assert(x,c)==(xx,cc)
   out.append(f'  have miss{idx} := two_exact h hc z (mask {P}) (by decide +kernel) {i} {j} {x} {c} {y} {mem(i)} {mem(j)} (by decide +kernel)')
  else:
   _,P,A,i,xx,cc,y=w;assert(x,c)==(xx,cc)
   out.append(f'  have miss{idx} := exposed_exact h hc z (mask {P}) (mask {A}) (by decide +kernel) (by decide +kernel) {i} {x} {c} {mem(i)} (by decide +kernel)')
  elig=f'(by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : ({x}:V)∉mask {I}) hin : ({x}:V)∈eligSet 14 D)'
  line=f'  have h{idx} := '+('code_diff'if r['strict']else'code_excludes')+f' h hc b hb f {x} {c} (by decide +kernel) {elig} miss{idx}'
  if r['strict']:
   i=r['common_center'];line+=f' (share h hc (i:={i}) (x:={x}) (y:={c}) {mem(i)} (by decide +kernel) (by decide +kernel))'
  out.append(line)
 prop=lambda r:f'¬ a{r["x"]}⊆a{r["c"]}'if r['strict']else f'a{r["x"]}=∅ ∨ ¬ a{r["x"]}⊆a{r["c"]}'
 out.append('  have impossible : ∀ '+' '.join('a'+str(v)for v in vs)+f' : Finset (Fin {k}), '+''.join('('+prop(r)+') → 'for r in rs)+'False := by decide +kernel')
 out.append('  exact impossible '+' '.join(f'(code f {v})'for v in vs)+' '+' '.join(f'h{i}'for i in range(len(rs))))
out+=['','end PEqualNP.Outside.L_meta_9775.UpstreamCore'];Path('results/orch9775/lemmas/ResidualCodeExclusions.lean').write_text('\n'.join(out)+'\n')
