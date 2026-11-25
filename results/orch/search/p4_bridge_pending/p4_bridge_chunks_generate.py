from pathlib import Path
import json,re
root=Path('/tmp/oec/pequalnp-pilot-64')
text=(root/'ReductionsBridge.lean').read_text()
d=json.loads((root/'p4-bridge-trace.json').read_text())
blocks=re.split(r'(?=  have hc[0-9]+ : ClauseSat)',text)
head=text.split('theorem encodedImpossible')[0]
proofs=[]
for s in blocks[1:]:
    s=s.split('  apply cnfUnsat')[0]
    proofs.append(s.rstrip())
assert len(proofs)==2537
out=[head]
chunks=[]
for k,start in enumerate(range(0,len(proofs),100)):
    stop=min(start+100,len(proofs));chunks.append(k)
    enc=[[2*abs(x)+(x<0) for x in cl] for cl in d['clauses'][start:stop]]
    out+=['def chunk'+str(k)+' : List (List Nat) := '+repr(enc),
          'theorem satChunk'+str(k)+' (c : Candidate) (hv : valid c)',
          '    (hr : ∀ r : Fin 16, output c r = target r)',
          '    (hl : derivativeLeft c = false) (hd : derivativeRight c = false) :',
          '    ∀ cl ∈ chunk'+str(k)+', ClauseSat (assignment c) cl := by',
          '  rcases hv with ⟨h0, h1, h2, h3, h4⟩']
    out+=proofs[start:stop]
    out+=['  simp only [chunk'+str(k)+', List.forall_mem_cons, List.forall_mem_nil]',
          '  exact ⟨'+', '.join('hc'+str(i) for i in range(start,stop))+', trivial⟩','#check satChunk'+str(k),'']
out+=['theorem encodedImpossibleChunks (c : Candidate) (hv : valid c)',
      '    (hr : ∀ r : Fin 16, output c r = target r)',
      '    (hl : derivativeLeft c = false) (hd : derivativeRight c = false) : False := by',
      '  apply cnfUnsat',
      '  refine ⟨assignment c, ?_⟩',
      '  change ∀ cl ∈ '+ ' ++ '.join('chunk'+str(k) for k in chunks)+' ++ [], ClauseSat (assignment c) cl',
      '  simp only [List.mem_append, or_imp, forall_and, List.forall_mem_nil]',
      '  exact ⟨'+', '.join('satChunk'+str(k)+' c hv hr hl hd' for k in chunks)+', trivial⟩','',
      'end PEqualNP.Outside.Pilot64Bridge','']
(root/'ReductionsBridgeChunks.lean').write_text('\n'.join(out))
print({'clauses':len(proofs),'chunks':len(chunks),'bytes':(root/'ReductionsBridgeChunks.lean').stat().st_size})
