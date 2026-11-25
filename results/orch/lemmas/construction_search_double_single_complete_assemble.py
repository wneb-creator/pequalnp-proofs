from pathlib import Path
job=Path('/tmp/oec/pequalnp-pilot-79');repo=Path('/workspace/pequalnp-proofs');inputs=[repo/'results/orch/lemmas/TwoDoubleKernel.lean',job/'DoubleSingleMatrixFull.lean'];imports=['import Mathlib.LinearAlgebra.LinearIndependent.Basic'];bodies=[]
for p in inputs:
 lines=p.read_text().splitlines();imports.extend(line for line in lines if line.startswith('import ') and line not in imports);bodies.append('\n'.join(line for line in lines if not line.startswith('import ')))
s=(job/'DoubleSingleGeometric.lean').read_text();ns='PEqualNP.Outside.L_gct_231_aux.DoubleSingleGeometry';s=s[s.index('namespace '+ns):];end='end '+ns+'\n';assert s.endswith(end);s=s[:-len(end)]+((job/'double_single_model_cases.lean.txt').read_text()+'\n' if 'lemma model_impossible_from_scaled' not in s else '')+(job/'double_single_actual_corollary.lean.txt').read_text()+'\n'+end
out=job/'DoubleSingleComplete.lean';out.write_text('\n'.join(imports)+'\n\n'+'\n\n'.join(bodies)+'\n\n'+s);print(out.stat().st_size)
