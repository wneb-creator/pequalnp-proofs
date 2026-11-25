import ast
import hashlib
import json
from pathlib import Path
import re

root=Path('/workspace/pequalnp-proofs')
scratch=Path('/tmp/oec/pequalnp-pilot-62')
control_path=root/'results/orch/checked/canonical-global-control.lean'
sample_path=root/'results/orch/checked/canonical-sample-data.lean'
control=control_path.read_text()
sample=sample_path.read_text()
witness=json.loads((scratch/'theta4-control-global51-compact.json').read_text())
masks=json.loads((scratch/'theta4-control-global51-masks.json').read_text())
program=re.search(r'def globalControl : Program 26 51 :=\s*(.*?)\n\nend',control,re.S).group(1)
lists=re.findall(r'\[([^\]]*)\]',program)
actual=[[int(v) for v in re.findall(r'⟨(\d+), by decide⟩',block)] for block in lists]
expected=[side for operation in witness['operand_wire_lists'] for side in operation]+[witness['output_wire_list']]
assert actual==expected and len(actual)==103
remainder=re.sub(r'⟨\d+, by decide⟩','',program)
assert not re.sub(r'[\[\](),\s]','',remainder)
cert=ast.literal_eval(re.search(r'def globalControlCertificates : List Nat :=\s*(\[[^\]]*\])',control,re.S).group(1))
assert cert==masks['or_masks'] and len(cert)==51
result=int(re.search(r'def globalControlResult : Nat := (\d+)',control).group(1))
assert result==masks['output_mask']==2**52-1
input_masks=ast.literal_eval(re.search(r'\(\s*(\[[^\]]*\])\s*: List Nat\)',sample,re.S).group(1))
assert input_masks==masks['input_masks'] and len(input_masks)==26
assert 'def sampleTruthMask : Nat := 2^520 - 1' in sample
assert 'def positiveResultMask : Nat := 2^52 - 1' in sample
report={'verdict':'data_match','program_operation_count':51,'program_reference_lists':103,
        'input_masks_checked':26,'or_output_masks_checked':51,'final_mask':result,
        'sample_count':520,'scope':'Data equality only; no new Lean theorem and no counterexample',
        'source_sha256':{str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [control_path,sample_path]}}
bench_path=root/'results/orch/checked/canonical-sample-facts-bench.lean'
bench=bench_path.read_text()
assert '∀ a : Fin 52, ∀ i : Fin 26' in bench
assert '(sampleInputMasks 0).testBit (52 + 13 * r.1.val + r.2.val) = AllRows.row r 0' in bench
report['sample_bit_benchmark']={'sha256':hashlib.sha256(bench_path.read_bytes()).hexdigest(),
    'positive_coordinates':52*26,'negative_coordinates_checked':468,
    'negative_coordinate':'0 only','other_negative_coordinates_pending':25*468}
out=root/'results/orch/search-counterexample/compiler-control-data-audit.json'
out.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
