from pathlib import Path
import hashlib
import json
import re

base = Path('/tmp/oec/pequalnp-pilot-178')
ns = 'namespace PEqualNP.Outside.L_meta_10760'
end = 'end PEqualNP.Outside.L_meta_10760'
manifest = []

def read(name):
    path = base / name
    text = path.read_text()
    manifest.append({'path': str(path), 'sha256': hashlib.sha256(text.encode()).hexdigest()})
    return text

def body(name):
    text = read(name)
    assert text.count(ns) == 1
    assert text.rstrip().endswith(end)
    return text.split(ns, 1)[1].rsplit(end, 1)[0]

lower = read('certificate_search/Lower13.lean')
lower = re.sub(r'^(?:lemma|theorem) ((?:k4_0|k3_0|k2_0|k1_0|h0_0|p0)\b)', r'def \1', lower, flags=re.M)
init_source = body('proof-route-normalized-init.lean').split('\nexample', 1)[0]
init_lines = init_source.splitlines()
init = '\n'.join(line for line in init_lines if re.match(r'^def init(?:L|M|G|W\d)\b', line)) + '\n'
for label in ['initL_eq', 'initM_eq', 'initG_eq']:
    line = next(line for line in init_lines if line.startswith('lemma ' + label + ' '))
    init += '\nset_option maxRecDepth 100000 in\nset_option maxHeartbeats 0 in\n' + line + '\n'
early_names = [
    'lrat_route/RootCut.leanfrag', 'lrat_route/PatchCut.leanfrag',
    'lrat_route/LookCut.leanfrag', 'lrat_route/BucketCut.leanfrag',
    'certificate_search/StrictNormalize.leanfrag', 'finite_search/CertificateDataChunked.leanfrag',
    'proof_route/LowerZeroSharedData.leanfrag', 'proof_route/LowerZeroSharedChecks.leanfrag',
    'proof_route/LowerZeroBucketCoverage.leanfrag', 'proof_route/LowerZeroBucketRoot.leanfrag',
    'proof_route/Lower13Split.leanfrag',
]
early = init + '\n' + '\n'.join(read(name) for name in early_names)
early = re.sub(r'^def ', 'noncomputable def ', early, flags=re.M)
needle = 'set_option maxRecDepth 100000 in\nset_option maxHeartbeats 0 in\ndef h0_0 :'
assert lower.count(needle) == 1
lower = lower.replace(needle, early + '\n' + needle)
old = 'def h0_0 : m0_0.all (okS ac4 0 12) = true := by decide +kernel'
assert lower.count(old) == 1
lower = lower.replace(old, 'def h0_0 : m0_0.all (okS ac4 0 12) = true := lower13Split')
assert lower.rstrip().endswith(end)
text = lower.rstrip()[:-len(end)]
text += body('root_helpers/Upper14.lean')
text += '\n' + read('gate_elimination/Tracked.lean')
count = read('root_helpers/NotCount.lean')
text += '\nlemma unique_not_count' + count.split('lemma unique_not_count', 1)[1].rsplit(end, 1)[0]
generic = read('certificate_search/OneNotBoundStep.lean').split('set_option maxRecDepth 100000 in', 1)[0]
text += '\nset_option maxRecDepth 100000 in\nset_option maxHeartbeats 0 in\n' + generic
endpoint = read('lrat_route/CheckedEndpoint.leanfrag')
endpoint_pre, endpoint_post = endpoint.split('\nlemma oneNotChecked', 1)
prelane_names = [
    'root_helpers/IndexMask.leanfrag', 'certificate_search/IndexedUnaryFinal.leanfrag',
    'certificate_search/BinaryFinalPrefix.leanfrag', 'lrat_route/BucketRows.leanfrag',
    'lrat_route/BucketCoverage.leanfrag',
]
late = '\n'.join(read(name) for name in prelane_names)
late += '\n' + endpoint_pre
late += '\n' + read('certificate_search/BinaryFinalLanes.leanfrag')
late += '\n' + read('certificate_search/BinaryFinalAssemble.leanfrag')
late += '\n' + read('lrat_route/BucketAssemble.leanfrag')
late += '\nlemma oneNotChecked' + endpoint_post
late = re.sub(r'^def ', 'noncomputable def ', late, flags=re.M)
text += '\n' + late
final = read('root_helpers/FinalTheorem.lean').replace(
    'oneNotLiveImpossible hOneNot S hS hl', 'oneNotLiveImpossibleChecked S hS hl')
for old, new in [(', ', ','), (' : ', ':'), (' := ', ':=')]:
    text = text.replace(old, new)
text += '\n' + end + '\n\n' + final
assert '_root_' not in text and '"' not in text
assert not re.search(r'\b(?:sorry|axiom|native_decide|unsafe|example)\b', text)
assert not re.search(r'\b\d{21,}\b', text)
assert [line for line in text.splitlines() if line.startswith('import ')] == ['import PEqualNP.Defs']
assert read('statement.txt').strip() in text
path = base / 'root_helpers/FinalCutCandidate.lean'
path.write_text(text)
(base / 'root_helpers/assembly-manifest.json').write_text(json.dumps(manifest, indent=2))
print('Assembled scratch candidate:', len(text.splitlines()), 'lines,', len(text.encode()), 'bytes')
print('Size limit:', 512 * 1024, '; within:', len(text.encode()) <= 512 * 1024)
print('SHA256', hashlib.sha256(text.encode()).hexdigest())
