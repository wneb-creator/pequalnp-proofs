from pathlib import Path
import hashlib,json,re
base=Path('/workspace/pequalnp-proofs/results/gct231/c4-U-qq')
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest=base/'SHA256SUMS'
assert digest(manifest)=='0eb6a2f21680531625ceda62accc632ee26ce034ff4028448c9d2078c91a4d80'
entries={line.split('  ',1)[1]:line.split('  ',1)[0] for line in manifest.read_text().splitlines()}
assert set(entries)=={p.name for p in base.iterdir() if p.is_file() and p.name!='SHA256SUMS'}
for name,h in entries.items():assert digest(base/name)==h
print('PASS manifest exact coverage and all',len(entries),'hashes',flush=True)
metadata=json.loads((base/'metadata.json').read_text())
for item,expected in zip(metadata,[23,35]):
 case=item['case'];run=json.loads((base/f'case{case}.run.json').read_text());assert run==item['run']
 assert run['status']=='UNKNOWN_OUTPUT_FILE_SIZE_LIMIT' and run['returncode']==-25
 assert (run['seconds_limit'],run['memory_mib_limit'],run['output_file_mib_limit'],run['pairs'])==(120,1024,256,32)
 assert digest(base/f'neogb-c4-Usaturated{case}-qq.in')==run['input_sha256']
 assert digest(base/f'case{case}.f4.in')==run['companion_sha256']
 log=(base/f'case{case}.log').read_text()
 rounds=[line for line in log.splitlines() if re.fullmatch(r'\s+\d+\s+\d+\s+\d+\s+\d+\s+x\s+\d+\s+[0-9.]+%\s+\d+ new\s+\d+ zero\s+[0-9.]+\s+\|\s+[0-9.]+\s*',line)]
 assert len(rounds)==expected==item['completed_rounds']
 assert rounds[-1]==item['last_completed_round']
 assert item['omitted_trace_bytes']==256*1024**2 and re.fullmatch('[0-9a-f]{64}',item['omitted_trace_sha256'])
 print('PASS',case,run['status'],run['wall_seconds'],'seconds, completed rounds',expected,flush=True)
print('SCOPE no basis/certificate/Lean verdict; large omitted trace hashes recorded but raw traces not reread or replayed.',flush=True)
