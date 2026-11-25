from pathlib import Path
import hashlib,json,gzip
repo=Path('/workspace/pequalnp-proofs');scratch=Path(__file__).resolve().parents[1]
def digest(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for block in iter(lambda:f.read(1024*1024),b''):h.update(block)
 return h.hexdigest()
inventory=(scratch/'frozen_archive_files.txt').read_text().splitlines()
for name,count,expected in [
 ('checkpoint-engine',240,'54b11bbfccf1ec1f07f078380a03a3515c7656e44249a4cc18b79cf4a1176416'),
 ('augmented-c4-cases23',36,'09cd9d5f24add2ecf33d398794cc37ef1f6e19d9a673a9f12a0cabf3fbb18b8f'),
 ('grouped-subset-r2-progress01',5,None)]:
 relative=Path('results/gct231')/name;folder=repo/relative;mf=folder/'sha256.json';manifest=json.loads(mf.read_text())
 assert len(manifest)==count
 if expected:assert digest(mf)==expected
 actual={str(Path(x).relative_to(relative)) for x in inventory if Path(x).is_relative_to(relative)}-{'sha256.json'}
 assert actual==set(manifest)
 for path,wanted in manifest.items():
  assert not Path(path).is_absolute() and '..' not in Path(path).parts
  assert digest(folder/path)==wanted,path
 print('PASS archive exact coverage and all hashes',name,count,digest(mf),flush=True)

folder=repo/'results/gct231/augmented-c4-cases23'
for case in [2,3]:
 result=json.loads((folder/f'neogb-c4-augmented{case}-p1009-r1.result.json').read_text())
 basis=json.loads((folder/f'neogb-c4-augmented{case}-p1009-r1-basis.json').read_text())
 assert result['status']=='COMPLETED' and result['returncode']==0 and result['unit_basis']
 assert basis['characteristic']==1009 and basis['nvars']==5 and basis['nterms']==1
 assert basis['basis']==[[['1',[0,0,0,0,0]]]]
 assert result['input_sha256']==digest(folder/f'neogb-c4-augmented{case}-p1009.in')
 print('PASS finite-field unit diagnostic',case,result['seconds'],flush=True)

folder=repo/'results/gct231/grouped-subset-r2-progress01';saved=json.loads((folder/'preservation.json').read_text());meta=json.loads((folder/'snapshot-metadata.json').read_text());launch=json.loads((folder/'launch.json').read_text())
assert meta==saved['metadata']
assert (meta['sequence'],meta['round'],meta['characteristic'],meta['nvars'])==(2,82,1009,18)
h=hashlib.sha256();size=0;newlines=0
with gzip.open(folder/'snapshot.in.gz','rb') as stream:
 for block in iter(lambda:stream.read(1024*1024),b''):
  h.update(block);size+=len(block);newlines+=block.count(b'\n')
assert h.hexdigest()==saved['snapshot_sha256_uncompressed'] and size==saved['snapshot_bytes_uncompressed']
base=scratch/'neogb-star-full-grouped-p1009.in'
assert digest(base)==launch['input_sha256']==launch['base_input_sha256']
with gzip.open(folder/'snapshot.in.gz','rt') as stream,base.open() as original:
 n,m,p,terms=map(int,stream.readline().split());lengths=list(map(int,stream.readline().split()))
 bn,bm,bp,bt=map(int,original.readline().split());bl=list(map(int,original.readline().split()))
 assert (n,p)==(bn,bp)==(18,1009) and bm==meta['original_generators']==31 and bt==meta['original_terms']==2450
 assert len(lengths)==m==bm+meta['appended_basis_rows'] and lengths[:bm]==bl
 assert sum(lengths)==terms==bt+meta['appended_basis_terms'] and newlines==terms+2
 for _ in range(bt):
  a=tuple(map(int,stream.readline().split()));b=tuple(map(int,original.readline().split()))
  assert a[2:]==b[2:] and a[0]*pow(a[1],-1,p)%p==b[0]*pow(b[1],-1,p)%p
assert meta['appended_basis_rows']==419 and meta['appended_basis_terms']==998940
assert meta['available_basis_rows']==meta['appended_basis_rows']+meta['omitted_basis_rows']
assert meta['available_basis_terms']==meta['appended_basis_terms']+meta['omitted_basis_terms']
assert meta['appended_basis_terms']<=meta['derived_term_budget']==1000000
print('PASS partial snapshot gzip identity, complete line/header counts, exact original prefix, and omission metadata',size,h.hexdigest(),flush=True)
print('SCOPE: snapshot is a partial finite-field restart generating set; no final basis or proof claim.',flush=True)
