from pathlib import Path
import hashlib,json,resource,subprocess,time,zstandard
OUT=Path('/tmp/oec/pequalnp-pilot-78/numeric/rank1-macaulay');meta={r['path']:r for r in json.loads((OUT/'compression.json').read_text())}
raw=zstandard.ZstdDecompressor().decompress((OUT/'D7-input.bin.zst').read_bytes());assert hashlib.sha256(raw).hexdigest()==meta['D7-input.bin']['sha256']
degrees=zstandard.ZstdDecompressor().decompress((OUT/'D7-degrees.bin.zst').read_bytes());assert hashlib.sha256(degrees).hexdigest()==meta['D7-degrees.bin']['sha256'];(OUT/'D7-degrees-retry.bin').write_bytes(degrees)
def limits():
    resource.setrlimit(resource.RLIMIT_AS,(512*2**20,512*2**20));resource.setrlimit(resource.RLIMIT_CPU,(180,185));resource.setrlimit(resource.RLIMIT_FSIZE,(2**20,2**20));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
start=time.monotonic()
with(OUT/'D7-mod-long.stdout').open('w')as out,(OUT/'D7-mod-long.stderr').open('w')as err:
    p=subprocess.Popen([str(OUT/'graded-constant-mod'),'-',str(OUT/'D7-degrees-retry.bin'),str(OUT/'D7-mod-long-constant.jsonl')],stdin=subprocess.PIPE,stdout=out,stderr=err,preexec_fn=limits)
    try:p.communicate(raw,timeout=240);code=p.returncode
    except subprocess.TimeoutExpired:p.kill();p.communicate();code='timeout'
report={'exit':code,'wall_seconds':time.monotonic()-start,'memory_mib':512,'cpu_budget':180,'input_sha256':meta['D7-input.bin']['sha256'],'scope':'One longer cached degree7 constant-membership diagnostic over F1000000007; no Q claim.'}
if code==0:report['constant_rows']=[json.loads(s)for s in(OUT/'D7-mod-long-constant.jsonl').read_text().splitlines()]
(OUT/'D7-mod-long-result.json').write_text(json.dumps(report,indent=2));print(json.dumps(report),flush=True)
