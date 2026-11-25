from pathlib import Path
import hashlib,json,resource,subprocess,sys,time,zstandard
base=Path('/tmp/oec/pequalnp-pilot-78/numeric/s4-hadamard')
degree=int(sys.argv[1]);budget=int(sys.argv[2]) if len(sys.argv)>2 else 900
prime=1000000007;name=f'solve-D{degree}-p{prime}'
metadata=json.loads((base/f'invariant-D{degree}-validation.json').read_text())
source=base/f'invariant-D{degree}.bin.zst'
def limits():
    resource.setrlimit(resource.RLIMIT_AS,(128*2**20,128*2**20))
    resource.setrlimit(resource.RLIMIT_CPU,(budget,budget+5))
    resource.setrlimit(resource.RLIMIT_FSIZE,(8*2**20,8*2**20))
    resource.setrlimit(resource.RLIMIT_CORE,(0,0))
start=time.monotonic();digest=hashlib.sha256();read_bytes=0
with (base/f'{name}.stdout').open('w') as out,(base/f'{name}.stderr').open('w') as err:
    p=subprocess.Popen([str(base.parent/'macaulay-sparse-fast'),'-',str(prime),str(metadata['constant_column']),'78',str(base/f'{name}.witness')],stdin=subprocess.PIPE,stdout=out,stderr=err,preexec_fn=limits)
    try:
        with source.open('rb') as compressed,zstandard.ZstdDecompressor().stream_reader(compressed) as stream:
            while chunk:=stream.read(2**16):digest.update(chunk);read_bytes+=len(chunk);p.stdin.write(chunk)
        p.stdin.close();assert digest.hexdigest()==metadata['binary_uncompressed_sha256']
        code=p.wait(timeout=max(1,budget+30-(time.monotonic()-start)))
    except subprocess.TimeoutExpired:p.kill();p.wait();code='timeout'
    except Exception:p.kill();p.wait();raise
result={'exit':code,'seconds':time.monotonic()-start,'budget_cpu_seconds':budget,'address_space_mib':128,'streamed_bytes':read_bytes,'input_sha256':digest.hexdigest()}
(base/f'{name}.result.json').write_text(json.dumps(result,indent=2));print(json.dumps(result),flush=True)
print((base/f'{name}.stdout').read_text(),flush=True)
