from pathlib import Path
import concurrent.futures,json,subprocess,time
base=Path('/tmp/oec/pequalnp-pilot-104')
package=Path('/workspace/pequalnp-proofs/lean/.lake/packages/mathlib')
hashes=dict(line.split() for line in (base/'2962-cache-hashes.stdout').read_text().splitlines())
mods=(base/'2962-required-mathlib-modules.txt').read_text().splitlines()
leantar='/tmp/oec/pequalnp-pilot-104/toolchain/lean-4.36.0-linux/bin/leantar'
work=base/'2962-cache-restore'
work.mkdir(exist_ok=True)
def restore(mod):
    c=package/'.lake/build/ir'/Path(*mod.split('.')).with_suffix('.c')
    if c.exists():return {'module':mod,'status':'already-present'}
    arc=work/hashes[mod]
    log=work/(mod+'.log')
    with log.open('wb') as out:
        r=subprocess.run(['curl','-f','-s','-S','https://cache.mathlib.org/mathlib4-master/f/'+arc.name,'-o',str(arc)],stdout=out,stderr=out)
        if r.returncode:return {'module':mod,'status':'fetch-error','exit':r.returncode}
        size=arc.stat().st_size
        r=subprocess.run([leantar,'-f','-x',str(arc)],cwd=package,stdout=out,stderr=out)
        if r.returncode:return {'module':mod,'status':'extract-error','exit':r.returncode}
    if not c.exists():return {'module':mod,'status':'missing-c'}
    arc.unlink()
    return {'module':mod,'status':'restored','archiveBytes':size,'cBytes':c.stat().st_size}
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
    futures=[pool.submit(restore,m) for m in mods]
    for f in concurrent.futures.as_completed(futures):
        result=f.result()
        print(json.dumps(result),flush=True)
        if result['status'] not in ['restored','already-present']:
            for pending in futures:pending.cancel()
            raise SystemExit(1)
