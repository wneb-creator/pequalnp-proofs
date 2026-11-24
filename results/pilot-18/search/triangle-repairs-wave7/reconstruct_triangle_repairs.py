"""Restore all eight preserved candidate CNFs in fresh scratch; no solver."""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import sys


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def within(root, relative):
    relative=Path(relative)
    if relative.is_absolute() or '..' in relative.parts:raise ValueError('Unsafe relative path')
    path=root/relative
    if path.is_symlink() or not path.resolve().is_relative_to(root.resolve()):raise ValueError('Redirected path')
    return path


def main(output):
    package=Path(__file__).resolve().parent
    recipe=json.loads((package/'reconstruction.json').read_text())
    root=Path('/tmp/oec/pequalnp-pilot-18')
    if root.resolve()!=root:raise ValueError('Redirected scratch root')
    output=output.resolve()
    if output.exists() or not output.is_relative_to(root):raise ValueError('Fresh output inside named scratch required')
    missing=[]
    for row in recipe['sources']:
        raw=within(package,row['package_path']).read_bytes()
        if sha(raw)!=row['sha256']:raise ValueError('Packaged source hash mismatch')
        destination=within(root,row['scratch_path'])
        if destination.exists():
            if not destination.is_file() or destination.read_bytes()!=raw:raise ValueError('Existing source differs; refusing overwrite')
        else:missing.append((destination,raw))
    for path,raw in missing:
        path.parent.mkdir(parents=True,exist_ok=True)
        with path.open('xb') as f:f.write(raw)
    output.mkdir(parents=True,exist_ok=False)
    commands=[];files=[]
    for family in recipe['families']:
        name=family['name'];destination=within(output,name)
        command=[sys.executable,'-B',str(within(root,family['generator'])),str(destination)]
        with (output/(name+'.stdout')).open('x') as out,(output/(name+'.stderr')).open('x') as err:
            result=subprocess.run(command,stdout=out,stderr=err,timeout=60)
        commands.append({'command':command,'exit_code':result.returncode})
        if result.returncode:raise RuntimeError('Generator failed; full logs preserved')
        expected=family['expected_files']
        if set(expected)!={p.name for p in destination.iterdir()}:raise ValueError('Generated file set mismatch')
        for filename,wanted in expected.items():
            actual=sha(within(destination,filename).read_bytes())
            if actual!=wanted:raise ValueError('Generated file hash mismatch')
            files.append({'family':name,'file':filename,'sha256':actual})
    report={'verdict':'PASS_EXACT_EIGHT_CNF_RECONSTRUCTION','commands':commands,'files':files,
            'file_count':len(files),'CNFs':sum(p['file'].endswith('.cnf') for p in files),
            'solver_launched':False,'network_used':False,'Lean_built':False,
            'scope':'Reconstruction only; no pilot or one-gate enumeration is executed.'}
    (output/'validation.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:report[k] for k in ['verdict','file_count','CNFs']}))


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('output',type=Path)
    main(parser.parse_args().output)
