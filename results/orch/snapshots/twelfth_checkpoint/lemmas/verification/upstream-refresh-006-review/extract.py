from pathlib import Path
import subprocess,json,re,datetime
root=Path('/workspace/pequalnp-proofs');out=Path('/tmp/oec/pequalnp-pilot-57/upstream-refresh-006');base='d4b3433bdf0f53b899c2806479d6f27a565d2e37'
def run(name,args,ok=(0,)):
 p=subprocess.run(args,cwd=root,capture_output=True,text=True)
 (out/(name+'.stdout')).write_text(p.stdout);(out/(name+'.stderr')).write_text(p.stderr)
 if p.returncode not in ok: raise RuntimeError((name,p.returncode))
 return p.stdout,p.returncode
head=run('head',['git','rev-parse','FETCH_HEAD'])[0].strip();assert re.fullmatch('[0-9a-f]{40}',head)
changes=run('paths',['git','--no-pager','diff','--name-status',base,head,'--','lean/PEqualNP'])[0]
files=[line.split('\t')[-1] for line in changes.splitlines() if not line.startswith('D\t') and line.endswith('.lean')]
run('commits',['git','--no-pager','log','--format=%H %cI %s',base+'..'+head])
exists=run('L650-exists',['git','cat-file','-e',head+':lean/PEqualNP/Outside/L_meta_650.lean'],ok=(0,128))[1]==0
statements=[]
for k,path in enumerate(files):
 name=Path(path).name
 body=run('show-'+str(k),['git','--no-pager','show',head+':'+path])[0]
 dest=out/name
 if dest.exists(): dest=out/path.replace('/','__')
 dest.write_text(body)
 matches=list(re.finditer(r'^theorem\s+PEqualNP\.Outside\.[^\s:]+',body,re.M))
 stmt=body[matches[-1].start():].split(':=',1)[0] if matches else ''
 statements.append({'file':dest.name,'path':path,'statement':stmt})
manifest={'old':base,'new':head,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'files':files,'l650_file_present':exists}
(out/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n');(out/'statements.json').write_text(json.dumps(statements,indent=2)+'\n')
print(json.dumps({'head':head,'files':len(files),'L650_file_present':exists,'reductions':[x['file'] for x in statements if x['file'].startswith('R_')]},indent=2))
