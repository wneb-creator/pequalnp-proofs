from pathlib import Path
import tarfile,json,socket,hashlib,shutil,time
p=Path('/tmp/oec/pequalnp-pilot-182')
items=json.loads((p/'compilation-artifacts-manifest.json').read_text())
lookup={x['archive_name']:x for x in items}
d=p/'cache-staging/compilation';d.mkdir(parents=True,exist_ok=True)
count=0
with tarfile.open(p/'compilation-artifacts.tar.gz','r|gz') as t:
 for member in t:
  assert member.isfile() and member.name in lookup
  e=lookup[member.name];dst=Path(e['path']);assert not dst.exists()
  src=d/str(count);h=hashlib.sha256()
  with t.extractfile(member) as inp,src.open('wb') as out:
   while b:=inp.read(1024*1024): h.update(b);out.write(b)
  assert src.stat().st_size==e['bytes'] and h.hexdigest()==e['sha256']
  with socket.socket(socket.AF_UNIX,socket.SOCK_STREAM) as c:
   c.connect(str(p/'ram-cache-3.sock'))
   c.sendall((json.dumps({'source':str(src),'destination':str(dst),'sha256':e['sha256']})+'\n').encode())
   ans=json.loads(c.makefile('rb').readline());assert ans['ok'],ans
  src.unlink();count+=1
assert count==len(items)
print('Restored all '+str(count)+' exact compilation artifacts temporarily; no library sources built.',flush=True)
