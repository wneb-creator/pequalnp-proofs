import gzip,hashlib,json,shutil,sys
from pathlib import Path
assert len(sys.argv)==2
manifest=json.loads(Path(sys.argv[1]).read_text())
assert manifest['format']=='ordered-cnf-composition-v1'
delta_path=Path(manifest['delta_path'])
delta_bytes=delta_path.read_bytes()
assert hashlib.sha256(delta_bytes).hexdigest()==manifest['delta_sha256']
header,delta_body=delta_bytes.split(b'\n',1)
assert header.decode().split()==['p','cnf',str(manifest['variables']),str(manifest['delta_clauses'])]
mapping_path=Path(manifest['mapping_path']);mapping_bytes=mapping_path.read_bytes()
assert hashlib.sha256(mapping_bytes).hexdigest()==manifest['mapping_sha256']
mapping=json.loads(mapping_bytes)
assert mapping['variables']==manifest['variables']
assert mapping['clauses']==manifest['base_clauses']+manifest['delta_clauses']
assert delta_body.endswith(b'\n') or not delta_body
out=sys.stdout.buffer
out.write(('p cnf '+str(manifest['variables'])+' '+str(mapping['clauses'])+'\n').encode())
h=hashlib.sha256()
with gzip.open(manifest['base_gzip'],'rb') as source:
    base_header=source.readline();h.update(base_header)
    assert base_header.decode().split()==['p','cnf',str(manifest['base_variables']),str(manifest['base_clauses'])]
    last=b''
    while chunk:=source.read(1048576):
        h.update(chunk);out.write(chunk);last=chunk[-1:]
    assert last in [b'',b'\n']
assert h.hexdigest()==manifest['base_uncompressed_sha256']
out.write(delta_body)
out.flush()
