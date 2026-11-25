from pathlib import Path
import hashlib,json,struct,sys,zstandard
BASE=Path('/tmp/oec/pequalnp-pilot-78/numeric');OUT=BASE/'s4-structure';group=sys.argv[1]
DATA=BASE/'s4-hadamard' if group=='triv' else OUT/('block-'+group)
meta=json.loads((DATA/'invariant-D5-validation.json').read_text());raw=zstandard.ZstdDecompressor().decompress((DATA/'invariant-D5.bin.zst').read_bytes(),max_output_size=meta['raw_bytes']);assert hashlib.sha256(raw).hexdigest()==meta['binary_uncompressed_sha256']
rows=json.loads(zstandard.ZstdDecompressor().decompress((DATA/'invariant-D5-rows.json.zst').read_bytes()));cols=json.loads(zstandard.ZstdDecompressor().decompress((DATA/'invariant-D5-columns.json.zst').read_bytes()));chart=json.loads((BASE/'s4-hadamard/chart.json').read_text());gd=[sum(x) for x in chart['parameter_exponents']];degrees=[gd[g]+len(m) for g,m in rows]
order=sorted(range(len(rows)),key=lambda i:(degrees[i],i));inverse={old:new for new,old in enumerate(order)}
nr,nc,nnz=struct.unpack('<IIQ',raw[:16]);entries=sorted((inverse[r],c,v) for r,c,v in struct.iter_unpack('<IIq',raw[16:]))
(OUT/f'rational-{group}-input.bin').write_bytes(struct.pack('<IIQ',nr,nc,nnz)+b''.join(struct.pack('<IIq',*e) for e in entries))
(OUT/f'rational-{group}-degrees.bin').write_bytes(b''.join(struct.pack('<I',len(m)) for m in cols)+b''.join(struct.pack('<I',degrees[old]) for old in order))
(OUT/f'rational-{group}-rowmap.json').write_text(json.dumps({'order':order,'rows':rows,'columns':cols},separators=(',',':')))
print(json.dumps({'group':group,'rows':nr,'columns':nc,'entries':nnz,'input_sha256':meta['binary_uncompressed_sha256']}))
