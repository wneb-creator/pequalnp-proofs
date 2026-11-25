from pathlib import Path
import hashlib,json,re

base=Path(__file__).resolve().parents[1]/'witness-codec'
manifest=base/'manifest.json'
assert hashlib.sha256(manifest.read_bytes()).hexdigest()=='3946eb4d2c7d8e12e9faab20443b70f0d756db8e910b7acea90ea8e0f729aa62'
records=json.loads(manifest.read_text());assert len(records)==40
for name,e in records.items():
    data=(base/name).read_bytes();assert len(data)==e['bytes'] and hashlib.sha256(data).hexdigest()==e['sha256']
assert {p.relative_to(base).as_posix() for p in base.rglob('*') if p.is_file()}==set(records)|{'manifest.json'}
compact=(base/'compact-witness-candidate.bin').read_bytes()
short=(base/'shortlist-witness-candidate.bin').read_bytes()
def tuples(text,name):
    body=re.search(r'def '+name+r' : [^\n]* := ([^\n]*)',text).group(1)
    return [(int(a),int(b,16)) for a,b in re.findall(r'\((\d+),\s*(0x[0-9a-f]+)\)',body)]
def decode(commands,packed,tree=None):
    def byte():
        nonlocal packed
        if tree is None:
            value=packed&255;packed>>=8;return value
        node=0
        for _ in range(16):
            child=(tree>>(20*node+10*(packed&1)))&1023;packed>>=1
            if child>=512:
                assert child<768;return child-512
            assert child<255;node=child
        raise AssertionError('Exhausted Huffman fuel')
    out=bytearray()
    for _ in range(commands):
        header=byte()
        if header<128:
            out.extend(byte() for _ in range(header+1))
        else:
            distance=byte()+(byte()<<8);assert 0<distance<=len(out)
            for _ in range(header-128+3):out.append(out[-distance])
    assert packed==0
    return bytes(out)
payload_results=[]
for name,expected,huff in [('Payload32768.lean',compact,False),('shortlist/Payload32768.lean',short,False),('ShortlistHuffmanPayload.lean',short,True)]:
    text=(base/name).read_text();tree=int(re.search(r'def tree : Nat := (0x[0-9a-f]+)',text).group(1),16) if huff else None
    chunks=tuples(text,'payload');out=b''.join(decode(n,p,tree) for n,p in chunks);assert out==expected
    payload_results.append(dict(file=name,chunks=len(chunks),decoded_bytes=len(out),source_bytes=len(text.encode()),decoded_sha256=hashlib.sha256(out).hexdigest()))
sample_results=[]
for e in json.loads((base/'kernel-samples.json').read_text()):
    name=e['module'];text=(base/(name+'.lean')).read_text();status=json.loads((base/(name+'.status.json')).read_text())
    assert status['exit_code']==e['compiler_exit']==0 and not (base/(name+'.compile.txt')).read_text()
    assert hashlib.sha256(text.encode()).hexdigest()==e['source_sha256'] and len(text.encode())==e['source_bytes']
    expected=b''.join(p.to_bytes(n,'little') for n,p in tuples(text,'expected'))
    original=compact if e['input_kind']=='compact' else short
    assert len(expected)==e['sample_bytes'] and expected==original[:len(expected)]
    assert hashlib.sha256(expected).hexdigest()==e['sample_sha256']
    huff='decodeHuff' in text
    tree=int(re.search(r'def tree : Nat := (0x[0-9a-f]+)',text).group(1),16) if huff else None
    decoded=b''.join(decode(n,p,tree) for n,p in tuples(text,'actual'));assert decoded==expected
    assert 'decide +kernel' in text
    assert not re.search(r'\b(sorry|axiom|native_decide|bv_decide|unsafe|partial|structure|inductive|instance)\b|_root_|"',text)
    sample_results.append(dict(module=name,checked_bytes=len(expected),kernel_exit=0))
for name in ['WitnessDecoder','WitnessHuffman']:
    assert json.loads((base/(name+'.status.json')).read_text())['exit_code']==0
    assert not (base/(name+'.compile.txt')).read_text()
    text=(base/(name+'.lean')).read_text()
    assert not re.search(r'\b(sorry|axiom|native_decide|bv_decide|unsafe|partial|structure|inductive|instance)\b|_root_|"',text)
payload=(base/'ShortlistHuffmanPayload.lean').stat().st_size
decoders=sum((base/(n+'.lean')).stat().st_size for n in ['WitnessDecoder','WitnessHuffman'])
report=dict(verdict='PASS',manifest_sha256=hashlib.sha256(manifest.read_bytes()).hexdigest(),manifest_entries=len(records),full_python_payload_roundtrips=payload_results,compiled_kernel_samples=sample_results,huffman_payload_source_bytes=payload,decoder_source_bytes=decoders,remaining_of_512KiB=524288-payload-decoders,scope='Preserved pure decoder prototypes and four finite kernel equalities only. Full candidate bytes independently roundtrip in Python; the whole candidate has not been kernel decoded or semantically checked as a search certificate. Missing checker, boundaries, priors and rectangle certificates remain outside this budget.')
print(json.dumps(report,indent=2))
