from pathlib import Path
import json,hashlib
b=Path(__file__).resolve().parent.parent/'sparse-engine'
for stem in ('toy-unit','toy-nonunit','toy-rational','rowzero'):
    old=json.loads((b/'certificate-trace-compact'/(stem+'.certificate.json')).read_text())
    new=json.loads((b/'certificate-trace-primitive'/(stem+'.certificate.json')).read_text())
    assert [x['polynomial'] for x in old['steps']]==[x['polynomial'] for x in new['steps']]
    oldoutputs=[x.split('\t',2)[2] for x in (b/'certificate-trace-compact'/(stem+'.trace')).read_text().splitlines() if x.startswith('O\t')]
    newoutputs=[x.split('\t',2)[2] for x in (b/'certificate-trace-primitive'/(stem+'.trace')).read_text().splitlines() if x.startswith('O\t')]
    assert oldoutputs==newoutputs
    print('PASS identical exact output polynomials',stem,len(newoutputs))
    if stem=='rowzero':assert new['record_counts']['S']-old['record_counts']['S']==29
for n in ['cert_trace_primitive.c','make_cert_trace_primitive.py','run_neogb_trace_primitive.py','certificate-trace-primitive/src/neogb/la_qq.c']:
    p=b/n;print(hashlib.sha256(p.read_bytes()).hexdigest(),n)
source=(b/'cert_trace_primitive.c').read_text()
function=source[source.index('static void ct_primitive_dense_row('):source.index('static void ct_print_poly(')]
harness=(Path(__file__).parent/'primitive_harness.c').read_text()
assert harness.count(function)==1
print('PASS harness contains exact frozen primitive helper body')
