from pathlib import Path
import json,sys

base=Path('/tmp/oec/pequalnp-pilot-78/numeric')
source=(base/'groebner_probe.py').read_text()
source=source[:source.index("print(json.dumps({'stage':'generated'")]
source=source.replace('resource.setrlimit(resource.RLIMIT_AS,(1536*2**20,1536*2**20))','')
source=source.replace('resource.setrlimit(resource.RLIMIT_CPU,(30,35))','')
charts=[(0,1,2),(0,1,4),(0,1,5),(0,1,7),(0,1,8),(0,4,7),(0,4,8),(0,5,6),(1,2,3),(1,2,5),(1,2,6)]
for chart in charts:
    sys.argv=['generator',','.join(map(str,chart)),'0']
    ns={};exec(compile(source,'generator','exec'),ns)
    polys=[v for e,v in ns['coeff'].items() if sum(e)>=2 and v]
    name='chart-'+''.join(map(str,chart))
    for characteristic in (0,101,2147483647):
        p=base/f'{name}-p{characteristic}.ms'
        p.write_text(','.join('x'+str(i) for i in range(18))+'\n'+str(characteristic)+'\n'+',\n'.join(str(poly).replace('**','^') for poly in polys)+'\n')
    print(json.dumps({'chart':chart,'polynomials':len(polys),'terms':sum(map(len,polys))}),flush=True)
