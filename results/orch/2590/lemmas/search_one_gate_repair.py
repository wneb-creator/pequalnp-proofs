import json,time,hashlib,datetime
from pathlib import Path
D=json.loads(Path('results/orch/2590/lemmas/search_petersen_baseline.json').read_text())
C=D['approximation_gates'];E=D['edges'];N=10
inputs=[sum(int(x>>i&1)<<x for x in range(1024)) for i in range(N)]
goal=sum(int(any(x>>a&1 and x>>b&1 for a,b in E))<<x for x in range(1024))
def evaluate(circ,output):
    w=inputs.copy()
    for op,a,b in circ:w.append((w[a]|w[b]) if op else(w[a]&w[b]))
    out=w[output];return (out&~goal).bit_count(),(goal&~out).bit_count()
start=time.monotonic();tested=0;best=1025;bestc=None
for pos in range(19):
    newwire=N+pos
    for a in range(newwire):
        occurrences=[(j,k) for j in range(pos,18) for k in (1,2) if C[j][k]==a]
        if a==27:occurrences.append((18,-1))
        for subset in range(1,1<<len(occurrences)):
            redirected={occurrences[k] for k in range(len(occurrences)) if subset>>k&1}
            for b in range(newwire):
                for op in (0,1):
                    circ=[list(g) for g in C[:pos]]+[[op,a,b]]
                    for j in range(pos,18):
                        g=C[j]
                        circ.append([g[0]]+[newwire if (j,k) in redirected else g[k]+int(g[k]>=newwire) for k in (1,2)])
                    output=newwire if (18,-1) in redirected else 27+int(27>=newwire)
                    fp,fn=evaluate(circ,output);tested+=1
                    if fp+fn<best:
                        best=fp+fn;bestc={'gates':circ,'output':output,'fp':fp,'fn':fn,'insert_position':pos,'sources':[a,b],'op':op,'redirected_occurrences':sorted(redirected)}
                        print(json.dumps({'improvement':bestc,'tested':tested,'elapsed':time.monotonic()-start}),flush=True)
                    if fp+fn==0:
                        print('FOUND',flush=True);raise SystemExit(0)
print(json.dumps({'status':'completed specified one-gate insertion class; no exact repair','tested':tested,'best_full_errors':best,'elapsed':time.monotonic()-start}),flush=True)
