from pathlib import Path
import json
import time

lines=Path('/tmp/oec/pequalnp-pilot-107/counterexample-residual-signed15.stdout').read_text().splitlines()
position=[i for i,l in enumerate(lines) if l.startswith('score')][-1]
seed=[tuple(map(int,l.split()[1:])) for l in lines[position+1:position+16]]
assert all(op in [0,1] for op,a,b in seed)
edges=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]
mask=(1<<512)-1
inputs=[sum(((x>>i)&1)<<x for x in range(512)) for i in range(9)]
goal=sum(int(any(x>>a&1 and x>>b&1 for a,b in edges))<<x for x in range(512))
best=512
trials=0
circuits=0
start=time.monotonic()
for gate in range(15):
    for op in range(2):
        for a in range(9+gate):
            for b in range(a,9+gate):
                circ=seed.copy()
                circ[gate]=(op,a,b)
                circuits+=1
                for source in range(24):
                    uses=[(j,side) for j,(p,q,r) in enumerate(circ)
                          for side,v in enumerate([q,r]) if v==source]
                    if source==23:uses.append((15,0))
                    for chosen in range(1,1<<len(uses)):
                        changed={uses[k] for k in range(len(uses)) if chosen>>k&1}
                        wires=inputs.copy()
                        for j,(p,q,r) in enumerate(circ):
                            left=wires[q]^(mask if (j,0) in changed else 0)
                            right=wires[r]^(mask if (j,1) in changed else 0)
                            wires.append(left&right if p==0 else left|right)
                        out=wires[-1]^(mask if (15,0) in changed else 0)
                        errors=(out^goal).bit_count()
                        trials+=1
                        if errors<best:
                            best=errors
                            print('best',best,'replacement',[gate,op,a,b],'source',source,
                                  'redirects',sorted(changed),flush=True)
                        if errors==0:
                            print('FOUND',json.dumps({'gates':circ,'negated_source':source,
                                  'redirects':sorted(changed)}),flush=True)
                            raise SystemExit(0)
print('DONE circuits',circuits,'trials',trials,'best_errors',best,
      'seconds',time.monotonic()-start,flush=True)
