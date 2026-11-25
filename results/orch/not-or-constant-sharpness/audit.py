import json
n=5
full=(1<<(1<<n))-1
inputs=[sum(((r>>i)&1)<<r for r in range(1<<n)) for i in range(n)]
a,b,x,y,z=inputs
h=a|b
c=full^h
active=set(inputs+[h,c])
gates=[(0,c,x),(1,a,c&x),(1,b,y),(0,a|(c&x),b|y),(1,(a|(c&x))&(b|y),h),(0,((a|(c&x))&(b|y))|h,z)]
values=[]
for d,v,w in gates:
    assert v in active and w in active and v!=w
    out=(v&w) if d==0 else(v|w)
    assert 0<out<full and out not in active
    active.remove(v);active.remove(w);active.add(out)
    values.append(out)
target=values[-1]
assert active=={target}
assert target==z&(h|(x&y))
assert all(not((target>>r)&1)for r in [0,1,2,4,8,16])
assert all(not((target>>r)&1)or((target>>s)&1)for r in range(32)for s in range(32)if r&s==r)
assert all(((target>>r)&1)==(((r>>2)&1)&((r>>3)&1)&((r>>4)&1))for r in range(32)if r&3==0)
assert all(any(((target>>r)&1)!=((target>>(r^(1<<i)))&1)for r in range(32))for i in range(5))
print(json.dumps(dict(verdict='PASS_FINITE_COUNTEREXAMPLE_TO_CONSTANT_MASS_ONLY',inputs=inputs,h=h,complement=c,gate_values=values,target=target,positive_gates=6,projected_constants=4,cofactor='x AND y AND z',cofactor_minimum_gates=2,reason_for_minimum='Three essential independent inputs require at least two binary gates; two AND gates attain it.',scope='Monotone target with no true singleton, strict fresh positive trace and exact constant-mass equality. The target includes a cubic term and this circuit is not gate-minimal. This does not refute any Petersen-specific or gate-minimality stability claim.'),indent=2))
