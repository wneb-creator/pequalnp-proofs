import sys,random,time
sys.argv=['c','1'];import fresh_meta3773_five_sixteen as curr
import fresh_meta3773_five_wide as old
m=curr.model;r=random.Random(1795);f0=m.raw+m.free
for n in range(9,16):
 for i in range(8):
  F=tuple(sorted(r.choices(f0,k=n)));outs=list(F)
  while len(outs)>1:
   a=outs.pop(r.randrange(len(outs)));b=outs.pop(r.randrange(len(outs)));outs.append((a&b)if r.randrange(2)else(a|b))
  if i%2:p=outs[0];q=m.M^p
  else:p=m.target;q=m.M^p
  x=old.solve(F,p,q);y=curr.solve(F,p,q);assert x==y and ((not i%2)or y),(n,i,x,y)
print('56 equivalences across 9..15 features,28 generated expression controls')
for mask in (127,63,126,31):
 F=tuple(sorted((*m.raw,*(v for j,v in enumerate(m.free)if mask>>j&1))));st=time.perf_counter();a=old.solve(F,m.target,m.M^m.target);t=time.perf_counter();b=curr.solve(F,m.target,m.M^m.target);print('helper mask',mask,'original',a,t-st,'component',b,time.perf_counter()-t);assert a==b
