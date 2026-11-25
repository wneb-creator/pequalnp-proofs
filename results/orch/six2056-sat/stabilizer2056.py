import argparse,json
from pathlib import Path
p=argparse.ArgumentParser()
p.add_argument('--data',required=True)
p.add_argument('--query',required=True)
p.add_argument('--output',required=True)
p.add_argument('--size',type=int,required=True)
a=p.parse_args();d=json.loads(Path(a.data).read_text());n=d['n'];lines=[];branches=[]
def bv(x,w):return f'(_ bv{x} {w})'
for e,(u,v)in enumerate(d['bad_edges']):
 permutations=[p for p in d['automorphisms']if{p[u],p[v]}=={u,v}and p!=list(range(n))]
 terms=[]
 for k,permutation in enumerate(permutations):
  coordinates=[]
  for j in range(a.size):
   width=(n+j).bit_length();images=[]
   for letter in 'ab':
    variable=f'{letter}{j}';expression=variable
    for i in reversed(range(n)):
     expression=f'(ite (= {variable} {bv(i,width)}) {bv(permutation[i],width)} {expression})'
    name=f'img{e}_{k}_{letter}{j}'
    lines.append(f'(define-fun {name} () (_ BitVec {width}) {expression})');images.append(name)
   left,right=images
   low=f'(ite (bvule {left} {right}) {left} {right})'
   high=f'(ite (bvule {left} {right}) {right} {left})'
   coordinates.extend([(f'a{j}',low),(f'b{j}',high)])
  lex='true'
  for left,right in reversed(coordinates):
   lex=f'(or (bvult {left} {right}) (and (= {left} {right}) {lex}))'
  name=f'lex{e}_{k}'
  lines.append(f'(define-fun {name} () Bool {lex})');terms.append(name)
 canonical='(and '+' '.join(terms)+')'if terms else'true'
 branches.append(f'(and (= ((_ extract 2 2) r{e}p{a.size-1}) #b0) {canonical})')
lines.append('(assert (or '+' '.join(branches)+'))')
Path(a.output).write_text(Path(a.query).read_text()+'\n'+'\n'.join(lines)+'\n')
