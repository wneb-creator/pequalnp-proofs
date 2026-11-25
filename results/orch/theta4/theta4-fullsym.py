import argparse,json
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--symmetries',required=True);p.add_argument('--query',required=True);p.add_argument('--output',required=True);p.add_argument('--size',type=int,required=True)
a=p.parse_args();data=json.loads(Path(a.symmetries).read_text());n=10;lines=[]
def bv(x,w):return f'(_ bv{x} {w})'
for k,permutation in enumerate(data['permutations']):
 if permutation==list(range(n)):continue
 coordinates=[]
 for j in range(a.size):
  width=(n+j).bit_length();images=[]
  for letter in 'ab':
   variable=f'{letter}{j}';expression=variable
   for i in reversed(range(n)):expression=f'(ite (= {variable} {bv(i,width)}) {bv(permutation[i],width)} {expression})'
   name=f'img{k}_{letter}{j}';lines.append(f'(define-fun {name} () (_ BitVec {width}) {expression})');images.append(name)
  left,right=images;low=f'(ite (bvule {left} {right}) {left} {right})';high=f'(ite (bvule {left} {right}) {right} {left})'
  coordinates.extend([(f'a{j}',low),(f'b{j}',high)])
 lex='true'
 for left,right in reversed(coordinates):lex=f'(or (bvult {left} {right}) (and (= {left} {right}) {lex}))'
 lines.append(f'(assert {lex})')
Path(a.output).write_text(Path(a.query).read_text()+'\n'+'\n'.join(lines)+'\n')
