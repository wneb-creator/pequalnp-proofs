import argparse,hashlib,json
from pathlib import Path
N=14
EDGES=[(0,8),(0,10),(1,7),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)]
MASK=(1<<(1<<N))-1
INPUTS=[sum(1<<x for x in range(1<<N) if x>>i&1) for i in range(N)]
TARGET=0
for a,b in EDGES: TARGET|=INPUTS[a]&INPUTS[b]

def logical_lines(text):
 result=[]; pending=''
 for raw in text.splitlines():
  line=raw.split('#',1)[0].strip()
  if not line:continue
  if line.endswith('\\'):
   pending+=line[:-1]+' ';continue
  line=pending+line;pending='';result.append(line)
 if pending:raise ValueError('Unclosed BLIF continuation')
 return result

def parse_blif(path):
 lines=logical_lines(Path(path).read_text())
 ins=[];outs=[];nodes={};i=0
 while i<len(lines):
  line=lines[i];p=line.split();i+=1
  if p[0]=='.inputs':ins.extend(p[1:])
  elif p[0]=='.outputs':outs.extend(p[1:])
  elif p[0]=='.gate':
   pins=dict(x.split('=',1) for x in p[2:])
   if 'Y' not in pins:raise ValueError('Gate has no Y output: '+line)
   output=pins.pop('Y')
   if output in nodes:raise ValueError('Duplicate node '+output)
   nodes[output]=('gate',p[1],pins)
  elif p[0]=='.names':
   cubes=[]
   while i<len(lines) and not lines[i].startswith('.'):
    cubes.append(lines[i].split());i+=1
   output=p[-1]
   if output in nodes:raise ValueError('Duplicate node '+output)
   nodes[output]=('names',p[1:-1],cubes)
  elif p[0] in {'.model','.end','.input_arrival','.output_required','.default_input_arrival','.default_output_required','.default_input_drive','.default_output_load','.input_drive','.output_load'}:pass
  else:raise ValueError('Unsupported BLIF directive: '+line)
 if len(outs)!=1:raise ValueError('Expected one output')
 if set(ins)!={f'x{i}' for i in range(N)}:raise ValueError('Unexpected input names/order')
 return ins,outs,nodes

class Builder:
 def __init__(self):self.gates=[];self.cache={}
 def emit(self,op,a,b=-1):
  if op<2:
   if a>b:a,b=b,a
   if a==b:return a
   if a==-1:return -1 if op==0 else b
  elif a>=N and self.gates[a-N][0]==2:return self.gates[a-N][1]
  key=(op,a,b if op<2 else -1)
  if key not in self.cache:
   self.cache[key]=N+len(self.gates);self.gates.append(list(key))
  return self.cache[key]
 def neg(self,a):return self.emit(2,a)
 def conj(self,a,b):return self.emit(0,a,b)
 def disj(self,a,b):return self.emit(1,a,b)
 def one(self):return self.neg(-1)
 def cover(self,fanins,cubes):
  if not cubes:return -1
  decoded=[]
  for fields in cubes:
   if not fanins:
    if len(fields)!=1 or fields[0] not in {'0','1'}:raise ValueError('Bad constant cube')
    decoded.append(('',fields[0]))
   else:
    pattern=fields[0];bit=fields[1] if len(fields)>1 else '1'
    if len(pattern)!=len(fanins) or any(c not in '01-' for c in pattern) or bit not in {'0','1'}:raise ValueError('Bad BLIF cube')
    decoded.append((pattern,bit))
  polarities={bit for _,bit in decoded}
  if len(polarities)!=1:raise ValueError('Mixed BLIF cover polarities')
  if len(fanins)<=2:
   polarity=int(decoded[0][1]);table=0
   for assignment in range(1<<len(fanins)):
    matched=any(all(c=='-' or int(c)==(assignment>>j&1) for j,c in enumerate(pattern)) for pattern,_ in decoded)
    if (polarity if matched else 1-polarity):table|=1<<assignment
   if not fanins:return self.one() if table else -1
   a=fanins[0]
   if len(fanins)==1:
    return -1 if table==0 else self.one() if table==3 else a if table==2 else self.neg(a)
   c=fanins[1]
   if table==0:return -1
   if table==15:return self.one()
   if table==10:return a
   if table==12:return c
   if table==5:return self.neg(a)
   if table==3:return self.neg(c)
   if table==8:return self.conj(a,c)
   if table==14:return self.disj(a,c)
   if table==7:return self.neg(self.conj(a,c))
   if table==1:return self.neg(self.disj(a,c))
   if table==2:return self.conj(a,self.neg(c))
   if table==4:return self.conj(self.neg(a),c)
   if table==11:return self.disj(a,self.neg(c))
   if table==13:return self.disj(self.neg(a),c)
   if table==6:return self.conj(self.disj(a,c),self.neg(self.conj(a,c)))
   if table==9:return self.disj(self.conj(a,c),self.neg(self.disj(a,c)))
   raise AssertionError('Unreachable two-input truth table')
  value=-1
  for pattern,_ in decoded:
   literals=[self.neg(v) if c=='0' else v for c,v in zip(pattern,fanins) if c!='-']
   if not literals:term=self.one()
   else:
    term=literals[0]
    for v in literals[1:]:term=self.conj(term,v)
   value=self.disj(value,term)
  return value if decoded[0][1]=='1' else self.neg(value)
 def prune(self,out):
  final=[];done={i:i for i in range(N)};done[-1]=-1
  def visit(w):
   if w in done:return done[w]
   op,a,b=self.gates[w-N]
   a=visit(a);b=visit(b) if op<2 else -1
   q=N+len(final);final.append([op,a,b]);done[w]=q;return q
  root=visit(out)
  if final and root!=N+len(final)-1:raise AssertionError('Output not last after pruning')
  return final,root

def translate(path):
 ins,outs,nodes=parse_blif(path);b=Builder();done={f'x{i}':i for i in range(N)};visiting=set()
 def visit(name):
  if name in done:return done[name]
  if name in visiting:raise ValueError('Combinational cycle')
  if name not in nodes:raise ValueError('Undriven signal '+name)
  visiting.add(name)
  kind,arg,body=nodes[name]
  if kind=='names':v=b.cover([visit(x) for x in arg],body)
  elif arg=='ZERO':v=-1
  elif arg=='ONE':v=b.one()
  elif arg=='BUF':v=visit(body['A'])
  elif arg=='INV':v=b.neg(visit(body['A']))
  elif arg=='AND2':v=b.conj(visit(body['A']),visit(body['B']))
  elif arg=='OR2':v=b.disj(visit(body['A']),visit(body['B']))
  elif arg in {'NAND2','NOR2','ANDNOT2','ORNOT2','XOR2','XNOR2','AND3','OR3','AND4','OR4','AO21','OA21','AO22','OA22','AOI21','OAI21','AOI22','OAI22','MUX2','MAJ3'}:
   ps={k:visit(signal) for k,signal in body.items()};a=ps['A'];c=ps['B']
   if arg=='NAND2':v=b.neg(b.conj(a,c))
   elif arg=='NOR2':v=b.neg(b.disj(a,c))
   elif arg=='ANDNOT2':v=b.conj(a,b.neg(c))
   elif arg=='ORNOT2':v=b.disj(a,b.neg(c))
   elif arg=='XOR2':v=b.conj(b.disj(a,c),b.neg(b.conj(a,c)))
   elif arg=='XNOR2':v=b.disj(b.conj(a,c),b.neg(b.disj(a,c)))
   elif arg in {'AND3','AND4'}:
    v=b.conj(b.conj(a,c),ps['C'])
    if arg=='AND4':v=b.conj(v,ps['D'])
   elif arg in {'OR3','OR4'}:
    v=b.disj(b.disj(a,c),ps['C'])
    if arg=='OR4':v=b.disj(v,ps['D'])
   elif arg in {'AO21','AOI21'}:
    v=b.disj(b.conj(a,c),ps['C'])
    if arg=='AOI21':v=b.neg(v)
   elif arg in {'OA21','OAI21'}:
    v=b.conj(b.disj(a,c),ps['C'])
    if arg=='OAI21':v=b.neg(v)
   elif arg in {'AO22','AOI22'}:
    v=b.disj(b.conj(a,c),b.conj(ps['C'],ps['D']))
    if arg=='AOI22':v=b.neg(v)
   elif arg in {'OA22','OAI22'}:
    v=b.conj(b.disj(a,c),b.disj(ps['C'],ps['D']))
    if arg=='OAI22':v=b.neg(v)
   elif arg=='MUX2':v=b.disj(b.conj(a,c),b.conj(b.neg(a),ps['C']))
   elif arg=='MAJ3':v=b.disj(b.conj(a,c),b.conj(b.disj(a,c),ps['C']))
  else:raise ValueError('Unsupported mapped cell '+arg)
  visiting.remove(name);done[name]=v;return v
 out=visit(outs[0]);gates,out=b.prune(out)
 ws=INPUTS.copy()
 for op,a,c in gates:
  va=0 if a==-1 else ws[a];vc=0 if c==-1 else ws[c]
  ws.append(va&vc if op==0 else va|vc if op==1 else MASK^va)
 value=0 if out==-1 else ws[out]
 delta=value^TARGET
 return {'gates':gates,'output':out,'gate_count':len(gates),'not_count':sum(g[0]==2 for g in gates),'errors':delta.bit_count(),'first_errors':[x for x in range(1<<N) if delta>>x&1][:10],'source':str(Path(path)),'sha256':hashlib.sha256(Path(path).read_bytes()).hexdigest()}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('blif');ap.add_argument('--out');args=ap.parse_args()
 result=translate(args.blif)
 if args.out:Path(args.out).write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({k:v for k,v in result.items() if k!='gates'},indent=2))
 if result['errors']:raise SystemExit(1)
if __name__=='__main__':main()
