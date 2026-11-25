"""Carry previously completed false suffix states between bounded five-point search chunks."""
import json,os,sys,struct
from pathlib import Path
import fresh_meta3773_five_sixteen as core
m=core.model;d=core.driver;job=Path(__file__).resolve().parent;cfg,mask,dup=map(int,sys.argv[1:4]);assert cfg==m.cfg
# Separate by stratum. Every key includes the full primitive truth tables and branch history.
cache_path=job/f'fresh-meta3773-five-{cfg}-{mask}-{dup}-deadstates.bin'
def encode(F,R,C,h):
 return struct.pack('<BBBBH',len(F),len(C),h,0,R)+struct.pack('<'+'Q'*len(F),*F)+struct.pack('<'+'H'*len(C),*C)
known=set(); valid=0
if cache_path.exists():
 with cache_path.open('rb')as inp:
  while True:
   header=inp.read(2)
   if len(header)!=2:break
   sz=struct.unpack('<H',header)[0];key=inp.read(sz)
   if len(key)!=sz:break
   known.add(key);valid+=sz+2
 # An interrupted append can only have left a trailing partial record.
 if valid!=cache_path.stat().st_size:
  with cache_path.open('r+b')as inp:inp.truncate(valid)
base=d.search;out=cache_path.open('ab',buffering=0)
def search(F,R,C,h):
 if not h or (F,R,C,h)==d.root_state:return base(F,R,C,h)
 key=encode(F,R,C,h)
 if key in known:return False
 ans=base(F,R,C,h)
 if not ans:
  record=struct.pack('<H',len(key))+key
  if out.write(record)!=len(record):raise OSError('Incomplete suffix-checkpoint write')
  known.add(key)
 return ans
d.search=search
print('model',m.data['points'],'rows',m.NP,len(m.N),'group',len(d.rpi),'prior completed suffix states',len(known),flush=True);print(d.run(mask,dup),flush=True)
