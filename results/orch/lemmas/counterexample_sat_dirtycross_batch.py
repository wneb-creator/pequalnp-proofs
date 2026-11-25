import sys
sys.dont_write_bytecode=True
import json
from counterexample_sat_dirtycross import solve
for N,mask,k,timeout in [(2,7,4,10),(3,417,6,30),(3,426,7,30),(3,427,8,60)]:
 print(json.dumps({'starting':{'N':N,'mask':mask,'known_minimum':k}}),flush=True)
 print(json.dumps(solve(N,mask,k,False,timeout)),flush=True)
