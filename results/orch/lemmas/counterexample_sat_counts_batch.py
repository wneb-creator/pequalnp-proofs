import sys
sys.dont_write_bytecode=True
import json
from counterexample_sat_counts import solve
for max_and,max_or in [(None,4),(2,None)]:
 print(json.dumps({'starting':{'N':3,'mask':427,'gates':10,'max_and':max_and,'max_or':max_or}}),flush=True)
 print(json.dumps(solve(3,427,10,False,60,max_and,max_or)),flush=True)
