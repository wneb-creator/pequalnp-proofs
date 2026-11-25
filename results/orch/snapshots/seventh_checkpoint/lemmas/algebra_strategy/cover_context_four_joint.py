"""Bounded bilinear-cover optimization with jointly selected outside prefixes.

The objective is paid core gates plus the exact extra outside-prefix cost.
This is a finite heuristic family, not a lower bound for arbitrary circuits.
"""
import itertools,json,argparse
from pathlib import Path
import numpy as np
from scipy.optimize import milp,Bounds,LinearConstraint
from scipy.sparse import coo_matrix

parser=argparse.ArgumentParser()
parser.add_argument('--all-edges',action='store_true')
parser.add_argument('--seconds',type=float,default=5)
parser.add_argument('--min-errors',action='store_true')
args=parser.parse_args()
HERE=Path(__file__).resolve().parent
case=json.loads((HERE.parent/'circuit_search/context-four-owner-packet.json').read_text())[0]
raw=case['input_original']
desired=set(map(tuple,case['edges']))
bad={(1,5),(3,5),(1,6),(0,8),(1,10)}
allowed=desired|bad
features=[]
groups=[]
for p in range(13):
    if p in case['group']:continue
    support=tuple(i for i in range(4,14) if (p+raw[i]-13)%13 in (0,1,3,9))
    assert len(support) in (2,3)
    if len(support)==2:
        features.append({'support':support,'owner':p,'optional':False})
    else:
        group=[]
        for pair in itertools.combinations(support,2):
            group.append(len(features))
            features.append({'support':pair,'owner':p,'optional':True})
        features.append({'support':support,'owner':p,'optional':False})
        groups.append(group)
assert len(features)==27 and len(groups)==6
chunks=[(i,) for i in range(4,14)]+[x['support'] for x in features]
rect=[]
for rmask in range(1,16):
    rows=[p for p in range(4) if rmask>>p&1]
    common=sorted(set.intersection(*[{l for p,l in allowed if p==r} for r in rows]))
    for cmask in range(1,1<<len(common)):
        lines=[l for j,l in enumerate(common) if cmask>>j&1]
        options=[j for j,s in enumerate(chunks) if set(s)<=set(lines)]
        rect.append((rows,lines,{(p,l) for p in rows for l in lines},options))

# x chooses rectangles; z chooses their overlapping OR chunks; y records use
# of optional features; t pays every optional pair beyond the first per owner.
cost=[float(len(r[0])) for r in rect]
z={}
for i,r in enumerate(rect):
    for j in r[3]:z[i,j]=len(cost);cost.append(1.)
y={}
for j,f in enumerate(features):
    if f['optional']:y[j]=len(cost);cost.append(0.)
t=[]
for group in groups:t.append(len(cost));cost.append(1.)
rr=[];cc=[];vv=[];lo=[];hi=[]
def constraint(items,lower=-np.inf,upper=np.inf):
    row=len(lo)
    for col,val in items:rr.append(row);cc.append(col);vv.append(val)
    lo.append(lower);hi.append(upper)
for edge in sorted(allowed if args.all_edges else desired):
    constraint([(i,1) for i,r in enumerate(rect) if edge in r[2]],lower=1)
for i,r in enumerate(rect):
    for line in r[1]:
        constraint([(z[i,j],1) for j in r[3] if line in chunks[j]]+[(i,-1)],lower=0)
    for j in r[3]:
        constraint([(z[i,j],1),(i,-1)],upper=0)
        if j>=10 and j-10 in y:
            constraint([(z[i,j],1),(y[j-10],-1)],upper=0)
for k,group in enumerate(groups):
    constraint([(y[j],1) for j in group]+[(t[k],-1)],upper=1)
for rows in {tuple(r[0]) for r in rect}:
    constraint([(i,1) for i,r in enumerate(rect) if tuple(r[0])==rows],upper=1)
gate_cost=cost[:]
false_masks=[]
if args.min_errors:
    constraint([(i,x) for i,x in enumerate(gate_cost) if x],upper=19)
    cost=[x*0.00001 for x in cost]
    for mask in range(1<<14):
        if any(mask>>p&1 and mask>>l&1 for p,l in desired):continue
        if not any(mask>>p&1 and mask>>l&1 for p,l in bad):continue
        false_masks.append(mask)
        yfalse=len(cost);cost.append(1.)
        for i,r in enumerate(rect):
            if any(mask>>p&1 for p in r[0]) and any(mask>>l&1 for l in r[1]):
                constraint([(i,1),(yfalse,-1)],upper=0)
upper=np.ones(len(cost))
for i in t:upper[i]=2
A=coo_matrix((vv,(rr,cc)),shape=(len(lo),len(cost))).tocsc()
result=milp(np.array(cost),integrality=np.ones(len(cost)),bounds=Bounds(np.zeros(len(cost)),upper),
 constraints=LinearConstraint(A,np.array(lo),np.array(hi)),
 options={'time_limit':args.seconds,'mip_rel_gap':0.,'disp':True})
out={'status':int(result.status),'message':result.message,'family':'bilinear rectangle cover with shared free-prefix choices',
     'all_augmented_edges_required':args.all_edges,'rectangles_considered':len(rect),'features':features,'groups':groups,
     'desired_target_edges':[list(e) for e in sorted(desired)],
     'allowed_extra_edges':[list(e) for e in sorted(bad)],
     'optimization_scope':('The fixed incorrect 21-edge augmented function, within this rectangle/chunk family only.'
        if args.all_edges else 'A relaxation: cover all16 target edges while optionally accepting any of five specified nonedges. Optimum does not establish an exact target circuit.'),
     'arbitrary_circuit_lower_bound':False,
     'objective_mode':'false assignments subject to core plus prefix cost at most18' if args.min_errors else 'minimum core plus prefix cost'}
if result.x is not None:
    out['core_plus_extra_objective']=float(sum(x*y for x,y in zip(gate_cost,result.x)))-1
    out['solver_objective']=float(result.fun)
    out['solver_dual_bound']=float(result.mip_dual_bound)
    out['selected_rectangles']=[{'rows':r[0],'lines':r[1],
        'chunks':[{'support':chunks[j],'feature':None if j<10 else j-10}
                  for j in r[3] if result.x[z[i,j]]>.5]}
        for i,r in enumerate(rect) if result.x[i]>.5]
    out['selected_optional_features']=[j for j,k in y.items() if result.x[k]>.5]
    out['extra_prefix_cost']=sum(round(result.x[k]) for k in t)
    achieved=set().union(*(rect[i][2] for i in range(len(rect)) if result.x[i]>.5))
    out['achieved_edges']=[list(e) for e in sorted(achieved)]
    out['achieved_extra_edges']=[list(e) for e in sorted(achieved-desired)]
    out['achieved_exact_target']=achieved==desired
    out['achieved_false_assignments']=sum(any(mask>>p&1 and mask>>l&1 for p,l in achieved) for mask in false_masks) if args.min_errors else None
tag='context-four-cover-joint-'+('errors' if args.min_errors else 'all21' if args.all_edges else 'subset')
(HERE/(tag+'.json')).write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
