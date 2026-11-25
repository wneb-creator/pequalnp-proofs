"""Exploratory signed rectangle weights for the19edge target.

A feasible exact rational weight is a lower bound on the number of leaves
in a monochromatic rectangle partition, hence on monotone formula leaves.
This script does not provide a Lean proof or a circuit lower bound.
"""
import json
from fractions import Fraction
from pathlib import Path
from datetime import datetime, timezone
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix

EDGES = [(p,h) for p,hs in enumerate([[8,10],[7,9,13],[8,13],[7,11,12],[10,11,13],[9,10,12],[8,9,11]]) for h in hs]
edge_masks = [(1 << a) | (1 << b) for a,b in EDGES]
def independent(mask):
    return not any(mask & e == e for e in edge_masks)
negatives = [s for s in range(16384) if independent(s) and all(s & (1 << v) or not independent(s | (1 << v)) for v in range(14))]
assert len(EDGES) == 19
rows, cols = len(EDGES), len(negatives)
weight_count = rows * cols
matrix_rows, matrix_cols, values, rhs = [], [], [], []
var_count = weight_count
families = []
def constraint(entries, bound):
    row = len(rhs)
    for col, value in entries:
        matrix_rows.append(row); matrix_cols.append(col); values.append(value)
    rhs.append(bound)
for v in range(14):
    positive_rows = [i for i,e in enumerate(EDGES) if v in e]
    negative_cols = [j for j,s in enumerate(negatives) if not s & (1 << v)]
    for mask in range(1, 1 << len(positive_rows)):
        subset = [i for k,i in enumerate(positive_rows) if mask & (1 << k)]
        aux = []
        for j in negative_cols:
            y = var_count; var_count += 1; aux.append(y)
            constraint([(i * cols + j, 1) for i in subset] + [(y,-1)], 0)
        constraint([(y,1) for y in aux], 1)
        families.append((v,subset,negative_cols))
def family_weight(weights, family):
    v, subset, js = family
    if v == 'negative0':
        return sum(max(Fraction(0),sum(weights[i*cols+j] for j in subset)) for i in js)
    return sum(max(Fraction(0),sum(weights[i*cols+j] for i in subset)) for j in js)
a = coo_matrix((values,(matrix_rows,matrix_cols)),shape=(len(rhs),var_count)).tocsr()
c = np.zeros(var_count); c[:weight_count] = -1
result = linprog(c,A_ub=a,b_ub=np.array(rhs),bounds=[(None,None)]*weight_count+[(0,None)]*(var_count-weight_count),method='highs')
report = {'utc':datetime.now(timezone.utc).isoformat(),'scope':'monotone formula partition for19edge Fano-minus-two; no circuit lower bound','variables':var_count,'constraints':len(rhs),'status':int(result.status),'message':result.message}
if result.success:
    weights = [Fraction(float(x)).limit_denominator(1000000) for x in result.x[:weight_count]]
    maximum = max(family_weight(weights, family) for family in families)
    scale = max(Fraction(1),maximum)
    weights = [w/scale for w in weights]
    maximum = max(family_weight(weights, family) for family in families)
    assert maximum <= 1
    total = sum(weights)
    report.update(numerical_optimum=-float(result.fun),exact_feasible_weight=str(total),integer_leaf_lower_bound=(total.numerator+total.denominator-1)//total.denominator,maximum_rectangle_weight=str(maximum),negative_masks=negatives,edges=EDGES,weights=[[str(weights[i*cols+j]) for j in range(cols)] for i in range(rows)])
Path('results/orch9775/kw_formula_lp.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in ('weights','negative_masks','edges')},indent=2))
