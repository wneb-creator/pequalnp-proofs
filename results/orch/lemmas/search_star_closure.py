import importlib.util
from pathlib import Path
from itertools import combinations_with_replacement

sp=importlib.util.spec_from_file_location('star',str(Path(__file__).with_name('search_star.py')))
star=importlib.util.module_from_spec(sp);sp.loader.exec_module(star)
FULL=(1<<12)-1
BASE=frozenset([0]+[(1<<(i+1))|(1<<11) for i in range(10)])

def products(state):
    out={FULL^a for a in state}
    for a,b in combinations_with_replacement(state,2):
        out.add(a&b);out.add(a|b)
    return out-state

def close(state,targets):
    while True:
        ns=products(state)&targets
        if not ns:return state
        state=state|ns

def search(groups):
    targets=frozenset([(1<<11)|sum(1<<(i+1) for i in group) for group in groups])
    start=close(BASE,targets)
    frontier={start};counts=[]
    for depth in range(3):
        counts.append(len(frontier))
        for state in frontier:
            if targets<=state:return True,counts
        if depth<2:
            frontier={close(state|{v},targets) for state in frontier for v in products(state)-targets}
    return False,counts

if __name__=='__main__':
    for i in range(8):print(i,search(star.family(i)),flush=True)
