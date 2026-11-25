from pathlib import Path
import itertools,json
D={0,1,3,9}; ALL=(1<<13)-1
reps=[(7,904),(13,2848),(19,708),(21,2720),(25,2656),(37,2440),(41,2370),(133,808)]
lines=[sum(1<<((w+d)%13) for d in D) for w in range(13)]
pencils=[sum(1<<w for w in range(13) if (p-w)%13 in D) for p in range(13)]
coltrip={sum(1<<i for i in t) for line in lines for t in itertools.combinations([i for i in range(13) if line>>i&1],3)}
conctrip={sum(1<<i for i in t) for pen in pencils for t in itertools.combinations([i for i in range(13) if pen>>i&1],3)}
def cap(x,trip): return not any(x&t==t for t in trip)
pointcaps=[x for x in range(8192) if cap(x,coltrip)]
linecaps=[x for x in range(8192) if cap(x,conctrip)]
def nonneighbors(A): return sum(1<<w for w in range(13) if not A&lines[w])
def row(a,b,m,t,dual):
 if dual: a,b=b,a
 sign=-1 if dual else 1
 return tuple(sum(1<<i for i in range(13) if (mask>>((sign*(m*i+t))%13))&1) for mask in (a,b))
rows={row(a,b,m,t,d) for a,b in reps for m in (1,3,9) for t in range(13) for d in (False,True)}
falsepairs={(A,B) for A in pointcaps for B in linecaps if B&nonneighbors(A)==B}
maxfalse=set()
for A,B in falsepairs:
 if not any((A|(1<<i),B) in falsepairs for i in range(13) if not A>>i&1) and not any((A,B|(1<<i)) in falsepairs for i in range(13) if not B>>i&1): maxfalse.add((A,B))
report={'point_collinear_triples':len(coltrip),'line_concurrent_triples':len(conctrip),'point_caps':len(pointcaps),'line_caps':len(linecaps),'false_inputs_of_envelope':len(falsepairs),'max_false_inputs_of_envelope':len(maxfalse),'generic_rows':len(rows),'max_false_equals_generic_rows':maxfalse==rows,'generic_row_sizes':sorted({(A.bit_count(),B.bit_count()) for A,B in rows}),'max_false_missing_from_generic':sorted(maxfalse-rows),'generic_missing_from_max_false':sorted(rows-maxfalse)}
assert maxfalse==rows
assert len(coltrip)==len(conctrip)==52
print(json.dumps(report,indent=2))
Path(__file__).with_name('envelope-result.json').write_text(json.dumps(report,indent=2))
