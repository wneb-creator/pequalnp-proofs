from pathlib import Path
exec(open(str(Path(__file__).with_name('projection.py'))).read().split('rows7=')[0])
A=[0,3,9];B=[2,4,10];S=sum(1<<p for p in A+B); T=ALL^((1<<5)|(1<<11)); projected={(P&S,W&T) for P,W in rows}
edges={(p,w) for p in A+B for w in range(13) if T>>w&1 and(p-w)%13 in D}
maxfalse=set()
sub=S
while True:
 W=nonneighbors(sub)&T
 P=sum(1<<p for p in A+B if not pencils[p]&W)
 if P==sub:maxfalse.add((P,W))
 if not sub:break
 sub=(sub-1)&S
pt=[t for t in coltrip if t&S==t];wt=[t for t in conctrip if t&T==t]
report={'point_input_count':S.bit_count(),'line_input_count':T.bit_count(),'edge_count':len(edges),'projected_generic_negatives':len(projected),'max_false_of_induced_edge_graph':len(maxfalse),'missing_max_false':len(maxfalse-projected),'collinear_point_triples':[[i for i in range(13) if t>>i&1]for t in pt],'concurrent_line_triple_count':len(wt),'sizes':sorted({(P.bit_count(),W.bit_count())for P,W in projected})}
print(json.dumps(report,indent=2));Path(__file__).with_name('grid-check-result.json').write_text(json.dumps(report,indent=2))
