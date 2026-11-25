from pathlib import Path
import sympy as s,resource,signal,time,json,importlib.util
job=Path('/tmp/oec/pequalnp-pilot-79');resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3));resource.setrlimit(resource.RLIMIT_CPU,(120,120));signal.signal(signal.SIGALRM,lambda a,b: (_ for _ in ()).throw(TimeoutError('120-second limit')));signal.alarm(120)
start=time.monotonic();meta={'classification':'Exact symbolic CAS exploration; not Lean checked','memory_limit_bytes':1024**3}
try:
 spec=importlib.util.spec_from_file_location('ng',job/'neogb-run-rational.py');ng=importlib.util.module_from_spec(spec);spec.loader.exec_module(ng)
 names,prime,polys=ng.parse_input(job/'centered-two-eliminated-rational.msolve');assert prime==0
 variables=s.symbols(' '.join(names));h=variables[-1];pars=variables[:-1]
 exprs=[sum(s.Rational(c.numerator,c.denominator)*s.prod(v**e for v,e in zip(variables,m)) for m,c in p.items()) for p in polys]
 exprs=[s.expand(p.subs(h,s.sqrt(-2))) for p in exprs];exprs=[p for p in exprs if p!=0]
 print(json.dumps({'stage':'start','variables':len(pars),'equations':len(exprs),'domain':'QQ(sqrt(-2))'}),flush=True)
 gb=s.groebner(exprs,*pars,domain=s.QQ.algebraic_field(s.sqrt(-2)),order='grevlex',method='f5b')
 (job/'centered-two-algebraic-basis.txt').write_text('CAS computation, not Lean checked.\n'+str(gb)+'\n')
 meta.update({'outcome':'completed','unit_ideal':list(gb)==[1],'basis_size':len(gb)})
except (TimeoutError,MemoryError) as exc:
 meta.update({'outcome':type(exc).__name__})
finally:
 meta['seconds']=time.monotonic()-start;(job/'centered-two-algebraic-run.json').write_text(json.dumps(meta,indent=2)+'\n');print(json.dumps(meta),flush=True)
