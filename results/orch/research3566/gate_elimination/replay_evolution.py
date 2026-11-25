import importlib.util,json,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent
combined='--combined' in sys.argv
if combined:sys.argv.remove('--combined')
name='evolve_combined' if combined else 'evolve_amplification'
spec=importlib.util.spec_from_file_location(name,HERE/(name+'.py'));module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
engine=module.ea if combined else module
seeds=json.loads((HERE/'evolution-search-seeds.json').read_text())['combined' if combined else 'helper']
engine.load_seeds=lambda:[tuple(tuple(g) for g in circuit) for circuit in seeds]
engine.main()
