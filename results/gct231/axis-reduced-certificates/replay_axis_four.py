from pathlib import Path
import argparse,resource,runpy,sys
p=argparse.ArgumentParser();p.add_argument('case',choices=['equal','different']);a=p.parse_args()
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
sys.set_int_max_str_digits(0)
here=Path(__file__).parent;base=here.parent;stem='axis-four-'+a.case
sys.argv=[str(base/'replay_neogb_compact.py'),str(here/(stem+'-trace.f4.in')),
          str(here/(stem+'-trace.trace')),str(here/(stem+'-certificate.json'))]
runpy.run_path(sys.argv[0],run_name='__main__')
