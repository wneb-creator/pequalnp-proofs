import resource,subprocess,sys,time
from pathlib import Path
source,log=sys.argv[1:]
start=time.monotonic()
with Path(log).open('w') as output:
 result=subprocess.run(['lake','env','lean',source],stdout=output,stderr=subprocess.STDOUT)
 usage=resource.getrusage(resource.RUSAGE_CHILDREN)
 output.write('\nEXIT '+str(result.returncode)+'\n')
 output.write('WALL_SECONDS '+str(time.monotonic()-start)+'\n')
 output.write('USER_SECONDS '+str(usage.ru_utime)+'\n')
 output.write('SYS_SECONDS '+str(usage.ru_stime)+'\n')
 output.write('PEAK_RSS_KIB '+str(usage.ru_maxrss)+'\n')
sys.exit(result.returncode)
