import os
from pathlib import Path
import resource
import signal
import subprocess
import sys
import time

source, log, *extra = sys.argv[1:]
command = ['lake', 'env', 'lean', '--profile']
if extra:
    assert len(extra) == 1
    command += ['-R', str(Path(source).parent), '-o', extra[0]]
command += [source]
limit = int(7.3 * 1024**3)
started = time.monotonic()
peak_cgroup = 0
stopped = False
with Path(log).open('w') as output:
    child = subprocess.Popen(command, stdout=output,
                             stderr=subprocess.STDOUT, start_new_session=True)
    while child.poll() is None:
        usage = int(Path('/sys/fs/cgroup/memory.current').read_text())
        peak_cgroup = max(peak_cgroup, usage)
        if usage >= limit:
            output.write('RESOURCE_STOP cgroup_memory_bytes=' + str(usage) + '\n')
            output.flush()
            os.killpg(child.pid, signal.SIGINT)
            stopped = True
            try:
                child.wait(timeout=5)
            except subprocess.TimeoutExpired:
                os.killpg(child.pid, signal.SIGTERM)
                try:
                    child.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    os.killpg(child.pid, signal.SIGKILL)
                    child.wait()
            break
        time.sleep(0.5)
    result = child.wait()
    usage = resource.getrusage(resource.RUSAGE_CHILDREN)
    output.write('\nEXIT ' + str(result) + '\n')
    output.write('RESOURCE_STOPPED ' + str(stopped) + '\n')
    output.write('WALL_SECONDS ' + str(time.monotonic()-started) + '\n')
    output.write('USER_SECONDS ' + str(usage.ru_utime) + '\n')
    output.write('SYS_SECONDS ' + str(usage.ru_stime) + '\n')
    output.write('PEAK_RSS_KIB ' + str(usage.ru_maxrss) + '\n')
    output.write('PEAK_CGROUP_BYTES ' + str(peak_cgroup) + '\n')
sys.exit(result if result >= 0 else 128-result)
