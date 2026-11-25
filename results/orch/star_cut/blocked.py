"""Run the existing exact normalized model with checked necessary local cuts."""
import normalized
from blocking_cuts import add_blocking

original_make=normalized.make

def make(prefix,samples,tail_size):
    c,schema=original_make(prefix,samples,tail_size)
    stats=add_blocking(c,schema,prefix)
    print('BLOCKING_CUTS',stats,flush=True)
    return c,schema

if __name__=='__main__':
    normalized.make=make
    normalized.main()
