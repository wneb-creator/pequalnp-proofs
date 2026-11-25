import normalized
from blocking_cuts_compact import add_blocking_compact

original_make=normalized.make

def make(prefix,samples,tail_size):
    c,schema=original_make(prefix,samples,tail_size)
    stats=add_blocking_compact(c,schema,prefix)
    print('BLOCKING_CUTS_COMPACT',stats,flush=True)
    return c,schema

if __name__=='__main__':
    normalized.make=make
    normalized.main()
