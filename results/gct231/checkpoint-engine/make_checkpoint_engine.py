"""Create an isolated finite-field native engine with periodic atomic snapshots."""
from pathlib import Path
import hashlib
import shutil

base=Path(__file__).parent
target=base/'checkpoint'
engine=target/'engine'
engine.mkdir(parents=True,exist_ok=True)
for name in ['gb.c','la_qq.c','convert.c']:
    shutil.copy2(base/'native/engine'/name,engine/name)
shutil.copy2(base/'msolve/src/neogb/f4.c',engine/'f4.c')
shutil.copy2(base/'checkpoint_basis.c',engine/'checkpoint_basis.c')
def once(text,old,new):
    assert text.count(old)==1,(old,text.count(old))
    return text.replace(old,new)
path=engine/'gb.c'
text=once(path.read_text(),'#include "f4.c"','#include "checkpoint_basis.c"\n#include "f4.c"')
path.write_text(text)
path=engine/'f4.c';text=path.read_text()
text=once(text,'    done = initialize_f4(&bs, &md, &mat, gmd, gbs, fc);',
    '    done = initialize_f4(&bs, &md, &mat, gmd, gbs, fc);\n'
    '    uint64_t pnp_round = 0;\n'
    '    pnp_checkpoint_snapshot(bs,md,pnp_round,1);')
text=once(text,'        print_round_timings(VERBSTREAM, md, rrt, crt);',
    '        print_round_timings(VERBSTREAM, md, rrt, crt);\n'
    '        if (*errp == 0) pnp_checkpoint_snapshot(bs,md,++pnp_round,0);')
text=once(text,'        reduce_final_basis(bs, mat, md);',
    '        reduce_final_basis(bs, mat, md);\n'
    '        pnp_checkpoint_snapshot(bs,md,pnp_round,1);')
path.write_text(text)
text=(base/'native/neogb_cli_native.c').read_text()
text=once(text,'#include "f4.h"','#include "f4.h"\n#include <math.h>\n'
    'void pnp_checkpoint_configure(const char*,int,int,int,int,const int32_t*,const int32_t*,const int32_t*,double,uint64_t);')
text=once(text,'if (argc < 3 || argc > 5)','if (argc != 9)')
text=once(text,'[MAX_PAIRS] [THREADS]','MAX_PAIRS THREADS CHECKPOINT_PREFIX INTERVAL_SECONDS STOP_ROUND BASE_GENERATORS')
text=once(text,'if (argc == 5)','if (argc >= 5)')
text=once(text,'    fclose(in);','''    fclose(in);
    if (!p) fail("checkpoint adapter supports finite fields only");
    char *interval_end, *stop_end, *base_end;
    double interval=strtod(argv[6],&interval_end);
    unsigned long long stop=strtoull(argv[7],&stop_end,10);
    long base_generators=strtol(argv[8],&base_end,10);
    if (*interval_end || !isfinite(interval) || interval<0 || interval>3600 ||
        *stop_end || stop>INT_MAX || *base_end || base_generators<1 ||
        base_generators>m) fail("bad checkpoint interval, stop round, or base prefix");
    int base_terms=0;
    for (int j=0;j<base_generators;j++) base_terms+=lens[j];
    pnp_checkpoint_configure(argv[5],n,(int)base_generators,p,base_terms,
        lens,exps,finite,interval,stop);''')
(target/'neogb_cli_checkpoint.c').write_text(text)
for path in [engine/'gb.c',engine/'f4.c',engine/'checkpoint_basis.c',
             engine/'la_qq.c',engine/'convert.c',target/'neogb_cli_checkpoint.c']:
    print(hashlib.sha256(path.read_bytes()).hexdigest(),path)
