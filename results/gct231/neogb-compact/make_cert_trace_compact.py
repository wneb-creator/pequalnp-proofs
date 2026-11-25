"""Create a separate serial QQ neogb trace tree; never mutate tested engines."""
from pathlib import Path
import hashlib
import shutil

base=Path(__file__).parent
vendor=base/'msolve'
dst=base/'certificate-trace-compact'
dst.mkdir(exist_ok=True)
shutil.copytree(vendor/'src',dst/'src',dirs_exist_ok=True,
                ignore=shutil.ignore_patterns('*.o','*.so','*.a'))
engine=dst/'src/neogb'
for name in ('gb.c','la_qq.c'):shutil.copy2(base/'qqfix'/name,engine/name)
shutil.copy2(base/'cert_trace_compact.c',engine/'cert_trace.c')

def once(text,old,new):
    assert text.count(old)==1,(old,text.count(old))
    return text.replace(old,new)
def edit(name,change):
    p=engine/name;p.write_text(change(p.read_text()))

edit('gb.c',lambda s:once(s,'#include "data.c"','#include "data.c"\n#include "cert_trace.c"'))
edit('engine.c',lambda s:once(s,'    *bsp  = bs;','    ct_initialize_basis(bs);\n    *bsp  = bs;'))

def hash_hooks(s):
    s=once(s,'  insert_poly_in_hash_table(row, poly, bht, sht);',
           '  insert_poly_in_hash_table(row, poly, bht, sht);\n  ct_seed(row,sht);')
    return once(s,'  insert_multiplied_poly_in_hash_table(row, hm, em, poly, bht, sht);',
                '  insert_multiplied_poly_in_hash_table(row, hm, em, poly, bht, sht);\n  ct_seed(row,sht);')
edit('hash.c',hash_hooks)

def row_hooks(s):
    begin=s.index('static inline mpz_t *remove_content_of_sparse_matrix_row_qq(')
    end=s.index('static hm_t *reduce_dense_row_by_known_pivots_sparse_only_ab_qq(',begin)
    part=s[begin:end]
    part=once(part,'    len_t i;','    mpz_t ct_before;\n    if (ct_log) mpz_init_set(ct_before,row[0]);\n    len_t i;')
    part=once(part,'    return row;','''    if (ct_log) {
        const void *ct_row=(const void*)(uintptr_t)ct_get(&ct_coeff_rows,row);
        ct_scale(ct_row,row[0],ct_before);
        mpz_clear(ct_before);
    }
    return row;''')
    s=s[:begin]+part+s[end:]

    begin=s.index('static hm_t *reduce_dense_row_by_known_pivots_sparse_qq(')
    end=s.index('static void exact_sparse_reduced_echelon_form_ab_first_qq(',begin)
    part=s[begin:end]
    part=once(part,'        if (mpz_divisible_p(dr[i], cfs[0]) != 0) {',
              '        const int ct_divisible=mpz_divisible_p(dr[i], cfs[0]) != 0;\n        if (ct_divisible) {')
    part=once(part,'        for (j = 0; j < os; ++j) {\n            mpz_submul',
              '        ct_reduce(dr,dts,mul1,mul2,ct_divisible);\n        for (j = 0; j < os; ++j) {\n            mpz_submul')
    part=once(part,'        mat->cf_qq[tmp_pos]  = cf;',
              '''        mat->cf_qq[tmp_pos]  = cf;
        if (ct_log) {
            ct_bind(row,dr);
            ct_put(&ct_coeff_rows,cf,(uint64_t)(uintptr_t)row);
        }''')
    s=s[:begin]+part+s[end:]

    begin=s.index('static void exact_sparse_reduced_echelon_form_qq(')
    end=s.index('static void exact_sparse_linear_algebra_ab_first_qq(',begin)
    part=s[begin:end]
    part=once(part,'            free(npiv);\n            npiv  = reduce_dense_row_by_known_pivots_sparse_qq(',
              '            ct_bind(drl,npiv);\n            free(npiv);\n            npiv  = reduce_dense_row_by_known_pivots_sparse_qq(')
    part=once(part,'            free(pivs[k]);','            ct_bind(dr,pivs[k]);\n            free(pivs[k]);')
    s=s[:begin]+part+s[end:]

    begin=s.index('static void interreduce_matrix_rows_qq(')
    part=s[begin:]
    part=once(part,'            free(pivs[l]);','            ct_bind(dr,pivs[l]);\n            free(pivs[l]);')
    return s[:begin]+part
edit('la_qq.c',row_hooks)

def conversion_hook(s):
    begin=s.index('static void convert_sparse_matrix_rows_to_basis_elements(')
    end=s.find('\nstatic ',begin+10)
    if end<0:end=len(s)
    part=once(s[begin:end],'        bs->hm[bl+k][DEG] = deg;',
        '        bs->hm[bl+k][DEG] = deg;\n        if (ct_log) ct_output(bs->hm[bl+k],bs->cf_qq[bl+k],bht);')
    return s[:begin]+part+s[end:]
edit('convert.c',conversion_hook)

wrapper=(base/'neogb_cli.c').read_text()
wrapper=once(wrapper,'#include "msolve/src/neogb/f4.h"',
             '#include "src/neogb/f4.h"\nvoid cert_trace_open(const char*,int);\nvoid cert_trace_generator(int,int,const int32_t*,mpz_t*);')
wrapper=wrapper.replace('argc != 3 && argc != 4','argc != 4 && argc != 5')
wrapper=once(wrapper,'usage: neogb_cli INPUT OUTPUT_JSON [MAX_PAIRS]',
             'usage: neogb_cli_trace INPUT OUTPUT_JSON TRACE [MAX_PAIRS]')
wrapper=once(wrapper,'    if (argc == 4) {','    if (argc == 5) {')
wrapper=once(wrapper,'strtol(argv[3], &end, 10)','strtol(argv[4], &end, 10)')
wrapper=once(wrapper,'    fclose(in);','''    fclose(in);
    if (p != 0) fail("certificate adapter supports characteristic zero only");
    cert_trace_open(argv[3],n);
    int ct_offset=0;
    for (int ct_i=0;ct_i<m;ct_i++) {
        cert_trace_generator(ct_i,lens[ct_i],exps+(size_t)ct_offset*n,rational+2*ct_offset);
        ct_offset+=lens[ct_i];
    }''')
(dst/'neogb_cli_trace.c').write_text(wrapper)
for name in ('cert_trace.c','gb.c','engine.c','hash.c','la_qq.c','convert.c'):
    path=engine/name
    print(hashlib.sha256(path.read_bytes()).hexdigest(),path)
