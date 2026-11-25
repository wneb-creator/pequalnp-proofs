from pathlib import Path
b=Path(__file__).parent
s=(b/'cert_trace_compact.c').read_text()
marker='static void ct_print_poly(const hm_t *row,mpz_t *coefficients,const ht_t *ht) {'
helper='''/* Divide the entire logical row by its positive content. Earlier consumed
 * dense entries are intentionally excluded: their columns have already been
 * eliminated. Retained cf entries are part of the row and must be included. */
static void ct_primitive_dense_row(mpz_t *dense,mpz_t *retained,len_t retained_count,
                                   hi_t first,hi_t end) {
    mpz_t content;
    mpz_init_set_ui(content,0);
    for (len_t j=0;j<retained_count && mpz_cmp_ui(content,1)!=0;j++) {
        if (mpz_sgn(retained[j])) mpz_gcd(content,content,retained[j]);
    }
    for (hi_t j=first;j<end && mpz_cmp_ui(content,1)!=0;j++) {
        if (mpz_sgn(dense[j])) mpz_gcd(content,content,dense[j]);
    }
    if (mpz_cmp_ui(content,1)>0) {
        for (len_t j=0;j<retained_count;j++) mpz_divexact(retained[j],retained[j],content);
        for (hi_t j=first;j<end;j++) {
            if (mpz_sgn(dense[j])) mpz_divexact(dense[j],dense[j],content);
        }
        mpz_t one;mpz_init_set_ui(one,1);
        ct_scale(dense,one,content);
        mpz_clear(one);
    }
    mpz_clear(content);
}
'''
assert s.count(marker)==1;s=s.replace(marker,helper+marker)
(b/'cert_trace_primitive.c').write_text(s)
s=(b/'make_cert_trace_compact.py').read_text().replace("dst=base/'certificate-trace-compact'","dst=base/'certificate-trace-primitive'").replace("base/'cert_trace_compact.c'","base/'cert_trace_primitive.c'")
marker="edit('la_qq.c',row_hooks)"
addition='''
def primitive_hook(s):
    begin=s.index('static hm_t *reduce_dense_row_by_known_pivots_sparse_qq(')
    end=s.index('static void exact_sparse_reduced_echelon_form_ab_first_qq(',begin)
    part=s[begin:end]
    part=once(part,'    int64_t np  = -1;','    int64_t np  = -1;\\n    unsigned ct_reductions=0;')
    old='''+repr('''            mpz_submul(dr[ds[j+3]], mul2, cfs[j+3]);
        }
    }
    if (rlen != 0) {''')+'''
    new='''+repr('''            mpz_submul(dr[ds[j+3]], mul2, cfs[j+3]);
        }
        if (++ct_reductions % 8 == 0) ct_primitive_dense_row(dr,cf,rlen,i+1,ncols);
    }
    if (rlen != 0) {''')+'''
    part=once(part,old,new)
    return s[:begin]+part+s[end:]
edit('la_qq.c',primitive_hook)
'''
assert s.count(marker)==1;s=s.replace(marker,marker+'\n'+addition)
(b/'make_cert_trace_primitive.py').write_text(s)
s=(b/'run_neogb_trace_compact.py').read_text().replace("base/'certificate-trace-compact/neogb_cli_trace'","base/'certificate-trace-primitive/neogb_cli_trace'")
(b/'run_neogb_trace_primitive.py').write_text(s)
