/* Exact ideal-membership trace support. Included after neogb data.c.
 * The row arithmetic remains untrusted: replay checks every polynomial identity.
 * This adapter is restricted to serial characteristic-zero option-2 runs. */
#include <inttypes.h>
#include <string.h>

typedef struct { uintptr_t *keys; uint64_t *values; size_t cap, used; } ct_map;
static ct_map ct_nodes = {0}, ct_coeff_rows = {0};
static FILE *ct_log = NULL;
static uint64_t ct_next = 0;
static int ct_nvars = 0;
static bs_t *ct_basis = NULL;

static void ct_fail(const char *message) {
    fprintf(stderr, "CERTIFICATE TRACE ERROR: %s\n", message);
    abort();
}
static size_t ct_hash(uintptr_t key, size_t cap) {
    uint64_t x = (uint64_t)key;
    x ^= x >> 33; x *= UINT64_C(0xff51afd7ed558ccd);
    x ^= x >> 33; x *= UINT64_C(0xc4ceb9fe1a85ec53);
    return (size_t)(x ^ (x >> 33)) & (cap-1);
}
static void ct_put(ct_map *m, const void *pointer, uint64_t value);
static void ct_grow(ct_map *m) {
    ct_map old = *m;
    m->cap = old.cap ? old.cap*2 : 1024;
    m->used = 0;
    m->keys = calloc(m->cap, sizeof(*m->keys));
    m->values = calloc(m->cap, sizeof(*m->values));
    if (!m->keys || !m->values) ct_fail("map allocation");
    for (size_t i=0;i<old.cap;i++)
        if (old.keys[i]) ct_put(m,(const void*)old.keys[i],old.values[i]);
    free(old.keys);free(old.values);
}
static void ct_put(ct_map *m, const void *pointer, uint64_t value) {
    uintptr_t key = (uintptr_t)pointer;
    if (!key) ct_fail("null map key");
    if (!m->cap || (m->used+1)*2 >= m->cap) ct_grow(m);
    size_t i=ct_hash(key,m->cap);
    while (m->keys[i] && m->keys[i]!=key) i=(i+1)&(m->cap-1);
    if (!m->keys[i]) { m->keys[i]=key; m->used++; }
    m->values[i]=value;
}
static uint64_t ct_get(const ct_map *m, const void *pointer) {
    if (!m->cap || !pointer) ct_fail("missing map key");
    uintptr_t key=(uintptr_t)pointer;
    size_t i=ct_hash(key,m->cap);
    while (m->keys[i] && m->keys[i]!=key) i=(i+1)&(m->cap-1);
    if (!m->keys[i]) ct_fail("untracked row or coefficient array");
    return m->values[i];
}
static void ct_bind(const void *target,const void *source) {
    if (ct_log) ct_put(&ct_nodes,target,ct_get(&ct_nodes,source));
}
static void ct_scale(const void *row,mpz_srcptr numerator,mpz_srcptr denominator) {
    if (!ct_log || mpz_cmp(numerator,denominator)==0) return;
    if (!mpz_sgn(numerator) || !mpz_sgn(denominator)) ct_fail("zero scale");
    uint64_t old=ct_get(&ct_nodes,row),id=++ct_next;
    fprintf(ct_log,"S\t%"PRIu64"\t%"PRIu64"\t",id,old);
    mpq_t q;mpq_init(q);mpz_set(mpq_numref(q),numerator);mpz_set(mpq_denref(q),denominator);mpq_canonicalize(q);
    gmp_fprintf(ct_log,"%Qd\n",q);mpq_clear(q);
    ct_put(&ct_nodes,row,id);
}
static void ct_reduce(const void *target,const void *pivot,mpz_srcptr u,mpz_srcptr v,int divisible) {
    if (!ct_log) return;
    mpz_t one;mpz_init_set_ui(one,1);
    if (!divisible) ct_scale(target,u,one);
    mpz_clear(one);
    uint64_t left=ct_get(&ct_nodes,target),right=ct_get(&ct_nodes,pivot),id=++ct_next;
    fprintf(ct_log,"A\t%"PRIu64"\t%"PRIu64"\t%"PRIu64"\t",id,left,right);
    mpz_t negative;mpz_init(negative);mpz_neg(negative,v);gmp_fprintf(ct_log,"%Zd\n",negative);mpz_clear(negative);
    ct_put(&ct_nodes,target,id);
}
static void ct_print_poly(const hm_t *row,mpz_t *coefficients,const ht_t *ht) {
    for (len_t i=0;i<row[LENGTH];i++) {
        if (i) fputs(" + ",ct_log);
        gmp_fprintf(ct_log,"(%Zd*",coefficients[i]);
        const exp_t *exps=ht->ev[row[OFFSET+i]];
        int variable=0,printed=0;
        for (len_t j=1;j<ht->evl;j++) {
            if (j==ht->ebl) continue;
            if (exps[j]) {
                if (printed++) fputc('*',ct_log);
                fprintf(ct_log,"x%d^%u",variable,(unsigned)exps[j]);
            }
            variable++;
        }
        if (variable!=ct_nvars) ct_fail("exponent-vector dimension");
        if (!printed) fputc('1',ct_log);
        fputc(')',ct_log);
    }
    fputc('\n',ct_log);
}
static void ct_seed(hm_t *row,const ht_t *ht) {
    if (!ct_log) return;
    if (!ct_basis) ct_fail("basis unavailable");
    uint64_t id=++ct_next;ct_put(&ct_nodes,row,id);
    fprintf(ct_log,"I\t%"PRIu64"\t",id);
    ct_print_poly(row,ct_basis->cf_qq[row[COEFFS]],ht);
}
static void ct_output(hm_t *row,mpz_t *coefficients,const ht_t *ht) {
    if (!ct_log) return;
    fprintf(ct_log,"O\t%"PRIu64"\t",ct_get(&ct_nodes,row));
    ct_print_poly(row,coefficients,ht);fflush(ct_log);
}
static void ct_initialize_basis(bs_t *bs) {
    if (!ct_log) return;
    ct_basis=bs;
    for (len_t i=0;i<bs->ld;i++) {
        ct_seed(bs->hm[i],bs->ht);
        ct_output(bs->hm[i],bs->cf_qq[bs->hm[i][COEFFS]],bs->ht);
    }
}
void cert_trace_open(const char *path,int nvars) {
    ct_log=fopen(path,"w");if (!ct_log) ct_fail("cannot open trace");
    ct_nvars=nvars;
}
void cert_trace_generator(int index,int length,const int32_t *exps,mpz_t *rational) {
    fprintf(ct_log,"G\t%d\t",index);
    for (int i=0;i<length;i++) {
        if (i) fputs(" + ",ct_log);
        gmp_fprintf(ct_log,"(%Zd/%Zd*",rational[2*i],rational[2*i+1]);
        int printed=0;
        for (int j=0;j<ct_nvars;j++) if (exps[i*ct_nvars+j]) {
            if (printed++) fputc('*',ct_log);
            fprintf(ct_log,"x%d^%d",j,exps[i*ct_nvars+j]);
        }
        if (!printed) fputc('1',ct_log);
        fputc(')',ct_log);
    }
    fputc('\n',ct_log);fflush(ct_log);
}
