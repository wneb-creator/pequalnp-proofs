#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <limits.h>
#include <gmp.h>
#include "msolve/src/neogb/f4.h"

static void fail(const char *s) { fprintf(stderr, "%s\n", s); exit(2); }

int main(int argc, char **argv) {
    if (argc != 3 && argc != 4) {
        fprintf(stderr, "usage: neogb_cli INPUT OUTPUT_JSON [MAX_PAIRS]\n");
        return 2;
    }
    FILE *in = fopen(argv[1], "r");
    if (!in) fail("cannot open input");
    int n, m, p, terms;
    if (fscanf(in, "%d %d %d %d", &n, &m, &p, &terms) != 4)
        fail("bad header: expected nvars ngens characteristic nterms");
    if (n < 1 || n > 1000 || m < 1 || m > 100000 || terms < 1 ||
        terms > 10000000 || p < 0 || p == 1)
        fail("unsupported header bounds");
    int pairs = 0;
    if (argc == 4) {
        char *end;
        long v = strtol(argv[3], &end, 10);
        if (*end || v < 0 || v > INT_MAX) fail("bad max-pairs value");
        pairs = (int)v;
    }
    int32_t *lens = malloc((size_t)m * sizeof(*lens));
    int32_t *exps = malloc((size_t)terms * n * sizeof(*exps));
    int32_t *finite = malloc((size_t)terms * sizeof(*finite));
    mpz_t *rational = malloc((size_t)terms * 2 * sizeof(*rational));
    mpz_t **rational_ptrs = malloc((size_t)terms * 2 * sizeof(*rational_ptrs));
    if (!lens || !exps || !finite || !rational || !rational_ptrs)
        fail("input allocation failed");
    int64_t sum = 0;
    for (int i = 0; i < m; ++i) {
        if (fscanf(in, "%d", &lens[i]) != 1 || lens[i] < 1)
            fail("bad generator length");
        sum += lens[i];
    }
    if (sum != terms) fail("generator lengths do not sum to nterms");
    mpz_t modulus, inverse, residue;
    mpz_inits(modulus, inverse, residue, NULL);
    if (p) {
        mpz_set_ui(modulus, (unsigned)p);
        if (mpz_probab_prime_p(modulus, 32) == 0) fail("modulus is composite");
    }
    for (int t = 0; t < terms; ++t) {
        for (int k = 0; k < 2; ++k) {
            mpz_init(rational[2*t+k]);
            rational_ptrs[2*t+k] = &rational[2*t+k];
            if (mpz_inp_str(rational[2*t+k], in, 10) == 0)
                fail("bad rational coefficient");
        }
        if (mpz_sgn(rational[2*t]) == 0 || mpz_sgn(rational[2*t+1]) <= 0)
            fail("zero coefficient or nonpositive denominator");
        if (p) {
            if (!mpz_invert(inverse, rational[2*t+1], modulus))
                fail("denominator not invertible modulo characteristic");
            mpz_mul(residue, rational[2*t], inverse);
            mpz_mod(residue, residue, modulus);
            finite[t] = (int32_t)mpz_get_ui(residue);
            if (!finite[t]) fail("coefficient vanishes modulo characteristic; regenerate input");
        }
        for (int j = 0; j < n; ++j)
            if (fscanf(in, "%d", &exps[(size_t)t*n+j]) != 1 ||
                exps[(size_t)t*n+j] < 0 || exps[(size_t)t*n+j] > 65535)
                fail("bad exponent");
    }
    int ch;
    do ch = fgetc(in); while (ch == ' ' || ch == '\n' || ch == '\r' || ch == '\t');
    if (ch != EOF) fail("extra input data");
    fclose(in);
    int32_t bld = 0, *blen = NULL, *bexp = NULL;
    void *bcf = NULL;
    fprintf(stderr, "NEOGB nvars=%d ngens=%d characteristic=%d terms=%d exact_sparse=2 pairs=%d threads=1\n",
            n, m, p, terms, pairs);
    int64_t returned = export_f4(malloc, &bld, &blen, &bexp, &bcf,
        lens, exps, p ? (void *)finite : (void *)rational_ptrs,
        (uint32_t)p, 0, 0, n, m, 17, 1, pairs, 0, 2, 1, 0, 2);
    FILE *out = fopen(argv[2], "w");
    if (!out) fail("cannot open output");
    fprintf(out, "{\"characteristic\":%d,\"nvars\":%d,\"nterms\":%lld,\"basis\":[",
            p, n, (long long)returned);
    int64_t offset = 0;
    for (int i = 0; i < bld; ++i) {
        if (i) fputc(',', out);
        fputc('[', out);
        for (int j = 0; j < blen[i]; ++j, ++offset) {
            if (j) fputc(',', out);
            fputc('[', out);
            if (p) fprintf(out, "\"%d\"", ((int32_t *)bcf)[offset]);
            else gmp_fprintf(out, "\"%Zd\"", ((mpz_t *)bcf)[offset]);
            fputs(",[", out);
            for (int k = 0; k < n; ++k) {
                if (k) fputc(',', out);
                fprintf(out, "%d", bexp[offset*n+k]);
            }
            fputs("]]", out);
        }
        fputc(']', out);
    }
    fputs("]}\n", out);
    if (offset != returned) fail("output term count mismatch");
    if (fclose(out)) fail("output close failed");
    free_f4_julia_result_data(free, &blen, &bexp, &bcf, bld, p);
    for (int i = 0; i < 2*terms; ++i) mpz_clear(rational[i]);
    free(rational_ptrs); free(rational); free(finite); free(exps); free(lens);
    mpz_clears(modulus, inverse, residue, NULL);
    return 0;
}
