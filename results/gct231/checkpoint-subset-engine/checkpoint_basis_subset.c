/* Finite-field research checkpoints. Included after io.c, before f4.c.
 * Every file retains the original generators and appends the current active
 * basis rows up to a derived-term budget. It is only a partial restart input. */
#include <stdint.h>
#include <inttypes.h>
#include <string.h>
#include <unistd.h>
#include <errno.h>

#ifndef PNP_CHECKPOINT_DERIVED_TERMS
#define PNP_CHECKPOINT_DERIVED_TERMS 1000000
#endif
#if PNP_CHECKPOINT_DERIVED_TERMS < 1 || PNP_CHECKPOINT_DERIVED_TERMS > 1000000
#error Invalid checkpoint derived-term budget
#endif
typedef struct {
    len_t index;
    int64_t length, leading_degree;
} pc_row_choice;

static int pc_compare_rows(const void *left, const void *right) {
    const pc_row_choice *a=left, *b=right;
    if (a->leading_degree != b->leading_degree)
        return a->leading_degree < b->leading_degree ? -1 : 1;
    if (a->length != b->length) return a->length < b->length ? -1 : 1;
    return a->index < b->index ? -1 : a->index > b->index;
}

static char *pc_prefix = NULL;
static int pc_n, pc_m, pc_field, pc_terms;
static int32_t *pc_lengths, *pc_exponents, *pc_coefficients;
static double pc_interval, pc_last;
static uint64_t pc_sequence, pc_current, pc_previous, pc_stop_round;

static void pc_fail(const char *message) {
    fprintf(stderr, "CHECKPOINT_FAILURE %s: %s\n", message, strerror(errno));
    fflush(stderr);
    exit(76);
}

void pnp_checkpoint_configure(const char *prefix, int n, int m, int field,
        int terms, const int32_t *lengths, const int32_t *exponents,
        const int32_t *coefficients, double interval, uint64_t stop_round) {
    if (pc_prefix || !prefix || field <= 1 || n <= 0 || m <= 0 || terms <= 0)
        pc_fail("invalid configuration");
    pc_prefix = strdup(prefix);
    pc_n=n; pc_m=m; pc_field=field; pc_terms=terms;
    pc_interval=interval; pc_stop_round=stop_round;
    pc_lengths=malloc((size_t)m*sizeof(*pc_lengths));
    pc_exponents=malloc((size_t)terms*(size_t)n*sizeof(*pc_exponents));
    pc_coefficients=malloc((size_t)terms*sizeof(*pc_coefficients));
    if (!pc_prefix || !pc_lengths || !pc_exponents || !pc_coefficients)
        pc_fail("configuration allocation");
    memcpy(pc_lengths,lengths,(size_t)m*sizeof(*pc_lengths));
    memcpy(pc_exponents,exponents,(size_t)terms*(size_t)n*sizeof(*pc_exponents));
    memcpy(pc_coefficients,coefficients,(size_t)terms*sizeof(*pc_coefficients));
}

static int32_t pc_coefficient(const bs_t *bs, const hm_t *row,
        const md_t *md, len_t j) {
    int64_t value;
    switch(md->ff_bits) {
        case 8: value=bs->cf_8[row[COEFFS]][j]; break;
        case 16: value=bs->cf_16[row[COEFFS]][j]; break;
        case 32: value=bs->cf_32[row[COEFFS]][j]; break;
        default: pc_fail("unsupported coefficient field"); return 0;
    }
    value %= pc_field;
    if (value < 0) value += pc_field;
    return (int32_t)value;
}

static int64_t pc_row_length(const bs_t *bs, const hm_t *row, const md_t *md) {
    if (!row) return 0;
    int64_t length=0;
    for (len_t j=0;j<row[LENGTH];j++)
        if (pc_coefficient(bs,row,md,j)) length++;
    return length;
}

static char *pc_filename(uint64_t sequence, const char *suffix) {
    size_t size=strlen(pc_prefix)+80+strlen(suffix);
    char *path=malloc(size);
    if (!path) pc_fail("filename allocation");
    if (sequence) snprintf(path,size,"%s.s%06" PRIu64 "%s",pc_prefix,sequence,suffix);
    else snprintf(path,size,"%s%s",pc_prefix,suffix);
    return path;
}

static void pc_close(FILE *file) {
    if (ferror(file) || fflush(file) || fsync(fileno(file)) || fclose(file))
        pc_fail("output flush or close");
}

static void pnp_checkpoint_snapshot(const bs_t *bs, const md_t *md,
        uint64_t round, int force) {
    if (!pc_prefix) return;
    int stopping=pc_stop_round && round >= pc_stop_round;
    if (!force && !stopping && realtime()-pc_last < pc_interval) return;
    if ((int)md->fc != pc_field || (int)bs->ht->nv != pc_n)
        pc_fail("field or variable mismatch");
    int64_t available_rows=0, available_terms=0;
    pc_row_choice *choices=malloc((size_t)(bs->lml ? bs->lml : 1)*sizeof(*choices));
    if (!choices) pc_fail("row selection allocation");
    for (len_t i=0;i<bs->lml;i++) {
        hm_t *row=bs->hm[bs->lmps[i]];
        int64_t length=pc_row_length(bs,row,md);
        if (!length) continue;
        int64_t degree=0;
        const exp_t *exponent=bs->ht->ev[row[OFFSET]];
        for (len_t k=1;k<bs->ht->evl;k++)
            if (k!=bs->ht->ebl) degree+=exponent[k];
        choices[available_rows++]=(pc_row_choice){i,length,degree};
        available_terms+=length;
    }
    qsort(choices,(size_t)available_rows,sizeof(*choices),pc_compare_rows);
    int64_t basis_rows=0, basis_terms=0;
    for (int64_t i=0;i<available_rows;i++) {
        if (choices[i].length > PNP_CHECKPOINT_DERIVED_TERMS-basis_terms) continue;
        if (basis_rows+pc_m >= 100000) continue;
        choices[basis_rows++]=choices[i];
        basis_terms+=choices[i].length;
    }
    if (basis_rows+pc_m > 100000 || basis_terms+pc_terms > 10000000)
        pc_fail("restart input would exceed validated wrapper bounds");
    uint64_t sequence=++pc_sequence;
    char *temporary=pc_filename(sequence,".in.tmp");
    char *complete=pc_filename(sequence,".in");
    FILE *file=fopen(temporary,"w");
    if (!file) pc_fail("open input snapshot");
    fprintf(file,"%d %" PRId64 " %d %" PRId64 "\n",pc_n,
        (int64_t)pc_m+basis_rows,pc_field,(int64_t)pc_terms+basis_terms);
    for (int i=0;i<pc_m;i++) fprintf(file,i ? " %d" : "%d",pc_lengths[i]);
    for (int64_t i=0;i<basis_rows;i++)
        fprintf(file," %" PRId64,choices[i].length);
    fputc('\n',file);
    for (int t=0;t<pc_terms;t++) {
        fprintf(file,"%d 1",pc_coefficients[t]);
        for (int j=0;j<pc_n;j++) fprintf(file," %d",pc_exponents[(size_t)t*pc_n+j]);
        fputc('\n',file);
    }
    const ht_t *ht=bs->ht;
    for (int64_t i=0;i<basis_rows;i++) {
        hm_t *row=bs->hm[bs->lmps[choices[i].index]];
        for (len_t j=0;j<row[LENGTH];j++) {
            int32_t coefficient=pc_coefficient(bs,row,md,j);
            if (!coefficient) continue;
            fprintf(file,"%d 1",coefficient);
            const exp_t *exponent=ht->ev[row[OFFSET+j]];
            int count=0;
            for (len_t k=1;k<ht->evl;k++) {
                if (k==ht->ebl) continue;
                if ((uint64_t)exponent[k] > 65535) pc_fail("restart exponent out of range");
                fprintf(file," %u",(unsigned)exponent[k]); count++;
            }
            if (count!=pc_n) pc_fail("restart exponent dimension");
            fputc('\n',file);
        }
    }
    pc_close(file);
    if (rename(temporary,complete)) pc_fail("publish snapshot input");
    char *meta_tmp=pc_filename(0,".latest.json.tmp");
    char *meta=pc_filename(0,".latest.json");
    file=fopen(meta_tmp,"w");
    if (!file) pc_fail("open snapshot metadata");
    fprintf(file,"{\"sequence\":%" PRIu64 ",\"round\":%" PRIu64
        ",\"characteristic\":%d,\"nvars\":%d,\"original_generators\":%d,"
        "\"original_terms\":%d,\"appended_basis_rows\":%" PRId64
        ",\"appended_basis_terms\":%" PRId64 ","
        "\"available_basis_rows\":%" PRId64 ",\"available_basis_terms\":%" PRId64 ","
        "\"omitted_basis_rows\":%" PRId64 ",\"omitted_basis_terms\":%" PRId64 ","
        "\"derived_term_budget\":%d,"
        "\"selection\":\"Increasing leading degree, then term count, then active-basis index; greedy budget.\","
        "\"scope\":\"Original generators plus a bounded subset of active polynomial consequences; partial restart generating set, not a Groebner verdict.\"}\n",
        sequence,round,pc_field,pc_n,pc_m,pc_terms,basis_rows,basis_terms,
        available_rows,available_terms,available_rows-basis_rows,
        available_terms-basis_terms,PNP_CHECKPOINT_DERIVED_TERMS);
    pc_close(file);
    if (rename(meta_tmp,meta)) pc_fail("publish snapshot metadata");
    if (pc_previous) {
        char *obsolete=pc_filename(pc_previous,".in");
        if (unlink(obsolete)) pc_fail("remove obsolete third snapshot");
        free(obsolete);
    }
    pc_previous=pc_current; pc_current=sequence; pc_last=realtime();
    fprintf(stderr,"CHECKPOINT sequence=%" PRIu64 " round=%" PRIu64
        " appended_rows=%" PRId64 " appended_terms=%" PRId64 "\n",
        sequence,round,basis_rows,basis_terms);
    fflush(stderr);
    free(choices);free(temporary);free(complete);free(meta_tmp);free(meta);
    if (stopping) exit(75);
}
