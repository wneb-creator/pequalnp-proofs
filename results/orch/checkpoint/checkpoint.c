/* Pilot diagnostic extension: bounded, atomic partial-generator snapshots.
 * A PARTIAL snapshot is not a Groebner basis or mathematical verdict.
 * Restart with the original input union this snapshot. */
#include <signal.h>
#include <stdarg.h>
#include <stdint.h>
#include <errno.h>
#include <fcntl.h>
#include <unistd.h>
#include <sys/stat.h>
#include <zlib.h>

static volatile sig_atomic_t cp_save_requested = 0, cp_stop_requested = 0;
static char *cp_path = NULL, *cp_csv = NULL, *cp_original_sha = NULL, **cp_names = NULL;
static unsigned cp_nv = 0, cp_round = 0, cp_stop_round = 0;
static uint64_t cp_max_bytes = 0, cp_written = 0;
static double cp_interval = 0, cp_stop_seconds = 0, cp_started = 0, cp_last = 0;
static int cp_partial = 0, cp_failed = 0, cp_subset = 0, cp_errno = 0;
static uint64_t cp_total_polys = 0, cp_total_terms = 0, cp_kept_polys = 0, cp_kept_terms = 0;
static const char *cp_reason = "none";
static int cp_fail(const char *reason, int code) {
    if (!strcmp(cp_reason, "none")) { cp_reason = reason; cp_errno = code; }
    return -1;
}
static void cp_signal(int signum) {
    cp_save_requested = 1;
    if (signum == SIGUSR2) cp_stop_requested = 1;
}
int neogb_checkpoint_configure(const char *path, const char *csv, const char *original_sha,
        double interval, unsigned stop_round, double stop_seconds,
        uint64_t max_bytes) {
    if (!path || !csv || !original_sha || strlen(original_sha) != 64 || !max_bytes || cp_path) return -1;
    cp_path = strdup(path); cp_csv = strdup(csv); cp_original_sha = strdup(original_sha);
    char *copy = strdup(csv), *save = NULL, *word;
    if (!cp_path || !cp_csv || !cp_original_sha || !copy) return -1;
    cp_nv = 1;
    for (const char *c = csv; *c; c++) if (*c == ',') cp_nv++;
    cp_names = calloc(cp_nv, sizeof(char *));
    if (!cp_names) { free(copy); return -1; }
    unsigned i = 0;
    for (word = strtok_r(copy, ",", &save); word; word = strtok_r(NULL, ",", &save)) {
        if (i >= cp_nv || !(cp_names[i++] = strdup(word))) { free(copy); return -1; }
    }
    free(copy);
    if (i != cp_nv) return -1;
    cp_interval = interval; cp_stop_round = stop_round;
    cp_stop_seconds = stop_seconds; cp_max_bytes = max_bytes;
    cp_started = cp_last = realtime();
    struct sigaction act;
    memset(&act, 0, sizeof(act)); act.sa_handler = cp_signal;
    sigemptyset(&act.sa_mask);
    if (sigaction(SIGUSR1, &act, NULL) || sigaction(SIGUSR2, &act, NULL)) return -1;
    return 0;
}
int neogb_checkpoint_was_partial(void) { return cp_partial; }
int neogb_checkpoint_failed(void) { return cp_failed; }
int neogb_checkpoint_subset(void) { return cp_subset; }
uint64_t neogb_checkpoint_kept(void) { return cp_kept_polys; }
uint64_t neogb_checkpoint_total(void) { return cp_total_polys; }

static int cp_put(gzFile f, const char *s) {
    size_t n = strlen(s);
    if (n > cp_max_bytes - cp_written || n > INT_MAX) return cp_fail("stream-size-cap", 0);
    if (gzwrite(f, s, (unsigned)n) != (int)n) return cp_fail("gzip-write", errno);
    cp_written += n;
    return 0;
}
static int cp_printf(gzFile f, const char *fmt, ...) {
    char small[128]; va_list args;
    va_start(args, fmt); int n = vsnprintf(small, sizeof(small), fmt, args); va_end(args);
    if (n < 0 || (size_t)n >= sizeof(small)) return cp_fail("format-buffer", 0);
    return cp_put(f, small);
}
typedef struct cp_candidate {
    bl_t index;
    len_t length;
    deg_t degree;
} cp_candidate;
static int cp_compare_candidate(const void *av, const void *bv) {
    const cp_candidate *a = av, *b = bv;
    if (a->length != b->length) return a->length < b->length ? -1 : 1;
    if (a->degree != b->degree) return a->degree < b->degree ? -1 : 1;
    return a->index < b->index ? -1 : a->index != b->index;
}
static int cp_snapshot(const bs_t *bs, const md_t *md) {
    cp_reason = "none"; cp_errno = 0; cp_written = 0;
    cp_total_polys = cp_total_terms = cp_kept_polys = cp_kept_terms = 0;
    if (!cp_path || bs->ht->nv != cp_nv) return cp_fail("variable-count-mismatch", 0);
    size_t plen = strlen(cp_path);
    char *tmp = malloc(plen + 48), *previous = malloc(plen + 16);
    cp_candidate *candidates = malloc((size_t)bs->ld * sizeof(cp_candidate));
    if (!tmp || !previous || !candidates) {
        free(tmp); free(previous); free(candidates); return cp_fail("selection-allocation", errno);
    }
    for (bl_t i = 0; i < bs->ld; i++) if (bs->hm[i]) {
        candidates[cp_total_polys++] = (cp_candidate){i, bs->hm[i][LENGTH], bs->hm[i][DEG]};
        cp_total_terms += bs->hm[i][LENGTH];
    }
    qsort(candidates, cp_total_polys, sizeof(cp_candidate), cp_compare_candidate);
    /* Every uint32 coefficient fits ten digits, uint16 exponent five digits.
     * This upper bound covers every variable in every term, even absent ones.
     * Whole shortest polynomials are retained; no polynomial is truncated.
     * ANY subset of derived polynomials union the original input has the
     * original ideal, independent of redundant flags and missing S-pairs. */
    uint64_t per_term = 11, budget = 512 + strlen(cp_csv);
    for (unsigned v = 0; v < cp_nv; v++) per_term += strlen(cp_names[v]) + 7;
    if (budget > cp_max_bytes) {
        free(tmp); free(previous); free(candidates); return cp_fail("header-size-cap", 0);
    }
    for (uint64_t i = 0; i < cp_total_polys; i++) {
        uint64_t bound = per_term * candidates[i].length + 2;
        if (bound > cp_max_bytes - budget) break;
        budget += bound;
        cp_kept_polys++; cp_kept_terms += candidates[i].length;
    }
    cp_subset = cp_kept_polys < cp_total_polys;
    snprintf(tmp, plen + 48, "%s.tmp.%ld", cp_path, (long)getpid());
    snprintf(previous, plen + 16, "%s.previous", cp_path);
    int fd = open(tmp, O_CREAT | O_TRUNC | O_WRONLY, 0600), bad = 0;
    if (fd < 0) {
        cp_fail("temporary-open", errno); free(tmp); free(previous); free(candidates); return -1;
    }
    gzFile f = gzdopen(fd, "wb1");
    if (!f) {
        cp_fail("gzip-open", errno); close(fd); unlink(tmp);
        free(tmp); free(previous); free(candidates); return -1;
    }
    bad |= cp_printf(f, "# PARTIAL subset=%d round=%u\n", cp_subset, cp_round);
    bad |= cp_printf(f, "# generators_retained=%llu generators_total=%llu\n",
            (unsigned long long)cp_kept_polys, (unsigned long long)cp_total_polys);
    bad |= cp_printf(f, "# terms_retained=%llu terms_total=%llu\n",
            (unsigned long long)cp_kept_terms, (unsigned long long)cp_total_terms);
    bad |= cp_put(f, "# Original-input union required; no Groebner-basis verdict.\n");
    bad |= cp_put(f, "# original_sha256="); bad |= cp_put(f, cp_original_sha); bad |= cp_put(f, "\n");
    bad |= cp_put(f, cp_csv); bad |= cp_put(f, "\n");
    bad |= cp_printf(f, "%u\n", md->fc);
    for (uint64_t i = 0; !bad && i < cp_kept_polys; i++) {
        const hm_t *row = bs->hm[candidates[i].index];
        const bl_t ci = row[COEFFS];
        for (len_t j = 0; !bad && j < row[LENGTH]; j++) {
            if (j) bad |= cp_put(f, "+");
            switch (md->ff_bits) {
                case 8: bad |= cp_printf(f, "%u", (unsigned)bs->cf_8[ci][j]); break;
                case 16: bad |= cp_printf(f, "%u", (unsigned)bs->cf_16[ci][j]); break;
                case 32: bad |= cp_printf(f, "%u", bs->cf_32[ci][j]); break;
                default: bad = cp_fail("unsupported-coefficient-width", 0); break;
            }
            const exp_t *ev = bs->ht->ev[row[OFFSET+j]];
            unsigned v = 0;
            for (len_t k = 1; !bad && k < bs->ht->evl; k++) {
                if (k == bs->ht->ebl) continue;
                if (v >= cp_nv) { bad = cp_fail("exponent-variable-overflow", 0); break; }
                if (ev[k]) {
                    bad |= cp_put(f, "*"); bad |= cp_put(f, cp_names[v]);
                    if (ev[k] != 1) bad |= cp_printf(f, "^%u", (unsigned)ev[k]);
                }
                v++;
            }
            if (!bad && v != cp_nv) bad = cp_fail("exponent-variable-count", 0);
        }
        if (!bad) bad |= cp_put(f, ",\n");
    }
    int zresult = gzclose(f);
    if (zresult != Z_OK) bad = cp_fail("gzip-close", zresult == Z_ERRNO ? errno : 0);
    if (!bad) {
        fd = open(tmp, O_RDONLY);
        if (fd < 0) bad = cp_fail("sync-open", errno);
        else { if (fsync(fd)) bad = cp_fail("sync-write", errno); close(fd); }
    }
    if (!bad) {
        if (unlink(previous) && errno != ENOENT) bad = cp_fail("previous-unlink", errno);
        struct stat previous_stat;
        if (!bad && stat(cp_path, &previous_stat) == 0) {
            if (previous_stat.st_size <= 16 * 1024 * 1024 && link(cp_path, previous))
                bad = cp_fail("previous-link", errno);
        } else if (!bad && errno != ENOENT) bad = cp_fail("latest-stat", errno);
        if (!bad && rename(tmp, cp_path)) bad = cp_fail("latest-rename", errno);
    }
    if (bad) { unlink(tmp); cp_failed = 1; }
    else fprintf(stderr,
            "CHECKPOINT PARTIAL subset=%d round=%u generators=%llu/%llu terms=%llu/%llu bytes=%llu conservative_bound=%llu cap=%llu\n",
            cp_subset, cp_round, (unsigned long long)cp_kept_polys, (unsigned long long)cp_total_polys,
            (unsigned long long)cp_kept_terms, (unsigned long long)cp_total_terms,
            (unsigned long long)cp_written, (unsigned long long)budget,
            (unsigned long long)cp_max_bytes);
    fflush(stderr);
    free(tmp); free(previous); free(candidates);
    return bad ? -1 : 0;
}
static int cp_round_end(const bs_t *bs, const md_t *md, int done) {
    if (!cp_path) return 0;
    cp_round++;
    double now = realtime();
    int stop = cp_stop_requested || (cp_stop_round && cp_round >= cp_stop_round)
        || (cp_stop_seconds > 0 && now - cp_started >= cp_stop_seconds);
    int save = done || cp_save_requested || stop || (cp_interval > 0 && now - cp_last >= cp_interval);
    if (save) {
        cp_save_requested = 0; cp_last = now;
        if (cp_snapshot(bs, md)) {
            cp_failed = 1; stop = 1;
            fprintf(stderr, "CHECKPOINT FAILED reason=%s code=%d bytes=%llu cap=%llu retained=%llu/%llu: prior snapshot retained; stopping PARTIAL\n",
                    cp_reason, cp_errno, (unsigned long long)cp_written,
                    (unsigned long long)cp_max_bytes, (unsigned long long)cp_kept_polys,
                    (unsigned long long)cp_total_polys);
        }
    }
    if (stop && !done) { cp_partial = 1; return 1; }
    return 0;
}
