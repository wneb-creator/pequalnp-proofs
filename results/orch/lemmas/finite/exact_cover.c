#include <stdint.h>
#include <string.h>
#define WORDS 16
#define ROWS 1024

int exact_cover(unsigned n, const uint64_t *wires, const uint64_t *goal, int oriented) {
    if (oriented) {
        for (unsigned r = 0; r < ROWS; ++r) {
            if ((goal[r >> 6] >> (r & 63)) & 1) continue;
            uint64_t possible[WORDS];
            memcpy(possible, goal, sizeof(possible));
            int nonzero = 1;
            for (unsigned i = 0; i < n && nonzero; ++i) {
                const uint64_t *w = wires + WORDS * i;
                if ((w[r >> 6] >> (r & 63)) & 1) continue;
                nonzero = 0;
                for (unsigned j = 0; j < WORDS; ++j) {
                    possible[j] &= ~w[j];
                    nonzero |= possible[j] != 0;
                }
            }
            if (nonzero) return 0;
        }
        return 1;
    }
    uint64_t buffers[2][ROWS][WORDS];
    for (unsigned j = 0; j < WORDS; ++j) buffers[0][0][j] = UINT64_MAX;
    unsigned count = 1, side = 0;
    for (unsigned i = 0; i < n; ++i) {
        const uint64_t *w = wires + WORDS * i;
        unsigned next = 0;
        for (unsigned k = 0; k < count; ++k) {
            const uint64_t *g = buffers[side][k];
            for (unsigned p = 0; p < 2; ++p) {
                uint64_t *h = buffers[1 - side][next];
                int pos = 0, neg = 0;
                for (unsigned j = 0; j < WORDS; ++j) {
                    h[j] = g[j] & (p ? w[j] : ~w[j]);
                    pos |= (h[j] & goal[j]) != 0;
                    neg |= (h[j] & ~goal[j]) != 0;
                }
                if (pos && neg) ++next;
            }
        }
        count = next;
        side = 1 - side;
        if (!count) return 1;
    }
    return 0;
}

#define PATTERNS (1u << 19)
static uint16_t row_at[PATTERNS];
static uint16_t chain_first[PATTERNS];
static uint16_t chain_second[PATTERNS];
static uint16_t chain_third[PATTERNS];
static uint8_t chain_stage[PATTERNS];

int one_not_chain(unsigned n, const uint64_t *wires, const uint64_t *goal, uint16_t *out) {
    if (n > 19) return 0;
    unsigned size = 1u << n;
    memset(row_at, 0, size * sizeof(uint16_t));
    for (unsigned r = 0; r < ROWS; ++r) {
        unsigned pattern = 0;
        for (unsigned i = 0; i < n; ++i) {
            const uint64_t *w = wires + WORDS * i;
            pattern |= ((w[r >> 6] >> (r & 63)) & 1u) << i;
        }
        row_at[pattern] = r + 1;
    }
    for (unsigned v = 0; v < size; ++v) {
        unsigned best = 0, predecessor = 0;
        for (unsigned bits = v; bits; bits &= bits - 1) {
            unsigned bit = bits & -bits;
            unsigned u = v ^ bit;
            if (chain_stage[u] > best) {
                best = chain_stage[u];
                predecessor = u;
            }
        }
        uint16_t first = best ? chain_first[predecessor] : 0;
        uint16_t second = best > 1 ? chain_second[predecessor] : 0;
        uint16_t third = best > 2 ? chain_third[predecessor] : 0;
        if (row_at[v]) {
            unsigned r = row_at[v] - 1;
            unsigned value = (goal[r >> 6] >> (r & 63)) & 1u;
            if (best == 0 && value) { first = r; best = 1; }
            else if (best == 1 && !value) { second = r; best = 2; }
            else if (best == 2 && value) { third = r; best = 3; }
            else if (best == 3 && !value) {
                out[0] = first; out[1] = second; out[2] = third; out[3] = r;
                return 1;
            }
        }
        chain_stage[v] = best;
        chain_first[v] = first;
        chain_second[v] = second;
        chain_third[v] = third;
    }
    return 0;
}
