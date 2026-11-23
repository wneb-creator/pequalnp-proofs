#include <algorithm>
#include <array>
#include <cassert>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <vector>

constexpr unsigned n = 13;
constexpr unsigned m = 23;
constexpr unsigned all = (1u << n) - 1;
constexpr std::array<std::array<unsigned, 2>, m> edges{{
    {3,5},{4,5},{2,6},{4,6},{1,7},{3,7},{6,7},{1,8},
    {2,8},{5,8},{0,9},{2,9},{3,9},{0,10},{1,10},{4,10},
    {0,11},{6,11},{7,11},{0,12},{5,12},{8,12},{11,12}
}};

// This second verifier uses edges and orientation bits directly, independently
// of the incoming-neighbor bitsets used by the search.
bool direct_check(unsigned orientation, unsigned chosen) {
    bool selected[n]{};
    bool absorbed[n]{};
    for (unsigned v = 0; v < n; ++v) selected[v] = (chosen >> v) & 1u;
    for (unsigned e = 0; e < m; ++e) {
        auto u = edges[e][0], v = edges[e][1];
        if (selected[u] && selected[v]) return false;
        if ((orientation >> e) & 1u) {
            if (selected[v]) absorbed[u] = true;
        } else {
            if (selected[u]) absorbed[v] = true;
        }
    }
    for (auto edge : edges) {
        auto u = edge[0], v = edge[1];
        if (!selected[u] && !selected[v] && !absorbed[u] && !absorbed[v]) return false;
    }
    return true;
}

int main() {
    const auto started = std::chrono::steady_clock::now();
    bool adjacent[n][n]{};
    for (auto edge : edges) {
        auto u = edge[0], v = edge[1];
        assert(u < n && v < n && u != v && !adjacent[u][v]);
        adjacent[u][v] = adjacent[v][u] = true;
    }
    for (unsigned a = 0; a < n; ++a)
        for (unsigned c = a + 1; c < n; ++c) {
            unsigned common = 0;
            for (unsigned b = 0; b < n; ++b) common += adjacent[a][b] && adjacent[c][b];
            if (common > 1) {
                std::cout << "ERROR graph is not C4-free; opposite vertices " << a << ' ' << c << '\n';
                return 2;
            }
        }
    std::array<bool, 1u << n> independent{};
    std::vector<unsigned> candidates;
    for (unsigned subset = 0; subset <= all; ++subset) {
        bool ok = true;
        for (auto edge : edges) {
            if (((subset >> edge[0]) & 1u) && ((subset >> edge[1]) & 1u)) {
                ok = false;
                break;
            }
        }
        independent[subset] = ok;
        if (ok) candidates.push_back(subset);
    }
    std::sort(candidates.begin(), candidates.end(), [](unsigned a, unsigned b) {
        auto ca = __builtin_popcount(a), cb = __builtin_popcount(b);
        return ca != cb ? ca > cb : a < b;
    });
    std::cout << "shard=1 graph=A n=" << n << " edges=" << m << " C4_free=true\n";
    std::cout << "independent_sets=" << candidates.size() << '\n';
    constexpr unsigned orientation_count = 1u << m;
    std::uint64_t candidates_tested = 0;
    std::array<std::uint64_t, n + 1> witness_sizes{};
    unsigned max_candidates = 0;
    for (unsigned orientation = 0; orientation < orientation_count; ++orientation) {
        std::array<unsigned, n> incoming{};
        for (unsigned e = 0; e < m; ++e) {
            auto u = edges[e][0], v = edges[e][1];
            if ((orientation >> e) & 1u) incoming[v] |= 1u << u;
            else incoming[u] |= 1u << v;
        }
        bool found = false;
        unsigned tried = 0;
        for (unsigned chosen : candidates) {
            ++tried;
            unsigned absorbed = 0;
            for (unsigned bits = chosen; bits; bits &= bits - 1)
                absorbed |= incoming[__builtin_ctz(bits)];
            auto remaining = all & ~(chosen | absorbed);
            if (independent[remaining]) {
                if (!direct_check(orientation, chosen)) {
                    std::cout << "ERROR independent verifier disagreed orientation=" << orientation << " chosen=" << chosen << '\n';
                    return 3;
                }
                ++witness_sizes[__builtin_popcount(chosen)];
                found = true;
                break;
            }
        }
        candidates_tested += tried;
        max_candidates = std::max(max_candidates, tried);
        if (!found) {
            std::cout << "COUNTEREXAMPLE orientation=" << orientation << " examined=" << (orientation + 1) << '\n';
            for (unsigned e = 0; e < m; ++e) {
                auto u = edges[e][0], v = edges[e][1];
                if (!((orientation >> e) & 1u)) std::swap(u,v);
                std::cout << u << " -> " << v << '\n';
            }
            return 1;
        }
    }
    std::cout << "orientations_examined=" << orientation_count << " violations=0 witnesses_independently_rechecked=" << orientation_count << '\n';
    std::cout << "candidates_tested=" << candidates_tested << " max_candidates_per_orientation=" << max_candidates << '\n';
    for (unsigned k = 0; k <= n; ++k)
        if (witness_sizes[k]) std::cout << "witness_size=" << k << " count=" << witness_sizes[k] << '\n';
    std::chrono::duration<double> elapsed = std::chrono::steady_clock::now() - started;
    std::cout << "elapsed_seconds=" << elapsed.count() << '\n';
}
