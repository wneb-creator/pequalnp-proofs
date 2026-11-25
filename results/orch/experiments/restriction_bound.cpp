#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <cstdio>
#include <vector>

using U = uint32_t;
std::array<U,26> adj;
std::vector<int8_t> memo(1u<<26,-1);
uint64_t states=0;

U nonisolated(U s) {
    U out=0, t=s;
    while(t) {unsigned v=std::countr_zero(t); t&=t-1;
        if(adj[v]&s) out |= U(1)<<v;
    }
    return out;
}

int bound(U s) {
    if (!s) return 0;
    if (memo[s]>=0) return memo[s];
    U core=nonisolated(s);
    if(core!=s) return memo[s]=bound(core);
    ++states;
    int n=std::popcount(s), best=n-1;
    U all=s;
    std::array<int,26> zs{},os{},degs{};
    while(all) {
        unsigned v=std::countr_zero(all); all&=all-1;
        U ns=adj[v]&s, s0=s&~(U(1)<<v), s1=s0&~ns;
        int d=std::popcount(ns);
        int z=bound(s0);
        U c1=nonisolated(s1);
        int o=c1 ? d+bound(c1) : d-1;
        zs[v]=z; os[v]=o; degs[v]=d;
        best=std::max(best,z+1);
        best=std::max(best,o+1);
        if(nonisolated(s0) && (c1 || d>=2))
            best=std::max(best,std::min(z,o)+2);
    }
    int first=1000;
    for (unsigned p=0;p<26;p++) if(s&(U(1)<<p)) {
        for(unsigned q=p+1;q<26;q++) if(s&(U(1)<<q)) {
            bool edge=adj[p]&(U(1)<<q);
            if(edge) {
                int a=0;
                if(nonisolated(s&~(U(1)<<p))) a=std::max(a,zs[p]+(degs[p]>=2?3:2));
                if(nonisolated(s&~(U(1)<<q))) a=std::max(a,zs[q]+(degs[q]>=2?3:2));
                a=std::max(a,os[p]+(degs[p]>=2?2:1));
                a=std::max(a,os[q]+(degs[q]>=2?2:1));
                first=std::min(first,a);
            }
            bool pdom=!edge && !((adj[p]&s)&~adj[q]);
            bool qdom=!edge && !((adj[q]&s)&~adj[p]);
            int a=std::max({zs[p]+(pdom?1:2),zs[q]+(qdom?1:2),
                os[p]+(pdom?2:3),os[q]+(qdom?2:3)});
            first=std::min(first,a);
        }
    }
    best=std::max(best,first);
    memo[s]=best;
    return best;
}

int main() {
    int ds[]={0,1,3,9};
    for(unsigned l=0;l<13;l++) for(int d:ds) {
        unsigned p=(l+d)%13;
        adj[p] |= U(1)<<(13+l);
        adj[13+l] |= U(1)<<p;
    }
    U full=(U(1)<<26)-1;
    std::printf("Enhanced first-gate exact-function restriction candidate lower bound: %d\n",bound(full));
    std::printf("Nontrivial states: %llu\n",(unsigned long long)states);
    std::printf("Delete point 0: %d\n",bound(full&~U(1)));
    std::printf("Fix point 0 true: %d\n",4+bound(full&~(U(1)|adj[0])));
}
