#include <cstdint>
#include <cstdio>
#include <vector>
#include <bit>
#include <set>
int main(){
const uint32_t nv[16]={447403349,143167761,25264899,163845,1671219,3855,8356095,21845,13107,126324495,255,626338474,912673996,947417328,1065385728,1073709056};
const uint32_t pv[16]={1,6,24,224,768,3072,4096,24576,98304,131072,786432,8227,33036,132176,266880,608256};
std::vector<uint32_t> N(65536),P(65536),T(65536);
for(unsigned S=1;S<65536;S++){unsigned i=std::countr_zero(S);N[S]=N[S&(S-1)]|nv[i];P[S]=P[S&(S-1)]|pv[i];}
std::set<uint64_t> shapes;
int best=0;unsigned bs=0,bt=0;uint32_t br=0;
for(int i=0;i<30;i++)for(int j=i;j<30;j++){
uint32_t R=(1u<<i)|(1u<<j);uint32_t allowed[16]={};
for(unsigned a=0;a<16;a++)for(unsigned b=0;b<16;b++)if(!(nv[a]&nv[b]&~R))allowed[a]|=1u<<b;
T[0]=65535;
for(unsigned S=1;S<65536;S++){
T[S]=T[S&(S-1)]&allowed[std::countr_zero(S)];
if(!(N[S]&N[T[S]]))continue;
int c=std::popcount(P[S]&P[T[S]]);
if(c==4){auto v=(uint64_t(N[S]&N[T[S]])<<20)|(P[S]&P[T[S]]);if(shapes.insert(v).second)printf("witness S=%u T=%u negative_mask=%u positive_mask=%u\n",S,T[S],N[S]&N[T[S]],P[S]&P[T[S]]);}
if(c>best){best=c;bs=S;bt=T[S];br=R;}
}}
for(auto v:shapes)printf("shape negative_mask=%u positive_mask=%u\n",unsigned(v>>20),unsigned(v&((1u<<20)-1)));
printf("max_dirty_crossing_edges=%d S=%u T=%u negative_bound_mask=%u actual_negative_mask=%u\n",best,bs,bt,br,N[bs]&N[bt]);
}
