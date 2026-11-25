#include <algorithm>
#include <array>
#include <cstdint>
#include <unordered_map>
#include <vector>
using namespace std;
extern "C" int feasible_multiset(int,const uint64_t*,uint64_t,uint64_t);
namespace {
struct Local {
 int n,np,nn;const uint64_t* f;array<uint64_t,64> px{},nx{}; unsigned sep[64][64]{}, patt[64]{}, natt[64]{};unordered_map<uint64_t,bool> cache;
 vector<unsigned> groups(unsigned S,uint64_t a,uint64_t b,bool is_or){
  vector<unsigned> g;for(unsigned v=S;v;v&=v-1)g.push_back(v&-v);
  uint64_t labels=is_or?a:b,other=is_or?b:a;
  for(uint64_t q=labels;q;q&=q-1){int j=__builtin_ctzll(q);unsigned need=0;for(uint64_t t=other;t;t&=t-1){int i=__builtin_ctzll(t);unsigned m=S&(is_or?sep[j][i]:sep[i][j]);if((m&(m-1))==0)need|=m;}if(!need)continue;unsigned bundle=0;vector<unsigned> next;for(auto v:g)if(v&need)bundle|=v;else next.push_back(v);next.push_back(bundle);g.swap(next);}
  return g;
 }
 bool fallback(unsigned S,uint64_t a,uint64_t b){vector<uint64_t> fs;for(unsigned x=S;x;x&=x-1)fs.push_back(f[__builtin_ctz(x)]);uint64_t p=0,q=0;for(auto x=a;x;x&=x-1)p|=px[__builtin_ctzll(x)];for(auto x=b;x;x&=x-1)q|=nx[__builtin_ctzll(x)];return feasible_multiset(fs.size(),fs.data(),p,q)==1;}
 uint64_t antichain(unsigned S,uint64_t rows,const unsigned* pattern,bool positive){
  uint64_t ans=rows;for(uint64_t a=rows;a;a&=a-1){int ai=__builtin_ctzll(a);unsigned av=S&pattern[ai];for(uint64_t b=rows;b;b&=b-1){int bi=__builtin_ctzll(b);if(ai==bi)continue;unsigned bv=S&pattern[bi];bool implied=positive?!(bv&~av):!(av&~bv);if(implied&&(bv!=av||bi<ai)){ans&=~(a&-a);break;}}}return ans;
 }
 bool rec(unsigned S,uint64_t a,uint64_t b){
  if(!a||!b)return true;
  a=antichain(S,a,patt,true);b=antichain(S,b,natt,false);
  unsigned sometimes_positive=0, sometimes_negative_zero=0;
  for(uint64_t x=a;x;x&=x-1)sometimes_positive|=patt[__builtin_ctzll(x)];
  for(uint64_t x=b;x;x&=x-1)sometimes_negative_zero|=~natt[__builtin_ctzll(x)];
  S&=sometimes_positive&sometimes_negative_zero;
  uint64_t key=(uint64_t(S)<<(np+nn))|(a<<nn)|b;auto it=cache.find(key);if(it!=cache.end())return it->second;
  unsigned common=S;for(uint64_t x=a;x;x&=x-1)for(uint64_t y=b;y;y&=y-1){unsigned m=S&sep[__builtin_ctzll(x)][__builtin_ctzll(y)];if(!m)return cache[key]=false;common&=m;}
  if(common)return cache[key]=true;
  if(__builtin_popcount(S)<=12)return cache[key]=fallback(S,a,b);
  for(bool is_or:{true,false}){
   auto g=groups(S,a,b,is_or);if(g.size()>16)return cache[key]=fallback(S,a,b);vector<unsigned> sides(1u<<(g.size()-1));uint64_t labels=is_or?a:b,other=is_or?b:a;
   for(int z=1;z<(int)sides.size();z++){
    unsigned left=sides[z]=sides[z&(z-1)]|g[__builtin_ctz(z)],right=S^left;uint64_t must_l=0,must_r=0;bool ok=true;
    for(auto x=labels;x;x&=x-1){int i=__builtin_ctzll(x);bool can_l=true,can_r=true;for(auto y=other;y;y&=y-1){int j=__builtin_ctzll(y);unsigned m=is_or?sep[i][j]:sep[j][i];can_l=can_l&&bool(m&left);can_r=can_r&&bool(m&right);if(!can_l&&!can_r)break;}
     if(!can_l&&!can_r){ok=false;break;}if(!can_l)must_r|=x&-x;if(!can_r)must_l|=x&-x;
    }
    if(!ok)continue;uint64_t optional=labels&~(must_l|must_r);
    for(auto w=optional;;w=(w-1)&optional){auto l=must_l|w,r=must_r|(optional^w);if((is_or?rec(left,l,b):rec(left,a,l))&&(is_or?rec(right,r,b):rec(right,a,r)))return cache[key]=true;if(!w)break;}
   }
  }return cache[key]=false;
 }
};}
extern "C" int feasible_components(int n,const uint64_t*f,uint64_t p,uint64_t q){
 if(!p||!q)return 1;int np=__builtin_popcountll(p),nn=__builtin_popcountll(q);if(n>21||np>62||nn>62||n+np+nn>64)return -1;
 Local model{n,np,nn,f};auto x=p;for(int j=0;j<np;j++,x&=x-1)model.px[j]=x&-x;x=q;for(int j=0;j<nn;j++,x&=x-1)model.nx[j]=x&-x;
 for(int i=0;i<np;i++)for(int k=0;k<n;k++)if(f[k]&model.px[i])model.patt[i]|=1u<<k;
 for(int j=0;j<nn;j++)for(int k=0;k<n;k++)if(f[k]&model.nx[j])model.natt[j]|=1u<<k;
 for(int i=0;i<np;i++)for(int j=0;j<nn;j++)model.sep[i][j]=model.patt[i]&~model.natt[j];
 return model.rec((1u<<n)-1,(1ull<<np)-1,(1ull<<nn)-1);
}
