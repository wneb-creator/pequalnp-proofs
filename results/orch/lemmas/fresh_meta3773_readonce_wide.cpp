#include <algorithm>
#include <cstdint>
#include <unordered_map>
#include <vector>
using namespace std;
namespace {
struct Model {
 int np,nn;uint64_t guards;vector<uint64_t> digits;vector<int> support;vector<uint64_t> coverage;unordered_map<uint64_t,bool> memo;
 uint64_t cover(int index,int p)const{return coverage[support[index]*np+p];}
 bool rec(int s,uint64_t a,uint64_t b){
  if(!a||!b)return true;
  uint64_t key=(uint64_t(s)<<(np+nn))|(uint64_t(a)<<nn)|b;auto prior=memo.find(key);if(prior!=memo.end())return prior->second;
  for(uint64_t q=a;q;q&=q-1)if((cover(s,__builtin_ctzll(q))&b)!=b)return memo[key]=false;
  if((support[s]&(support[s]-1))==0)return memo[key]=true;
  // A componentwise valid multiset split has no borrow between the guarded packed count digits.
  uint64_t left=digits[s]|guards;
  for(int t=1;2*t<=s;t++){
   if(((left-digits[t])&guards)!=guards)continue;
   int u=s-t;uint64_t ca=b,cb=b,ta=0,tb=0;
   for(uint64_t q=a;q;q&=q-1){int i=__builtin_ctzll(q);uint64_t x=cover(t,i),y=cover(u,i);ca&=x;cb&=y;if((x&b)==b)ta|=1ull<<i;if((y&b)==b)tb|=1ull<<i;}
   if((ca|cb)==b){uint64_t opt=ca&cb,ls=b&~cb,rs=b&~ca;for(uint64_t p=opt;;p=(p-1)&opt){if(rec(t,a,ls|p)&&rec(u,a,rs|(p^opt)))return memo[key]=true;if(!p)break;}}
   if((ta|tb)==a){uint64_t opt=ta&tb,ls=a&~tb,rs=a&~ta;for(uint64_t p=opt;;p=(p-1)&opt){if(rec(t,ls|p,b)&&rec(u,rs|(p^opt),b))return memo[key]=true;if(!p)break;}}
  }
  return memo[key]=false;
 }
};}
extern "C" int feasible_multiset(int n,const uint64_t* fs,uint64_t P,uint64_t N){
 if(!P||!N)return 1;
 int np=__builtin_popcountll(P),nn=__builtin_popcountll(N);
 if(np>62||nn>62||np+nn+n>64||n>21)return -1;
 vector<uint64_t> f;vector<int> multiplicity;for(int i=0;i<n;i++){auto ix=find(f.begin(),f.end(),fs[i]);if(ix==f.end()){f.push_back(fs[i]);multiplicity.push_back(1);}else multiplicity[ix-f.begin()]++;}
 int distinct=f.size(),num=1,shift=0;uint64_t guards=0;vector<int> radix,bitpos;
 for(int m:multiplicity){radix.push_back(num);num*=m+1;int width=32-__builtin_clz(m);bitpos.push_back(shift);guards|=1ull<<(shift+width);shift+=width+1;}
 if(num>(1<<21)||shift>63)return -1;
 Model m{np,nn,guards,vector<uint64_t>(num),vector<int>(num),vector<uint64_t>((1<<distinct)*np),{}};
 for(int j=0;j<distinct;j++){
  int block=radix[j];for(int d=1;d<=multiplicity[j];d++)for(int i=0;i<block;i++){int id=d*block+i;m.digits[id]=m.digits[i]|uint64_t(d)<<bitpos[j];m.support[id]=m.support[i]|(1<<j);}
  int pindex=0;for(uint64_t p=P;p;p&=p-1,pindex++){uint64_t nm=0;int qindex=0;if(f[j]&(1ull<<__builtin_ctzll(p)))for(uint64_t q=N;q;q&=q-1,qindex++)if(!(f[j]&(1ull<<__builtin_ctzll(q))))nm|=1ull<<qindex;m.coverage[(1<<j)*np+pindex]=nm;}
 }
 for(int s=1;s<(1<<distinct);s++){int bit=s&-s,rest=s^bit;if(rest)for(int i=0;i<np;i++)m.coverage[s*np+i]=m.coverage[bit*np+i]|m.coverage[rest*np+i];}
 return m.rec(num-1,(1ull<<np)-1,(1ull<<nn)-1);
}
