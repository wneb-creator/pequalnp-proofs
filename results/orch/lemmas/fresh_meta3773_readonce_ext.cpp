#include <algorithm>
#include <cstdint>
#include <unordered_map>
#include <vector>
using namespace std;
namespace {
struct Solver {
 int n, np, nn;
 vector<uint32_t> covered;
 unordered_map<uint64_t,bool> memo;
 inline uint32_t cover(int S,int i) const { return covered[S*np+i]; }
 bool rec(int S,int A,int B){
  if(!A||!B) return true;
  const uint64_t key=(uint64_t(S)<<44)|(uint64_t(A)<<24)|uint64_t(B);
  auto found=memo.find(key); if(found!=memo.end()) return found->second;
  for(int q=A;q;q&=q-1) if((cover(S,__builtin_ctz(q))&B)!=B) return memo[key]=false;
  if((S&(S-1))==0) return memo[key]=true;
  for(int T=(S-1)&S;T;T=(T-1)&S){
   int U=S^T; if(T>=U) continue;
   int ca=B,cb=B,ta=0,tb=0;
   for(int q=A;q;q&=q-1){int i=__builtin_ctz(q);int t=cover(T,i),u=cover(U,i);ca&=t;cb&=u;if((t&B)==B)ta|=1<<i;if((u&B)==B)tb|=1<<i;}
   if((ca|cb)==B){int opt=ca&cb,ls=B&~cb,rs=B&~ca;for(int sel=opt;;sel=(sel-1)&opt){if(rec(T,A,ls|sel)&&rec(U,A,rs|(opt^sel)))return memo[key]=true;if(!sel)break;}}
   if((ta|tb)==A){int opt=ta&tb,ls=A&~tb,rs=A&~ta;for(int sel=opt;;sel=(sel-1)&opt){if(rec(T,ls|sel,B)&&rec(U,rs|(opt^sel),B))return memo[key]=true;if(!sel)break;}}
  }
  return memo[key]=false;
 }
};
}
extern "C" int feasible(int n,const uint64_t *features,uint64_t P,uint64_t N){
 if(!P||!N)return 1;
 int np=__builtin_popcountll(P),nn=__builtin_popcountll(N);if(np>20||nn>24||n>20)return -1;
 Solver s{n,np,nn,vector<uint32_t>((1<<n)*np),{}};
 for(int j=0;j<n;j++){int i=0;for(uint64_t p=P;p;p&=p-1,i++){
  int negmask=0,k=0; if(features[j]&(1ull<<__builtin_ctzll(p)))for(uint64_t q=N;q;q&=q-1,k++)if(!(features[j]&(1ull<<__builtin_ctzll(q))))negmask|=1<<k;
  s.covered[(1<<j)*np+i]=negmask;
 }}
 for(int S=1;S<(1<<n);S++){int bit=S&-S,rest=S^bit;if(!rest)continue;for(int i=0;i<np;i++)s.covered[S*np+i]=s.covered[bit*np+i]|s.covered[rest*np+i];}
 return s.rec((1<<n)-1,(1<<np)-1,(1<<nn)-1)?1:0;
}
extern "C" int splits(int n,const uint64_t *F,int np,int nn,uint32_t *out){
 if(np>20||nn>24||n>20) return -1;
 vector<uint32_t> cov((1<<n)*np);const int N=(1<<nn)-1, af=(1<<n)-1;
 for(int j=0;j<n;j++)for(int p=0;p<np;p++)if(F[j]&(1u<<p))cov[(1<<j)*np+p]=N&~(F[j]>>np);
 for(int s=1;s<=af;s++){int bit=s&-s,rest=s^bit;if(rest)for(int p=0;p<np;p++)cov[s*np+p]=cov[bit*np+p]|cov[rest*np+p];}
 int count=0;
 for(int s=1;s<af;s++){
  if(!(s&(s-1)))continue;
  int t=af^s,gp=0,gn=0;
  for(int p=0;p<np;p++){int miss=N&~cov[t*np+p];if(miss)gp|=1<<p;gn|=miss;}
  bool ok=true;for(int q=gp;q;q&=q-1)if((cov[s*np+__builtin_ctz(q)]&gn)!=gn){ok=false;break;}
  if(ok){out[3*count]=s;out[3*count+1]=gp;out[3*count+2]=gn;count++;}
 }return count;
}
