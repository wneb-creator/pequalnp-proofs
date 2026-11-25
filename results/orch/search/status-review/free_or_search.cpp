#include <vector>
#include <array>
#include <random>
#include <iostream>
#include <chrono>
#include <cmath>
#include <algorithm>
struct G{uint64_t a,b;};
std::mt19937_64 rng(65114802602ULL);
int N=14,K=6,R=0;uint64_t target=0,valid=0;
std::array<uint64_t,32> v;
std::vector<G> init(int skip){std::vector<G> gs;for(int l=0;l<7;++l)if(l!=skip){uint64_t mask=0;for(int p=0;p<7;++p)if((p-l+7)%7==0||(p-l+7)%7==1||(p-l+7)%7==3)mask|=1ULL<<p;gs.push_back({mask,1ULL<<(7+l)});}return gs;}
uint64_t disj(uint64_t mask){uint64_t z=0;while(mask){int i=__builtin_ctzll(mask);mask&=mask-1;z|=v[i];}return z;}
int eval(const std::vector<G>& gs,uint64_t out){for(int j=0;j<K;++j)v[N+j]=disj(gs[j].a)&disj(gs[j].b);uint64_t z=disj(out);return __builtin_popcountll((z^target)&valid);}
void print(const std::vector<G>&gs,uint64_t out){for(int j=0;j<K;++j)std::cout<<N+j<<" "<<gs[j].a<<" & "<<gs[j].b<<"\n";std::cout<<"output="<<out<<"\n";}
int main(int argc,char**argv){
 std::array<int,7> ns{};std::vector<int> rows;
 for(int p=0;p<7;++p)for(int l=0;l<7;++l)if((p-l+7)%7==0||(p-l+7)%7==1||(p-l+7)%7==3){ns[p]|=1<<l;rows.push_back((1<<p)|(1<<(7+l)));}
 for(int S=0;S<128;++S){int T=127;for(int p=0;p<7;++p)if(S>>p&1)T&=~ns[p];int U=0;for(int p=0;p<7;++p)if(!(ns[p]&T))U|=1<<p;if(S==U)rows.push_back(S|(T<<7));}
 R=rows.size();target=(1ULL<<21)-1;valid=(1ULL<<R)-1;
 for(int i=0;i<N;++i)for(int r=0;r<R;++r)if(rows[r]>>i&1)v[i]|=1ULL<<r;
 std::cout<<"rows="<<R<<" and_budget="<<K<<"\n";
 auto began=std::chrono::steady_clock::now();double seconds=argc>1?std::atof(argv[1]):120.;uint64_t out=((1ULL<<K)-1)<<N;auto gs=init(0);int cur=eval(gs,out),best=cur;
 for(uint64_t it=0;;++it){
  if(it%100000==0){double sec=std::chrono::duration<double>(std::chrono::steady_clock::now()-began).count();if(sec>=seconds){std::cout<<"done iterations="<<it<<" best="<<best<<"\n";break;}if(it%2000000==0){gs=init((it/2000000)%7);out=((1ULL<<K)-1)<<N;cur=eval(gs,out);std::cout<<"restart="<<it<<" seconds="<<sec<<" best="<<best<<"\n"<<std::flush;}}
  int j=rng()%K;auto old=gs[j];uint64_t oldout=out;
  int mode=rng()%20;
  if(mode==0)out^=1ULL<<(N+rng()%K);
  else{uint64_t& m=(rng()%2)?gs[j].a:gs[j].b;int flips=mode<3?2:1;for(int t=0;t<flips;++t)m^=1ULL<<(rng()%(N+j));}
  int next=eval(gs,out);double T=0.08+0.6*(1.-double(it%2000000)/2000000.);
  if(next<=cur || std::generate_canonical<double,53>(rng)<std::exp(double(cur-next)/T))cur=next;else {gs[j]=old;out=oldout;}
  if(cur<best){best=cur;std::cout<<"BEST errors="<<best<<" iteration="<<it<<"\n";print(gs,out);std::cout<<std::flush;}
  if(cur==0){std::cout<<"FOUND\n";print(gs,out);break;}
 }
}
