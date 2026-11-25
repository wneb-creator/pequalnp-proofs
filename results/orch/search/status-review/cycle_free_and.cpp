#include <vector>
#include <array>
#include <random>
#include <iostream>
#include <chrono>
#include <cmath>
struct G{uint64_t a,b;};
std::mt19937_64 rng(26021480ULL);
int N=8,K=6,R=0;uint64_t target=0,valid=0;
std::array<uint64_t,32> v;
uint64_t bit(int i){return 1ULL<<i;}
std::vector<G> init(){return {{bit(4),bit(5)},{bit(5),bit(6)},{bit(6),bit(7)},
 {bit(0)|bit(8),bit(1)|bit(9)}, {bit(11),bit(2)|bit(10)}, {bit(12),bit(3)|bit(7)}};}
uint64_t conj(uint64_t mask){uint64_t z=valid;while(mask){int i=__builtin_ctzll(mask);mask&=mask-1;z&=v[i];}return z;}
int eval(const std::vector<G>&gs,uint64_t out){for(int j=0;j<K;++j)v[N+j]=conj(gs[j].a)|conj(gs[j].b);return __builtin_popcountll((conj(out)^target)&valid);}
void print(const std::vector<G>&gs,uint64_t out){for(int j=0;j<K;++j)std::cout<<N+j<<" "<<gs[j].a<<" | "<<gs[j].b<<"\n";std::cout<<"output_AND="<<out<<"\n";}
int main(int argc,char**argv){std::vector<int>rows;std::array<int,4>ns{};
 for(int p=0;p<4;++p)for(int l=0;l<4;++l)if(l==p||l==(p+1)%4){ns[p]|=1<<l;rows.push_back((1<<p)|(1<<(4+l)));}
 for(int S=0;S<16;++S){int T=15;for(int p=0;p<4;++p)if(S>>p&1)T&=~ns[p];int U=0;for(int p=0;p<4;++p)if(!(ns[p]&T))U|=1<<p;if(S==U)rows.push_back(S|(T<<4));}
 R=rows.size();target=(1ULL<<8)-1;valid=(1ULL<<R)-1;for(int i=0;i<N;++i)for(int r=0;r<R;++r)if(rows[r]>>i&1)v[i]|=1ULL<<r;
 auto gs=init();uint64_t out=bit(13);int cur=eval(gs,out),best=cur;std::cout<<"rows="<<R<<" OR_budget="<<K<<" initial="<<cur<<"\n";
 auto began=std::chrono::steady_clock::now();double secmax=argc>1?std::atof(argv[1]):180.;
 for(uint64_t it=0;;++it){if(it%100000==0){double sec=std::chrono::duration<double>(std::chrono::steady_clock::now()-began).count();if(sec>=secmax){std::cout<<"done iterations="<<it<<" best="<<best<<"\n";break;}if(it%3000000==0){gs=init();out=bit(13);cur=eval(gs,out);std::cout<<"restart="<<it<<" seconds="<<sec<<" best="<<best<<"\n"<<std::flush;}}
  int j=rng()%K;auto old=gs[j];auto oldout=out;int mode=rng()%20;
  if(mode==0)out^=bit(rng()%(N+K));else {auto&m=(rng()%2)?gs[j].a:gs[j].b;int flips=mode<3?2:1;for(int k=0;k<flips;++k)m^=bit(rng()%(N+j));}
  int nxt=eval(gs,out);double T=0.025+0.35*(1.-double(it%3000000)/3000000.);
  if(nxt<=cur||std::generate_canonical<double,53>(rng)<std::exp(double(cur-nxt)/T))cur=nxt;else {gs[j]=old;out=oldout;}
  if(cur<best){best=cur;std::cout<<"BEST="<<best<<" iteration="<<it<<"\n";print(gs,out);std::cout<<std::flush;}if(cur==0){std::cout<<"FOUND\n";print(gs,out);break;}
 }
}
