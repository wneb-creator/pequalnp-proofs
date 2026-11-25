#include <array>
#include <vector>
#include <random>
#include <iostream>
#include <fstream>
#include <chrono>
#include <algorithm>
#include <cmath>
using Sig=std::array<uint64_t,12>;
struct G{int a,b;bool andop;};
struct Score{int bad,deriv,live; double total()const{return 18.*bad+20.*deriv+live;}};
std::array<Sig,100> vals;
std::array<int,100> der;
std::array<bool,100> live;
std::mt19937_64 rng(2602);
std::vector<G> seed;
Sig want{};
Score eval(const std::vector<G>& gs){
 for(int j=0;j<(int)gs.size();++j){auto g=gs[j];int k=26+j;
  for(int b=0;b<12;++b)vals[k][b]=g.andop?(vals[g.a][b]&vals[g.b][b]):(vals[g.a][b]|vals[g.b][b]);
  if(!g.andop)der[k]=der[g.a]|der[g.b];
  else{
   bool ax=(vals[g.a][756/64]>>(756%64))&1,bx=(vals[g.b][756/64]>>(756%64))&1;
   bool ay=(vals[g.a][757/64]>>(757%64))&1,by=(vals[g.b][757/64]>>(757%64))&1;
   der[k]=(ax&&(der[g.b]&1) || (der[g.a]&1)&&bx) | ((ay&&(der[g.b]&2) || (der[g.a]&2)&&by)<<1);
  }
 }
 int out=25+gs.size(),bad=0;
 for(int b=0;b<12;++b){auto z=vals[out][b]^want[b];if(b==11)z&=((1ULL<<52)-1);bad+=__builtin_popcountll(z);}
 live.fill(false);live[out]=true;int ct=0;
 for(int j=gs.size()-1;j>=0;--j)if(live[26+j]){++ct;live[gs[j].a]=live[gs[j].b]=true;}
 return {bad,__builtin_popcount((unsigned)der[out]),ct};
}
std::vector<G> start(bool side){
 if(!seed.empty()) return seed;
 std::vector<G> gs;std::vector<int> terms;
 auto add=[&](int a,int b,bool op){gs.push_back({a,b,op});return 25+(int)gs.size();};
 for(int l=0;l<13;++l){std::vector<int> ns;for(int p=0;p<13;++p)if((p-l+13)%13==0||(p-l+13)%13==1||(p-l+13)%13==3||(p-l+13)%13==9)ns.push_back(p);
  if(side){ns.clear();for(int r=0;r<13;++r)if((l-r+13)%13==0||(l-r+13)%13==1||(l-r+13)%13==3||(l-r+13)%13==9)ns.push_back(13+r);}
  int u=ns[0];for(int k=1;k<4;++k)u=add(u,ns[k],false);
  int t=add(u,side?l:13+l,true);
  if(l==0){int dup=add(u,side?l:13+l,true);t=add(t,dup,true);}
  terms.push_back(t);
 }
 int u=terms[0];for(int k=1;k<13;++k)u=add(u,terms[k],false);
 return gs;
}
void print(const std::vector<G>& gs){for(int j=0;j<(int)gs.size();++j)std::cout<<26+j<<" "<<gs[j].a<<" "<<(gs[j].andop?'&':'|')<<" "<<gs[j].b<<"\n";}
int main(int argc,char** argv){
 if(argc>2){std::ifstream in(argv[2]); int a,b,op;while(in>>a>>b>>op)seed.push_back({a,b,bool(op)});}
 std::vector<int> rows;
 for(int l=0;l<13;++l)for(int p=0;p<13;++p)if((p-l+13)%13==0||(p-l+13)%13==1||(p-l+13)%13==3||(p-l+13)%13==9)rows.push_back((1<<p)|(1<<(13+l)));
 std::array<int,13> ns{};for(int p=0;p<13;++p)for(int l=0;l<13;++l)if((p-l+13)%13==0||(p-l+13)%13==1||(p-l+13)%13==3||(p-l+13)%13==9)ns[p]|=1<<l;
 for(int S=0;S<8192;++S){int N=0;for(int p=0;p<13;++p)if(S>>p&1)N|=ns[p];int T=8191^N,S2=0;for(int p=0;p<13;++p)if(!(ns[p]&T))S2|=1<<p;if(S==S2)rows.push_back(S|(T<<13));}
 std::cout<<"samples="<<rows.size()<<"\n";if(rows.size()!=756)return 2;
 rows.push_back(1);rows.push_back(1<<13);
 for(int x=0;x<26;++x){for(int i=0;i<(int)rows.size();++i)if(rows[i]>>x&1)vals[x][i/64]|=1ULL<<(i%64);der[x]=x==13?1:x==0?2:0;}
 want[0]=(1ULL<<52)-1;
 double seconds=argc>1?std::atof(argv[1]):120.;auto began=std::chrono::steady_clock::now();
 uint64_t it=0;int best=65;auto gs=start(false);auto score=eval(gs);
 std::cout<<"initial bad="<<score.bad<<" deriv="<<score.deriv<<" live="<<score.live<<"\n";
 for(;;++it){
  if(it%100000==0){double sec=std::chrono::duration<double>(std::chrono::steady_clock::now()-began).count();if(sec>=seconds)break;if(it%2000000==0){gs=start((it/2000000)%2);score=eval(gs);std::cout<<"restart iteration="<<it<<" seconds="<<sec<<"\n"<<std::flush;}}
  int j=rng()%gs.size();auto old=gs[j];auto cand=old;
  if(rng()%8==0)cand.andop=!cand.andop;
  else if(rng()%2)cand.a=rng()%(26+j);else cand.b=rng()%(26+j);
  if(cand.a==cand.b)continue;gs[j]=cand;
  auto next=eval(gs);double T=0.5+5.0*(1.-double(it%2000000)/2000000.);
  double delta=next.total()-score.total();
  if(delta<=0 || std::generate_canonical<double,53>(rng)<std::exp(-delta/T))score=next;else gs[j]=old;
  if(score.bad==0 && score.deriv==0 && score.live<best){best=score.live;std::cout<<"FOUND live="<<best<<" iteration="<<it<<"\n";print(gs);std::cout<<std::flush;if(best<=64)return 0;}
 }
 std::cout<<"done iterations="<<it<<" best="<<best<<"\n";
}
