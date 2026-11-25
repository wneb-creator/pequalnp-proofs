#include <array>
#include <vector>
#include <iostream>
#include <fstream>
#include <random>
#include <chrono>
#include <cmath>
struct G{int a,b;bool op;};
std::array<uint64_t,40> v;std::array<int,40>d;std::vector<std::vector<G>> seeds;uint64_t target,mask;
std::mt19937_64 rng(2602);
struct Score{int bad,der,live;double cost()const{return 12.*bad+12.*der+live;}};
Score eval(const std::vector<G>&g){
 for(int j=0;j<(int)g.size();++j){auto [a,b,o]=g[j];v[10+j]=o?v[a]&v[b]:v[a]|v[b];
  if(!o)d[10+j]=d[a]|d[b];else d[10+j]=(((v[a]>>29&1)&&(d[b]&1))||((d[a]&1)&&(v[b]>>29&1)))|((((v[a]>>30&1)&&(d[b]&2))||((d[a]&2)&&(v[b]>>30&1)))<<1);
 }
 uint64_t live=1ULL<<(9+g.size());int ct=0;for(int j=g.size()-1;j>=0;--j)if(live>>(10+j)&1){++ct;live|=1ULL<<g[j].a;live|=1ULL<<g[j].b;}
 return {__builtin_popcountll((v[9+g.size()]^target)&mask),__builtin_popcount((unsigned)d[9+g.size()]),ct};
}
void print(const std::vector<G>&gs){for(int j=0;j<(int)gs.size();++j)std::cout<<10+j<<" "<<gs[j].a<<" "<<(gs[j].op?'&':'|')<<" "<<gs[j].b<<"\n";}
int main(int argc,char**argv){
 std::vector<std::pair<int,int>> es;for(auto [a,b]:std::vector<std::pair<int,int>>{{0,1},{0,2},{1,2},{0,3},{0,4},{3,4}}){es.push_back({a,b+5});es.push_back({b,a+5});}
 std::vector<int> rows;for(auto[a,b]:es)rows.push_back((1<<a)|(1<<b));
 auto independent=[&](int r){for(auto[a,b]:es)if((r>>a&1)&&(r>>b&1))return false;return true;};
 for(int r=0;r<1024;++r)if(independent(r)){bool maximal=true;for(int i=0;i<10;++i)if(!(r>>i&1)&&independent(r|(1<<i)))maximal=false;if(maximal)rows.push_back(r);}
 std::cout<<"critical="<<rows.size()<<"\n";if(rows.size()!=29)return 2;rows.push_back(1<<1);rows.push_back(1<<7);target=(1ULL<<12)-1;mask=(1ULL<<29)-1;
 for(int i=0;i<10;++i){for(int r=0;r<(int)rows.size();++r)if(rows[r]>>i&1)v[i]|=1ULL<<r;d[i]=i==7?1:i==1?2:0;}
 for(int f=2;f<argc;++f){std::ifstream in(argv[f]);std::vector<G>g;int a,b,o;while(in>>a>>b>>o)g.push_back({a,b,bool(o)});seeds.push_back(g);auto s=eval(g);std::cout<<"seed="<<f<<" gates="<<g.size()<<" bad="<<s.bad<<" deriv="<<s.der<<" live="<<s.live<<"\n";if(s.bad||s.der)return 3;}
 double maxsec=std::atof(argv[1]);auto began=std::chrono::steady_clock::now();auto g=seeds[0];auto cur=eval(g);int best=17;
 for(uint64_t it=0;;++it){if(it%100000==0){double sec=std::chrono::duration<double>(std::chrono::steady_clock::now()-began).count();if(sec>maxsec){std::cout<<"done iterations="<<it<<" best="<<best<<"\n";break;}if(it%2000000==0){g=seeds[(it/2000000)%seeds.size()];cur=eval(g);std::cout<<"restart="<<it<<" seconds="<<sec<<"\n"<<std::flush;}}
  auto old=g;int j=rng()%g.size();bool legal=true;
  if(rng()%20==0){int rep=rng()%(10+j);for(int l=j+1;l<(int)g.size();++l){if(g[l].a==10+j)g[l].a=rep;if(g[l].b==10+j)g[l].b=rep;if(g[l].a==g[l].b)legal=false;}}
  else if(rng()%8==0)g[j].op=!g[j].op;else if(rng()%2)g[j].a=rng()%(10+j);else g[j].b=rng()%(10+j);
  if(!legal||g[j].a==g[j].b){g=old;continue;}
  auto nxt=eval(g);double T=0.2+3.0*(1.-double(it%2000000)/2000000.);double delta=nxt.cost()-cur.cost();
  if(delta<=0||std::generate_canonical<double,53>(rng)<std::exp(-delta/T))cur=nxt;else g=old;
  if(cur.bad==0&&cur.der==0&&cur.live<best){best=cur.live;std::cout<<"FOUND live="<<best<<" iteration="<<it<<"\n";print(g);std::cout<<std::flush;if(best<=16)break;}
 }
}
