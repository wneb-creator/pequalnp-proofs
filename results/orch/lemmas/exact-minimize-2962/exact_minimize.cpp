#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <random>
#include <string>
#include <vector>
using U = uint64_t;
struct Gate { int op,a,b; };
struct Circuit { std::vector<Gate> g; int out; };
struct Model { std::string name; int n,k,rows; U target; std::vector<U> inputs; std::vector<Circuit> seeds; int best=1000; U tests=0; std::vector<Circuit> elite; };
std::mt19937_64 rng(718276);
int pick(int n){return int(rng()%n);}
double unit(){return (rng()>>11)*0x1.0p-53;}
U evaluate(const Model&m,const Circuit&c,std::array<U,128>*save=nullptr){
 std::array<U,128> v{}; std::copy(m.inputs.begin(),m.inputs.end(),v.begin());
 for(size_t i=0;i<c.g.size();++i){auto g=c.g[i]; v[m.n+i]=g.op?(v[g.a]|v[g.b]):(v[g.a]&v[g.b]);}
 if(save)*save=v;
 return v[c.out];
}
int active(const Model&m,const Circuit&c){
 U seen=0; if(c.out>=m.n)seen|=U(1)<<(c.out-m.n);
 for(int j=int(c.g.size())-1;j>=0;--j)if(seen>>j&1){for(int w:{c.g[j].a,c.g[j].b})if(w>=m.n)seen|=U(1)<<(w-m.n);}
 return std::popcount(seen);
}
Circuit remove_gate(const Model&m,const Circuit&c,int j,int replacement){
 Circuit d; int wire=m.n+j;
 auto sub=[&](int w){if(w==wire)return replacement;return w>wire?w-1:w;};
 for(int i=0;i<int(c.g.size());++i)if(i!=j){auto g=c.g[i];d.g.push_back({g.op,sub(g.a),sub(g.b)});}
 d.out=sub(c.out);return d;
}
Circuit seed(const Model&m){
 auto c=m.seeds[pick(m.seeds.size())];int j=pick(c.g.size());
 int replacement=pick(5)<4?(pick(2)?c.g[j].a:c.g[j].b):pick(m.n+j);
 return remove_gate(m,c,j,replacement);
}
Circuit mutate(const Model&m,const Circuit&c){
 Circuit d=c; int type=pick(100);
 if(type<72){
  int count=1+(pick(100)<13)+(pick(100)<3);
  while(count--){int j=pick(m.k),field=pick(7); if(field==0)d.g[j].op^=1;
    else if(field<4)d.g[j].a=pick(m.n+j);else d.g[j].b=pick(m.n+j);}
 }else if(type<78){d.out=pick(m.n+m.k);}
 else if(type<88){
  int j=pick(m.k-1); auto b=d.g[j+1];int w=m.n+j;
  if(b.a!=w&&b.b!=w){
   std::swap(d.g[j],d.g[j+1]);
   auto swapw=[&](int x){return x==w?w+1:x==w+1?w:x;};
   for(int t=j+2;t<m.k;++t){d.g[t].a=swapw(d.g[t].a);d.g[t].b=swapw(d.g[t].b);} d.out=swapw(d.out);
  }
 }else{
  std::array<U,128> v;evaluate(m,c,&v); int j=pick(m.k),w=m.n+j,rep=-1;
  for(int t=0;t<w;++t)if(v[t]==v[w]){rep=t;break;}
  if(rep<0)rep=pick(2)?d.g[j].a:d.g[j].b;
  d=remove_gate(m,d,j,rep);
  int a=pick(m.n+m.k-1),b=pick(m.n+m.k-1);d.g.push_back({pick(2),a,b});
  if(pick(2))d.out=m.n+m.k-1;
 }
 return d;
}
void save(const std::string&path,const Model&m,const Circuit&c,int loss,U mask){
 std::ofstream f(path); f<<"{\"model\":\""<<m.name<<"\",\"n\":"<<m.n<<",\"gate_budget\":"<<m.k<<",\"loss\":"<<loss<<",\"output\":"<<c.out<<",\"signature\":"<<mask<<",\"gates\":[";
 for(size_t i=0;i<c.g.size();++i){auto g=c.g[i];if(i)f<<',';f<<'['<<g.op<<','<<g.a<<','<<g.b<<']';}f<<"]}\n";
}
int main(int argc,char**argv){
 if(argc!=4){std::cerr<<"usage: exact_minimize DATA SECONDS OUTPUT_DIRECTORY\n";return 2;}
 std::ifstream f(argv[1]);int count;f>>count;std::vector<Model> models(count);
 for(auto&m:models){int ns;f>>m.name>>m.n>>m.k>>m.rows>>ns;f>>m.target;m.inputs.resize(m.n);for(auto&x:m.inputs)f>>x;
  for(int s=0;s<ns;++s){Circuit c;f>>c.out;for(int j=0;j<m.k+1;++j){Gate g;f>>g.op>>g.a>>g.b;c.g.push_back(g);}if(evaluate(m,c)!=m.target){std::cerr<<"bad seed\n";return 3;}m.seeds.push_back(c);}}
 if(!f){std::cerr<<"bad data\n";return 4;}
 auto start=std::chrono::steady_clock::now();double limit=std::stod(argv[2]),last=0;U rounds=0;
 auto elapsed=[&](){return std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();};
 while(elapsed()<limit){
  auto&m=models[rounds++%models.size()]; Circuit c=(m.elite.empty()||pick(100)<65)?seed(m):m.elite[pick(m.elite.size())];
  U val=evaluate(m,c);int used=active(m,c);
  double fpweight=1.0+pick(4)*0.4;
  auto score=[&](U v,int ac){return std::popcount(m.target&~v)+fpweight*std::popcount(v&~m.target)+0.015*ac;};
  double energy=score(val,used),temp=(pick(100)<70?0.05:0.7+unit()*1.3);
  for(int iter=0;iter<30000&&elapsed()<limit;++iter){
   auto d=mutate(m,c);U nv=evaluate(m,d);++m.tests;int nl=std::popcount(nv^m.target),nu=active(m,d);double ne=score(nv,nu);
   if(nl<m.best){m.best=nl;m.elite.clear();save(std::string(argv[3])+"/minimize-best-"+m.name+".json",m,d,nl,nv);std::cout<<"BEST "<<m.name<<" loss="<<nl<<" evaluations="<<m.tests<<" seconds="<<elapsed()<<std::endl;}
   if(nl==0){save(std::string(argv[3])+"/minimize-FOUND.json",m,d,nl,nv);std::cout<<"FOUND "<<m.name<<std::endl;return 0;}
   if(nl==m.best&&pick(2000)==0){if(m.elite.size()<64)m.elite.push_back(d);else m.elite[pick(64)]=d;}
   double t=temp*(1.0-double(iter)/32000.0);
   if(ne<=energy||unit()<std::exp((energy-ne)/t)){c=std::move(d);val=nv;used=nu;energy=ne;}
  }
  double now=elapsed();if(now-last>30){last=now;std::cout<<"PROGRESS seconds="<<now;for(auto&m:models)std::cout<<' '<<m.name<<"_evaluations="<<m.tests<<" best="<<m.best;std::cout<<std::endl;}
 }
 std::cout<<"DONE seconds="<<elapsed();for(auto&m:models)std::cout<<' '<<m.name<<"_evaluations="<<m.tests<<" best="<<m.best;std::cout<<std::endl;
 return 1;
}
