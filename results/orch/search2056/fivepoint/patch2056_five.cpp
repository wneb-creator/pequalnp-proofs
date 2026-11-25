#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <numeric>
#include <random>
#include <vector>
using U=uint64_t;constexpr int GATES=23,POINTS=5;
struct Gate{int op,a,b;};using Net=std::array<Gate,GATES>;
struct Data{int inputs=0,id=0;std::vector<int>rows;std::vector<std::array<int,2>>edges;std::array<U,48>val{};U target=0,negative=0,mask=0;int raw=0,fp=0,bad=0;std::array<Net,2>best{};std::array<int,2>bs{100000,100000},br{100000,100000};std::array<std::vector<Net>,2>pool;long long iterations=0;int restarts=0;};
int eval(Data&d,Net&c,int mode){
 U P[48]={},L[48]={},G[48]={};for(int i=0;i<d.inputs;i++)if(i<POINTS)P[i]=d.val[i]&d.target;else L[i]=d.val[i]&d.target;
 int inputDuplicate=0,empty=0,duplicate=0;
 for(int j=0;j<GATES;j++){auto g=c[j];U value=g.op?(d.val[g.a]|d.val[g.b]):(d.val[g.a]&d.val[g.b]);U profile=value&d.target;
  if(std::popcount(profile)==1){int k=std::countr_zero(profile);g={0,d.edges[k][0],d.edges[k][1]};c[j]=g;value=d.val[g.a]&d.val[g.b];}
  int w=d.inputs+j;d.val[w]=value;if(g.op){P[w]=P[g.a]|P[g.b];L[w]=L[g.a]|L[g.b];G[w]=G[g.a]|G[g.b];}else G[w]=(P[g.a]&L[g.b])|(L[g.a]&P[g.b]);
  empty+=profile==0;duplicate+=g.a==g.b;for(int i=0;i<d.inputs;i++)if(value==d.val[i]){inputDuplicate++;break;}
 }
 U output=d.val[d.inputs+GATES-1],err=(output^d.target)&d.mask;d.raw=std::popcount(err);d.fp=std::popcount(err&d.negative);d.bad=std::popcount(output&d.target&~G[d.inputs+GATES-1]);
 return d.raw+2*inputDuplicate+2*empty+2*duplicate+(mode&&d.bad==0?6:0);
}
void show(const Data&d,const Net&c,int score,int mode,double seconds){std::cout<<"{\"case\":"<<d.id<<",\"inputs\":"<<d.inputs<<",\"mode\":"<<mode<<",\"seconds\":"<<seconds<<",\"score\":"<<score<<",\"raw\":"<<d.raw<<",\"fp\":"<<d.fp<<",\"bad_edges\":"<<d.bad<<",\"iterations\":"<<d.iterations<<",\"gates\":[";for(int j=0;j<GATES;j++){auto g=c[j];if(j)std::cout<<",";std::cout<<"["<<g.op<<","<<g.a<<","<<g.b<<"]";}std::cout<<"]}"<<std::endl;}
std::vector<Gate>star(const Data&d,std::mt19937&rng,bool dirty){
 std::vector<Gate>c;std::array<int,POINTS>order;std::iota(order.begin(),order.end(),0);std::shuffle(order.begin(),order.end(),rng);std::array<std::vector<int>,POINTS>nb;
 for(auto e:d.edges)nb[e[0]].push_back(e[1]);int repeated=rng()%POINTS,dup=repeated;
 if(dirty){int other=rng()%4?nb[repeated][rng()%nb[repeated].size()]:rng()%d.inputs;if(other==repeated)other=(other+1)%d.inputs;c.push_back({1,repeated,other});c.push_back({0,repeated,d.inputs});dup=d.inputs+1;}
 auto inp=[&](int x){return x==repeated?dup:x;};std::vector<int>roots;
 for(int p:order){auto leaves=nb[p];std::shuffle(leaves.begin(),leaves.end(),rng);int a=inp(leaves[0]);for(int k=1;k<(int)leaves.size();k++){int w=d.inputs+c.size();c.push_back({1,a,inp(leaves[k])});a=w;}int w=d.inputs+c.size();c.push_back({0,inp(p),a});roots.push_back(w);}
 while(roots.size()>1){int ia=rng()%roots.size(),a=roots[ia];roots.erase(roots.begin()+ia);int ib=rng()%roots.size(),b=roots[ib];roots.erase(roots.begin()+ib);int w=d.inputs+c.size();c.push_back({1,a,b});roots.push_back(w);}return c;
}
Net deleted(const Data&d,std::vector<Gate>base,std::mt19937&rng){int protect=base.size()==26?2:0;
 while(base.size()>GATES){std::vector<int>eligible;for(int j=protect;j<(int)base.size()-1;j++)if(base[j].op==1&&(base[j].a<d.inputs||base[j].b<d.inputs))eligible.push_back(j);
  int rem=(!eligible.empty()&&rng()%4)?eligible[rng()%eligible.size()]:protect+rng()%(base.size()-1-protect);int sub=base[rem].a>=d.inputs?base[rem].a:base[rem].b>=d.inputs?base[rem].b:rng()%2?base[rem].a:base[rem].b;
  base.erase(base.begin()+rem);for(auto&q:base){auto fix=[&](int v){if(v==d.inputs+rem)v=sub;if(v>d.inputs+rem)v--;return v;};q.a=fix(q.a);q.b=fix(q.b);}}
 Net c;std::copy(base.begin(),base.end(),c.begin());return c;
}
bool valid(const Data&d,const Net&c){for(int j=0;j<GATES;j++)if(c[j].a>=d.inputs+j||c[j].b>=d.inputs+j)return false;return true;}
void mutate(const Data&d,Net&c,std::mt19937&rng,int strength){
 for(int t=0;t<strength;t++){int j=rng()%GATES,kind=rng()%20;auto&g=c[j];
  if(kind<2)g.op=1-g.op;else if(kind<8)g.a=rng()%(d.inputs+j);else if(kind<14)g.b=rng()%(d.inputs+j);
  else if(kind==14)g={int(rng()%2),int(rng()%(d.inputs+j)),int(rng()%(d.inputs+j))};
  else if(kind==15){int old=rng()%(d.inputs+j),sub=rng()%(d.inputs+j);for(int k=j;k<GATES;k++){if(c[k].a==old)c[k].a=sub;if(c[k].b==old)c[k].b=sub;}}
  else if(kind==16){int old=d.inputs+j,sub=rng()%2?g.a:g.b;for(int k=j+1;k<GATES;k++){if(c[k].a==old)c[k].a=sub;if(c[k].b==old)c[k].b=sub;}}
  else if(kind==17){int h=rng()%GATES;std::swap(c[h].op,c[j].op);}
  else if(kind==18){int a=g.a,b=g.b;if(a<d.inputs)std::swap(a,b);if(a>=d.inputs){int h=a-d.inputs,uses=0;for(int k=h+1;k<GATES;k++)uses+=(c[k].a==a)+(c[k].b==a);if(uses==1&&c[h].op==g.op&&b<d.inputs+h){int old=c[h].b;c[h].b=b;g.a=a;g.b=old;}}}
  else{int h=rng()%GATES;if(h<j)std::swap(h,j);if(h!=j&&c[h].a<d.inputs+j&&c[h].b<d.inputs+j){std::swap(c[h],c[j]);for(int k=j+1;k<GATES;k++){if(c[k].a==d.inputs+j)c[k].a=d.inputs+h;else if(c[k].a==d.inputs+h)c[k].a=d.inputs+j;if(c[k].b==d.inputs+j)c[k].b=d.inputs+h;else if(c[k].b==d.inputs+h)c[k].b=d.inputs+j;}}}
 }
}
int main(int argc,char**argv){if(argc!=4)return 2;std::ifstream f(argv[1]);int count;f>>count;if(count!=3)return 3;std::vector<Data>cases(count);
 for(int id=0;id<count;id++){auto&d=cases[id];d.id=id;int pos,neg;f>>d.inputs>>pos>>neg;if(pos!=20||neg!=32||d.inputs+GATES>48)return 4;
  for(int k=0;k<pos+neg;k++){int r;f>>r;d.rows.push_back(r);for(int i=0;i<d.inputs;i++)if((r>>i)&1)d.val[i]|=U(1)<<k;
   if(k<pos){d.target|=U(1)<<k;d.edges.push_back({std::countr_zero((unsigned)r),std::countr_zero((unsigned)(r&(r-1)))});}else d.negative|=U(1)<<k;d.mask|=U(1)<<k;}
 }
 std::mt19937 rng(std::stoul(argv[3]));int seconds=std::stoi(argv[2]);for(auto&d:cases)for(int t=0;t<64;t++){auto base=star(d,rng,t%2);std::vector<U>v(d.inputs+base.size());std::copy(d.val.begin(),d.val.begin()+d.inputs,v.begin());for(int j=0;j<(int)base.size();j++){auto g=base[j];v[d.inputs+j]=g.op?(v[g.a]|v[g.b]):(v[g.a]&v[g.b]);}if((v.back()&d.mask)!=d.target){std::cerr<<"positive control failed case"<<d.id<<std::endl;return 5;}}
 std::cerr<<"PASS192 randomized positive seed controls across3 cases"<<std::endl;
 auto start=std::chrono::steady_clock::now();auto elapsed=[&]{return std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();};
 while(elapsed()<seconds){auto&d=cases[rng()%cases.size()];int mode=rng()%2;Net c;if(!d.pool[mode].empty()&&rng()%3){c=d.pool[mode][rng()%d.pool[mode].size()];mutate(d,c,rng,1+rng()%5);if(!valid(d,c))c=deleted(d,star(d,rng,mode||rng()%4==0),rng);}else c=deleted(d,star(d,rng,mode||rng()%4==0),rng);
  int sc=eval(d,c,mode),cycle=30000+int(rng()%70000);double initial=.5+double(rng()%600)/100.0;
  for(int z=0;z<cycle;z++,d.iterations++){Net nc=c;int strength=1;auto rm=rng()%100;if(rm<10)strength=2;else if(rm<13)strength=3+rng()%4;mutate(d,nc,rng,strength);if(!valid(d,nc))continue;int ns=eval(d,nc,mode),rr=d.raw;
   if(ns<d.bs[mode]||(ns==d.bs[mode]&&rr<d.br[mode])){d.bs[mode]=ns;d.br[mode]=rr;d.best[mode]=nc;show(d,nc,ns,mode,elapsed());}if(rr==0){show(d,nc,ns,mode,elapsed());return 0;}
   if(ns<=d.bs[mode]+2&&rng()%200==0){auto&pool=d.pool[mode];if(pool.size()<128)pool.push_back(nc);else pool[rng()%pool.size()]=nc;}
   double temp=.04+initial*std::exp(-double(z)/(cycle/6.0));bool accept=ns<=sc||std::generate_canonical<double,32>(rng)<std::exp(double(sc-ns)/temp);if(accept){c=nc;sc=ns;}
  }d.restarts++;if(d.restarts%100==0){for(int m=0;m<2;m++)if(d.bs[m]<100000){int sc=eval(d,d.best[m],m);show(d,d.best[m],sc,m,elapsed());}}
 }
 for(auto&d:cases)for(int m=0;m<2;m++)if(d.bs[m]<100000){int sc=eval(d,d.best[m],m);show(d,d.best[m],sc,m,elapsed());}return 0;
}
