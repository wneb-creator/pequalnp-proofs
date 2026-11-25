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
using U=uint64_t;
constexpr int INPUTS=10,GATES=19,WIRES=29;
struct Gate{int op,a,b;};using Net=std::array<Gate,GATES>;
std::array<U,WIRES>val;U target=0,negative=0,mask=0;int canonical=-1;
int raw,fp,joint,accepted;
int E[15][2]={{0,1},{1,2},{2,3},{3,4},{4,0},{0,5},{1,6},{2,7},{3,8},{4,9},{5,7},{7,9},{9,6},{6,8},{8,5}};
int covers[5]={907,822,621,469,250};
int eval(const Net&c){
 unsigned char good[WIRES]={};good[0]=1;good[1]=2;int duplicate=0;
 for(int j=0;j<GATES;j++){auto g=c[j];val[INPUTS+j]=g.op?(val[g.a]|val[g.b]):(val[g.a]&val[g.b]);int a=good[g.a],b=good[g.b];good[INPUTS+j]=g.op?(a|b):(((a&1)&&(b&2))||((a&2)&&(b&1))?4:0);duplicate+=g.a==g.b;}
 U err=(val[WIRES-1]^target)&mask;raw=std::popcount(err);fp=std::popcount(err&negative);joint=(good[WIRES-1]&4)!=0;accepted=(val[WIRES-1]>>canonical)&1;
 return raw+8*joint+16*(1-accepted)+2*duplicate;
}
void show(const Net&c,int score,long long it,double seconds){std::cout<<"{\"seconds\":"<<seconds<<",\"score\":"<<score<<",\"raw\":"<<raw<<",\"fp\":"<<fp<<",\"joint\":"<<joint<<",\"accepted\":"<<accepted<<",\"iterations\":"<<it<<",\"gates\":[";for(int j=0;j<GATES;j++){auto g=c[j];if(j)std::cout<<",";std::cout<<"["<<g.op<<","<<g.a<<","<<g.b<<"]";}std::cout<<"]}"<<std::endl;}
std::vector<Gate>star(std::mt19937&rng){
 int cover=covers[rng()%5];std::array<std::vector<int>,10>neighbors;std::vector<int>centers;
 for(int i=0;i<10;i++)if((cover>>i)&1)centers.push_back(i);
 for(auto&e:E){int a=e[0],b=e[1];bool ca=(cover>>a)&1,cb=(cover>>b)&1;if(ca&&cb){if(rng()%2)neighbors[a].push_back(b);else neighbors[b].push_back(a);}else if(ca)neighbors[a].push_back(b);else neighbors[b].push_back(a);}
 std::shuffle(centers.begin(),centers.end(),rng);std::vector<Gate>c;std::vector<int>roots;int dup=0;
 if(rng()%4){int other=rng()%4?1:1+rng()%9;c.push_back({1,0,other});c.push_back({0,0,INPUTS});dup=INPUTS+1;}
 auto inp=[&](int i){return i==0?dup:i;};
 for(int center:centers){auto nb=neighbors[center];std::shuffle(nb.begin(),nb.end(),rng);int a=inp(nb[0]);for(int k=1;k<(int)nb.size();k++){int d=INPUTS+c.size();c.push_back({1,a,inp(nb[k])});a=d;}int d=INPUTS+c.size();c.push_back({0,inp(center),a});roots.push_back(d);}
 while(roots.size()>1){int ia=rng()%roots.size(),a=roots[ia];roots.erase(roots.begin()+ia);int ib=rng()%roots.size(),b=roots[ib];roots.erase(roots.begin()+ib);int d=INPUTS+c.size();c.push_back({1,a,b});roots.push_back(d);}return c;
}
Net deleted(std::vector<Gate>base,std::mt19937&rng){
 int protect=base.size()==22?2:0;
 while(base.size()>GATES){std::vector<int>eligible;for(int j=protect;j<(int)base.size()-1;j++)if(base[j].op==1&&(base[j].a<INPUTS||base[j].b<INPUTS))eligible.push_back(j);
  int rem=(!eligible.empty()&&rng()%4)?eligible[rng()%eligible.size()]:protect+rng()%(base.size()-1-protect),sub=base[rem].a>=INPUTS?base[rem].a:base[rem].b>=INPUTS?base[rem].b:rng()%2?base[rem].a:base[rem].b;
  base.erase(base.begin()+rem);for(auto&q:base){auto fix=[&](int v){if(v==INPUTS+rem)v=sub;if(v>INPUTS+rem)v--;return v;};q.a=fix(q.a);q.b=fix(q.b);}}
 Net c;std::copy(base.begin(),base.end(),c.begin());return c;
}
bool valid(const Net&c){for(int j=0;j<GATES;j++)if(c[j].a>=INPUTS+j||c[j].b>=INPUTS+j)return false;return true;}
void mutate(Net&c,std::mt19937&rng,int strength){
 for(int t=0;t<strength;t++){int j=rng()%GATES,kind=rng()%20;auto&g=c[j];
  if(kind<2)g.op=1-g.op;else if(kind<8)g.a=rng()%(INPUTS+j);else if(kind<14)g.b=rng()%(INPUTS+j);
  else if(kind==14)g={int(rng()%2),int(rng()%(INPUTS+j)),int(rng()%(INPUTS+j))};
  else if(kind==15){int old=rng()%(INPUTS+j),sub=rng()%(INPUTS+j);for(int k=j;k<GATES;k++){if(c[k].a==old)c[k].a=sub;if(c[k].b==old)c[k].b=sub;}}
  else if(kind==16){int old=INPUTS+j,sub=rng()%2?g.a:g.b;for(int k=j+1;k<GATES;k++){if(c[k].a==old)c[k].a=sub;if(c[k].b==old)c[k].b=sub;}}
  else if(kind==17){int h=rng()%GATES;std::swap(c[h].op,c[j].op);}
  else if(kind==18){int a=g.a,b=g.b;if(a<INPUTS)std::swap(a,b);if(a>=INPUTS){int h=a-INPUTS,uses=0;for(int k=h+1;k<GATES;k++)uses+=(c[k].a==a)+(c[k].b==a);if(uses==1&&c[h].op==g.op&&b<INPUTS+h){int old=c[h].b;c[h].b=b;g.a=a;g.b=old;}}}
  else{int h=rng()%GATES;if(h<j)std::swap(h,j);if(h!=j&&c[h].a<INPUTS+j&&c[h].b<INPUTS+j){std::swap(c[h],c[j]);for(int k=j+1;k<GATES;k++){if(c[k].a==INPUTS+j)c[k].a=INPUTS+h;else if(c[k].a==INPUTS+h)c[k].a=INPUTS+j;if(c[k].b==INPUTS+j)c[k].b=INPUTS+h;else if(c[k].b==INPUTS+h)c[k].b=INPUTS+j;}}}
 }
}
int main(int argc,char**argv){
 if(argc!=4)return 2;std::ifstream f(argv[1]);std::vector<int>rows;int row;while(f>>row)rows.push_back(row);if(rows.size()!=30)return 3;
 for(int k=0;k<30;k++){int r=rows[k];if(r==3)canonical=k;for(int i=0;i<10;i++)if((r>>i)&1)val[i]|=U(1)<<k;bool y=false;for(auto&e:E)y|=((r>>e[0])&(r>>e[1])&1);if(y)target|=U(1)<<k;else negative|=U(1)<<k;mask|=U(1)<<k;}if(canonical<0)return 4;
 std::mt19937 rng(std::stoul(argv[3]));int seconds=std::stoi(argv[2]);
 for(int t=0;t<128;t++){auto base=star(rng);std::vector<U>v(INPUTS+base.size());std::copy(val.begin(),val.begin()+INPUTS,v.begin());for(int j=0;j<(int)base.size();j++){auto g=base[j];v[INPUTS+j]=g.op?(v[g.a]|v[g.b]):(v[g.a]&v[g.b]);}if((v.back()&mask)!=target){std::cerr<<"positive seed failed"<<std::endl;return 5;}}
 std::cerr<<"PASS128 randomized positive seed controls"<<std::endl;
 auto start=std::chrono::steady_clock::now();auto elapsed=[&]{return std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();};
 Net best{};int bs=100000,braw=100000;std::vector<Net>pool;long long it=0;int restarts=0;
 while(elapsed()<seconds){Net c;if(!pool.empty()&&rng()%3){c=pool[rng()%pool.size()];mutate(c,rng,1+rng()%5);if(!valid(c))c=deleted(star(rng),rng);}else c=deleted(star(rng),rng);
  int sc=eval(c),cycle=30000+int(rng()%70000);double initial=.5+double(rng()%400)/100.0;
  for(int z=0;z<cycle;z++,it++){Net nc=c;int strength=1;auto rm=rng()%100;if(rm<10)strength=2;else if(rm<13)strength=3+rng()%4;mutate(nc,rng,strength);if(!valid(nc))continue;int ns=eval(nc),rr=raw;
   if(ns<bs||(ns==bs&&rr<braw)){bs=ns;braw=rr;best=nc;show(best,ns,it,elapsed());}if(!rr){show(nc,ns,it,elapsed());return 0;}
   if(ns<=bs+2&&rng()%200==0){if(pool.size()<128)pool.push_back(nc);else pool[rng()%pool.size()]=nc;}
   double temp=.04+initial*std::exp(-double(z)/(cycle/6.0));bool accept=ns<=sc||std::generate_canonical<double,32>(rng)<std::exp(double(sc-ns)/temp);if(accept){c=nc;sc=ns;}
  }restarts++;if(restarts%100==0){int sc=eval(best);show(best,sc,it,elapsed());}
 }int sc=eval(best);show(best,sc,it,elapsed());return 0;
}
