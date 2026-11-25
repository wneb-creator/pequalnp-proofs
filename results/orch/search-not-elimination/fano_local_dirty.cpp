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
struct Gate { int op,a,b; };
using Net=std::array<Gate,26>;
std::array<U,40> val;
U target=0,negative=0,mask=0;
int lastRaw=100000,lastFp=100000;
int canonicalBit=-1;
int eval(const Net& c,int weight) {
 for(int j=0;j<26;j++){const auto&g=c[j];val[14+j]=g.op?(val[g.a]|val[g.b]):(val[g.a]&val[g.b]);}
 U err=(target^val[39])&mask;
 lastRaw=std::popcount(err);lastFp=std::popcount(err&negative);
 unsigned char good[40]={};good[0]=1;good[7]=2;
 for(int j=0;j<26;j++){auto g=c[j];int a=good[g.a],b=good[g.b];good[14+j]=g.op?(a|b):(((a&1)&&(b&2))||((a&2)&&(b&1))?4:0);}
 int penalty=((good[39]&4)?4:0)+(((val[39]>>canonicalBit)&1)?0:4);
 for(int j=0;j<26;j++){for(int i=0;i<14+j;i++)if((val[14+j]&mask)==(val[i]&mask)){penalty+=2;break;}}
 return lastRaw+(weight-1)*lastFp+penalty;
}
void show(const Net& c,int score,long long it,int weight,double seconds) {
 std::cout<<"{\"seconds\":"<<seconds<<",\"score\":"<<score<<",\"raw\":"<<lastRaw<<",\"fp\":"<<lastFp<<",\"iterations\":"<<it<<",\"weight\":"<<weight<<",\"gates\":[";
 for(int j=0;j<26;j++){auto g=c[j];if(j)std::cout<<",";std::cout<<"["<<g.op<<","<<g.a<<","<<g.b<<"]";}
 std::cout<<"]}"<<std::endl;
}
std::vector<Gate> star(std::mt19937& rng) {
 std::vector<Gate> c;std::vector<int> roots;
 std::array<int,7> order;std::iota(order.begin(),order.end(),0);std::shuffle(order.begin(),order.end(),rng);
 bool sides=rng()%2;
 for(int i:order){std::vector<int> nb;for(int j=0;j<7;j++)if((sides?(j-i+7)%7:(i-j+7)%7)==0||(sides?(j-i+7)%7:(i-j+7)%7)==1||(sides?(j-i+7)%7:(i-j+7)%7)==3)nb.push_back(sides?j:7+j);
  std::shuffle(nb.begin(),nb.end(),rng);int a=14+c.size();c.push_back({1,nb[0],nb[1]});int b=14+c.size();c.push_back({1,a,nb[2]});int d=14+c.size();c.push_back({0,sides?7+i:i,b});roots.push_back(d);
 }
 while(roots.size()>1){int ia=rng()%roots.size(),a=roots[ia];roots.erase(roots.begin()+ia);int ib=rng()%roots.size(),b=roots[ib];roots.erase(roots.begin()+ib);int d=14+c.size();c.push_back({1,a,b});roots.push_back(d);}
 return c;
}
Net deleteGate(std::vector<Gate> base,std::mt19937& rng){
 int rem=rng()%26,sub=rng()%2?base[rem].a:base[rem].b;Net c;
 for(int j=0,p=0;j<27;j++)if(j!=rem){auto q=base[j];auto fix=[&](int v){if(v==14+rem)v=sub;if(v>14+rem)v--;return v;};q.a=fix(q.a);q.b=fix(q.b);c[p++]=q;}
 return c;
}
void mutate(Net& c,std::mt19937& rng,int strength){
 for(int t=0;t<strength;t++){
  int j=rng()%26,kind=rng()%16;auto&g=c[j];
  if(kind<2)g.op=1-g.op;
  else if(kind<7)g.a=rng()%(14+j);
  else if(kind<12)g.b=rng()%(14+j);
  else if(kind==12){g={int(rng()%2),int(rng()%(14+j)),int(rng()%(14+j))};}
  else if(kind==13){int old=rng()%(14+j),sub=rng()%(14+j);for(int k=j;k<26;k++){if(c[k].a==old)c[k].a=sub;if(c[k].b==old)c[k].b=sub;}}
  else if(kind==14){int h=rng()%26;if(h<j)std::swap(h,j);if(h!=j&&c[h].a!=14+j&&c[h].b!=14+j&&c[h].a<14+j&&c[h].b<14+j){std::swap(c[h],c[j]);for(int k=j+1;k<26;k++){if(c[k].a==14+j)c[k].a=14+h;else if(c[k].a==14+h)c[k].a=14+j;if(c[k].b==14+j)c[k].b=14+h;else if(c[k].b==14+h)c[k].b=14+j;}bool valid=true;for(int k=0;k<26;k++)if(c[k].a>=14+k||c[k].b>=14+k)valid=false;if(!valid)return;}}
  else {int old=14+j,sub=rng()%2?g.a:g.b;for(int k=j+1;k<26;k++){if(c[k].a==old)c[k].a=sub;if(c[k].b==old)c[k].b=sub;}}
 }
}
int main(int argc,char**argv){
 if(argc!=4)return 2;std::ifstream f(argv[1]);int row;std::vector<int> rows;while(f>>row)rows.push_back(row);if(rows.size()!=58)return 3;
 std::mt19937 rng(std::stoul(argv[3]));int seconds=std::stoi(argv[2]);
 for(int k=0;k<58;k++){int r=rows[k];if(r==129)canonicalBit=k;for(int i=0;i<14;i++)if((r>>i)&1)val[i]|=U(1)<<k;bool b=false;for(int p=0;p<7;p++)for(int l=0;l<7;l++)if(((p-l+7)%7==0||(p-l+7)%7==1||(p-l+7)%7==3)&&((r>>p)&1)&&((r>>(7+l))&1))b=true;if(b)target|=U(1)<<k;else negative|=U(1)<<k;mask|=U(1)<<k;}
 auto start=std::chrono::steady_clock::now();auto elapsed=[&]{return std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();};
 std::vector<Net> pool;Net best{};int bestRaw=100000,bestScore=100000;long long it=0;int restarts=0;
 while(elapsed()<seconds){
  int weight=1;Net c;
  if(!pool.empty()&&rng()%3){c=pool[rng()%pool.size()];mutate(c,rng,1+rng()%5);}else c=deleteGate(star(rng),rng);
  int sc=eval(c,weight);int cycle=30000+int(rng()%70000);double initial=0.4+double(rng()%200)/100.0;
  for(int z=0;z<cycle;z++,it++){
   Net nc=c;int strength=1;auto rm=rng()%100;if(rm<8)strength=2;else if(rm<10)strength=3+rng()%4;mutate(nc,rng,strength);
   bool valid=true;for(int j=0;j<26;j++)if(nc[j].a>=14+j||nc[j].b>=14+j)valid=false;if(!valid)continue;
   int ns=eval(nc,weight);int rr=lastRaw;
   if(ns<bestScore||(ns==bestScore&&rr<bestRaw)){bestRaw=rr;bestScore=ns;best=nc;show(best,ns,it,weight,elapsed());}
   if(rr==0)return 0;
   if(ns<=bestScore+2&&rng()%300==0){if(pool.size()<128)pool.push_back(nc);else pool[rng()%pool.size()]=nc;}
   double temp=0.04+initial*std::exp(-double(z)/(cycle/6.0));
   bool accept=ns<=sc||std::generate_canonical<double,32>(rng)<std::exp(double(sc-ns)/temp);
   if(accept){c=nc;sc=ns;}
  }
  restarts++;if(restarts%100==0){eval(best,1);show(best,lastRaw,it,1,elapsed());}
 }
 eval(best,1);show(best,lastRaw,it,1,elapsed());return 0;
}
