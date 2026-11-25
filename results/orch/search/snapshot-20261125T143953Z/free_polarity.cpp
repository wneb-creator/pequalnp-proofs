#include <array>
#include <vector>
#include <fstream>
#include <iostream>
#include <random>
#include <chrono>
#include <cmath>
#include <bit>
#include <cstdint>
using namespace std;
struct Gate{int op,a,b;};
using TT=array<uint64_t,16>;
mt19937_64 rng;
array<TT,10>inputs;TT target,critical;
vector<vector<Gate>>seeds;
uint64_t evaluations=0;
int count_gates;
int score(const vector<Gate>&c,int mode,int*plain=nullptr){
 array<TT,30>w;for(int i=0;i<10;i++)w[i]=inputs[i];
 for(int j=0;j<count_gates;j++){
  auto g=c[j];
  if(g.op==0)for(int k=0;k<16;k++)w[10+j][k]=w[g.a][k]&w[g.b][k];
  if(g.op==1)for(int k=0;k<16;k++)w[10+j][k]=w[g.a][k]|w[g.b][k];
  if(g.op==2)for(int k=0;k<16;k++)w[10+j][k]=w[g.a][k]&~w[g.b][k];
  if(g.op==3)for(int k=0;k<16;k++)w[10+j][k]=~w[g.a][k]&w[g.b][k];
 }
 int s=0,p=0;
 for(int k=0;k<16;k++){
  auto e=w[9+count_gates][k]^target[k];p+=popcount(e);s+=popcount(e);
  if(mode==1)s+=4*popcount(e&critical[k]);
  if(mode==2)s+=3*popcount(e&~target[k]);
 }
 if(plain)*plain=p;evaluations++;return s;
}
vector<Gate>initial(){
 auto c=seeds[rng()%seeds.size()];
 while((int)c.size()>count_gates){
  int drop=rng()%(c.size()-1),replacement=(rng()%2?c[drop].a:c[drop].b);
  c.erase(c.begin()+drop);
  for(auto&g:c){
   if(g.a==10+drop)g.a=replacement;else if(g.a>10+drop)g.a--;
   if(g.b==10+drop)g.b=replacement;else if(g.b>10+drop)g.b--;
  }
 }
 return c;
}
void dump(const vector<Gate>&c,int s,int p){
 cerr<<"score="<<s<<" errors="<<p<<" evaluations="<<evaluations<<"\n";
 for(int j=0;j<count_gates;j++)cerr<<10+j<<" "<<c[j].op<<" "<<c[j].a<<" "<<c[j].b<<"\n";
 cerr.flush();
}
void save(const vector<Gate>&c,const char*path){
 ofstream f(path);f<<"{\"signed_gates\":[\n";
 for(int j=0;j<count_gates;j++){
  auto g=c[j];int a=g.a>=10?g.a+1:g.a,b=g.b>=10?g.b+1:g.b;
  f<<"[\""<<(g.op==1?"OR":"AND")<<"\",[["<<a<<","<<(g.op==3?"true":"false")<<"],["<<b<<","<<(g.op==2?"true":"false")<<"]]]"<<(j+1==count_gates?"\n":",\n");
 }
 f<<"],\"output_sign\":false,\"correct_all_1024\":true,\"binary_gates\":"<<count_gates<<"}\n";
}
int main(int argc,char**argv){
 if(argc!=6)return 2;rng.seed(stoull(argv[1]));int seconds=stoi(argv[2]);count_gates=stoi(argv[3]);
 if(count_gates<1||count_gates>20)return 3;
 ifstream in(argv[4]);int ns;in>>ns;seeds.resize(ns,vector<Gate>(20));for(auto&s:seeds)for(auto&g:s)in>>g.op>>g.a>>g.b;
 vector<pair<int,int>>E={{0,1},{1,2},{2,3},{3,4},{4,0},{0,5},{1,6},{2,7},{3,8},{4,9},{5,7},{7,9},{9,6},{6,8},{8,5}};
 auto truth=[&](int r){for(auto[a,b]:E)if((r>>a&1)&&(r>>b&1))return true;return false;};
 for(int r=0;r<1024;r++){
  for(int i=0;i<10;i++)if(r>>i&1)inputs[i][r/64]|=1ull<<(r%64);
  bool t=truth(r);if(t)target[r/64]|=1ull<<(r%64);
  bool crit=t&&popcount((unsigned)r)==2;
  if(!t){crit=true;for(int i=0;i<10;i++)if(!(r>>i&1)&&!truth(r|(1<<i)))crit=false;}
  if(crit)critical[r/64]|=1ull<<(r%64);
 }
 auto start=chrono::steady_clock::now();uint64_t runs=0;int best=1024;
 while(chrono::duration<double>(chrono::steady_clock::now()-start).count()<seconds){
  auto c=initial();int mode=runs%3,s=score(c,mode);
  for(int j=0;j<100000;j++){
   int i=rng()%count_gates,mut=rng()%6;auto old=c[i];auto&g=c[i];
   if(mut==0)g.op=rng()%4;
   if(mut==1)g.a=rng()%(10+i);
   if(mut==2)g.b=rng()%(10+i);
   if(mut==3){g.a=rng()%(10+i);g.b=rng()%(10+i);}
   if(mut==4){g.op=rng()%4;g.a=rng()%(10+i);}
   if(mut==5){g.op=rng()%4;g.a=rng()%(10+i);g.b=rng()%(10+i);}
   int p=0,ns=score(c,mode,&p);
   if(p<best){best=p;dump(c,ns,p);}
   if(!p){save(c,argv[5]);cout<<"FOUND binary_gates="<<count_gates<<" evaluations="<<evaluations<<"\n";return 0;}
   double temp=0.05+(runs%5==4?3.0:0.6)*(1.0-(j%20000)/20000.0);
   bool take=ns<=s||generate_canonical<double,53>(rng)<exp((s-ns)/temp);
   if(take)s=ns;else c[i]=old;
  }
  runs++;if(runs%100==0)cerr<<"progress runs="<<runs<<" best="<<best<<" evaluations="<<evaluations<<"\n";
 }
 cerr<<"DONE runs="<<runs<<" best="<<best<<" evaluations="<<evaluations<<"\n";
}
