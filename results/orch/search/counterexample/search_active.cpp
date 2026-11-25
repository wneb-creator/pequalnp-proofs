#include <array>
#include <vector>
#include <random>
#include <iostream>
#include <fstream>
#include <chrono>
#include <algorithm>
#include <cmath>
#include <cstdint>
using namespace std;
using TT=array<uint64_t,16>;
struct Gate {int op,a,b;};
using Circuit=array<Gate,19>;
const vector<pair<int,int>> edges={{0,1},{1,2},{2,3},{3,4},{4,0},{0,5},{1,6},{2,7},{3,8},{4,9},{5,7},{7,9},{9,6},{6,8},{8,5}};
array<TT,30> base;
TT target;
vector<int> covers;
mt19937_64 rng;
int rnd(int n){return rng()%n;}
void init(){
 for(int x=0;x<1024;x++){
  for(int i=0;i<10;i++)if((x>>i)&1)base[i][x/64]|=1ull<<(x%64);
  bool f=false;for(auto [a,b]:edges)f|=((x>>a)&1)&&((x>>b)&1);
  if(f)target[x/64]|=1ull<<(x%64);
 }
 for(int m=0;m<1024;m++)if(__builtin_popcount((unsigned)m)==6){bool good=true;for(auto [a,b]:edges)if(!((m>>a)&1)&&!((m>>b)&1))good=false;if(good)covers.push_back(m);}
}
pair<int,int> score(const Circuit& c){
 auto w=base;
 for(int i=0;i<19;i++){
  auto g=c[i];for(int j=0;j<16;j++)w[i+10][j]=g.op==0?(w[g.a][j]&w[g.b][j]):g.op==1?(w[g.a][j]|w[g.b][j]):~w[g.a][j];
 }
 int fp=0,fn=0;for(int j=0;j<16;j++){fp+=__builtin_popcountll(w[28][j]&~target[j]);fn+=__builtin_popcountll(~w[28][j]&target[j]);}
 return {fp,fn};
}
Circuit start(){
 vector<Gate> v;int mask=covers[rnd(covers.size())];
 vector<vector<int>> ns(10);
 for(auto [a,b]:edges){int ctr;if(!((mask>>a)&1))ctr=b;else if(!((mask>>b)&1))ctr=a;else ctr=rnd(2)?a:b;ns[ctr].push_back(ctr==a?b:a);}
 vector<int> order,terms;for(int i=0;i<10;i++)if(!ns[i].empty())order.push_back(i);shuffle(order.begin(),order.end(),rng);
 for(int i:order){shuffle(ns[i].begin(),ns[i].end(),rng);int a=ns[i][0];for(int j=1;j<(int)ns[i].size();j++){v.push_back({1,a,ns[i][j]});a=9+v.size();}v.push_back({0,i,a});terms.push_back(9+v.size());}
 while(terms.size()>1){int i=rnd(terms.size());int a=terms[i];terms.erase(terms.begin()+i);i=rnd(terms.size());int b=terms[i];terms.erase(terms.begin()+i);v.push_back({1,a,b});terms.push_back(9+v.size());}
 if(v.size()!=20)abort();
 int drop=rnd(19);int rep=rnd(2)?v[drop].a:v[drop].b;
 v.erase(v.begin()+drop);
 for(auto&g:v)for(int*p:{&g.a,&g.b}){if(*p==10+drop)*p=rep;else if(*p>10+drop)--*p;}
 Circuit c;copy(v.begin(),v.end(),c.begin());return c;
}
int activeNots(const Circuit& c){
 bool active[29]={}; active[28]=true;int n=0;
 for(int i=18;i>=0;i--)if(active[i+10]){active[c[i].a]=true;if(c[i].op!=2)active[c[i].b]=true;else n++;}
 return n;
}
int countNots(const Circuit& c){int n=0;for(auto g:c)n+=g.op==2;return n;}
Circuit reorder(Circuit c){
 Circuit result; bool used[19]={};int map[29];for(int i=0;i<10;i++)map[i]=i;
 for(int j=0;j<19;j++){
  vector<int> ready;for(int i=0;i<19;i++)if(!used[i]&&(i!=18||j==18)&&(c[i].a<10||used[c[i].a-10])&&(c[i].op==2||c[i].b<10||used[c[i].b-10]))ready.push_back(i);
  if(ready.empty())return c;
  int i=ready[rnd(ready.size())];used[i]=true;map[i+10]=j+10;result[j]={c[i].op,map[c[i].a],c[i].op==2?0:map[c[i].b]};
 }
 return result;
}
void dump(const Circuit&c,const string&path){ofstream f(path);for(int i=0;i<19;i++)f<<i+10<<" "<<c[i].op<<" "<<c[i].a<<" "<<c[i].b<<"\n";}
int main(int argc,char**argv){
 int seed=argc>1?stoi(argv[1]):1,seconds=argc>2?stoi(argv[2]):600;
 string path=argc>3?argv[3]:"best.txt";rng.seed(seed);init();
 Circuit warm;bool warmOK=false;
 if(argc>4){ifstream f(argv[4]);int wire;warmOK=true;for(auto&g:warm)if(!(f>>wire>>g.op>>g.a>>g.b))warmOK=false;}
 auto t0=chrono::steady_clock::now();long long trials=0,restarts=0;int global=1000000;pair<int,int> gb;
 while(chrono::duration<double>(chrono::steady_clock::now()-t0).count()<seconds){
  Circuit c=warmOK&&rnd(4)?reorder(warm):start();auto s=score(c);int weight=(restarts%3==0?6:restarts%3==1?3:1);int fit=s.first*weight+s.second+(activeNots(c)==0?12:0);
  const int steps=200000;
  for(int k=0;k<steps;k++){
   Circuit next=c;int i=rnd(19);int kind=rnd(10);
   if(kind<2)next[i].op=rnd(3);
   else if(kind<6)next[i].a=rnd(10+i);
   else next[i].b=rnd(10+i);
   if(rnd(30)==0){int j=rnd(19);next[j].op=rnd(3);next[j].a=rnd(10+j);next[j].b=rnd(10+j);}
   if(countNots(next)>3)continue;auto ns=score(next);int nf=ns.first*weight+ns.second+(activeNots(next)==0?12:0);
   double temp=0.15+3.5*(1.0-double(k%50000)/50000.0);
   if(nf<=fit||uniform_real_distribution<double>(0,1)(rng)<exp((fit-nf)/temp)){c=next;fit=nf;s=ns;}
   int total=s.first+s.second;
   if(total<global&&activeNots(c)>0){global=total;gb=s;dump(c,path);cout<<"seed="<<seed<<" sec="<<chrono::duration<double>(chrono::steady_clock::now()-t0).count()<<" trials="<<trials<<" errors="<<global<<" fp="<<s.first<<" fn="<<s.second<<endl;if(!global)return 0;}
   trials++;
  }
  restarts++;
 }
 cout<<"DONE seed="<<seed<<" trials="<<trials<<" restarts="<<restarts<<" best="<<global<<" fp="<<gb.first<<" fn="<<gb.second<<endl;
}
