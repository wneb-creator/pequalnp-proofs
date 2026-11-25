#include <array>
#include <bit>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <random>
#include <vector>
#include <algorithm>

using TT=std::array<uint64_t,16>;
struct Gate {int op,a,b;};
using Circuit=std::array<Gate,19>;
std::mt19937 rng;
std::array<TT,10> inputs;
TT target;
std::vector<std::pair<int,int>> edges={{0,1},{1,2},{2,3},{3,4},{4,0},{0,5},{1,6},{2,7},{3,8},{4,9},{5,7},{7,9},{9,6},{6,8},{8,5}};
int r(int n){return rng()%n;}
int loss(const Circuit& c){
 std::array<TT,29> w;
 for(int i=0;i<10;i++)w[i]=inputs[i];
 int nc=0;
 for(int i=0;i<19;i++){
  auto g=c[i];nc+=g.op==2;
  for(int j=0;j<16;j++)w[10+i][j]=g.op==0?(w[g.a][j]&w[g.b][j]):g.op==1?(w[g.a][j]|w[g.b][j]):~w[g.a][j];
 }
 int fp=0,fn=0;
 for(int j=0;j<16;j++){fp+=std::popcount(w[28][j]&~target[j]);fn+=std::popcount(~w[28][j]&target[j]);}
#ifdef ACTIVE_NOT
 bool active[29]={};active[28]=true;int an=0;
 for(int i=18;i>=0;i--)if(active[10+i]){auto g=c[i];an+=g.op==2;active[g.a]=true;if(g.op!=2)active[g.b]=true;}
 return fn+13*fp+(an==0?1000:0)+(nc>3?1000:0);
#else
 return fn+13*fp+(nc==0?1000:0);
#endif
}
void print(const Circuit& c,int score,long long it){
 std::cout<<"score="<<score<<" iteration="<<it<<" gates=[";
 for(int i=0;i<19;i++)std::cout<<(i?",":"")<<"["<<c[i].op<<","<<c[i].a<<","<<c[i].b<<"]";
 std::cout<<"]"<<std::endl;
}
Circuit seed(){
 int independent[5]={116,201,402,554,773};
 int mask=independent[r(5)];
 std::vector<int> cover;
 for(int i=0;i<10;i++)if(!(mask>>i&1))cover.push_back(i);
 std::shuffle(cover.begin(),cover.end(),rng);
 std::array<std::vector<int>,10> stars;
 for(auto [a,b]:edges){
  if(mask>>a&1)stars[b].push_back(a);
  else if(mask>>b&1)stars[a].push_back(b);
  else if(r(2))stars[a].push_back(b);
  else stars[b].push_back(a);
 }
 std::vector<Gate> gs;
 std::vector<int> outs;
 for(int a:cover){
  auto vs=stars[a];
  if(vs.empty())continue;
  std::shuffle(vs.begin(),vs.end(),rng);
  int wire=vs[0];
  for(size_t j=1;j<vs.size();j++){gs.push_back({1,wire,vs[j]});wire=9+gs.size();}
  gs.push_back({0,a,wire});outs.push_back(9+gs.size());
 }
 std::shuffle(outs.begin(),outs.end(),rng);
 while(outs.size()>1){
  int a=outs.back();outs.pop_back();int b=outs.back();outs.pop_back();
  gs.push_back({1,a,b});outs.push_back(9+gs.size());
 }
 if(gs.size()!=20){std::cerr<<"bad seed "<<gs.size()<<std::endl;exit(2);}
 int del=r(19),rep=r(2)?gs[del].a:gs[del].b;
 Circuit c;
 for(int i=0,j=0;i<20;i++)if(i!=del){
  auto g=gs[i];
  auto fix=[&](int x){if(x==10+del)x=rep;return x>10+del?x-1:x;};
  c[j++]={g.op,fix(g.a),fix(g.b)};
 }
 c[r(19)].op=2;
 return c;
}
int main(int argc,char**argv){
 if(argc<3){std::cout<<"usage: evolve SEED SECONDS\n";return 0;}
 rng.seed(std::stoul(argv[1]));int seconds=std::stoi(argv[2]);
 for(int x=0;x<1024;x++){
  for(int i=0;i<10;i++)if(x>>i&1)inputs[i][x/64]|=uint64_t(1)<<(x%64);
  bool t=false;for(auto [a,b]:edges)t|=(x>>a&1)&&(x>>b&1);
  if(t)target[x/64]|=uint64_t(1)<<(x%64);
 }
 auto start=std::chrono::steady_clock::now();
 int best=100000;long long it=0;
 while(std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<seconds){
  Circuit c=seed();int score=loss(c),local=score,stale=0;
  for(int k=0;k<300000;k++,it++){
   Circuit d=c;int changes=1+(r(100)<10?1+r(3):0);
   for(int z=0;z<changes;z++){
    int i=r(19),mode=r(4);
    if(mode==0){int no=0;for(auto g:d)no+=g.op==2;if(d[i].op==2){int j=r(19);d[i].op=r(2);d[j].op=2;}else d[i].op=r(3);}
    else if(mode==1)d[i].a=r(10+i);
    else if(mode==2)d[i].b=r(10+i);
    else{d[i].a=r(10+i);d[i].b=r(10+i);}
   }
   int ds=loss(d);
   if(ds<=score){c=d;score=ds;}else if(r(1000000)<20){c=d;score=ds;}
   if(score<local){local=score;stale=0;}else stale++;
   if(score<best){best=score;print(c,score,it);}
   if(score==0)return 0;
   if(stale>50000)break;
  }
 }
 std::cout<<"finished best="<<best<<" iterations="<<it<<std::endl;
}
