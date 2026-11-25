#include <array>
#include <vector>
#include <random>
#include <chrono>
#include <iostream>
#include <algorithm>
#include <csignal>
using namespace std;
using Word=unsigned long long;
using Bits=array<Word,16>;
constexpr int N=24, B=11, OUTPUT=B+N-1;
struct Gate{int op,a,b;};
using Circuit=array<Gate,N>;
using Values=array<Bits,B+N>;
mt19937 rng;
volatile sig_atomic_t stopFlag=0;
void stopped(int){stopFlag=1;}
array<Bits,B> inputs;
Bits target;
vector<pair<int,int>> edges={{0,1},{1,2},{2,3},{3,4},{4,0},{0,5},{1,6},{2,7},{3,8},{4,9},{5,7},{7,9},{9,6},{6,8},{8,5}};
vector<int> covers;
int cost(const Circuit& c){
 array<bool,B+N> used{};used[OUTPUT]=true;bool neg=false;int n=0;
 for(int i=N-1;i>=0;i--)if(used[B+i]){n++;auto g=c[i];neg|=g.op==2;used[g.a]=true;if(g.op!=2)used[g.b]=true;}
 return n+!neg;
}
Values values(const Circuit&c){
 Values w;for(int j=0;j<B;j++)w[j]=inputs[j];
 for(int i=0;i<N;i++){auto g=c[i];for(int k=0;k<16;k++)w[B+i][k]=g.op==0?w[g.a][k]&w[g.b][k]:g.op==1?w[g.a][k]|w[g.b][k]:~w[g.a][k];}
 return w;
}
int score(const Circuit&c){
 auto w=values(c);int err=0;for(int k=0;k<16;k++)err+=__builtin_popcountll(w[OUTPUT][k]^target[k]);
 return err*128+cost(c);
}
Bits forceOutput(const Circuit&c,Values w,int i,Word v){
 w[B+i].fill(v);
 for(int j=i+1;j<N;j++){auto g=c[j];for(int k=0;k<16;k++)w[B+j][k]=g.op==0?w[g.a][k]&w[g.b][k]:g.op==1?w[g.a][k]|w[g.b][k]:~w[g.a][k];}
 return w[OUTPUT];
}
int coordinate(Circuit&c,int i,int temp){
 array<bool,B+N> live{};live[OUTPUT]=true;
 for(int j=N-1;j>=0;j--)if(live[B+j]){auto g=c[j];live[g.a]=true;if(g.op!=2)live[g.b]=true;}
 if(!live[B+i]){c[i]={int(rng()%3),int(rng()%(B+i)),int(rng()%(B+i))};return score(c);}
 auto w=values(c);Bits f0=forceOutput(c,w,i,0),f1=forceOutput(c,w,i,~0ULL),care,want;
 for(int k=0;k<16;k++){care[k]=f0[k]^f1[k];want[k]=target[k]^f0[k];}
 int best=100000000,count=0;Gate selected=c[i];
 for(int op=0;op<3;op++)for(int a=0;a<B+i;a++)for(int b=(op==2?a:0);b<=a;b++){
  int err=0;
  for(int k=0;k<16;k++){Word v=op==0?w[a][k]&w[b][k]:op==1?w[a][k]|w[b][k]:~w[a][k];err+=__builtin_popcountll((v^want[k])&care[k]);}
  Gate old=c[i];c[i]={op,a,b};int sc=err*128+cost(c);c[i]=old;
  if(temp)sc+=rng()%(temp+1);
  if(sc<best){best=sc;count=1;selected={op,a,b};}else if(sc==best&&rng()%++count==0)selected={op,a,b};
 }
 c[i]=selected;return score(c);
}

int resubstitute(Circuit&c){
 array<bool,B+N> live{};live[OUTPUT]=true;
 for(int j=N-1;j>=0;j--)if(live[B+j]){auto g=c[j];live[g.a]=true;if(g.op!=2)live[g.b]=true;}
 vector<pair<int,int>> pairs;
 for(int j=0;j<N-1;j++)if(!live[B+j])for(int i=j+1;i<N;i++)if(live[B+i])pairs.push_back({j,i});
 if(pairs.empty())return score(c);
 auto [j,i]=pairs[rng()%pairs.size()];auto w=values(c);
 Bits f0=forceOutput(c,w,i,0),f1=forceOutput(c,w,i,~0ULL),care,want;
 for(int z=0;z<16;z++){care[z]=f0[z]^f1[z];want[z]=target[z]^f0[z];}
 int best=cost(c),count=1;Gate keepJ=c[j],keepI=c[i],oldJ=c[j],oldI=c[i];
 for(int op=0;op<3;op++)for(int a=0;a<B+j;a++)for(int b=(op==2?a:0);b<=a;b++){
  Bits h;for(int z=0;z<16;z++)h[z]=op==0?w[a][z]&w[b][z]:op==1?w[a][z]|w[b][z]:~w[a][z];
  for(int op2=0;op2<3;op2++)for(int d=0;d<(op2==2?1:B+j);d++){
   bool correct=true;
   for(int z=0;z<16;z++){
    Word v=op2==0?h[z]&w[d][z]:op2==1?h[z]|w[d][z]:~h[z];
    if((v^want[z])&care[z]){correct=false;break;}
   }
   if(!correct)continue;
   c[j]={op,a,b};c[i]={op2,B+j,d};int sc=cost(c);
   if(sc<best){best=sc;count=1;keepJ=c[j];keepI=c[i];}
   else if(sc==best&&rng()%++count==0){keepJ=c[j];keepI=c[i];}
  }
 }
 c[j]=keepJ;c[i]=keepI;return score(c);
}
Circuit seed(){
 int cover=covers[rng()%covers.size()];array<vector<int>,10> star;
 for(auto[a,b]:edges){if((cover>>a&1)&&(cover>>b&1)){if(rng()%2)swap(a,b);}else if(!(cover>>a&1))swap(a,b);star[a].push_back(b);}
 vector<int> centers;for(int v=0;v<10;v++)if(!star[v].empty())centers.push_back(v);shuffle(centers.begin(),centers.end(),rng);
 vector<Gate>g;vector<int>roots;
 for(int v:centers){shuffle(star[v].begin(),star[v].end(),rng);int cur=star[v][0];for(size_t j=1;j<star[v].size();j++){g.push_back({1,cur,star[v][j]});cur=B+g.size()-1;}g.push_back({0,v,cur});roots.push_back(B+g.size()-1);}
 shuffle(roots.begin(),roots.end(),rng);int cur=roots[0];for(size_t j=1;j<roots.size();j++){g.push_back({1,cur,roots[j]});cur=B+g.size()-1;}
 while(g.size()<N){int pos=rng()%g.size();for(size_t i=pos;i<g.size();i++)for(int*p:{&g[i].a,&g[i].b})if(*p>=B+pos)++*p;g.insert(g.begin()+pos,{int(rng()%3),int(rng()%(B+pos)),int(rng()%(B+pos))});}
 Circuit c;copy(g.begin(),g.end(),c.begin());return c;
}
void reorder(Circuit&c){
 int i=rng()%(N-2);auto next=c[i+1];
 if(next.a==B+i || (next.op!=2 && next.b==B+i))return;
 swap(c[i],c[i+1]);
 for(int j=i+2;j<N;j++)for(int*p:{&c[j].a,&c[j].b}){
  if(*p==B+i)++*p;else if(*p==B+i+1)--*p;
 }
}
void show(const Circuit&c,int s,long long trial){cout<<"best "<<s<<" trial "<<trial<<" gates [";for(auto g:c)cout<<"("<<g.op<<","<<g.a<<","<<g.b<<"),";cout<<"]"<<endl;}
int main(int argc,char**argv){signal(SIGINT,stopped);signal(SIGTERM,stopped);rng.seed(argc>1?stoul(argv[1]):259204);int secs=argc>2?stoi(argv[2]):1200;
 for(int x=0;x<1024;x++){for(int j=0;j<10;j++)if(x>>j&1)inputs[j][x/64]|=1ULL<<(x%64);for(auto[a,b]:edges)if((x>>a&1)&&(x>>b&1)){target[x/64]|=1ULL<<(x%64);break;}}
 for(int c=0;c<1024;c++)if(__builtin_popcount((unsigned)c)==6){bool yes=true;for(auto[a,b]:edges)if(!(c>>a&1)&&!(c>>b&1))yes=false;if(yes)covers.push_back(c);}
 auto start=chrono::steady_clock::now();int global=1000000;long long trial=0;
 for(int run=0;;run++){
  Circuit c=seed();int s=score(c);if(s<global){global=s;show(c,s,trial);}
  for(int iter=0;iter<15000;iter++,trial++){
   if(trial%1000==0&&(stopFlag||chrono::duration<double>(chrono::steady_clock::now()-start).count()>secs)){cout<<"done "<<trial<<" best "<<global<<endl;return 0;}
   int temp=(iter%2000<1000)?2:(iter%2000<1500?6:12);
   s=coordinate(c,rng()%N,temp);
   if(iter%100==0 && s<128){s=resubstitute(c);if(s>=128){cerr<<"FAULT resubstitution"<<endl;return 2;}}
   if(iter%10==0){for(int j=0;j<20;j++)reorder(c);if(score(c)!=s){cerr<<"FAULT reorder"<<endl;return 2;}}
   if(s<global){global=s;show(c,s,trial);if(s<=19)return 0;}
  }
 }
}
